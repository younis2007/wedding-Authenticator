import { createClient } from "@supabase/supabase-js";

const url = import.meta.env.VITE_SUPABASE_URL;
const key = import.meta.env.VITE_SUPABASE_ANON_KEY;

// Falls back to null (local-only state, no persistence) when the env vars aren't
// configured — lets the app keep working in dev/preview contexts without a backend.
export const supabase = url && key ? createClient(url, key) : null;
