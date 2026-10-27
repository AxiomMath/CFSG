module

public import Certificates.Data.Kernel.LyGlue.Defs
public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.KC.LyGlue

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.Certificates.Kernel.PkCV

instance : Small 243 := ⟨by decide⟩
instance : Small 1080 := ⟨by decide⟩
instance : Small 66825 := ⟨by decide⟩

variable {n : Nat} [hs : Small n]

@[expose] noncomputable def wordC (L : Int → CV n) : List Int → CV n
  | [] => 1
  | l :: ws => L l * wordC L ws

theorem wprod_eq (L : Int → CV n) {F : Int → Nat} :
    ∀ ws : List Int, (∀ l ∈ ws, F l = (L l).1) →
      wprod n (wC n) (mask (wC n)) F ws = (wordC L ws).1
  | [], _ => rfl
  | l :: ws, h => by
    change strictN (wprod n (wC n) (mask (wC n)) F ws)
      (fun q => pcomp n (wC n) (mask (wC n)) (F l) q) = _
    rw [strictN_eqP, wprod_eq L ws (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')),
      h l List.mem_cons_self]
    rfl

theorem wpt_eq (L : Int → CV n) {F : Int → Nat} {a : Nat} (ha : a < n) :
    ∀ ws : List Int, (∀ l ∈ ws, F l = (L l).1) →
      wpt (wC n) (mask (wC n)) F ws a = img n (wordC L ws).1 a
  | [], _ => by
    change a = pg (wC n) (mask (wC n)) (pidn n (wC n)) a
    exact (CFSG.KS.PF.pg_pidn hs.lt (lt_wC n) ha).symm
  | l :: ws, h => by
    change pg (wC n) (mask (wC n)) (F l) (wpt (wC n) (mask (wC n)) F ws a) =
      pg (wC n) (mask (wC n)) (pcomp n (wC n) (mask (wC n)) (L l).1 (wordC L ws).1) a
    rw [wpt_eq L ha ws (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')), h l List.mem_cons_self,
      pg_pcomp lt32 ha]

theorem ev_wordC (L : Int → CV n) (ws : List Int) :
    ev (wordC L ws) = CFSG.Sporadic.Th.wordG (fun l => ev (L l)) ws := by
  induction ws with
  | nil => exact ev_one
  | cons l ws ih =>
    change ev (L l * wordC L ws) = ((l :: ws).map _).prod
    rw [ev_mul, ih, List.map_cons, List.prod_cons]
    rfl

end CFSG.KC.LyGlue

end
