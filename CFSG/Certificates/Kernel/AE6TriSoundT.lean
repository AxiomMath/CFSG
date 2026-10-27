module

public import Certificates.Data.Kernel.AE6Tri.DefsTAT
public import CFSG.Certificates.Kernel.AE6TriSound

public section

namespace CFSG.KC.AE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KS.Raw

@[expose] def tv (g : Nat → Equiv.Perm (Fin 360)) :
    List (List (List Nat)) → Nat → Equiv.Perm (Fin 360)
  | [] => g
  | lv :: S => tv (fun c => wv g (lv.getD c [])) S

@[expose] noncomputable def tabL (G : List Nat) : List (List (List Nat)) → List Nat
  | [] => G
  | lv :: S => tabL (lv.map fun w => awN G w) S

theorem tabOf_eq (S : List (List (List Nat))) (k : List Nat → Bool) :
    ∀ G : List Nat, tabOf G S k = k (tabL G S) := by
  induction S with
  | nil => intro G; rfl
  | cons lv S ih =>
    intro G
    change forceMap lv (fun w => awN G w) (fun T => tabOf T S k) = _
    rw [forceMap_eq, ih]
    rfl

theorem tabL_rep {G : List Nat} {g : Nat → Equiv.Perm (Fin 360)} (hG : GRep G g) :
    ∀ S, GRep (tabL G S) (tv g S)
  | [] => hG
  | lv :: S => tabL_rep (G := lv.map fun w => awN G w) (fun c => prep_mapAw hG lv c) S

theorem tabEq_sound {G : List Nat} {g : Nat → Equiv.Perm (Fin 360)} (hG : GRep G g)
    {A B : List (List (List Nat))} {R : List Nat} (h : tabEq G A B R = true) :
    ∀ c ∈ R, tv g A c = tv g B c := by
  unfold tabEq at h
  simp only [tabOf_eq] at h
  intro c hc
  obtain ⟨_, e⟩ := allIx_mem h c hc
  exact (eqN_iff (tabL_rep hG A c) (tabL_rep hG B c)).1 e

end CFSG.KC.AE6Tri

end
