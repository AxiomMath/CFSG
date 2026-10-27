
module

public import Certificates.Data.Kernel.GH74Tab.Adm
public import CFSG.GH74.GLS.C3.Layer2.L4ModelGen

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2.Model

variable {n : ℕ} [NeZero n] (t : Tab n)

theorem finalG_mono_of {P Q : Tbl → Fin 64 → Bool} (hPQ : ∀ a u, P a u = true → Q a u = true)
    {a : Tbl} (h : t.finalG P a = true) : t.finalG Q a = true := by
  unfold Tab.finalG at h ⊢
  simp only [imp_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h ⊢
  intro h1 u h2 h3 h4 h5
  exact hPQ _ _ (h h1 u h2 h3 h4 h5)

theorem claimG_mono_of {P Q : Tbl → Fin 64 → Bool} (hPQ : ∀ a u, P a u = true → Q a u = true)
    (h : t.claimG P = true) : t.claimG Q = true := by
  unfold Tab.claimG at h ⊢
  simp only [imp_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h ⊢
  intro h0 o0 h1 o1 h2 o2 h3 o3 ha
  exact finalG_mono_of t hPQ (h h0 o0 h1 o1 h2 o2 h3 o3 ha)

theorem claimG_of_adm (L : List (Nat × Nat)) {P : Tbl → Fin 64 → Bool}
    (hS : t.claimG (admP L) = true) (hP : ∀ p ∈ L, P (tblOf p.1) (f64 p.2) = true) :
    t.claimG P = true := by
  refine claimG_mono_of t (fun a u h => ?_) hS
  simp only [admP, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨p, hp, rfl, rfl⟩ := h
  exact hP p hp

end CFSG.KC.GH74Tab

end
