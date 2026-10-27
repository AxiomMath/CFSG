module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppELoc

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem not_conj_inv_le {B Q U W : Subgroup G} {q : ℕ} (h : C5.Rank1 B Q U W q) {x : G}
    (hx : x ∈ normalizer (B : Set G)) (hx1 : ¬ conjSubgroup U x ≤ Q) :
    ¬ conjSubgroup U x⁻¹ ≤ Q := by
  intro hle
  apply hx1
  have h1 : conjSubgroup (conjSubgroup U x⁻¹) x ≤ conjSubgroup Q x := conjSubgroup_mono hle x
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, h.conj_Q_eq hx] at h1
  intro v hv
  rw [h.Q_eq]
  refine ⟨h.conj_le_B hx hv, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  exact ((Subgroup.mem_centralizer_iff.1 (h1 hu).2 v hv)).symm

structure KFacts (B L U Q W : Subgroup G) (x : G) : Prop where
  supQ : conjSubgroup U x ⊔ Q = B
  commU : ⁅U, conjSubgroup U x⁆ = W
  infU : U ⊓ conjSubgroup U x = W
  W_conj : conjSubgroup W x = W
  infQ : conjSubgroup U x ⊓ Q = W
  infC : U ⊓ centralizer (conjSubgroup U x : Set G) = W
  Q_eq : Q = U ⊔ (Q ⊓ centralizer (L : Set G))
  D_le : Q ⊓ centralizer (L : Set G) ≤ conjSubgroup Q x
  Qx : conjSubgroup Q x = B ⊓ centralizer (conjSubgroup U x : Set G)
  U_le_B : U ≤ B
  Ux_le_B : conjSubgroup U x ≤ B

theorem Loc.kfacts {B L U Q W : Subgroup G} {q : ℕ} (h : Loc B L U Q W q) {x : G}
    (hx : x ∈ normalizer (B : Set G)) (hx1 : ¬ conjSubgroup U x ≤ Q) : KFacts B L U Q W x := by
  have hx2 := not_conj_inv_le h.rk hx hx1
  obtain ⟨hD, hDx⟩ := h.rk.Q_eq_sup_centralizer hx hx1 h.hUL h.hLQ h.hZ (h.hgen x hx hx1 hx2)
  have hc := h.rk.commutator_conj hx hx1 hx2
  refine ⟨h.rk.sup_Q_conj hx hx2, hc.1, hc.2, h.rk.conj_W hx hx1 hx2, ?_,
    h.rk.inf_centralizer_conj hx hx1, hD, hDx, h.rk.conj_Q_eq hx, h.rk.U_le_B,
    h.rk.conj_le_B hx⟩
  rw [h.rk.inf_Q_conj hx hx2, h.rk.conj_W hx hx1 hx2]

end CFSG.QuasithinUnique.AppE
