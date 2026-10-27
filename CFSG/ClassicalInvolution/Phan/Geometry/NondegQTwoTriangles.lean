module

public import CFSG.ClassicalInvolution.Phan.Geometry.NondegQTwoLift
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves

public section

namespace CFSG.ClassicalInvolution.Phan

open SimpleGraph Module CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Recog
open CFSG.ClassicalInvolution.Phan.Geometry

variable {K : Type*} [Field K] {σ : K ≃+* K} {d : ℕ}
    {W : Submodule K (Fin d → K)}

theorem ndNull_of_support_le (hd : 3 ≤ finrank K W) {T : NdVert σ W}
    {p : ↥(nsPts σ W)} (c : (collGraph σ W).Walk p p)
    (hc : ∀ q ∈ c.support, q.1 ≤ T.1) : c ∈ ndNull hd p :=
  ndHomotopic_nil_of_support_le _ (ndExpand_support_le hd c hc)

theorem exists_ndVert_contains_collTriangle [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (h4 : 4 ≤ finrank K W) {p q r : ↥(nsPts σ W)}
    (hpq : (collGraph σ W).Adj p q) (hqr : (collGraph σ W).Adj q r)
    (hrp : (collGraph σ W).Adj r p) :
    ∃ T : NdVert σ W, p.1 ≤ T.1 ∧ q.1 ≤ T.1 ∧ r.1 ≤ T.1 := by
  have hpr : Orth σ p.1 r.1 :=
    ((isCollinear_iff_orth hσ hK ⟨le_top, r.2.2⟩ ⟨le_top, p.2.2⟩).mp hrp).symm hσ
  have hqr' : Orth σ q.1 r.1 :=
    (isCollinear_iff_orth hσ hK ⟨le_top, q.2.2⟩ ⟨le_top, r.2.2⟩).mp hqr
  let S := (p.1 ⊔ q.1) ⊔ r.1
  have hnd : Nondeg σ S :=
    Nondeg.sup_of_orth hσ hpq.2 r.2.2.2 (hpr.sup_left hqr')
  have hpS : p.1 ≤ S := le_trans le_sup_left le_sup_left
  have hqS : q.1 ≤ S := le_trans le_sup_right le_sup_left
  have hrS : r.1 ≤ S := le_sup_right
  have hdim : finrank K S ≤ 3 := by
    calc
      finrank K S ≤ finrank K ↥(p.1 ⊔ q.1) + finrank K r.1 :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      _ = 3 := by rw [finrank_sup_of_ne_pts p.2.2.1 q.2.2.1 hpq.1, r.2.2.1]
  have hSW : S ≤ W := sup_le (sup_le p.2.1 q.2.1) r.2.1
  have hSbot : S ≠ ⊥ := by
    intro he
    have hpbot : p.1 = ⊥ := eq_bot_iff.mpr (by simpa [he] using hpS)
    have hpdim := p.2.2.1
    rw [hpbot, finrank_bot] at hpdim
    omega
  have hSne : S ≠ W := by
    intro he
    rw [he] at hdim
    omega
  exact ⟨⟨S, hSW, hSbot, hSne, hnd⟩, hpS, hqS, hrS⟩

theorem ndTriangle_null [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (h4 : 4 ≤ finrank K W) {p q r : ↥(nsPts σ W)}
    (hpq : (collGraph σ W).Adj p q) (hqr : (collGraph σ W).Adj q r)
    (hrp : (collGraph σ W).Adj r p) :
    CycleHomotopic (ndNull (σ := σ) (W := W) (by omega)) (triWalk hpq hqr hrp) .nil := by
  obtain ⟨T, hpT, hqT, hrT⟩ := exists_ndVert_contains_collTriangle hσ hK h4 hpq hqr hrp
  apply cycleHomotopic_of_mem (ndNull (σ := σ) (W := W) (by omega))
  apply ndNull_of_support_le (T := T)
  intro S hS
  simp only [triWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · exact hpT
  · exact hqT
  · exact hrT
  · exact hpT

theorem ndNullLen3 [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (h4 : 4 ≤ finrank K W) : NullLen (ndNull (σ := σ) (W := W) (by omega)) 3 := by
  intro u p hp
  match u, p, hp with
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ => exact ndTriangle_null hσ hK h4 h₁ h₂ h₃

end CFSG.ClassicalInvolution.Phan
