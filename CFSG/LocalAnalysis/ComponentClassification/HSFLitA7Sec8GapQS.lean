module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapSuz

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData

variable (A : BData S F T₁)

theorem conj_mem_E0 (n : A.NA) {g : X} (hg : g ∈ S.E0 F.yF F.kF) :
    (n : X) * g * (n : X)⁻¹ ∈ S.E0 F.yF F.kF := by
  obtain ⟨v, hv, rfl⟩ := A.exists_of_mem_E0 hg
  rw [A.conj_Φ]
  refine A.Φ_mem_E0 fun i => ?_
  have : (2 : ZMod 4) • (A.mat n *ᵥ v) = A.mat n *ᵥ ((2 : ZMod 4) • v) := by
    rw [Matrix.mulVec_smul]
  have h2 : (2 : ZMod 4) • v = 0 := funext fun j => by simpa using hv j
  have := congrFun this i
  rw [h2, Matrix.mulVec_zero] at this
  simpa using this

theorem map_E0 (n : A.NA) :
    (S.E0 F.yF F.kF).map (MulAut.conj (n : X)).toMonoidHom = S.E0 F.yF F.kF := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩; exact A.conj_mem_E0 n hg
  · intro g hg
    refine ⟨(n : X)⁻¹ * g * (n : X), ?_, by simp [mul_assoc]⟩
    have := A.conj_mem_E0 n⁻¹ hg
    simpa using this

theorem map_E₁ (n : A.NA) {a : X} (ha : (n : X) * S.t * (n : X)⁻¹ = S.t * a) :
    F.E₁.map (MulAut.conj (n : X)).toMonoidHom = E0t F a := by
  rw [A.E₁_eq_E0t]
  exact map_E0t (A.map_E0 n) (by rw [mul_one, ha])

end BData

namespace BData.Syl

variable {A : BData S F T₁} (Y : A.Syl)

theorem mem_zpowers_of_pow_four (hnc : ¬ SubConj F.E₁ F.E₂) {x : Y.RV} (hx : x ∈ Y.QV)
    (h4 : x ^ 4 = 1) : x ∈ zpowers (Y.pi Y.cR) := by
  classical
  have : IsCyclic Y.QV := Y.isCyclic_QV hnc
  have : Fintype Y.QV := Fintype.ofFinite _
  let c' : Y.QV := ⟨Y.pi Y.cR, Y.mem_QV_of (Y.AA_le_Q (A.Φ_mem _))⟩
  have hc' : orderOf c' = 4 := by rw [Subgroup.orderOf_mk, Y.orderOf_cR]
  set Sx : Finset Y.QV := Finset.univ.filter fun a => a ^ 4 = 1 with hSx
  have hcard : Sx.card ≤ 4 := IsCyclic.card_pow_eq_one_le (by norm_num)
  set Z : Finset Y.QV := (Finset.range 4).image fun i => c' ^ i with hZ
  have hZS : Z ⊆ Sx := by
    intro a ha
    simp only [hZ, Finset.mem_image, Finset.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← pow_mul, mul_comm, pow_mul, ← hc', pow_orderOf_eq_one, one_pow]
  have hZcard : Z.card = 4 := by
    rw [hZ, Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      have := pow_inj_mod.mp hij
      rwa [hc', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  have heq : Z = Sx := Finset.eq_of_subset_of_card_le hZS (by rw [hZcard]; exact hcard)
  have hxS : (⟨x, hx⟩ : Y.QV) ∈ Sx := by
    simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext h4
  rw [← heq] at hxS
  simp only [hZ, Finset.mem_image, Finset.mem_range] at hxS
  obtain ⟨i, -, hi⟩ := hxS
  have hxi : x = Y.pi Y.cR ^ i := by
    have := congrArg Subtype.val hi
    simpa [c'] using this.symm
  rw [hxi]
  exact pow_mem (mem_zpowers _) i

theorem mem_AA_of_pow_four (hnc : ¬ SubConj F.E₁ F.E₂) {q : X} (hq : q ∈ Y.Q)
    (h4 : q ^ 4 = 1) : q ∈ A.AA := by
  let qR : Y.R := ⟨q, Y.Q_le_R hq⟩
  have hx : Y.pi qR ^ 4 = 1 := by
    rw [← map_pow]
    have : qR ^ 4 = 1 := Subtype.ext (by simpa using h4)
    rw [this, map_one]
  obtain ⟨i, hi⟩ := Y.mem_zpowers_of_pow_four hnc (Y.mem_QV_of hq) hx
  change Y.pi Y.cR ^ i = Y.pi qR at hi
  rw [← map_zpow, pi_eq_iff] at hi
  have hci : ((Y.cR ^ i : Y.R) : X) ∈ A.AA := by
    rw [SubgroupClass.coe_zpow]; exact zpow_mem (A.Φ_mem _) i
  have := mul_mem hci (A.VV_le_AA hi)
  rwa [mul_inv_cancel_left] at this

theorem mem_E0_of_comm_t {q : X} (hq : q ∈ Y.Q) (ht : q * S.t = S.t * q) :
    q ∈ S.E0 F.yF F.kF := by
  have hqA : q ∈ A.AA := Y.mem_AA_of_Q_S₁ hq ((BData.T_le_S₁ A) (Y.mem_T_of_comm hq.1 ht))
  obtain ⟨v, rfl⟩ := A.mem_AA.mp hqA
  exact A.Φ_mem_E0 ((A.t_conj_eq_iff v).mp (by rw [← ht, mul_inv_cancel_right]))

theorem t_conj_mem_Q {q : X} (hq : q ∈ Y.Q) : S.t * q * S.t⁻¹ ∈ Y.Q :=
  (mem_normalizer_iff.mp Y.t_inv_mem_Q q).mp hq

theorem psi_mem_E0 (hnc : ¬ SubConj F.E₁ F.E₂) {q : X} (hq : q ∈ Y.Q) :
    S.t * q * S.t⁻¹ * q ∈ S.E0 F.yF F.kF := by
  have ht' : S.t⁻¹ = S.t := by rw [inv_eq_iff_mul_eq_one, t_mul_t]
  have hq' := Y.t_conj_mem_Q hq
  refine Y.mem_E0_of_comm_t (mul_mem hq' hq) ?_
  have hc := Y.Q_comm hnc hq' hq
  rw [ht'] at hc ⊢
  have htt : S.t * S.t = 1 := t_mul_t
  calc S.t * q * S.t * q * S.t = (S.t * q * S.t * q) * S.t := rfl
    _ = (q * (S.t * q * S.t)) * S.t := by rw [hc]
    _ = q * S.t * q * (S.t * S.t) := by group
    _ = q * S.t * q := by rw [htt, mul_one]
    _ = (S.t * S.t) * q * S.t * q := by rw [htt, one_mul]
    _ = S.t * (S.t * q * S.t * q) := by group

end BData.Syl

end Sec8

end CFSG.ComponentClassification.HSFLit
