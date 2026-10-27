module

public import CFSG.ClassicalInvolution.Q3.Q3URStd
public import CFSG.ClassicalInvolution.Q3.Q3WL65
public import CFSG.ClassicalInvolution.Q3.ModelCenterClassical
public import CFSG.ClassicalInvolution.Models.Transfer.Unitary
public import CFSG.ClassicalInvolution.Q3.Q3URClose

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem card_gf9 : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
  CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl

theorem two_ne_zero_gf9 : (2 : GaloisField 3 2) ≠ 0 :=
  two_ne_zero_of_charP_ne_two (K := GaloisField 3 2) (p := 3) (by norm_num)

theorem card_fixedSubfield_gf9 : Nat.card (fixedSubfield (GaloisField 3 2) 3 1) = 3 := by
  rw [card_fixedSubfield card_gf9]
  norm_num

section Center

theorem centerExp_su3 {n : ℕ} (hn3 : 3 ≤ n) {z : Su (GaloisField 3 2) 3 1 n}
    (hz : z ∈ Subgroup.center (Su (GaloisField 3 2) 3 1 n)) : z ^ 8 = 1 := by
  have hK := card_gf9
  have hk : Nat.card (GaloisField 3 2) = 2 ^ 3 + 1 := hK.trans (by norm_num)
  have hZ := (isQuasisimple_statedSU_of_card (F := GaloisField 3 2) (p := 3) (f := 1) hK hn3
    (fun h => by have := (Prod.mk.inj h).2; norm_num at this)).2
  let e := MulEquiv.subgroupCongr (SUid_eq_statedSU hK n)
  have hz' : e z ∈ Subgroup.center (StatedSU n (3 ^ 1) (GaloisField 3 2)) := by
    rw [← map_center_mulEquiv e]
    exact ⟨z, hz, rfl⟩
  rw [hZ, Subgroup.mem_subgroupOf] at hz'
  have he : ((e z : StatedSU n (3 ^ 1) (GaloisField 3 2)) : GL (Fin n) (GaloisField 3 2)) =
      (z : GL (Fin n) (GaloisField 3 2)) := rfl
  have h8 := CFSG.ClassicalInvolution.Q3.pow_eq_one_of_mem_statedScalars hk hz'
  rw [he] at h8
  apply Subtype.ext
  simpa using h8

theorem ker_orderOf_not_dvd_three_su3 {n : ℕ} (hn3 : 3 ≤ n) {X : Type*} [Group X]
    {θ : Su (GaloisField 3 2) 3 1 n →* X}
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 n)) :
    ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z := by
  intro z hz h3
  have h8 := orderOf_dvd_of_pow_eq_one (centerExp_su3 hn3 (hker hz))
  have := h3.trans h8
  omega

theorem eq_one_or_suMat_eq_neg_one3 {n : ℕ} (hn3 : 3 ≤ n) {z : Su (GaloisField 3 2) 3 1 n}
    (hz : z ∈ Subgroup.center (Su (GaloisField 3 2) 3 1 n)) (hz2 : z * z = 1) :
    z = 1 ∨ suMat z = -1 := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_su3 card_gf9 (by norm_num) hn3 hz
  have hsq : Matrix.scalar (Fin n) (c * c) = 1 := by
    rw [map_mul, ← hc, ← suMat_mul, hz2, suMat_one]
  rw [← map_one (Matrix.scalar (Fin n)), Matrix.scalar_inj] at hsq
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    apply suMat_injective
    rw [hc, h, map_one, suMat_one]
  · right
    rw [hc, h, map_neg, map_one]

end Center

section LongRoot

variable {n : ℕ} {hn : 2 ≤ n}

theorem not_mem_center_of_isLongRootSU2_3 (hn3 : 3 ≤ n) {L : Subgroup (Su (GaloisField 3 2) 3 1 n)}
    {i : Su (GaloisField 3 2) 3 1 n} (h : IsLongRootSU2 (GaloisField 3 2) 3 1 hn L i) :
    i ∉ Subgroup.center (Su (GaloisField 3 2) 3 1 n) := by
  intro hc
  have hdim := h.finrank_minusSpaceSU two_ne_zero_gf9
  rcases eq_one_or_suMat_eq_neg_one3 hn3 hc h.mul_self with h1 | h1
  · have := (h.isClassicalSL2 card_gf9 (by norm_num)).orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  · have : minusSpaceSU i = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [mem_minusSpaceSU, h1, Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [this, finrank_top, Module.finrank_fin_fun] at hdim
    omega

theorem map_ne_one_of_isLongRootSU2_3 (hn3 : 3 ≤ n) {X : Type*} [Group X]
    {θ : Su (GaloisField 3 2) 3 1 n →* X}
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 n))
    {L : Subgroup (Su (GaloisField 3 2) 3 1 n)} {i : Su (GaloisField 3 2) 3 1 n}
    (h : IsLongRootSU2 (GaloisField 3 2) 3 1 hn L i) : θ i ≠ 1 :=
  fun h1 => not_mem_center_of_isLongRootSU2_3 hn3 h (hker (MonoidHom.mem_ker.mpr h1))

theorem eq_one_of_mem_ker_of_isLongRootSU2_3 (hn3 : 3 ≤ n)
    {L : Subgroup (Su (GaloisField 3 2) 3 1 n)} {i : Su (GaloisField 3 2) 3 1 n}
    (h : IsLongRootSU2 (GaloisField 3 2) 3 1 hn L i) {X : Type*} [Group X]
    {θ : Su (GaloisField 3 2) 3 1 n →* X}
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 n)) :
    ∀ z ∈ L, z ∈ θ.ker → z = 1 :=
  eq_one_of_mem_ker_of_isClassicalSL2 θ (odd_natCard_fixedSubfield card_gf9 (by norm_num)) hker
    (h.isClassicalSL2 card_gf9 (by norm_num)) (map_ne_one_of_isLongRootSU2_3 hn3 hker h)

theorem eq_of_map_eq_of_isLongRootSU2_3 (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup (Su (GaloisField 3 2) 3 1 n)} {i₁ i₂ : Su (GaloisField 3 2) 3 1 n}
    (h₁ : IsLongRootSU2 (GaloisField 3 2) 3 1 hn L₁ i₁)
    (h₂ : IsLongRootSU2 (GaloisField 3 2) 3 1 hn L₂ i₂) {X : Type*} [Group X]
    {θ : Su (GaloisField 3 2) 3 1 n →* X}
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 n))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) (hθ : θ i₁ = θ i₂) : i₁ = i₂ := by
  have h2 := two_ne_zero_gf9
  have hz : i₁ * i₂⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, mul_inv_cancel]
  have hzi : i₁ = (i₁ * i₂⁻¹) * i₂ := by rw [inv_mul_cancel_right]
  have hzc := hker hz
  have hz2 : (i₁ * i₂⁻¹) * (i₁ * i₂⁻¹) = 1 :=
    sq_eq_one_of_mul_sq_eq_one h₂.mul_self hzc (by rw [← hzi]; exact h₁.mul_self)
  have hz1 : i₁ * i₂⁻¹ = 1 := by
    rcases hlift with hn4 | hfree
    · rcases eq_one_or_suMat_eq_neg_one3 hn3 hzc hz2 with h1 | h1
      · exact h1
      · exfalso
        apply hn4
        have hmat : suMat i₁ = -suMat i₂ := by
          rw [hzi, suMat_mul, h1, neg_one_mul]
        have hconj := h₁.finrank_minusSpaceSU h2
        rw [minusSpaceSU, hmat] at hconj
        have := eq_two_mul_of_finrank_eigSpace_neg h2 h₂.coe_mul_self
          (h₂.finrank_minusSpaceSU h2) hconj
        omega
    · exact hfree _ hz hz2
  exact mul_inv_eq_one.mp hz1

theorem kerConjFree_of_isLongRootSU2_3 (hn3 : 3 ≤ n) {L : Subgroup (Su (GaloisField 3 2) 3 1 n)}
    {i : Su (GaloisField 3 2) 3 1 n} (h : IsLongRootSU2 (GaloisField 3 2) 3 1 hn L i)
    {X : Type*} [Group X] {θ : Su (GaloisField 3 2) 3 1 n →* X}
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 n))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) : KerConjFree θ i := by
  intro g z hz hg
  have hθ : θ (g * i * g⁻¹) = θ i := by
    rw [hg, map_mul, MonoidHom.mem_ker.mp hz, one_mul]
  have hgi := eq_of_map_eq_of_isLongRootSU2_3 hn3 (h.conj g) h hker hlift hθ
  rw [hg] at hgi
  exact mul_eq_right.mp hgi

theorem commute_and_ne_of_map_su3 (hn3 : 3 ≤ n) {L₂ : Subgroup (Su (GaloisField 3 2) 3 1 n)}
    {i₂ : Su (GaloisField 3 2) 3 1 n} (h₂ : IsLongRootSU2 (GaloisField 3 2) 3 1 hn L₂ i₂)
    {X : Type*} [Group X] {θ : Su (GaloisField 3 2) 3 1 n →* X}
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 n))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) {i₁ : Su (GaloisField 3 2) 3 1 n}
    (hc : Commute (θ i₁) (θ i₂)) (hne : θ i₁ ≠ θ i₂) : Commute i₁ i₂ ∧ i₁ ≠ i₂ :=
  ⟨commute_of_commute_map θ (kerConjFree_of_isLongRootSU2_3 hn3 h₂ hker hlift) hc,
    fun e => hne (congrArg θ e)⟩

end LongRoot

section Image

variable {n : ℕ} {hn : 2 ≤ n} {X : Type} [Group X] {θ : Su (GaloisField 3 2) 3 1 n →* X}

theorem orderOf_eq_two_of_image3 (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 n)) {L' : Subgroup X} {i' : X}
    (h : IsLongRootSU2Image θ hn L' i') : orderOf i' = 2 := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  have hc := hL.isClassicalSL2 card_gf9 (by norm_num)
  exact orderOf_map_eq_two (eq_one_of_mem_ker_of_isLongRootSU2_3 hn3 hL hker) hc.mem
    hc.orderOf_eq_two

theorem eq_of_orderOf_eq_two_of_image3 (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 n)) {L' : Subgroup X} {i' : X}
    (h : IsLongRootSU2Image θ hn L' i') {t : X} (ht : t ∈ L') (h2 : orderOf t = 2) : t = i' := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  exact eq_map_of_orderOf_eq_two (eq_one_of_mem_ker_of_isLongRootSU2_3 hn3 hL hker)
    (fun _ htL ht2 => hL.eq_of_orderOf_eq_two card_gf9 (by norm_num) htL ht2) ht h2

end Image

section Lemma65

variable {n : ℕ} {hn : 2 ≤ n} {X : Type} [Group X] {θ : Su (GaloisField 3 2) 3 1 n →* X}

theorem lemma_6_5_su_map_of_commute3 (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 n))
    {L₁ L₂ : Subgroup (Su (GaloisField 3 2) 3 1 n)} {i₁ i₂ : Su (GaloisField 3 2) 3 1 n}
    (h₁ : IsLongRootSU2 (GaloisField 3 2) 3 1 hn L₁ i₁)
    (h₂ : IsLongRootSU2 (GaloisField 3 2) 3 1 hn L₂ i₂) (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    (∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x) ∨
      (θ i₂ ∉ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ∧
        UnitaryBlockStandardPair (GaloisField 3 2) 3 1 (L₁.map θ ⊔ L₂.map θ) (L₁.map θ)
          (L₂.map θ)) := by
  obtain ⟨e⟩ := (h₁.isClassicalSL2 card_gf9 (by norm_num)).nonempty_mulEquiv
  have hL₁ := pow_three_mem_commutator_of_equiv card_fixedSubfield_gf9 e
  rcases lemma_6_5_su card_gf9 (by norm_num) hn3 h₁ h₂ hc hne with
    ⟨hcomm, -⟩ | ⟨hnot, ρ, hinj, hrange, hU, hV⟩
  · left
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · right
    refine ⟨fun hmem => hnot (mem_centralizer_of_map3 θ hker
      (ker_orderOf_not_dvd_three_su3 hn3 hker) hL₁ hmem), ?_⟩
    refine unitaryBlockStandardPair_of_normalized
      (CFSG.ClassicalInvolution.Models.Transfer.ker_comp_le_center ρ hinj hker) ?_ ?_ ?_
    · rw [MonoidHom.range_comp, hrange, Subgroup.map_sup]
    · rw [← Subgroup.map_map, hU]
    · rw [← Subgroup.map_map, hV]

end Lemma65

end CFSG.ClassicalInvolution.Q3.Q3W
