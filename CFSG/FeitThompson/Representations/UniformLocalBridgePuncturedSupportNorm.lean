module

public import CFSG.FeitThompson.Representations.LocalCharacterRowsRestrictIrreducibly
import CFSG.FeitThompson.Representations.PrimeTIDegreeSignCongruence
import CFSG.FeitThompson.Representations.InducedFamilyIrreducibleRowOrthogonal
import CFSG.FeitThompson.Representations.CoprimeAutomorphismCosetPartition
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

def primeTIbridgeSupport (K W₁ W₂ : Subgroup L) : Set L :=
  ((K : Set L) \ {1}) ∪ Group.conjugatesOfSet (cyclicTIset W₁ W₂)

theorem primeTIbridgeSupport_eq (K W₁ W₂ : Subgroup L) :
    primeTIbridgeSupport K W₁ W₂
      = ((K : Set L) \ {1}) ∪ Group.conjugatesOfSet (cyclicTIset W₁ W₂) := (rfl)

theorem mem_primeTIbridgeSupport_of_isConj {v x : L} (hv : v ∈ cyclicTIset W₁ W₂)
    (hvx : IsConj v x) : x ∈ primeTIbridgeSupport K W₁ W₂ :=
  Or.inr (Group.mem_conjugatesOfSet_iff.2 ⟨v, hv, hvx⟩)

theorem mem_primeTIbridgeSupport_of_mem_of_ne_one {x : L} (hx : x ∈ K) (hx1 : x ≠ 1) :
    x ∈ primeTIbridgeSupport K W₁ W₂ := Or.inl ⟨hx, hx1⟩

namespace IsPrimeCyclicTIHyp

theorem mem_normalizer_coe_of_normal (K : Subgroup L) [K.Normal] (g : L) :
    g ∈ Subgroup.normalizer (K : Set L) := by
  rw [Subgroup.mem_set_normalizer_iff'']
  intro y
  exact ⟨fun hy => by simpa using ‹K.Normal›.conj_mem y hy g⁻¹,
    fun hy => by simpa [mul_assoc] using ‹K.Normal›.conj_mem _ hy g⟩

open Pointwise in
theorem exists_conj_eq_mul_of_notMem [Finite L] (h : IsPrimeCyclicTIHyp K W₁ W₂) {x : L}
    (hx : x ∉ K) : ∃ w ∈ W₁, w ≠ 1 ∧ ∃ y ∈ W₂, IsConj (y * w) x := by
  have hKn := h.normal
  obtain ⟨k, hk, w, hw, rfl⟩ := h.exists_decomp x
  have hw1 : w ≠ 1 := by rintro rfl; exact hx (by simpa using hk)
  have hcop : (Nat.card ↥K).Coprime (orderOf w) :=
    h.coprime_natCard.coprime_dvd_right (Subgroup.orderOf_dvd_natCard W₁ hw)
  have hmem : k * w ∈ (K : Set L) * ({w} : Set L) :=
    Set.mul_mem_mul (SetLike.mem_coe.2 hk) rfl
  rw [← sUnion_centralizerCosetConjugates hcop (isOfFinOrder_of_finite w)
    (mem_normalizer_coe_of_normal K w), Set.mem_sUnion] at hmem
  obtain ⟨S, hS, hxS⟩ := hmem
  obtain ⟨g, hg, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  rw [mem_conjAct_smul_set_iff, mem_centralizerCoset_iff, h.centralizer_eq w hw hw1] at hxS
  exact ⟨w, hw, hw1, g⁻¹ * (k * w) * g * w⁻¹, hxS, isConj_iff.2 ⟨g, by group⟩⟩

theorem mul_mem_cyclicTIset (h : IsPrimeCyclicTIHyp K W₁ W₂) {y w : L} (hy : y ∈ W₂)
    (hy1 : y ≠ 1) (hw : w ∈ W₁) (hw1 : w ≠ 1) : y * w ∈ cyclicTIset W₁ W₂ := by
  refine mem_cyclicTIset.2 ⟨(W₁ ⊔ W₂).mul_mem (Subgroup.mem_sup_right hy)
    (Subgroup.mem_sup_left hw), fun hmem => ?_, fun hmem => ?_⟩
  · have hyy : y ∈ W₁ ⊓ W₂ := Subgroup.mem_inf.2 ⟨by
      have hey : y = y * w * w⁻¹ := by group
      rw [hey]; exact W₁.mul_mem hmem (W₁.inv_mem hw), hy⟩
    rw [h.inf_left_right_eq_bot] at hyy
    exact hy1 (Subgroup.mem_bot.1 hyy)
  · have hww : w ∈ W₁ ⊓ W₂ := Subgroup.mem_inf.2 ⟨hw, by
      have hew : w = y⁻¹ * (y * w) := by group
      rw [hew]; exact W₂.mul_mem (W₂.inv_mem hy) hmem⟩
    rw [h.inf_left_right_eq_bot] at hww
    exact hw1 (Subgroup.mem_bot.1 hww)

theorem notMem_of_mem_left_of_ne_one (h : IsPrimeCyclicTIHyp K W₁ W₂) {w : L} (hw : w ∈ W₁)
    (hw1 : w ≠ 1) : w ∉ K := by
  intro hwK
  have hb : w ∈ K ⊓ W₁ := Subgroup.mem_inf.2 ⟨hwK, hw⟩
  rw [h.inf_eq_bot] at hb
  exact hw1 (Subgroup.mem_bot.1 hb)

theorem notMem_of_mem_cyclicTIset (h : IsPrimeCyclicTIHyp K W₁ W₂) {z : L}
    (hz : z ∈ cyclicTIset W₁ W₂) : z ∉ K := by
  obtain ⟨hzW, hz1, hz2⟩ := mem_cyclicTIset.1 hz
  intro hzK
  obtain ⟨x, hx, y, hy, rfl⟩ := h.exists_mul_eq_of_mem_sup hzW
  have hxK : x ∈ K := by
    have hex : x = x * y * y⁻¹ := by group
    rw [hex]; exact K.mul_mem hzK (K.inv_mem (h.right_le hy))
  have hb : x ∈ K ⊓ W₁ := Subgroup.mem_inf.2 ⟨hxK, hx⟩
  rw [h.inf_eq_bot] at hb
  rw [Subgroup.mem_bot.1 hb, one_mul] at hz2
  exact hz2 hy

noncomputable def primeTIbridge (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) (ζ : L → ℂ) (δ n : ℤ)
    (i : Irr ↥W₁) (j : Irr ↥W₂) : L → ℂ :=
  h.primeTIirr σ i j - (δ : ℂ) • h.primeTIirr σ i (principalIrr ↥W₂) - (n : ℂ) • ζ

theorem primeTIbridge_apply (h : IsPrimeCyclicTIHyp K W₁ W₂) (ζ : L → ℂ) (δ n : ℤ)
    (i : Irr ↥W₁) (j : Irr ↥W₂) (x : L) :
    h.primeTIbridge σ ζ δ n i j x = h.primeTIirr σ i j x
      - (δ : ℂ) * h.primeTIirr σ i (principalIrr ↥W₂) x - (n : ℂ) * ζ x := by
  simp [primeTIbridge]

section Inner

variable [Fintype L]

theorem cfInner_primeTIbridge_left (h : IsPrimeCyclicTIHyp K W₁ W₂) (ζ : L → ℂ) (δ n : ℤ)
    (i : Irr ↥W₁) (j : Irr ↥W₂) (g : L → ℂ) :
    cfInner (h.primeTIbridge σ ζ δ n i j) g = cfInner (h.primeTIirr σ i j) g
      - (δ : ℂ) * cfInner (h.primeTIirr σ i (principalIrr ↥W₂)) g - (n : ℂ) * cfInner ζ g := by
  rw [primeTIbridge, cfInner_sub_left, cfInner_sub_left, cfInner_smul_left, cfInner_smul_left]

theorem cfInner_primeTIbridge_right (h : IsPrimeCyclicTIHyp K W₁ W₂) (ζ : L → ℂ) (δ n : ℤ)
    (i : Irr ↥W₁) (j : Irr ↥W₂) (g : L → ℂ) :
    cfInner g (h.primeTIbridge σ ζ δ n i j) = cfInner g (h.primeTIirr σ i j)
      - (δ : ℂ) * cfInner g (h.primeTIirr σ i (principalIrr ↥W₂)) - (n : ℂ) * cfInner g ζ := by
  rw [primeTIbridge, cfInner_sub_right, cfInner_sub_right, cfInner_smul_right,
    cfInner_smul_right, map_intCast, map_intCast]

end Inner

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

structure IsUniformBridgeData (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) (ζ : L → ℂ) (d n δ : ℤ) : Prop where
  isometry : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ
  mem_indFam : ζ ∈ indFam K (Irr ↥K \ {1})
  mem_Irr : ζ ∈ Irr L
  apply_one : ζ 1 = (Nat.card ↥W₁ : ℂ)
  one_lt : 1 < d
  two_le : 2 ≤ n
  sign : δ = 1 ∨ δ = -1
  primeTIirr_one : ∀ (i : Irr ↥W₁) (j : Irr ↥W₂), j ≠ principalIrr ↥W₂ →
    h.primeTIirr σ i j 1 = (d : ℂ)
  primeTISign_eq : ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ → h.primeTISign σ j = (δ : ℂ)
  sub_eq : d - δ = n * (Nat.card ↥W₁ : ℤ)

variable {h : IsPrimeCyclicTIHyp K W₁ W₂} {ζ : L → ℂ} {d n δ : ℤ}

theorem IsUniformBridgeData.sign_sq (hB : IsUniformBridgeData h σ ζ d n δ) :
    (δ : ℂ) * (δ : ℂ) = 1 := by
  rcases hB.sign with hδ | hδ <;> rw [hδ] <;> norm_num

theorem IsUniformBridgeData.sub_eq_complex (hB : IsUniformBridgeData h σ ζ d n δ) :
    (d : ℂ) - (δ : ℂ) = (n : ℂ) * (Nat.card ↥W₁ : ℂ) := by
  exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hB.sub_eq

theorem primeTIbridge_mem_virtualChars (hB : IsUniformBridgeData h σ ζ d n δ)
    (i : Irr ↥W₁) (j : Irr ↥W₂) : h.primeTIbridge σ ζ δ n i j ∈ virtualChars L := by
  have h1 : h.primeTIirr σ i j ∈ virtualChars L :=
    Irr_subset_virtualChars (h.primeTIirr_mem_Irr hB.isometry i j)
  have h2 : h.primeTIirr σ i (principalIrr ↥W₂) ∈ virtualChars L :=
    Irr_subset_virtualChars (h.primeTIirr_mem_Irr hB.isometry i _)
  have h3 : ζ ∈ virtualChars L := Irr_subset_virtualChars hB.mem_Irr
  have e1 : (δ : ℂ) • h.primeTIirr σ i (principalIrr ↥W₂)
      = δ • h.primeTIirr σ i (principalIrr ↥W₂) := Int.cast_smul_eq_zsmul _ _ _
  have e2 : (n : ℂ) • ζ = n • ζ := Int.cast_smul_eq_zsmul _ _ _
  rw [primeTIbridge, e1, e2]
  exact (virtualChars L).sub_mem
    ((virtualChars L).sub_mem h1 ((virtualChars L).smul_mem δ h2))
    ((virtualChars L).smul_mem n h3)

theorem primeTIbridge_mem_classFun (hB : IsUniformBridgeData h σ ζ d n δ)
    (i : Irr ↥W₁) (j : Irr ↥W₂) : h.primeTIbridge σ ζ δ n i j ∈ classFun L :=
  mem_classFun_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualChars (primeTIbridge_mem_virtualChars hB i j))

theorem primeTIbridge_one (hB : IsUniformBridgeData h σ ζ d n δ) (i : Irr ↥W₁)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) : h.primeTIbridge σ ζ δ n i j 1 = 0 := by
  rw [primeTIbridge_apply, hB.primeTIirr_one i j hj,
    h.primeTIirr_principal_right hB.isometry i, h.inflateLeft_one i, hB.apply_one, mul_one]
  linear_combination hB.sub_eq_complex

theorem primeTIbridge_apply_coe_left (hB : IsUniformBridgeData h σ ζ d n δ) (i : Irr ↥W₁)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) {x : ↥W₁} (hx : x ≠ 1) :
    h.primeTIbridge σ ζ δ n i j (x : L) = 0 := by
  have hKn := h.normal
  have hxK : (x : L) ∉ K := h.notMem_of_mem_left_of_ne_one x.2 (by simpa using hx)
  rw [primeTIbridge_apply, h.primeTIirr_apply_coe_left hB.isometry i j hx,
    h.primeTIirr_apply_coe_left hB.isometry i (principalIrr ↥W₂) hx,
    h.primeTISign_principal hB.isometry, hB.primeTISign_eq j hj,
    eq_zero_of_mem_indFam_of_notMem K hB.mem_indFam hxK]
  ring

theorem primeTIbridge_eq_zero_of_notMem (hB : IsUniformBridgeData h σ ζ d n δ) (i : Irr ↥W₁)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) {x : L}
    (hx : x ∉ primeTIbridgeSupport K W₁ W₂) : h.primeTIbridge σ ζ δ n i j x = 0 := by
  by_cases hxK : x ∈ K
  ·
    have hx1 : x = 1 := by
      by_contra hne
      exact hx (mem_primeTIbridgeSupport_of_mem_of_ne_one hxK hne)
    rw [hx1]
    exact primeTIbridge_one hB i hj
  · obtain ⟨w, hw, hw1, y, hy, hconj⟩ := h.exists_conj_eq_mul_of_notMem hxK
    rcases eq_or_ne y 1 with rfl | hy1
    ·
      rw [one_mul] at hconj
      rw [← mem_classFun.1 (primeTIbridge_mem_classFun hB i j) w x hconj]
      exact primeTIbridge_apply_coe_left hB i hj (x := ⟨w, hw⟩) (by simpa using hw1)
    · exact absurd (mem_primeTIbridgeSupport_of_isConj
        (h.mul_mem_cyclicTIset hy hy1 hw hw1) hconj) hx

theorem cfInner_primeTIirr_zeta_eq_zero (hB : IsUniformBridgeData h σ ζ d n δ)
    (i : Irr ↥W₁) (j : Irr ↥W₂) : cfInner (h.primeTIirr σ i j) ζ = 0 := by
  have := h.cfInner_primeTIirr_eq_zero hB.isometry hB.mem_indFam hB.mem_Irr hB.apply_one i j
  rw [← conj_cfInner, this, map_zero]

theorem cfInner_primeTIirr_primeTIbridge (hB : IsUniformBridgeData h σ ζ d n δ) (i : Irr ↥W₁)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (h.primeTIirr σ i j) (h.primeTIbridge σ ζ δ n i j) = 1 := by
  rw [cfInner_primeTIbridge_right, h.cfInner_primeTIirr hB.isometry i i j j,
    h.cfInner_primeTIirr hB.isometry i i j (principalIrr ↥W₂),
    cfInner_primeTIirr_zeta_eq_zero hB i j, if_pos ⟨rfl, rfl⟩, if_neg (by simp [hj])]
  ring

theorem cfInner_primeTIirr_principal_primeTIbridge (hB : IsUniformBridgeData h σ ζ d n δ)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (h.primeTIirr σ i (principalIrr ↥W₂)) (h.primeTIbridge σ ζ δ n i j) = -(δ : ℂ) := by
  rw [cfInner_primeTIbridge_right,
    h.cfInner_primeTIirr hB.isometry i i (principalIrr ↥W₂) j,
    h.cfInner_primeTIirr hB.isometry i i (principalIrr ↥W₂) (principalIrr ↥W₂),
    cfInner_primeTIirr_zeta_eq_zero hB i (principalIrr ↥W₂),
    if_neg (by simp [Ne.symm hj]), if_pos ⟨rfl, rfl⟩]
  ring

theorem cfInner_zeta_primeTIbridge (hB : IsUniformBridgeData h σ ζ d n δ) (i : Irr ↥W₁)
    (j : Irr ↥W₂) : cfInner ζ (h.primeTIbridge σ ζ δ n i j) = -(n : ℂ) := by
  rw [cfInner_primeTIbridge_right,
    h.cfInner_primeTIirr_eq_zero hB.isometry hB.mem_indFam hB.mem_Irr hB.apply_one i j,
    h.cfInner_primeTIirr_eq_zero hB.isometry hB.mem_indFam hB.mem_Irr hB.apply_one i
      (principalIrr ↥W₂), cfInner_self_of_mem_Irr hB.mem_Irr]
  ring

theorem cfInner_self_primeTIbridge (hB : IsUniformBridgeData h σ ζ d n δ) (i : Irr ↥W₁)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (h.primeTIbridge σ ζ δ n i j) (h.primeTIbridge σ ζ δ n i j) = 2 + (n : ℂ) ^ 2 := by
  rw [cfInner_primeTIbridge_left, cfInner_primeTIirr_primeTIbridge hB i hj,
    cfInner_primeTIirr_principal_primeTIbridge hB i hj, cfInner_zeta_primeTIbridge hB i j]
  linear_combination hB.sign_sq

theorem cfInner_primeTIbridge_zeta (hB : IsUniformBridgeData h σ ζ d n δ) (i : Irr ↥W₁)
    (j : Irr ↥W₂) :
    cfInner (h.primeTIbridge σ ζ δ n i j) ζ = -(n : ℂ) := by
  rw [cfInner_primeTIbridge_left, cfInner_primeTIirr_zeta_eq_zero hB i j,
    cfInner_primeTIirr_zeta_eq_zero hB i (principalIrr ↥W₂),
    cfInner_self_of_mem_Irr hB.mem_Irr]
  ring

theorem cfInner_primeTIirr_primeTIrow_eq_ite [Fintype ↑(Irr ↥W₁)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (i : Irr ↥W₁) (j k : Irr ↥W₂) [Decidable (j = k)] :
    cfInner (h.primeTIirr σ i j) (h.primeTIrow σ k) = if j = k then 1 else 0 := by
  classical
  rw [primeTIrow_def, cfInner_sum_right,
    Finset.sum_congr rfl (fun l _ => h.cfInner_primeTIirr hσ i l j k)]
  by_cases hjk : j = k <;> simp [hjk]

theorem cfInner_primeTIbridge_primeTIrow [Fintype ↑(Irr ↥W₁)]
    (hB : IsUniformBridgeData h σ ζ d n δ) (i : Irr ↥W₁) (j k : Irr ↥W₂)
    [Decidable (j = k)] [Decidable (principalIrr ↥W₂ = k)] :
    cfInner (h.primeTIbridge σ ζ δ n i j) (h.primeTIrow σ k)
      = (if j = k then 1 else 0) - (δ : ℂ) * (if principalIrr ↥W₂ = k then 1 else 0) := by
  rw [cfInner_primeTIbridge_left, cfInner_primeTIirr_primeTIrow_eq_ite h hB.isometry i j k,
    cfInner_primeTIirr_primeTIrow_eq_ite h hB.isometry i (principalIrr ↥W₂) k,
    h.cfInner_primeTIrow_eq_zero hB.isometry hB.mem_indFam hB.mem_Irr hB.apply_one k]
  ring

theorem primeTIbridge_apply_of_mem_cyclicTIset (hB : IsUniformBridgeData h σ ζ d n δ)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) {v : ↥(W₁ ⊔ W₂)}
    (hv : (v : L) ∈ cyclicTIset W₁ W₂) :
    h.primeTIbridge σ ζ δ n i j (v : L)
      = (δ : ℂ) * (h.isCyclicTIPair.prodChar (i : ↥W₁ → ℂ) (j : ↥W₂ → ℂ) v
          - h.isCyclicTIPair.prodChar (i : ↥W₁ → ℂ)
              ((principalIrr ↥W₂ : Irr ↥W₂) : ↥W₂ → ℂ) v) := by
  have hKn := h.normal
  have hvB : (v : L) ∈ primeTIset W₁ W₂ := cyclicTIset_subset_primeTIset hv
  rw [primeTIbridge_apply, h.primeTIirr_apply_of_mem_primeTIset hB.isometry i j hvB,
    h.primeTIirr_apply_of_mem_primeTIset hB.isometry i (principalIrr ↥W₂) hvB,
    h.primeTISign_principal hB.isometry, hB.primeTISign_eq j hj,
    eq_zero_of_mem_indFam_of_notMem K hB.mem_indFam (h.notMem_of_mem_cyclicTIset hv)]
  ring

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
