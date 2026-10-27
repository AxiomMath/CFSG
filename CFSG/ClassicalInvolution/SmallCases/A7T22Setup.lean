module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2
public import CFSG.ClassicalInvolution.Asc77.AscT7BSetup

public section

namespace CFSG.ClassicalInvolution.A7T22

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure Hyp22Core (Ω : Set (Subgroup G)) (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G) : Prop where
  hyp : HypOmegaGen Ω
  memK : K ∈ Ω
  memK' : K' ∈ Ω
  memK₃ : K₃ ∈ Ω
  hz : IsUniqueInvolution K z
  hz' : IsUniqueInvolution K' z
  hz₃ : IsUniqueInvolution K₃ z
  ne₁₂ : K' ≠ K
  ne₁₃ : K₃ ≠ K
  ne₂₃ : K₃ ≠ K'
  hu₁ : u₁ ∈ K ∧ orderOf u₁ = 4
  hu₂ : u₂ ∈ K' ∧ orderOf u₂ = 4
  hu₃ : u₃ ∈ K₃ ∧ orderOf u₃ = 4
  c₁₂ : u₁ * u₂ = u₂ * u₁
  c₁₃ : u₁ * u₃ = u₃ * u₁
  c₂₃ : u₂ * u₃ = u₃ * u₂

theorem exists_orderOf_eq_four_of_isSylow2In (hΩ : HypOmegaGen Ω) {J R : Subgroup G}
    (hJ : J ∈ Ω) (hR : IsSylow2In R J) : ∃ u ∈ R, orderOf u = 4 := by
  obtain ⟨k, -, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ hR)
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  refine ⟨((e.symm (QuaternionGroup.xa 0) : R) : G), (e.symm _).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact QuaternionGroup.orderOf_xa 0

theorem exists_sylow_triple (hΩ : HypOmegaGen Ω) {K K' K₃ : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hK' : K' ∈ Ω) (hK₃ : K₃ ∈ Ω) (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hz₃ : IsUniqueInvolution K₃ z) (h12 : K' ≠ K) (h13 : K₃ ≠ K) (h23 : K₃ ≠ K') :
    ∃ R₁ R₂ R₃ : Subgroup G, IsSylow2In R₁ K ∧ IsSylow2In R₂ K' ∧ IsSylow2In R₃ K₃ ∧
      Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hR₁ : IsSylow2In ((S : Subgroup ↥K).map K.subtype) K := isSylow2In_map_subtype K S
  set R₁ : Subgroup G := (S : Subgroup ↥K).map K.subtype with hR₁def
  have hR₁N : R₁ ≤ Subgroup.normalizer (K' : Set G) :=
    hR₁.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hK hK' h12.symm hz hz')
  obtain ⟨R₂, hR₂, hfix₂⟩ := exists_sylow_normalized hR₁.2.1 hR₁N
  have hR₁R₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix₂ r hr)
  have hP : IsPGroup 2 ↥(R₁ ⊔ R₂) := hR₁.2.1.to_sup_of_normal_right' hR₂.2.1 hR₁R₂
  have c12 : Commutes R₁ R₂ :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK' h12.symm hz hz' hR₁.1 hR₂.1 hP
  have hPN : R₁ ⊔ R₂ ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (hR₁.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hK hK₃ h13.symm hz hz₃))
      (hR₂.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hK' hK₃ h23.symm hz' hz₃))
  obtain ⟨R₃, hR₃, hfix₃⟩ := exists_sylow_normalized hP hPN
  have hPR₃ : R₁ ⊔ R₂ ≤ Subgroup.normalizer (R₃ : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix₃ r hr)
  have hQ : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) := hP.to_sup_of_normal_right' hR₃.2.1 hPR₃
  have c13 : Commutes R₁ R₃ :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK₃ h13.symm hz hz₃ hR₁.1 hR₃.1
      (hQ.to_le (sup_le_sup_right le_sup_left _))
  have c23 : Commutes R₂ R₃ :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK' hK₃ h23.symm hz' hz₃ hR₂.1 hR₃.1
      (hQ.to_le (sup_le_sup_right le_sup_right _))
  exact ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, c12, c13, c23⟩

theorem exists_hyp22Core (hΩ : HypOmegaGen Ω) {K K' K₃ : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hK' : K' ∈ Ω) (hK₃ : K₃ ∈ Ω) (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hz₃ : IsUniqueInvolution K₃ z) (h12 : K' ≠ K) (h13 : K₃ ≠ K) (h23 : K₃ ≠ K') :
    ∃ u₁ u₂ u₃ : G, Hyp22Core Ω K K' K₃ z u₁ u₂ u₃ := by
  obtain ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, c12, c13, c23⟩ :=
    exists_sylow_triple hΩ hK hK' hK₃ hz hz' hz₃ h12 h13 h23
  obtain ⟨u₁, hu₁R, hu₁4⟩ := exists_orderOf_eq_four_of_isSylow2In hΩ hK hR₁
  obtain ⟨u₂, hu₂R, hu₂4⟩ := exists_orderOf_eq_four_of_isSylow2In hΩ hK' hR₂
  obtain ⟨u₃, hu₃R, hu₃4⟩ := exists_orderOf_eq_four_of_isSylow2In hΩ hK₃ hR₃
  exact ⟨u₁, u₂, u₃, hΩ, hK, hK', hK₃, hz, hz', hz₃, h12, h13, h23, ⟨hR₁.1 hu₁R, hu₁4⟩,
    ⟨hR₂.1 hu₂R, hu₂4⟩, ⟨hR₃.1 hu₃R, hu₃4⟩, c12 u₁ hu₁R u₂ hu₂R, c13 u₁ hu₁R u₃ hu₃R,
    c23 u₂ hu₂R u₃ hu₃R⟩

omit [Finite G] in
theorem exists_third_twin {K K' : Subgroup G} (hK' : K' ∈ twinSet Ω K)
    (hperp : KPerp Ω K = twinSet Ω K) (hne : KPerp Ω K ≠ {K, K'}) :
    ∃ K₃ ∈ twinSet Ω K, K₃ ≠ K ∧ K₃ ≠ K' := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply hne
  apply Set.Subset.antisymm
  · intro J hJ
    rw [hperp] at hJ
    by_cases hJK : J = K
    · exact Or.inl hJK
    · exact Or.inr (hcon J hJ hJK)
  · intro J hJ
    rcases hJ with rfl | rfl
    · exact Set.mem_insert _ _
    · rw [hperp]
      exact hK'

theorem exists_hyp22Core_of_perp (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hK'K : K' ≠ K)
    (hperp : KPerp Ω K = twinSet Ω K) (hne : KPerp Ω K ≠ {K, K'}) :
    ∃ (K₃ : Subgroup G) (u₁ u₂ u₃ : G), K₃ ∈ twinSet Ω K ∧ Hyp22Core Ω K K' K₃ z u₁ u₂ u₃ := by
  obtain ⟨K₃, hK₃, h13, h23⟩ := exists_third_twin hK' hperp hne
  obtain ⟨u₁, u₂, u₃, h⟩ := exists_hyp22Core hΩ hK hK'.1 hK₃.1 hz
    (isUniqueInvolution_of_mem_twinSet hz hK') (isUniqueInvolution_of_mem_twinSet hz hK₃) hK'K
    h13 h23
  exact ⟨K₃, u₁, u₂, u₃, hK₃, h⟩

namespace Hyp22Core

variable {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem not_mem_of_orderOf_four (hΩ : HypOmegaGen Ω) {L L' : Subgroup G} (hL : L ∈ Ω)
    (hL' : L' ∈ Ω) (hne : L' ≠ L) {u : G} (hu4 : orderOf u = 4) (huL : u ∈ L) (huL' : u ∈ L') :
    False :=
  hne (Sec6Gen.eq_of_le_of_le hΩ hL hL' (T7A.isPGroup_zpowers_of_orderOf_four hu4)
    (by rw [Nat.card_zpowers, hu4]) (Subgroup.zpowers_le.mpr huL)
    (Subgroup.zpowers_le.mpr huL')).symm

omit [Finite G] in
theorem sq₁ (h : Hyp22Core Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₁ = z :=
  T7A.sq_eq_of_orderOf_four h.hz h.hu₁.1 h.hu₁.2

omit [Finite G] in
theorem sq₂ (h : Hyp22Core Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₂ = z :=
  T7A.sq_eq_of_orderOf_four h.hz' h.hu₂.1 h.hu₂.2

omit [Finite G] in
theorem sq₃ (h : Hyp22Core Ω K K' K₃ z u₁ u₂ u₃) : u₃ * u₃ = z :=
  T7A.sq_eq_of_orderOf_four h.hz₃ h.hu₃.1 h.hu₃.2

theorem isElemAbelian2_B (h : Hyp22Core Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) 3 := by
  have hΩ := h.hyp
  obtain ⟨h₁, o₁⟩ := h.hu₁
  obtain ⟨h₂, o₂⟩ := h.hu₂
  obtain ⟨h₃, o₃⟩ := h.hu₃
  have s₁ := h.sq₁
  have s₂ := h.sq₂
  have s₃ := h.sq₃
  have zc₁ : z * u₁ = u₁ * z := e189_commute_of_mem h.hz h₁
  have zc₂ : z * u₂ = u₂ * z := e189_commute_of_mem h.hz' h₂
  have zc₃ : z * u₃ = u₃ * z := e189_commute_of_mem h.hz₃ h₃
  have hz2 : z * z = 1 := h.hz.sq
  have hc12 : Commute u₁ u₂ := h.c₁₂
  have hc13 : Commute u₁ u₃ := h.c₁₃
  have hc23 : Commute u₂ u₃ := h.c₂₃
  have q₁₂ : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [← h.c₁₂]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [s₁, s₂, hz2]
  have q₂₃ : (u₂ * u₃) * (u₂ * u₃) = 1 := by
    calc (u₂ * u₃) * (u₂ * u₃) = u₂ * (u₃ * u₂) * u₃ := by group
      _ = u₂ * (u₂ * u₃) * u₃ := by rw [← h.c₂₃]
      _ = (u₂ * u₂) * (u₃ * u₃) := by group
      _ = 1 := by rw [s₂, s₃, hz2]
  have hcu₁₂ : Commute (u₁ * u₂) z :=
    Commute.mul_left (zc₁.symm : Commute u₁ z) (zc₂.symm : Commute u₂ z)
  have hcu₂₃ : Commute (u₂ * u₃) z :=
    Commute.mul_left (zc₂.symm : Commute u₂ z) (zc₃.symm : Commute u₃ z)
  have hcomm : ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), ∀ b ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G),
      a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · rfl
    · exact hcu₁₂.eq
    · exact (Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)).eq
    · exact hcu₁₂.symm.eq
    · rfl
    · exact hcu₂₃.symm.eq
    · exact (Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)).symm.eq
    · exact hcu₂₃.eq
    · rfl
  have hsq : ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact q₁₂
    · exact hz2
    · exact q₂₃
  refine ⟨?_, fun x hx => T7A.sq_closure hsq hcomm x hx⟩
  have hne12 : u₁ * u₂ ≠ z := by
    intro he
    refine not_mem_of_orderOf_four hΩ h.memK h.memK' h.ne₁₂ o₂ ?_ h₂
    have : u₂ = u₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁) h.hz.mem
  have hne1 : u₁ * u₂ ≠ 1 := by
    intro he
    refine not_mem_of_orderOf_four hΩ h.memK h.memK' h.ne₁₂ o₂ ?_ h₂
    have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact Subgroup.inv_mem _ h₁
  have hc1 : u₂ * u₃ ≠ 1 := by
    intro he
    refine not_mem_of_orderOf_four hΩ h.memK' h.memK₃ h.ne₂₃ o₃ ?_ h₃
    have : u₃ = u₂⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact Subgroup.inv_mem _ h₂
  have hnot : u₂ * u₃ ∉ Subgroup.closure ({u₁ * u₂, z} : Set G) := by
    intro hx
    rcases T7B.mem_closure_pair q₁₂ hz2 hne1 h.hz.ne_one hcu₁₂.eq hx with h' | h' | h' | h'
    · exact hc1 h'
    · have h3 : u₃ = u₁ := mul_left_cancel (h'.trans h.c₁₂)
      exact not_mem_of_orderOf_four hΩ h.memK h.memK₃ h.ne₁₃ o₃ (h3 ▸ h₁) h₃
    · have h3 : u₃ = u₂⁻¹ * z := by rw [← h']; group
      refine not_mem_of_orderOf_four hΩ h.memK' h.memK₃ h.ne₂₃ o₃ ?_ h₃
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₂) h.hz'.mem
    · have h'' : u₂ * u₃ = u₂ * (u₁ * z) := by rw [h', h.c₁₂]; group
      have h3 : u₃ = u₁ * z := mul_left_cancel h''
      refine not_mem_of_orderOf_four hΩ h.memK h.memK₃ h.ne₁₃ o₃ ?_ h₃
      rw [h3]
      exact Subgroup.mul_mem _ h₁ h.hz.mem
  have := T7B.natCard_closure_three_eq_eight q₁₂ hz2 q₂₃ hne1 h.hz.ne_one hne12 hc1
    hcu₁₂.eq (hcomm _ (by simp) _ (by simp)) (hcomm _ (by simp) _ (by simp)) hnot
  rw [this]
  norm_num

end Hyp22Core

end CFSG.ClassicalInvolution.A7T22
