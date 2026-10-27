module

public import CFSG.ClassicalInvolution.Q3.Q3TMain
public import CFSG.ClassicalInvolution.Q3.Q3CBasic
public import CFSG.ClassicalInvolution.Q3.Q3CTwo
public import CFSG.ClassicalInvolution.Q3.Q3CDatum
public import CFSG.ClassicalInvolution.Q3.Closure

public section

namespace CFSG.ClassicalInvolution.Q3.Q3C

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

@[expose] def TypeC3Third : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        ∃ (K₃ : Subgroup G) (z₃ : G), K₃ ∈ conjClass3 K ∧ IsClassicalMember3 K₃ z₃ ∧
          Commutes K₁ K₃ ∧ Commutes K₂ K₃ ∧ z₃ ≠ z₁ ∧ z₃ ≠ z₂

@[expose] def TypeC3Prod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        ∃ g : G, g * z * g⁻¹ = z₁ * z₂

@[expose] def TypeC3SDatum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ t₁ t₂ t₃ : G),
        AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ →
          ∀ b ∈ axisOf z₁ z₂ t₁ t₂ t₃, b ∉ Subgroup.closure ({z₁, z₂} : Set G) →
            SBaseDatum (axisOf z₁ z₂ t₁ t₂ t₃) b

@[expose] def TypeC3SDatumL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ t₁ t₂ t₃ : G),
        AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ →
          ∀ b ∈ axisOf z₁ z₂ t₁ t₂ t₃, b ∉ Subgroup.closure ({z₁, z₂} : Set G) →
            SBaseDatumL (Subgroup.closure ({z₁, z₂} : Set G)) b

@[expose] def TypeC3SDatumS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ t₁ t₂ t₃ : G),
        AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ →
          SBaseDatumL (Subgroup.closure ({z₁, z₂} : Set G)) (t₁ * t₂ * t₃)

@[expose] def TypeC3Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ t₁ t₂ t₃ : G),
        AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ → rankTwoSpan (axisOf z₁ z₂ t₁ t₂ t₃) = ⊤

@[expose] def TypeC3GenLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ t₁ t₂ t₃ : G),
        AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ →
          ∀ a ∈ Subgroup.closure ({z₁, z₂} : Set G), a ≠ 1 →
            CentralizerGenerationModOTwo (conjClass3 K) (axisOf z₁ z₂ t₁ t₂ t₃) a ∧
              InvolutionLink3 (conjClass3 K) (axisOf z₁ z₂ t₁ t₂ t₃) {K₁, K₂, K₃} a

@[expose] def TypeC3GenAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ t₁ t₂ t₃ : G),
        AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ →
          CentralizerGenerationModOTwo (conjClass3 K) (axisOf z₁ z₂ t₁ t₂ t₃) z₁ ∧
            InvolutionLink3 (conjClass3 K) (axisOf z₁ z₂ t₁ t₂ t₃) {K₁, K₂, K₃} z₁

@[expose] def TypeC3ClassicalBalance : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        ∀ a ∈ Subgroup.closure ({z₁, z₂} : Set G), a ≠ 1 → ComponentBalanceAt (conjClass3 K) a

section Permutation

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K₁ K₂ K₃ : Subgroup G}
  {z₁ z₂ t₁ t₂ t₃ : G}

theorem axisData3_swap12 (hd : AxisData3 Ω K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃) :
    AxisData3 Ω K₂ K₁ K₃ z₂ z₁ t₂ t₁ t₃ :=
  ⟨⟨hd.tri.edge.symm, hd.tri.mem₃, by rw [← hd.tri.edge.comm_involutions]; exact hd.tri.cls₃,
      hd.tri.comm₂₃, hd.tri.comm₁₃⟩, hd.mem₂, hd.mem₁, hd.mem₃, hd.sq₂, hd.sq₁,
    by rw [hd.sq₃]; exact hd.tri.edge.comm_involutions⟩

theorem axisData3_rotate (hd : AxisData3 Ω K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃) :
    AxisData3 Ω K₃ K₁ K₂ (z₁ * z₂) z₁ t₃ t₁ t₂ := by
  have hz1 : z₁ * z₁ = 1 := hd.tri.edge.cls₁.isCentralInvolution.sq
  have e : z₁ * z₂ * z₁ = z₂ := by
    calc z₁ * z₂ * z₁ = z₁ * (z₂ * z₁) := mul_assoc _ _ _
      _ = z₁ * (z₁ * z₂) := by rw [← hd.tri.edge.comm_involutions]
      _ = (z₁ * z₁) * z₂ := (mul_assoc _ _ _).symm
      _ = z₂ := by rw [hz1, one_mul]
  have hne : z₁ * z₂ ≠ z₁ := fun h' => hd.tri.edge.cls₂.ne_one (by simpa using h')
  refine ⟨⟨⟨hd.tri.mem₃, hd.tri.edge.mem₁, hd.tri.cls₃, hd.tri.edge.cls₁,
      fun x hx y hy => (hd.tri.comm₁₃ y hy x hx).symm, hne⟩, hd.tri.edge.mem₂, ?_,
      fun x hx y hy => (hd.tri.comm₂₃ y hy x hx).symm, hd.tri.edge.comm⟩, hd.mem₃, hd.mem₁,
    hd.mem₂, hd.sq₃, hd.sq₁, ?_⟩
  · rw [e]; exact hd.tri.edge.cls₂
  · rw [e]; exact hd.sq₂

theorem axisOf_swap12 (hd : AxisData3 Ω K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃) :
    axisOf z₂ z₁ t₂ t₁ t₃ = axisOf z₁ z₂ t₁ t₂ t₃ := by
  have hct : t₂ * t₁ = t₁ * t₂ := (hd.tri.edge.comm t₁ hd.mem₁ t₂ hd.mem₂).symm
  unfold axisOf
  rw [hct, Set.pair_comm z₂ z₁]

theorem axisOf_rotate (hd : AxisData3 Ω K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃) :
    axisOf (z₁ * z₂) z₁ t₃ t₁ t₂ = axisOf z₁ z₂ t₁ t₂ t₃ := by
  have hz1 : z₁ * z₁ = 1 := hd.tri.edge.cls₁.isCentralInvolution.sq
  have c13 : t₁ * t₃ = t₃ * t₁ := hd.tri.comm₁₃ t₁ hd.mem₁ t₃ hd.mem₃
  have c23 : t₂ * t₃ = t₃ * t₂ := hd.tri.comm₂₃ t₂ hd.mem₂ t₃ hd.mem₃
  have hs : t₃ * t₁ * t₂ = t₁ * t₂ * t₃ := by
    calc t₃ * t₁ * t₂ = (t₃ * t₁) * t₂ := rfl
      _ = (t₁ * t₃) * t₂ := by rw [c13]
      _ = t₁ * (t₃ * t₂) := by group
      _ = t₁ * (t₂ * t₃) := by rw [c23]
      _ = t₁ * t₂ * t₃ := by group
  unfold axisOf
  rw [hs]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h | h
    · rw [h]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [Set.mem_singleton_iff] at h
      rw [h]; exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h | h
    · rw [h]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at h
      have e : x = z₁ * (z₁ * z₂) := by rw [h, ← mul_assoc, hz1, one_mul]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

end Permutation

theorem typeC3Triangle_of_third (h : TypeC3Third) : TypeC3Triangle := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  obtain ⟨K₃, z₃, hK₃, hz₃, h13, h23, h1, h2⟩ :=
    h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  exact ⟨K₃, isTriangle3_of_third hB he hK₃ hz₃ h13 h23 h1 h2⟩

theorem typeC3Third_of_prod (h : TypeC3Prod) : TypeC3Third := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  obtain ⟨g, hg⟩ := h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  have hK₃ : conjSub g K ∈ conjClass3 K := ⟨g, rfl⟩
  have hz₃ : IsClassicalMember3 (conjSub g K) (z₁ * z₂) := hg ▸ hz.conj g
  have h1 : z₁ * z₂ ≠ z₁ := fun h' => he.cls₂.ne_one (by simpa using h')
  have h2 : z₁ * z₂ ≠ z₂ := fun h' => he.cls₁.ne_one (by simpa using h')
  have hc1 : (z₁ * z₂) * z₁ = z₁ * (z₁ * z₂) := by
    rw [mul_assoc, ← he.comm_involutions]
  have hc2 : (z₁ * z₂) * z₂ = z₂ * (z₁ * z₂) := by
    rw [← mul_assoc, ← he.comm_involutions, mul_assoc]
  have h13 := commutes_of_not_a2Configuration3 hz hA2 hK₃ he.mem₁ hz₃ he.cls₁ h1 hc1
  have h23 := commutes_of_not_a2Configuration3 hz hA2 hK₃ he.mem₂ hz₃ he.cls₂ h2 hc2
  exact ⟨conjSub g K, z₁ * z₂, hK₃, hz₃, fun x hx y hy => (h13 y hy x hx).symm,
    fun x hx y hy => (h23 y hy x hx).symm, h1, h2⟩

theorem typeC3SDatum_of_datumL (h : TypeC3SDatumL) : TypeC3SDatum := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd b hbA hbB
  exact sBaseDatum_of_datumL hnab hBelow hd.isElemAbelian_axis hd.card_axis
    (pair_le_axis z₁ z₂ t₁ t₂ t₃) hd.tri.edge.card_pair hbA hbB
    (h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd b hbA hbB)

theorem typeC3SDatumL_of_s (h : TypeC3SDatumS) : TypeC3SDatumL := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd b hbA hbB
  have hz1 : z₁ * z₁ = 1 := hd.tri.edge.cls₁.isCentralInvolution.sq
  have hz2 : z₂ * z₂ = 1 := hd.tri.edge.cls₂.isCentralInvolution.sq
  have hprod := mul_mem_of_not_mem_of_not_mem hd.isElemAbelian_axis hd.card_axis
    (pair_le_axis z₁ z₂ t₁ t₂ t₃) hd.tri.edge.card_pair hbA (s_mem_axis z₁ z₂ t₁ t₂ t₃) hbB
    hd.s_not_mem_pair
  have hb : b = (b * (t₁ * t₂ * t₃)) * (t₁ * t₂ * t₃) := by
    rw [mul_assoc, hd.s_mul_self, mul_one]
  have hz₂t₁ : z₂ * t₁ = t₁ * z₂ := (hd.tri.edge.comm t₁ hd.mem₁ z₂ hd.tri.edge.cls₂.mem).symm
  have ht₁ : t₁⁻¹ = z₁ * t₁ := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc t₁ * (z₁ * t₁) = t₁ * ((t₁ * t₁) * t₁) := by rw [hd.sq₁]
      _ = (t₁ * t₁) * (t₁ * t₁) := by group
      _ = 1 := by rw [hd.sq₁, hz1]
  have ht₂ : t₂⁻¹ = z₂ * t₂ := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc t₂ * (z₂ * t₂) = t₂ * ((t₂ * t₂) * t₂) := by rw [hd.sq₂]
      _ = (t₂ * t₂) * (t₂ * t₂) := by group
      _ = 1 := by rw [hd.sq₂, hz2]
  have hsq₁ : t₁⁻¹ * t₁⁻¹ = z₁ := by
    rw [← mul_inv_rev, hd.sq₁]
    exact inv_eq_of_mul_eq_one_right hz1
  have hsq₂ : t₂⁻¹ * t₂⁻¹ = z₂ := by
    rw [← mul_inv_rev, hd.sq₂]
    exact inv_eq_of_mul_eq_one_right hz2
  have hd₁ : AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁⁻¹ t₂ t₃ :=
    ⟨hd.tri, K₁.inv_mem hd.mem₁, hd.mem₂, hd.mem₃, hsq₁, hd.sq₂, hd.sq₃⟩
  have hd₂ : AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁ t₂⁻¹ t₃ :=
    ⟨hd.tri, hd.mem₁, K₂.inv_mem hd.mem₂, hd.mem₃, hd.sq₁, hsq₂, hd.sq₃⟩
  have hd₁₂ : AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁⁻¹ t₂⁻¹ t₃ :=
    ⟨hd.tri, K₁.inv_mem hd.mem₁, K₂.inv_mem hd.mem₂, hd.mem₃, hsq₁, hsq₂, hd.sq₃⟩
  rcases mem_closure_pair_commuting hz1 hz2 hd.tri.edge.comm_involutions hprod with
    h0 | h0 | h0 | h0
  · rw [hb, h0, one_mul]
    exact h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd
  · have e : b = t₁⁻¹ * t₂ * t₃ := by rw [hb, h0, ht₁]; group
    rw [e]
    exact h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁⁻¹ t₂ t₃ hd₁
  · have e : b = t₁ * t₂⁻¹ * t₃ := by
      rw [hb, h0, ht₂]
      calc z₂ * (t₁ * t₂ * t₃) = (z₂ * t₁) * t₂ * t₃ := by group
        _ = t₁ * (z₂ * t₂) * t₃ := by rw [hz₂t₁]; group
    rw [e]
    exact h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂⁻¹ t₃ hd₂
  · have e : b = t₁⁻¹ * t₂⁻¹ * t₃ := by
      rw [hb, h0, ht₁, ht₂]
      calc z₁ * z₂ * (t₁ * t₂ * t₃) = z₁ * (z₂ * t₁) * t₂ * t₃ := by group
        _ = (z₁ * t₁) * (z₂ * t₂) * t₃ := by rw [hz₂t₁]; group
    rw [e]
    exact h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁⁻¹ t₂⁻¹ t₃ hd₁₂

theorem typeC3Gen_of_local (h : TypeC3GenLocal) : TypeC3Gen := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hconn : CFSG.ClassicalInvolution.Generic.DeltaClosure.OmegaConnected (conjClass3 K) :=
    CFSG.ClassicalInvolution.Generic.DeltaClosure.omegaConnected_range_conjSub hΔ
  have hloc := h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd
  have hz₁A : z₁ ∈ axisOf z₁ z₂ t₁ t₂ t₃ :=
    pair_le_axis z₁ z₂ t₁ t₂ t₃ (Subgroup.subset_closure (by simp))
  have hz₂A : z₂ ∈ axisOf z₁ z₂ t₁ t₂ t₃ :=
    pair_le_axis z₁ z₂ t₁ t₂ t₃ (Subgroup.subset_closure (by simp))
  have hz₃A : z₁ * z₂ ∈ axisOf z₁ z₂ t₁ t₂ t₃ := mul_mem hz₁A hz₂A
  have hfr : ∀ a : G, IsFrameInvolution3 ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      a ∈ Subgroup.closure ({z₁, z₂} : Set G) ∧ a ≠ 1 := by
    rintro a ⟨M, hM, ha⟩
    refine ⟨?_, ha.ne_one⟩
    rcases hM with rfl | rfl | rfl
    · rw [involution_unique3 ha hd.tri.edge.cls₁]
      exact Subgroup.subset_closure (by simp)
    · rw [involution_unique3 ha hd.tri.edge.cls₂]
      exact Subgroup.subset_closure (by simp)
    · rw [involution_unique3 ha hd.tri.cls₃]
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  refine rankTwoSpan_eq_top3 (S := ({K₁, K₂, K₃} : Set (Subgroup G))) hΩ
    ⟨hd.isElemAbelian_axis, hd.card_axis.ge, ?_, ⟨K₁, by simp⟩, ?_, ?_, ?_⟩ hconn
  · intro M hM
    rcases hM with rfl | rfl | rfl
    · exact hd.tri.edge.mem₁
    · exact hd.tri.edge.mem₂
    · exact hd.tri.mem₃
  · intro M hM
    rcases hM with rfl | rfl | rfl
    · exact ⟨z₁, hz₁A, hd.tri.edge.cls₁⟩
    · exact ⟨z₂, hz₂A, hd.tri.edge.cls₂⟩
    · exact ⟨z₁ * z₂, hz₃A, hd.tri.cls₃⟩
  · intro a _ hfa
    obtain ⟨haB, ha1⟩ := hfr a hfa
    exact (hloc a haB ha1).1
  · intro a _ hfa
    obtain ⟨haB, ha1⟩ := hfr a hfa
    exact (hloc a haB ha1).2

theorem typeC3GenLocal_of_at (h : TypeC3GenAt) : TypeC3GenLocal := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd a ha ha1
  have hz1 : z₁ * z₁ = 1 := hd.tri.edge.cls₁.isCentralInvolution.sq
  have hz2 : z₂ * z₂ = 1 := hd.tri.edge.cls₂.isCentralInvolution.sq
  rcases mem_closure_pair_commuting hz1 hz2 hd.tri.edge.comm_involutions ha with
    h0 | h0 | h0 | h0
  · exact absurd h0 ha1
  · rw [h0]
    exact h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd
  · rw [h0]
    have := h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₂ K₁ K₃ z₂ z₁ t₂ t₁ t₃
      (axisData3_swap12 hd)
    rw [axisOf_swap12 hd, Set.insert_comm K₂ K₁ {K₃}] at this
    exact this
  · rw [h0]
    have := h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₃ K₁ K₂ (z₁ * z₂) z₁ t₃ t₁ t₂
      (axisData3_rotate hd)
    have hfr : ({K₃, K₁, K₂} : Set (Subgroup G)) = {K₁, K₂, K₃} := by
      ext M
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [axisOf_rotate hd, hfr] at this
    exact this

theorem typeC3ClassicalBalance_of_kg1 (hKG1 : LieLocallyTwoBalanced3)
    (hM11 : M11LocallyTwoBalanced) : TypeC3ClassicalBalance := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he a _ ha1
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hnc : a ∉ Subgroup.center G := fun hbc =>
    not_subset_center_of_ne_one hnab ha1 (Set.singleton_subset_iff.mpr hbc)
  exact componentBalanceAt_of_localLieSystems3 CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
    m11Facts hKG1 hM11 hΩ hIH (fun h => hnc (h rfl))

theorem typeC3Alpha_of_inputs (hBal : TypeC3ClassicalBalance) (hTri : TypeC3Triangle)
    (hS : TypeC3SDatum) (hGen : TypeC3Gen) : TypeC3Alpha := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  obtain ⟨K₃, htri⟩ := hTri G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  obtain ⟨t₁, t₂, t₃, hd⟩ := exists_axisData3 htri
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hIH
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hnab hb1 (Set.singleton_subset_iff.mpr hbc)
  have hcl : ∀ a ∈ Subgroup.closure ({z₁, z₂} : Set G), a ≠ 1 →
      ComponentBalanceAt (conjClass3 K) a :=
    hBal G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  have hbal := rankThreeBalance_of_axis lieSystemOddCentralizer3_proved hΩ.conjInvariant hO hnc hd
    hcl (hS G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd)
  have hgen := hGen G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd
  have hA : EdgeAxis3 z₁ z₂ (axisOf z₁ z₂ t₁ t₂ t₃) := ⟨pair_le_axis z₁ z₂ t₁ t₂ t₃, hbal, hgen⟩
  exact hA.alphaCore_eq_bot hnab (hA.pair_mem he)

theorem typeC3Alpha_of_kg1_inputs (hKG1 : LieLocallyTwoBalanced3) (hM11 : M11LocallyTwoBalanced)
    (hTri : TypeC3Triangle) (hS : TypeC3SDatum) (hGen : TypeC3Gen) : TypeC3Alpha :=
  typeC3Alpha_of_inputs (typeC3ClassicalBalance_of_kg1 hKG1 hM11) hTri hS hGen

structure TypeC3Inputs : Prop where
  classicalBalance : TypeC3ClassicalBalance
  prod : TypeC3Prod
  sDatum : TypeC3SDatumS
  gen : TypeC3GenAt
  recognition : TypeC3Rec

theorem TypeC3Inputs.alpha (h : TypeC3Inputs) : TypeC3Alpha :=
  typeC3Alpha_of_inputs h.classicalBalance (typeC3Triangle_of_third (typeC3Third_of_prod h.prod))
    (typeC3SDatum_of_datumL (typeC3SDatumL_of_s h.sDatum))
    (typeC3Gen_of_local (typeC3GenLocal_of_at h.gen))

theorem TypeC3Inputs.smallTypeC3 (h : TypeC3Inputs) : SmallTypeC3I :=
  smallTypeC3_of_alpha_rec h.alpha h.recognition

theorem TypeC3Inputs.of_finest (hKG1 : LieLocallyTwoBalanced3) (hM11 : M11LocallyTwoBalanced)
    (hProd : TypeC3Prod) (hS : TypeC3SDatumS) (hGen : TypeC3GenAt) (hRec : TypeC3Rec) :
    TypeC3Inputs :=
  ⟨typeC3ClassicalBalance_of_kg1 hKG1 hM11, hProd, hS, hGen, hRec⟩

theorem smallTypeC3_of_finest (hKG1 : LieLocallyTwoBalanced3) (hM11 : M11LocallyTwoBalanced)
    (hProd : TypeC3Prod) (hS : TypeC3SDatumS) (hGen : TypeC3GenAt) (hRec : TypeC3Rec) :
    SmallTypeC3I :=
  (TypeC3Inputs.of_finest hKG1 hM11 hProd hS hGen hRec).smallTypeC3

end CFSG.ClassicalInvolution.Q3.Q3C
