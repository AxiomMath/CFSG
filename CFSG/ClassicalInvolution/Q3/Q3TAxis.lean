module

public import CFSG.ClassicalInvolution.Q3.Q3TSetup

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement MatrixGroups

section Triangle

variable {G : Type} [Group G]

theorem not_central_of_sq [Finite G] {K : Subgroup G} {z : G} (hK : IsClassicalMember3 K z)
    {t : G} (ht : t ∈ K) (hsq : t * t = z) : ¬ ∀ k ∈ K, t * k = k * t := by
  intro hcen
  obtain ⟨φ, hφ⟩ := hK.exists_chart
  have hc : φ ⟨t, ht⟩ ∈ Subgroup.center SL(2, ZMod 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hφ.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hcen k k.2).symm)
  have h1 : φ ⟨z, hK.mem⟩ = -1 := hφ.map_central hK.isCentralInvolution
  have h2 : φ (⟨t, ht⟩ * ⟨t, ht⟩) = φ ⟨z, hK.mem⟩ := congrArg φ (Subtype.ext hsq)
  rw [map_mul, h1] at h2
  have hne : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide +kernel
  have hmm : (-1 : SL(2, ZMod 3)) * (-1) = 1 := by decide +kernel
  rcases (mem_center_sl2_iff _).mp hc with h | h
  · rw [h, mul_one] at h2
    exact hne h2.symm
  · rw [h, hmm] at h2
    exact hne h2.symm

structure IsTriangle3 (Ω : Set (Subgroup G)) (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ : G) : Prop where
  edge : IsEdge3 Ω K₁ K₂ z₁ z₂
  mem₃ : K₃ ∈ Ω
  cls₃ : IsClassicalMember3 K₃ (z₁ * z₂)
  comm₁₃ : Commutes K₁ K₃
  comm₂₃ : Commutes K₂ K₃

structure AxisData3 (Ω : Set (Subgroup G)) (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ t₁ t₂ t₃ : G) :
    Prop where
  tri : IsTriangle3 Ω K₁ K₂ K₃ z₁ z₂
  mem₁ : t₁ ∈ K₁
  mem₂ : t₂ ∈ K₂
  mem₃ : t₃ ∈ K₃
  sq₁ : t₁ * t₁ = z₁
  sq₂ : t₂ * t₂ = z₂
  sq₃ : t₃ * t₃ = z₁ * z₂

@[expose] def axisOf (z₁ z₂ t₁ t₂ t₃ : G) : Subgroup G :=
  Subgroup.closure (insert (t₁ * t₂ * t₃) ({z₁, z₂} : Set G))

section Existence

variable [Finite G] {Ω : Set (Subgroup G)} {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ : G}

theorem exists_axisData3 (h : IsTriangle3 Ω K₁ K₂ K₃ z₁ z₂) :
    ∃ t₁ t₂ t₃ : G, AxisData3 Ω K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ := by
  obtain ⟨t₁, ht₁, -, -, h₁, -⟩ := h.edge.cls₁.exists_quaternion_pair
  obtain ⟨t₂, ht₂, -, -, h₂, -⟩ := h.edge.cls₂.exists_quaternion_pair
  obtain ⟨t₃, ht₃, -, -, h₃, -⟩ := h.cls₃.exists_quaternion_pair
  exact ⟨t₁, t₂, t₃, ⟨h, ht₁, ht₂, ht₃, h₁, h₂, h₃⟩⟩

end Existence

theorem pair_le_axis (z₁ z₂ t₁ t₂ t₃ : G) :
    Subgroup.closure ({z₁, z₂} : Set G) ≤ axisOf z₁ z₂ t₁ t₂ t₃ :=
  Subgroup.closure_mono (Set.subset_insert _ _)

theorem s_mem_axis (z₁ z₂ t₁ t₂ t₃ : G) : t₁ * t₂ * t₃ ∈ axisOf z₁ z₂ t₁ t₂ t₃ :=
  Subgroup.subset_closure (Set.mem_insert _ _)

namespace AxisData3

variable {Ω : Set (Subgroup G)} {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ t₁ t₂ t₃ : G}
  (h : AxisData3 Ω K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃)

include h

theorem le_centralizer_pair₃ :
    K₃ ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact h.tri.comm₁₃ _ h.tri.edge.cls₁.mem k hk
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h.tri.comm₂₃ _ h.tri.edge.cls₂.mem k hk

theorem s_mem_centralizer :
    t₁ * t₂ * t₃ ∈ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (h.tri.edge.le_centralizer_pair h.mem₁)
    (h.tri.edge.le_centralizer_pair' h.mem₂)) (h.le_centralizer_pair₃ h.mem₃)

theorem s_mul_self : (t₁ * t₂ * t₃) * (t₁ * t₂ * t₃) = 1 := by
  have c12 : Commute t₁ t₂ := h.tri.edge.comm t₁ h.mem₁ t₂ h.mem₂
  have c13 : Commute t₁ t₃ := h.tri.comm₁₃ t₁ h.mem₁ t₃ h.mem₃
  have c23 : Commute t₂ t₃ := h.tri.comm₂₃ t₂ h.mem₂ t₃ h.mem₃
  have hc : Commute (t₁ * t₂) t₃ := c13.mul_left c23
  have e : (t₁ * t₂ * t₃) ^ 2 = t₁ ^ 2 * t₂ ^ 2 * t₃ ^ 2 := by
    rw [Commute.mul_pow hc, Commute.mul_pow c12]
  rw [← pow_two, e, pow_two t₁, pow_two t₂, pow_two t₃, h.sq₁, h.sq₂, h.sq₃]
  have hz1 := h.tri.edge.cls₁.isCentralInvolution.sq
  have hz2 := h.tri.edge.cls₂.isCentralInvolution.sq
  have hzc := h.tri.edge.comm_involutions
  calc z₁ * z₂ * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
    _ = z₁ * (z₁ * z₂) * z₂ := by rw [← hzc]
    _ = (z₁ * z₁) * (z₂ * z₂) := by group
    _ = 1 := by rw [hz1, hz2, one_mul]

theorem s_not_mem_pair [Finite G] : t₁ * t₂ * t₃ ∉ Subgroup.closure ({z₁, z₂} : Set G) := by
  intro hs
  refine not_central_of_sq h.tri.edge.cls₁ h.mem₁ h.sq₁ fun k hk => ?_
  have hsk : (t₁ * t₂ * t₃) * k = k * (t₁ * t₂ * t₃) :=
    Subgroup.mem_centralizer_iff.mp (h.tri.edge.le_centralizer_pair hk) _ hs
  have h2 : k * t₂ = t₂ * k := h.tri.edge.comm k hk t₂ h.mem₂
  have h3 : k * t₃ = t₃ * k := h.tri.comm₁₃ k hk t₃ h.mem₃
  have e : k * t₂ * t₃ = t₂ * t₃ * k := by
    calc k * t₂ * t₃ = (k * t₂) * t₃ := rfl
      _ = (t₂ * k) * t₃ := by rw [h2]
      _ = t₂ * (k * t₃) := by group
      _ = t₂ * (t₃ * k) := by rw [h3]
      _ = t₂ * t₃ * k := by group
  have hm : (t₁ * k) * (t₂ * t₃) = (k * t₁) * (t₂ * t₃) := by
    calc (t₁ * k) * (t₂ * t₃) = t₁ * (k * t₂ * t₃) := by group
      _ = t₁ * (t₂ * t₃ * k) := by rw [e]
      _ = (t₁ * t₂ * t₃) * k := by group
      _ = k * (t₁ * t₂ * t₃) := hsk
      _ = (k * t₁) * (t₂ * t₃) := by group
  exact mul_right_cancel hm

theorem isElemAbelian_axis : IsElemAbelian 2 (axisOf z₁ z₂ t₁ t₂ t₃) := by
  have hz1 := h.tri.edge.cls₁.isCentralInvolution.sq
  have hz2 := h.tri.edge.cls₂.isCentralInvolution.sq
  have hzc := h.tri.edge.comm_involutions
  have hsC := h.s_mem_centralizer
  have hs1 : t₁ * t₂ * t₃ * z₁ = z₁ * (t₁ * t₂ * t₃) :=
    (Subgroup.mem_centralizer_iff.mp hsC z₁ (Subgroup.subset_closure (by simp))).symm
  have hs2 : t₁ * t₂ * t₃ * z₂ = z₂ * (t₁ * t₂ * t₃) :=
    (Subgroup.mem_centralizer_iff.mp hsC z₂ (Subgroup.subset_closure (by simp))).symm
  refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
  · intro s hs
    rcases hs with rfl | hs
    · exact h.s_mul_self
    · rcases hs with rfl | hs
      · exact hz1
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hz2
  · intro s hs t ht
    rcases hs with rfl | hs <;> rcases ht with rfl | ht
    · rfl
    · rcases ht with rfl | ht
      · exact hs1
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        exact hs2
    · rcases hs with rfl | hs
      · exact hs1.symm
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hs2.symm
    · rcases hs with rfl | hs <;> rcases ht with rfl | ht
      · rfl
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        exact hzc
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hzc.symm
      · rw [Set.mem_singleton_iff] at hs ht
        subst hs ht
        rfl

theorem card_axis [Finite G] : Nat.card (axisOf z₁ z₂ t₁ t₂ t₃) = 8 := by
  have hB : Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) = 4 := h.tri.edge.card_pair
  have hscomm : ∀ x ∈ ({z₁, z₂} : Set G), (t₁ * t₂ * t₃) * x = x * (t₁ * t₂ * t₃) := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp h.s_mem_centralizer x
      (Subgroup.subset_closure hx)).symm
  have hle : Nat.card (axisOf z₁ z₂ t₁ t₂ t₃) ≤ 8 := by
    have := Theorem5.card_closure_insert_le h.s_mul_self hscomm
    rw [hB] at this
    exact this
  have hBA := pair_le_axis z₁ z₂ t₁ t₂ t₃
  have hdvd : 4 ∣ Nat.card (axisOf z₁ z₂ t₁ t₂ t₃) := hB ▸ Subgroup.card_dvd_of_le hBA
  have hpos : 0 < Nat.card (axisOf z₁ z₂ t₁ t₂ t₃) := Nat.card_pos
  by_contra h8
  have h4 : Nat.card (axisOf z₁ z₂ t₁ t₂ t₃) = 4 := by omega
  have hEq := Subgroup.eq_of_le_of_card_ge hBA (by omega)
  exact h.s_not_mem_pair (hEq ▸ s_mem_axis z₁ z₂ t₁ t₂ t₃)

theorem pair_mem_axis [Finite G] :
    Subgroup.closure ({z₁, z₂} : Set G) ∈
      signalizerFunctorEk 2 2 (axisOf z₁ z₂ t₁ t₂ t₃) :=
  ⟨pair_le_axis z₁ z₂ t₁ t₂ t₃, by rw [h.tri.edge.card_pair]; norm_num⟩

end AxisData3

end Triangle

section Weak

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K₁ K₂ K₃ : Subgroup G}
  {z₁ z₂ t₁ t₂ t₃ : G} (h : AxisData3 Ω K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃)

namespace AxisData3

include h

omit [Finite G] in
theorem axis_le_centralizingLayer {b : G} (hb : b ∈ Subgroup.closure ({z₁, z₂} : Set G)) :
    axisOf z₁ z₂ t₁ t₂ t₃ ≤ centralizingLayer Ω {b} := by
  have hbc : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer
      (Subgroup.closure ({z₁, z₂} : Set G) : Set G) → K ≤ Subgroup.centralizer ({b} : Set G) :=
    fun hK => hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have hK₁ : K₁ ≤ centralizingLayer Ω {b} :=
    le_centralizingLayer ⟨h.tri.edge.mem₁, hbc h.tri.edge.le_centralizer_pair⟩
  have hK₂ : K₂ ≤ centralizingLayer Ω {b} :=
    le_centralizingLayer ⟨h.tri.edge.mem₂, hbc h.tri.edge.le_centralizer_pair'⟩
  have hK₃ : K₃ ≤ centralizingLayer Ω {b} :=
    le_centralizingLayer ⟨h.tri.mem₃, hbc h.le_centralizer_pair₃⟩
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases hx with rfl | hx
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK₁ h.mem₁) (hK₂ h.mem₂)) (hK₃ h.mem₃)
  · rcases hx with rfl | hx
    · exact hK₁ h.tri.edge.cls₁.mem
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hK₂ h.tri.edge.cls₂.mem

theorem weakBalanced_classical (hΩ : ConjInvariant Ω) (hO : LocalOddCentralizer3 Ω)
    (hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G) :
    ∀ a ∈ axisOf z₁ z₂ t₁ t₂ t₃, a ≠ 1 → ∀ b ∈ Subgroup.closure ({z₁, z₂} : Set G), b ≠ 1 →
      ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, axisOf z₁ z₂ t₁ t₂ t₃⁆ ≤
        involutionOddCore b := by
  have hA := h.isElemAbelian_axis
  intro a ha ha1 b hb hb1
  rw [Subgroup.commutator_le]
  intro r hr g hg
  refine commutator_mem_involutionOddCore_of_localOddCentralizer3 hΩ hO (hnc b hb1)
    (h.axis_le_centralizingLayer hb ha) (orderOf_eq_prime (hA.2 a ha) ha1) hr
    ⟨h.axis_le_centralizingLayer hb hg, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm (⟨g, hg⟩ : axisOf z₁ z₂ t₁ t₂ t₃) ⟨a, ha⟩))

end AxisData3

end Weak

section Rest

variable {G : Type} [Group G]

@[expose] def WeakBalancedOutside (A B : Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ∉ B →
    ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b

theorem weakBalanced_of_classical_of_outside {A B : Subgroup G}
    (hcl : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ B, b ≠ 1 →
      ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b)
    (hout : WeakBalancedOutside A B) : WeakBalanced A := by
  intro a ha ha1 b hb hb1
  by_cases hbB : b ∈ B
  · exact hcl a ha ha1 b hbB hb1
  · exact hout a ha ha1 b hb hbB

structure AxisRest3 (A B : Subgroup G) : Prop where
  weakOutside : WeakBalancedOutside A B
  two : TwoBalancedWrt A
  generation : rankTwoSpan A = ⊤

end Rest

@[expose] def TypeC3Triangle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        ∃ K₃ : Subgroup G, IsTriangle3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂

@[expose] def TypeC3AxisRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ t₁ t₂ t₃ : G),
        AxisData3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ →
          AxisRest3 (axisOf z₁ z₂ t₁ t₂ t₃) (Subgroup.closure ({z₁, z₂} : Set G))

theorem typeC3Axes_of_triangle_rest (h1 : TypeC3Triangle) (h2 : TypeC3AxisRest) :
    TypeC3Axes := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  obtain ⟨K₃, htri⟩ := h1 G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  obtain ⟨t₁, t₂, t₃, hd⟩ := exists_axisData3 htri
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hIH
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hnab hb1 (Set.singleton_subset_iff.mpr hbc)
  have hrest := h2 G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ hd
  refine ⟨axisOf z₁ z₂ t₁ t₂ t₃, pair_le_axis z₁ z₂ t₁ t₂ t₃, ⟨hd.isElemAbelian_axis, hd.card_axis,
    weakBalanced_of_classical_of_outside (hd.weakBalanced_classical hΩ.conjInvariant hO hnc)
      hrest.weakOutside, hrest.two⟩, hrest.generation⟩

end CFSG.ClassicalInvolution.Q3
