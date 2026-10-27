module

public import CFSG.ClassicalInvolution.Asc77.AscT7JLayer
public import CFSG.ClassicalInvolution.Asc77.AscT7JHyp51u
public import CFSG.ClassicalInvolution.Asc77.AscT7HX22
import CFSG.ClassicalInvolution.Asc77.AscT7S22Sigma
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3FrameChain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Inputs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Hyp22FourTwins : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃ ∧
        ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ ∨ M = K₄

@[expose] def Hyp22Fuse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ K₄ ∈ twinSet Ω K, K₄ ≠ K → K₄ ≠ K' → K₄ ≠ K₃ →
        ∃ (R R' : Subgroup G) (b b' y : G),
          IsSylow2In R (ExactLayer.exactCore (u₁ * u₂) K₃) ∧
          IsSylow2In R' (ExactLayer.exactCore (u₁ * u₂) K₄) ∧ Commutes R R' ∧
          b ∈ ExactLayer.exactCore (u₁ * u₂) K₃ ∧ b' ∈ ExactLayer.exactCore (u₁ * u₂) K₄ ∧
          b * b = z ∧ b' * b' = z ∧ y ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) ∧
          y * z * y⁻¹ = b * b' * (u₁ * u₂) ∧ b * b' * (u₁ * u₂) ≠ z ∧
          z * (b * b' * (u₁ * u₂)) = (b * b' * (u₁ * u₂)) * z

@[expose] def C22_8Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤

end Inputs

namespace T7J

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem not_mem_tqMembers_of_mul (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z u v c : G} (hz : IsUniqueInvolution K z) (huK : u ∈ K)
    (hu4 : orderOf u = 4) (hv : v ∈ trivialOnQuot K) (hc : c = u * v) : K ∉ tqMembers Ω c := by
  intro hKt
  have hcK : c ∈ trivialOnQuot K := hKt.2
  have hu : u ∈ trivialOnQuot K := by
    have : u = c * v⁻¹ := by rw [hc]; group
    rw [this]
    exact Subgroup.mul_mem _ hcK (Subgroup.inv_mem _ hv)
  have hcomm : ∀ y ∈ K, ⁅u, y⁆ ∈ oddCoreOf K := fun y hy =>
    (mem_trivialOnQuot_iff.mp hu).2 y hy
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := T7A.isPGroup_zpowers_of_orderOf_four hu4
  rcases hΩ.center_two hp hq hK hz u huK hu2 hcomm with h | h
  · rw [h, orderOf_one] at hu4
    omega
  · rw [h] at hu4
    have : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    omega

end Layer

end T7J

section Reduction

variable {p f : ℕ} [Fact p.Prime]

theorem c22_8X_layer_of_inputs (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G} (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) := by
  have hs := h.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hBelow : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  obtain ⟨K₄, hK₄, hK₄K, hK₄K', hK₄K₃, hV⟩ := h4 G Ω K K' K₃ z u₁ u₂ u₃ hs
  obtain ⟨R, R', b, b', y, hR, hR', hRR', hb, hb', ob, ob', hyc, hyz, htz, hzt⟩ :=
    hF G Ω K K' K₃ z u₁ u₂ u₃ h K₄ hK₄ hK₄K hK₄K' hK₄K₃
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have hu₁K₃ : u₁ ∈ trivialOnQuot K₃ :=
    T7J.twin_le_trivialOnQuot hΩ hKΩ hK₃Ω hs.hK₃K.symm hz hzK₃ hs.hu₁.1
  have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ :=
    T7J.twin_le_trivialOnQuot hΩ hK'Ω hK₃Ω hs.hK₃K'.symm hzK' hzK₃ hs.hu₂.1
  have hu₁K₄ : u₁ ∈ trivialOnQuot K₄ :=
    T7J.twin_le_trivialOnQuot hΩ hKΩ hK₄Ω hK₄K.symm hz hzK₄ hs.hu₁.1
  have hu₂K₄ : u₂ ∈ trivialOnQuot K₄ :=
    T7J.twin_le_trivialOnQuot hΩ hK'Ω hK₄Ω hK₄K'.symm hzK' hzK₄ hs.hu₂.1
  have hK₃t : K₃ ∈ tqMembers Ω (u₁ * u₂) := ⟨hK₃Ω, Subgroup.mul_mem _ hu₁K₃ hu₂K₃⟩
  have hK₄t : K₄ ∈ tqMembers Ω (u₁ * u₂) := ⟨hK₄Ω, Subgroup.mul_mem _ hu₁K₄ hu₂K₄⟩
  have hu₂K : u₂ ∈ trivialOnQuot K :=
    T7J.twin_le_trivialOnQuot hΩ hK'Ω hKΩ hs.hne hzK' hz hs.hu₂.1
  have hu₁K' : u₁ ∈ trivialOnQuot K' :=
    T7J.twin_le_trivialOnQuot hΩ hKΩ hK'Ω hs.hne.symm hz hzK' hs.hu₁.1
  have hnotK : K ∉ tqMembers Ω (u₁ * u₂) :=
    T7J.not_mem_tqMembers_of_mul hp hq hΩ hKΩ hz hs.hu₁.1 hs.hu₁.2 hu₂K rfl
  have hnotK' : K' ∉ tqMembers Ω (u₁ * u₂) :=
    T7J.not_mem_tqMembers_of_mul hp hq hΩ hK'Ω hzK' hs.hu₂.1 hs.hu₂.2 hu₁K' hs.comm₁₂
  have hperp₃ : ∀ J ∈ tqMembers Ω (u₁ * u₂), J ∈ KPerp Ω K₃ → J = K₃ ∨ J = K₄ := by
    intro J hJt hJperp
    rw [T7S22.perp_of_twin hs hs.hK₃, twinSet_eq_of_mem_twinSet hz hs.hK₃] at hJperp
    rcases hV J hJperp with rfl | rfl | rfl | rfl
    · exact absurd hJt hnotK
    · exact absurd hJt hnotK'
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hperp₄ : ∀ J ∈ tqMembers Ω (u₁ * u₂), J ∈ KPerp Ω K₄ → J = K₄ ∨ J = K₃ := by
    intro J hJt hJperp
    rw [T7S22.perp_of_twin hs hK₄, twinSet_eq_of_mem_twinSet hz hK₄] at hJperp
    rcases hV J hJperp with rfl | rfl | rfl | rfl
    · exact absurd hJt hnotK
    · exact absurd hJt hnotK'
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hc1 : u₁ * u₂ ≠ 1 :=
    (T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hMz : IsClassicalMember p f K₃ z := isClassicalMember_of_twin hΩ hK₃Ω hzK₃
  have hnc : ¬ ({u₁ * u₂} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one (exists_noncomm_of_isClassicalMember hMz) hc1
  have hL : conjSub y K₃ ∈ tqMembers Ω (u₁ * u₂) :=
    conjSub_mem_tqMembers hΩ.conjInvariant hyc hK₃t
  have htL : IsUniqueInvolution (conjSub y K₃) (b * b' * (u₁ * u₂)) := by
    rw [← hyz]
    exact hzK₃.conj y
  exact T7J.layer_orth_six_weak_proved hp hq hΩ hBelow hc2 hnc hK₃t hK₄t hL hzK₃ hzK₄ hperp₃
    hperp₄ htL hzt htz hR hR' hRR' hb hb' ob ob' rfl

theorem c22_8X_of_inputs (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f) (hgen : C22_8Gen p f) :
    C22_8X p f :=
  fun G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h =>
    ⟨c22_8X_layer_of_inputs h4 hF h, hgen G Ω K K' K₃ z u₁ u₂ u₃ h⟩

theorem hyp22FourthTwin_of_fourTwins (h4 : Hyp22FourTwins p f) : Hyp22FourthTwin p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  obtain ⟨K₄, hK₄, h1, h2, h3, -⟩ := h4 G Ω K K' K₃ z u₁ u₂ u₃ h
  exact ⟨K₄, hK₄, h1, h2, h3⟩

end Reduction

end CFSG.ClassicalInvolution.Asc77
