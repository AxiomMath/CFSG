module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

@[expose] def Asc75Lemma34Disjoint : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S A₁ A₂ H : Subgroup G),
    A₁ ⊓ A₂ = ⊥ →
    IsSylowTwoOf S ⊤ → A₁ ≤ S → A₂ ≤ S → (∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) →
    1 < CFSG.Open.pRank 2 A₁ → 1 < CFSG.Open.pRank 2 A₂ →
    H = Subgroup.closure {g : G | CFSG.conjugate A₁ g ⊓ A₁ ≠ ⊥ ∨ CFSG.conjugate A₁ g ⊓ A₂ ≠ ⊥ ∨
      CFSG.conjugate A₂ g ⊓ A₁ ≠ ⊥ ∨ CFSG.conjugate A₂ g ⊓ A₂ ≠ ⊥} →
    ((A₁ : Set G) ∪ (A₂ : Set G) ⊆ ↑(H ⊓ S)) →
    (∀ a ∈ (A₁ : Set G) ∪ (A₂ : Set G), ∀ h ∈ H, h⁻¹ * a * h ∈ S →
      h⁻¹ * a * h ∈ (A₁ : Set G) ∪ (A₂ : Set G)) →
    fusionStronglyClosed ((A₁ : Set G) ∪ (A₂ : Set G)) (S ⊓ Subgroup.normalizer (A₁ : Set G)) →
    fusionStronglyClosed ((A₁ : Set G) ∪ (A₂ : Set G)) (S ⊓ Subgroup.normalizer (A₂ : Set G)) →
    H = ⊤ ∨
    (A₁ ≤ A₂ ∧ fusionStronglyEmbedded ((H ⊓ Subgroup.normalClosure (A₁ : Set G)).subgroupOf
      (Subgroup.normalClosure (A₁ : Set G)))) ∨
    (A₂ ≤ A₁ ∧ fusionStronglyEmbedded ((H ⊓ Subgroup.normalClosure (A₂ : Set G)).subgroupOf
      (Subgroup.normalClosure (A₂ : Set G)))) ∨
    ((∃ g : G, CFSG.conjugate A₁ g = A₂) ∧
      ((∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥A₁ ≃* DihedralGroup n)) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥A₁ ≃* SemidihedralGroup n)) ∧
      Nat.card ↥(A₁ ⊓ A₂) = 2)

section Fixed

variable {G : Type*} [Group G]

theorem unique_fixed_of_fusion {M : Subgroup G} {t : G}
    (hcent : Subgroup.centralizer ({t} : Set G) ≤ M)
    (hfusion : ∀ g : G, g⁻¹ * t * g ∈ M → ∃ m ∈ M, g⁻¹ * t * g = m⁻¹ * t * m) :
    ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M := by
  intro g hg
  obtain ⟨m, hm, hgm⟩ := hfusion g hg
  have hc : g * m⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (g * m⁻¹)⁻¹ * t * (g * m⁻¹) = t := by
      calc (g * m⁻¹)⁻¹ * t * (g * m⁻¹) = m * (g⁻¹ * t * g) * m⁻¹ := by group
        _ = m * (m⁻¹ * t * m) * m⁻¹ := by rw [hgm]
        _ = t := by group
    calc g * m⁻¹ * t = (g * m⁻¹) * ((g * m⁻¹)⁻¹ * t * (g * m⁻¹)) := by rw [h1]
      _ = t * (g * m⁻¹) := by group
  have : g = (g * m⁻¹) * m := by group
  rw [this]
  exact M.mul_mem (hcent hc) hm

theorem le_of_unique_fixed_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {T M : Subgroup G}
    (hT : IsPGroup p ↥T) {t : G} (htT : t ∈ T) (htM : t ∈ M)
    (hfix : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) : T ≤ M := by
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥T)
  set W : Subgroup ↥T := (M ⊓ T).subgroupOf T with hW
  by_cases htop : W = ⊤
  · intro x hx
    have : (⟨x, hx⟩ : ↥T) ∈ W := by rw [htop]; trivial
    exact (Subgroup.mem_subgroupOf.mp this).1
  · exfalso
    have hlt : W < Subgroup.normalizer (W : Set ↥T) := hnc W (lt_top_iff_ne_top.mpr htop)
    obtain ⟨u, hun, huW⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp hlt).2
    have htW : (⟨t, htT⟩ : ↥T) ∈ W := Subgroup.mem_subgroupOf.mpr ⟨htM, htT⟩
    have h1 : u⁻¹ * ⟨t, htT⟩ * u ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (W : Set ↥T)).inv_mem hun)
        ⟨t, htT⟩).mp htW
      simpa using this
    have h2 : (u : G)⁻¹ * t * u ∈ M := (Subgroup.mem_subgroupOf.mp h1).1
    exact huW (Subgroup.mem_subgroupOf.mpr ⟨hfix (u : G) h2, u.2⟩)

end Fixed

end CFSG.QuasithinUnique
