module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrFrattini

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open scoped commutatorElement

section Pow

variable {G : Type*} [Group G] [Finite G]

theorem IrrAct.pow_of_coprime {y : G} {U Z : Subgroup G} {r n : ℕ} (hirr : IrrAct y U Z)
    (hyr : ∀ u ∈ U, y ^ r * u * (y ^ r)⁻¹ * u⁻¹ ∈ Z) (hnr : Nat.Coprime n r) :
    IrrAct (y ^ n) U Z := by
  refine ⟨hirr.1, fun W hZW hWU hyW => ?_⟩
  refine hirr.2 W hZW hWU ?_
  have hr : y ^ r ∈ Subgroup.normalizer (W : Set G) :=
    mem_normalizer_of_powerMap (U := U) (y := y ^ r) hZW (fun u hu => ⟨1, by simpa using hyr u hu⟩)
      hWU
  obtain ⟨s, t, hst⟩ : ∃ s t : ℤ, (n : ℤ) * s + r * t = 1 :=
    ⟨Nat.gcdA n r, Nat.gcdB n r, by
      have := Nat.gcd_eq_gcd_ab n r
      rw [hnr] at this
      exact_mod_cast this.symm⟩
  have : y = (y ^ n) ^ s * (y ^ r) ^ t := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    rw [hst, zpow_one]
  rw [this]
  exact mul_mem (Subgroup.zpow_mem _ hyW s) (Subgroup.zpow_mem _ hr t)

end Pow

section Sub

variable {X : Type*} [Group X]

theorem IrrAct.subgroupOf {N U Z : Subgroup X} {y : X} (hy : y ∈ N) (hUN : U ≤ N)
    (h : IrrAct y U Z) : IrrAct (⟨y, hy⟩ : ↥N) (U.subgroupOf N) (Z.subgroupOf N) := by
  refine ⟨fun z hz => h.1 hz, fun W₁ hZW hWU hyW => ?_⟩
  set W : Subgroup X := W₁.map N.subtype with hW
  have hZW' : Z ≤ W := fun z hz =>
    ⟨⟨z, hUN (h.1 hz)⟩, hZW (Subgroup.mem_subgroupOf.2 hz), rfl⟩
  have hWU' : W ≤ U := by
    rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hWU hw)
  have hyW' : y ∈ Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.mem_normalizer_iff] at hyW ⊢
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, (hyW w).1 hw, rfl⟩
    · rintro ⟨w', hw', hwx⟩
      set v : ↥N := (⟨y, hy⟩ : ↥N)⁻¹ * w' * (⟨y, hy⟩ : ↥N) with hv
      have hvW : v ∈ W₁ := by
        refine (hyW v).2 ?_
        have : (⟨y, hy⟩ : ↥N) * v * (⟨y, hy⟩ : ↥N)⁻¹ = w' := by rw [hv]; group
        rw [this]
        exact hw'
      refine ⟨v, hvW, ?_⟩
      have hwx' : (w' : X) = y * x * y⁻¹ := hwx
      show (v : X) = x
      have : (v : X) = y⁻¹ * (w' : X) * y := rfl
      rw [this, hwx']
      group
  rcases h.2 W hZW' hWU' hyW' with h1 | h1
  · left
    refine le_antisymm (fun w hw => Subgroup.mem_subgroupOf.2 ?_) hZW
    rw [← h1]
    exact ⟨w, hw, rfl⟩
  · right
    refine le_antisymm hWU (fun u hu => ?_)
    have : (u : X) ∈ W := by
      rw [h1]
      exact Subgroup.mem_subgroupOf.1 hu
    obtain ⟨w, hw, hwu⟩ := this
    have : w = u := Subtype.ext hwu
    rwa [this] at hw

end Sub

section Map

variable {A B : Type*} [Group A] [Group B] [Finite A]

theorem relIndex_map_eq (ρ : A →* B) {U Z : Subgroup A} (hZU : Z ≤ U) (hker : U ⊓ ρ.ker ≤ Z) :
    (Z.map ρ).relIndex (U.map ρ) = Z.relIndex U := by
  rw [Subgroup.relIndex_map_map]
  set K := ρ.ker with hK
  set A' := U ⊓ K with hA'
  have hKU : K.relIndex (U ⊔ K) = K.relIndex U := Subgroup.relIndex_sup_right U K
  have hKZ : K.relIndex (Z ⊔ K) = K.relIndex Z := Subgroup.relIndex_sup_right Z K
  have hchain : K.relIndex (Z ⊔ K) * (Z ⊔ K).relIndex (U ⊔ K) = K.relIndex (U ⊔ K) :=
    Subgroup.relIndex_mul_relIndex K (Z ⊔ K) (U ⊔ K) le_sup_right (sup_le_sup_right hZU K)
  have hKZe : K ⊓ Z = A' := by
    refine le_antisymm (fun x hx => ⟨hZU hx.2, hx.1⟩) (fun x hx => ⟨hx.2, hker hx⟩)
  have hKUe : K ⊓ U = A' := by rw [inf_comm]
  have e1 : K.relIndex Z = A'.relIndex Z := by
    rw [← Subgroup.inf_relIndex_right K Z, hKZe]
  have e2 : K.relIndex U = A'.relIndex U := by
    rw [← Subgroup.inf_relIndex_right K U, hKUe]
  have hchain2 : A'.relIndex Z * Z.relIndex U = A'.relIndex U :=
    Subgroup.relIndex_mul_relIndex A' Z U hker hZU
  have hne : A'.relIndex Z ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [hKZ, hKU, e1, e2, ← hchain2] at hchain
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hchain

end Map

end CFSG.AGLEmbedding.ParabAutIrr
