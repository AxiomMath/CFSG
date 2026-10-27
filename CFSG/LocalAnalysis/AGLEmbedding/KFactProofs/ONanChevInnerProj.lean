module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover

public section

namespace CFSG.AGLEmbedding

theorem liftableNormalizerGen_of_proj_swaps {H L : Type*} [Group H] [Group L] (π : H →* L)
    (hπ : Function.Surjective π) (θ : Multiplicative (Fin 4 → ZMod 3) →* H)
    (hθ : Function.Injective (π.comp θ)) (g : Fin 4 → Fin 4 → H)
    (hg₁ : ∀ i j, i ≠ j → g i j * θ (Multiplicative.ofAdd (Pi.single i 1)) * (g i j)⁻¹ =
      θ (Multiplicative.ofAdd (Pi.single j 1)))
    (hg₂ : ∀ i j, i ≠ j → g i j * θ (Multiplicative.ofAdd (Pi.single j 1)) * (g i j)⁻¹ =
      θ (Multiplicative.ofAdd (Pi.single i 1)))
    (φ : Multiplicative (Fin 2 → ZMod 3) →* Multiplicative (Fin 4 → ZMod 3))
    (hφ : Function.Injective φ)
    (hgen : ⊤ ≤ Subgroup.normalizer (θ.range : Set H) ⊔
      Subgroup.normalizer ((θ.comp φ).range : Set H)) :
    LiftableNormalizerGen L := by
  have hmap : ∀ x a b : H, x * a * x⁻¹ = b → π x * π a * (π x)⁻¹ = π b := fun x a b h => by
    rw [← map_inv, ← map_mul, ← map_mul, h]
  obtain ⟨hexp, hcard, hlift⟩ := liftsComm_of_swaps (π.comp θ) hθ (fun i j => π (g i j))
    (fun i j hij => hmap _ _ _ (hg₁ i j hij)) (fun i j hij => hmap _ _ _ (hg₂ i j hij))
  have hFE : ((π.comp θ).comp φ).range ≤ (π.comp θ).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨φ a, rfl⟩
  have hFcard : Nat.card ((π.comp θ).comp φ).range = 3 ^ 2 := by
    have hinj : Function.Injective ((π.comp θ).comp φ) := hθ.comp hφ
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    simp
  refine ⟨(π.comp θ).range, {(π.comp θ).range, ((π.comp θ).comp φ).range}, hexp, ?_,
    ⟨_, Set.mem_insert _ _⟩, ?_, hlift, ?_⟩
  · rw [hcard]
    norm_num
  · rintro F (rfl | rfl)
    · refine ⟨le_rfl, ?_⟩
      rw [hcard]
      norm_num
    · exact ⟨hFE, hFcard.ge⟩
  · set S : Set (Subgroup L) := {(π.comp θ).range, ((π.comp θ).comp φ).range} with hS
    have hN : Subgroup.normalizer (θ.range : Set H) ⊔
        Subgroup.normalizer ((θ.comp φ).range : Set H) ≤
        (⨆ F ∈ S, Subgroup.normalizer (F : Set L)).comap π := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · have h1 : π a ∈ Subgroup.normalizer ((θ.range.map π : Subgroup L) : Set L) :=
          Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem _ ha)
        rw [← MonoidHom.range_comp] at h1
        exact (le_iSup₂ (f := fun F (_ : F ∈ S) => Subgroup.normalizer (F : Set L))
          (π.comp θ).range (Set.mem_insert _ _)) h1
      · have h1 : π b ∈ Subgroup.normalizer (((θ.comp φ).range.map π : Subgroup L) : Set L) :=
          Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem _ hb)
        rw [← MonoidHom.range_comp, ← MonoidHom.comp_assoc] at h1
        exact (le_iSup₂ (f := fun F (_ : F ∈ S) => Subgroup.normalizer (F : Set L))
          ((π.comp θ).comp φ).range (Set.mem_insert_of_mem _ rfl)) h1
    intro l _
    obtain ⟨h, rfl⟩ := hπ l
    exact hN (hgen (Subgroup.mem_top h))


theorem mem_normalizer_of_involution {G : Type*} [Group G] (E : Subgroup G) {s : G}
    (hs : s * s = 1) (h : ∀ y ∈ E, s * y * s⁻¹ ∈ E) : s ∈ Subgroup.normalizer (E : Set G) := by
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have h2 := h _ hy
  have : s * (s * y * s⁻¹) * s⁻¹ = y := by
    rw [hinv]
    calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
      _ = y := by rw [hs]; simp
  rwa [this] at h2

end CFSG.AGLEmbedding
