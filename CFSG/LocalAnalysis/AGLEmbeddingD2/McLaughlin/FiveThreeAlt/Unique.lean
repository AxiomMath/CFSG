module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Module

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem isMinSec_of_cost [Finite W] (ρ : Representation (ZMod 2) G W) {L B : Subgroup G}
    (hLL : ⁅L, L⁆ = L) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hUinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤))
    (hUU : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤)
    (hntU : ¬ SecTrivial ρ L ⊥ (commOn ρ L ⊤)) {r : ℕ} (hr1 : 1 ≤ r)
    (hsU : secCod ρ B ⊥ (commOn ρ L ⊤) ≤ r)
    (hcostQ : ∀ Z₀ Z₁ : Submodule (ZMod 2) W, Z₁ ≤ commOn ρ L ⊤ → IsMinSec ρ (L ⊔ B) Z₀ Z₁ →
      ¬ SecTrivial ρ L Z₀ Z₁ → r ≤ secCod ρ B Z₀ Z₁) :
    IsMinSec ρ (L ⊔ B) (fixOn ρ L (commOn ρ L ⊤)) (commOn ρ L ⊤) := by
  set U := commOn ρ L ⊤ with hU
  have h₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) ⊥ := fun _ _ u hu => by
    rw [Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  have hcost : ∀ Y₀ Y₁ : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y₀ →
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y₁ → Y₀ ≤ Y₁ → Y₁ ≤ U → ¬ SecTrivial ρ L Y₀ Y₁ →
      r ≤ secCod ρ B Y₀ Y₁ := by
    intro Y₀ Y₁ hY₀ hY₁ hle hY₁U hnt
    obtain ⟨X₀, X₁, hX₀, hX₁, hmin, hntX⟩ := exists_isMinSec_not_secTrivial hLL hY₀ hY₁ hle hnt
    have h1 := hcostQ X₀ X₁ (hX₁.trans hY₁U) hmin hntX
    have hmono : secCod ρ B X₀ X₁ ≤ secCod ρ B Y₀ Y₁ :=
      secCod_mono_sub hX₀ hmin.2.2.1.le hX₁ (isInvariant_mono le_sup_right hmin.1)
        (isInvariant_mono le_sup_right hmin.2.1)
    omega
  set C := fixOn ρ L U with hC
  have hLBN : L ⊔ B ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hCinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) C := isInvariant_fixOn hLBN hUinv
  have hCU : C ≤ U := fun v hv => (mem_fixOn.mp hv).1
  have htop : ∀ Z : Submodule (ZMod 2) W, Z ≤ U → SecTrivial ρ L Z U → Z = U := by
    intro Z hZU ht
    apply le_antisymm hZU
    have h1 : commOn ρ L U ≤ Z := by
      rw [commOn, Submodule.span_le]
      rintro _ ⟨k, hk, u, hu, rfl⟩
      exact ht k hk u hu
    rw [hU] at h1 ⊢
    rwa [hUU] at h1
  have hbot : ∀ Z : Submodule (ZMod 2) W, Z ≤ U → SecTrivial ρ L ⊥ Z → Z ≤ C := by
    intro Z hZU ht v hv
    refine mem_fixOn.mpr ⟨hZU hv, fun k hk => ?_⟩
    have h1 := ht k hk v hv
    rwa [Submodule.mem_bot, sub_eq_zero] at h1
  have hCltU : C < U := by
    refine lt_of_le_of_ne hCU fun h => hntU ?_
    intro k hk v hv
    rw [Submodule.mem_bot, sub_eq_zero]
    have hv' : v ∈ C := h ▸ hv
    exact (mem_fixOn.mp hv').2 k hk
  refine ⟨hCinv, hUinv, hCltU, fun Z hZ hCZ hZU => ?_⟩
  by_cases h1 : SecTrivial ρ L Z U
  · exact Or.inr (htop Z hZU h1)
  · by_cases h2 : SecTrivial ρ L ⊥ Z
    · exact Or.inl (le_antisymm (hbot Z hZU h2) hCZ)
    · exfalso
      have c1 := hcost ⊥ Z h₀ hZ bot_le hZU h2
      have c2 := hcost Z U hZ hUinv hZU le_rfl h1
      have c3 := secCod_add_le (ρ := ρ) (B := B) (bot_le : (⊥ : Submodule (ZMod 2) W) ≤ Z) hZU
        (isInvariant_mono le_sup_right hZ)
      omega

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
