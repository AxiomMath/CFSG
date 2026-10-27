module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOVacuity
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOCentral
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOFamilies

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace FFO

@[expose] def LinkPSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.Open.IsComponentOf L ⊤ →
    ∀ a y : G, a ∈ Subgroup.normalizer (L : Set G) → y ∈ Subgroup.normalizer (L : Set G) →
      a * y * a⁻¹ = y⁻¹ → ∀ r e : ℕ, r.Prime → r ≠ 2 → orderOf y = r ^ e →
      y ^ r ∈ L ⊔ Subgroup.centralizer (L : Set G) → y ∉ L ⊔ Subgroup.centralizer (L : Set G) →
      FamPSL (↥L ⧸ Subgroup.center ↥L) r → r ∣ Nat.card (Subgroup.center ↥L) →
      ∃ z ∈ L, z ≠ 1 ∧ orderOf z = r ∧ (∀ l ∈ L, l * z = z * l) ∧ a * z * a⁻¹ = z⁻¹ ∧
        Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G)

@[expose] def LinkPSU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.Open.IsComponentOf L ⊤ →
    ∀ a y : G, a ∈ Subgroup.normalizer (L : Set G) → y ∈ Subgroup.normalizer (L : Set G) →
      a * y * a⁻¹ = y⁻¹ → ∀ r e : ℕ, r.Prime → r ≠ 2 → orderOf y = r ^ e →
      y ^ r ∈ L ⊔ Subgroup.centralizer (L : Set G) → y ∉ L ⊔ Subgroup.centralizer (L : Set G) →
      FamPSU (↥L ⧸ Subgroup.center ↥L) r → r ∣ Nat.card (Subgroup.center ↥L) →
      ∃ z ∈ L, z ≠ 1 ∧ orderOf z = r ∧ (∀ l ∈ L, l * z = z * l) ∧ a * z * a⁻¹ = z⁻¹ ∧
        Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G)

@[expose] def InvertsOddOnSwap (Fam : (Y : Type) → [Group Y] → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W), Function.Injective ρ → CFSG.Open.IsKGroup G →
    CFSG.pCore 2 G = ⊥ → ∀ A : Subgroup G, CFSG.IsElementaryAbelian 2 ↥A →
    CFSG.RankThree.FFModules.IsBestOffender ρ A → ∀ L : Subgroup G,
    CFSG.Open.IsComponentOf L ⊤ → A ≤ Subgroup.normalizer (L : Set G) → ⁅L, A⁆ = L →
    ∀ a ∈ A, a ∉ L ⊔ Subgroup.centralizer (L : Set G) →
    ∀ y ∈ Subgroup.normalizer (L : Set G), a * y * a⁻¹ = y⁻¹ →
      ∀ r e : ℕ, r.Prime → r ≠ 2 → orderOf y = r ^ e →
        y ^ r ∈ L ⊔ Subgroup.centralizer (L : Set G) →
        (r ≠ 3 → ¬ A ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G)) →
          Fam (↥L ⧸ Subgroup.center ↥L) r → y ∉ L ⊔ Subgroup.centralizer (L : Set G) →
          ∃ M₁ : Submodule (ZMod 2) W, Disjoint M₁ (M₁.map (ρ a)) ∧ 2 < Nat.card M₁ ∧
            ∀ b ∈ A, M₁.map (ρ b) = M₁ ∨ M₁.map (ρ b) = M₁.map (ρ a)

theorem invertsOddOn_of_swap {Fam : (Y : Type) → [Group Y] → ℕ → Prop}
    (h : InvertsOddOnSwap Fam) : InvertsOddOn Fam := by
  intro G _ _ W _ _ _ ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha haK y hy hinv r e hr hr2 hord hyr
    hnn hF
  by_contra hyX
  obtain ⟨M₁, hdisj, hM, hA⟩ :=
    h G W ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha haK y hy hinv r e hr hr2 hord hyr hnn hF hyX
  have := card_le_two_of_swapped_pair hAel hAb ha M₁ hdisj hA
  omega

end FFO

theorem invertsOddOn_psu_of_link_and_noOffender
    (hlink : FFO.LinkPSU) (hvac : FFO.PSUNoOffender) : FFO.InvertsOddOn FFO.FamPSU := by
  intro G _ _ W _ _ _ ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha haK y hy hinv r e hr hr2 hord hyr
    hnn hF
  by_contra hyX
  obtain ⟨n, f, hm, hdvd⟩ := id hF
  have hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hLbot : L ≠ ⊥ := by
    rintro rfl
    have hs : IsSimpleGroup (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := hL.2.2.2
    have := hs.toNontrivial
    have : Subsingleton ↥(⊥ : Subgroup G) := inferInstance
    have : Subsingleton (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := inferInstance
    exact not_subsingleton _ ‹_›
  have hn3 : 3 ≤ n := hm.1.2.2.1
  by_cases hn : n = 3
  · subst hn
    have hbot := commutator_eq_bot_of_psu_three G W ρ hρ hO2 A hAel hAb L hL hm
    rw [hLA] at hbot
    exact hLbot hbot
  · have hn4 : 4 ≤ n := by omega
    by_cases hrZ : r ∣ Nat.card (Subgroup.center ↥L)
    · obtain ⟨z, hzL, hz1, hzord, hzc, hzinv, hzN⟩ :=
        hlink G L hL a y (hAN ha) hy hinv r e hr hr2 hord hyr hyX hF hrZ
      exact FFO.false_of_inverts_central hρ hAel hAb hz1
        (by rw [hzord]; exact hr.odd_of_ne_two hr2) ha hzinv (fun b hb => hzN (hAN hb)) hperf hzL
        hzc
    · have hbot := commutator_eq_bot_of_psu_noOffenderAt (hvac n f r hn4 hr hr2 hdvd) G W ρ hρ hO2 A
        hAel hAb L hL hrZ hm
      rw [hLA] at hbot
      exact hLbot hbot

theorem ffOffenderInvertsOddD4_of_swap (h : FFO.InvertsOddOnSwap FFO.FamD4) :
    FFOffenderInvertsOddD4 :=
  FFO.invertsOddOn_of_swap h

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
