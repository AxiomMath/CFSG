module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

structure Hyp31iOdd (G : Type) [Group G] [Finite G] (z : G) (p f : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : Assembly.KProper Blueprint.Catalog G
  notCat : ¬ Blueprint.Catalog G
  hz : orderOf z = 2
  oneClass : ∀ x : G, orderOf x = 2 → ∃ g : G, g * z * g⁻¹ = x
  hp : p.Prime
  hp2 : p ≠ 2
  spin : ∃ Lb : Subgroup (↥(centralizer ({z} : Set G)) ⧸
      pPrimeCore 2 ↥(centralizer ({z} : Set G))),
    Lb.Normal ∧ ¬ 2 ∣ Lb.index ∧ IsCoverOf .POmegaOdd 3 p f 2 ↥Lb ∧
      centralizer (Lb : Set (↥(centralizer ({z} : Set G)) ⧸
        pPrimeCore 2 ↥(centralizer ({z} : Set G)))) ≤ Lb

section Hyp

variable {G : Type} [Group G] [Finite G] {z : G} {p f : ℕ}

theorem Hyp31iOdd.toHyp31i (h : Hyp31iOdd G z p f) (h5 : 5 ≤ p ^ f) : Hyp31i G z p f :=
  ⟨h.simple, h.nonab, h.kProper, h.notCat, h.hz, h.oneClass, h.hp, h.hp2, h5, h.spin⟩

end Hyp

@[expose] def Lemma38Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (p f : ℕ), Hyp31iOdd G z p f →
    pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥

theorem one_lt_pow_of_isCoverOf {Y : Type} [Group Y] {p f : ℕ}
    (hY : IsCoverOf .POmegaOdd 3 p f 2 Y) : 1 < p ^ f := by
  obtain ⟨-, -, hm⟩ := hY
  rcases hm with ⟨-, -, K, _, _, hK, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  rw [← hK]
  exact Finite.one_lt_card

theorem pow_eq_three_or_five_le_of_isCoverOf {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hY : IsCoverOf .POmegaOdd 3 p f 2 Y) : p ^ f = 3 ∨ 5 ≤ p ^ f := by
  have h1 := one_lt_pow_of_isCoverOf hY
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  generalize p ^ f = q at h1 hodd ⊢
  obtain ⟨k, hk⟩ := hodd
  omega

@[expose] def Solomon74SpinSevenAsUsedOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) → z ∈ L →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L) →
    (L.subgroupOf (centralizer {z})).Characteristic →
    centralizer {z} ⊓ coreActionKernel L =
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ zpowers z →
    ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ L →
    (∀ x ∈ centralizer ({z} : Set G), (∃ g : G, g * z * g⁻¹ = x) ↔ (x ∈ L ∧ orderOf x = 2)) →
    ∀ S : Sylow 2 G, ¬ (S : Subgroup G) ≤ L

theorem solomon74SpinSevenAsUsedThree_of_odd (h : Solomon74SpinSevenAsUsedOdd) :
    Solomon74SpinSevenAsUsedThree := by
  intro G _ _ _ hnonab hKP hcat z hz L hL hzL p f hp hp2 hcov _ hchar hQ hH hconj
  exact h G hnonab hKP hcat z hz L hL hzL p f hp hp2 hcov hchar hQ hH hconj

end CFSG.ComponentClassification.HarrisLit.T1.S74
