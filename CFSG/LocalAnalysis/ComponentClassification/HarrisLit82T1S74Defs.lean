module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup

structure Hyp31i (G : Type) [Group G] [Finite G] (z : G) (p f : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : Assembly.KProper Blueprint.Catalog G
  notCat : ¬ Blueprint.Catalog G
  hz : orderOf z = 2
  oneClass : ∀ x : G, orderOf x = 2 → ∃ g : G, g * z * g⁻¹ = x
  hp : p.Prime
  hp2 : p ≠ 2
  h5 : 5 ≤ p ^ f
  spin : ∃ Lb : Subgroup (↥(centralizer ({z} : Set G)) ⧸
      pPrimeCore 2 ↥(centralizer ({z} : Set G))),
    Lb.Normal ∧ ¬ 2 ∣ Lb.index ∧ IsCoverOf .POmegaOdd 3 p f 2 ↥Lb ∧
      centralizer (Lb : Set (↥(centralizer ({z} : Set G)) ⧸
        pPrimeCore 2 ↥(centralizer ({z} : Set G)))) ≤ Lb

@[expose] def Lemma38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (p f : ℕ), Hyp31i G z p f →
    pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥

end CFSG.ComponentClassification.HarrisLit.T1.S74
