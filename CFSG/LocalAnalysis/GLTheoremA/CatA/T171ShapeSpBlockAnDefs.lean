module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnModel
public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

theorem subsingleton_pSimple_of_not_dvd {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {J : Subgroup G} (hpJ : ¬ p ∣ Nat.card J) : Subsingleton (PSimple p J) := by
  have hcop : Nat.Coprime p (Nat.card ↥J) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpJ
  have hcard : Nat.card (⊤ : Subgroup ↥J) = Nat.card ↥J :=
    Nat.card_congr (Subgroup.topEquiv (G := ↥J)).toEquiv
  have hcop' : Nat.Coprime p (Nat.card (⊤ : Subgroup ↥J)) := by
    rw [hcard]
    exact hcop
  have htop : (⊤ : Subgroup ↥J) ≤ GLAPPrimeCore p ↥J := by
    rw [GLAPPrimeCore]
    exact CFSG.GroupTheory.le_pPrimeCore_of_normal inferInstance hcop'
  have hcore : GLAPPrimeCore p ↥J = ⊤ := top_unique htop
  have hsub : Subsingleton (PQuot p J) := by
    have h : PQuot p J = (↥J ⧸ (⊤ : Subgroup ↥J)) := by
      unfold PQuot
      rw [hcore]
    exact h ▸ QuotientGroup.subsingleton_quotient_top
  exact (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p J))).subsingleton

theorem mem_inner_of_subsingleton {G : Type} [Group G] [Subsingleton G] (α : MulAut G) :
    α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
  have hα : α = 1 := by
    ext x
    exact Subsingleton.elim _ _
  rw [hα]
  exact Subgroup.one_mem _

@[expose] def SpPairedBlockAnalysis : Prop :=
  ∀ {m n p : ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 2 ^ n → 2 ≤ m →
    p.Prime → p ≠ 2 →
    ∀ (x y : StatedSp m K), x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ≠ 1 →
    ∀ {h : K[X]}, (hh : h ∈ primaryFactors (spEnd x)) → h ≠ X - 1 →
      (h : K[X]) ≠ reciprocalPolynomial h →
      SpPairedBlock 2 n p x ⟨h, hh⟩ →
      ∀ J : Subgroup (StatedProj (StatedSp m K)),
        J = (⁅spSupported x ({h, reciprocalPolynomial h} : Set K[X]),
          spSupported x ({h, reciprocalPolynomial h} : Set K[X])⁆).map (proj m K) →
        (hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K)))) →
        (catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
            MI.indAut p J (proj m K y) hN ∈ innAutDerived (PSimple p J)) ∨
          MI.indAut p J (proj m K y) hN ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

@[expose] def SpSelfDualBlockAnalysis : Prop :=
  ∀ {m n p : ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 2 ^ n → 2 ≤ m →
    p.Prime → p ≠ 2 →
    ∀ (x y : StatedSp m K), x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ≠ 1 →
    ∀ {h : K[X]}, (hh : h ∈ primaryFactors (spEnd x)) → h ≠ X - 1 →
      reciprocalPolynomial (h : K[X]) = h →
      SpSelfDualBlock 2 n p x ⟨h, hh⟩ →
      ∀ J : Subgroup (StatedProj (StatedSp m K)),
        J = (⁅spSupported x ({h} : Set K[X]), spSupported x ({h} : Set K[X])⁆).map
          (proj m K) →
        CFSG.Assembly.IsQuasisimple ↥J →
        (hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K)))) →
        (catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx) ∧
            MI.indAut p J (proj m K y) hN ∈ innAutDerived (PSimple p J)) ∨
          (catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
            MI.indAut p J (proj m K y) hN ∈ innAutDerived (PSimple p J)) ∨
          MI.indAut p J (proj m K y) hN ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
