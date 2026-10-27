module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnFixed
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift

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

theorem sympComponentBlockAnalysis_of
    (hpair : SpPairedBlockAnalysis) (hself : SpSelfDualBlockAnalysis)
    : SympComponentBlockAnalysis := by
  have hfix := @spFixedBlockAnalysis_holds
  intro m n p K _ _ hK hm hp hp2 x y hxp hyp hxy hx1 J hJ hN
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hpJ : p ∣ Nat.card J
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    have hJ' : GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) J :=
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).2
        ⟨hJ.1, CFSG.StandardType.isPComponent_subgroupOf_of_isComponentOf_of_dvd hJ hpJ⟩
    obtain ⟨O, hO, hJeq⟩ := sympComponentOrbit hK hm hp hp2 hxp hx1 hJ'
    obtain ⟨h, hh, hO'⟩ := hO
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso
        rw [h0, pow_zero] at hK
        have h2c := Finite.one_lt_card (α := K)
        omega
      · exact h0
    haveI hchar : CharP K 2 := by
      letI : Fintype K := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by rw [Fintype.card_eq_nat_card, hK])
    have hpK : (p : K) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff K 2] at h0
      exact hp2 (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp |>.1 h0).symm
    haveI : NeZero m := ⟨by omega⟩
    have hm1 : 1 ≤ m := by omega
    have ha1 : proj m K x ≠ 1 := fun h1 =>
      hx1 ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
        (r := m) (K := K)).1 (by rw [h1, map_one]))
    have ha : orderOf (proj m K x) = p :=
      orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) ha1
    have hxp' : orderOf x = p := orderOf_eq_prime hxp hx1
    have hblocks : SpPrimaryBlocks 2 n p x (proj m K x) :=
      (symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := n) (p := p) (r := m)
        (K := K) Nat.prime_two hn1 hK hp hp2 hp2 hm1 (proj m K x) ha).2 x rfl hxp'
    by_cases h1 : h = X - 1
    ·
      have hOset : (O : Set K[X]) = {X - 1} := by
        rw [← hO']
        show ({h, reciprocalPolynomial h} : Set K[X]) = {X - 1}
        rw [h1, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one,
          Set.pair_eq_singleton]
      rw [hOset] at hJeq
      exact Or.inr (Or.inr (hfix hK hm hp hp2 x y hxp hyp hxy hx1 J hJeq hN))
    by_cases hsd : reciprocalPolynomial h = h
    ·
      have hOset : (O : Set K[X]) = {h} := by
        rw [← hO']
        show ({h, reciprocalPolynomial h} : Set K[X]) = {h}
        rw [hsd, Set.pair_eq_singleton]
      rw [hOset] at hJeq
      rcases hself hK hm hp hp2 x y hxp hyp hxy hx1 hh h1 hsd
        (hblocks.selfDual ⟨h, hh⟩ h1 hsd) J hJeq hJ.2.2 hN with hU | hL | hI
      · exact Or.inr (Or.inl hU)
      · exact Or.inl hL
      · exact Or.inr (Or.inr hI)
    ·
      have hOset : (O : Set K[X]) = {h, reciprocalPolynomial h} := hO'.symm
      rw [hOset] at hJeq
      rcases hpair hK hm hp hp2 x y hxp hyp hxy hx1 hh h1 (Ne.symm hsd)
        (hblocks.paired ⟨h, hh⟩ (Ne.symm hsd)) J hJeq hN with hL | hI
      · exact Or.inl hL
      · exact Or.inr (Or.inr hI)
  ·
    haveI := subsingleton_pSimple_of_not_dvd hp hpJ
    exact Or.inr (Or.inr (mem_inner_of_subsingleton _))

@[expose] def SpPairedBlockModel : Prop :=
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
        Nonempty (LinBlockModel p J (proj m K y) hN) ∨
          MI.indAut p J (proj m K y) hN ∈
            CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

theorem spPairedBlockAnalysis_of_model (hmodel : SpPairedBlockModel) :
    SpPairedBlockAnalysis := by
  intro m n p K _ _ hK hm hp hp2 x y hxp hyp hxy hx1 h hh h1 hne hb J hJeq hN
  rcases hmodel hK hm hp hp2 x y hxp hyp hxy hx1 hh h1 hne hb J hJeq hN with hM | hI
  · obtain ⟨M⟩ := hM
    exact Or.inl (linBlockModel_analysis hp hp2 M)
  · exact Or.inr hI

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
