module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeNeThree

import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171D4

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

set_option linter.unusedSectionVars false


private theorem pow_two_mod_three_of_not_dvd_succ {e : ℕ} (h : ¬ 3 ∣ 2 ^ e + 1) :
    2 ^ e % 3 = 1 := by
  have hlt : 2 ^ e % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h0 : 2 ^ e % 3 ≠ 0 := by
    intro hz
    exact absurd (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hz))
      (by norm_num)
  have h2 : 2 ^ e % 3 ≠ 2 := by
    intro hz
    apply h
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hz]
  omega

private theorem catalogIs_isD4any_of_lie_exists {S : Type} [Group S]
    (h : catalogIs S (onLie fun i : TauCeti.LieTypeIndex =>
      ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2)) :
    catalogIs S isD4any := by
  obtain ⟨j, hj, hiso⟩ := h
  cases j with
  | lie i =>
      obtain ⟨q, hiq, hqp⟩ := hj
      refine ⟨.lie i, ?_, hiso⟩
      simp only [isD4any, onLie]
      rw [hiq]
      exact hqp
  | cyclic p hp => exact hj.elim
  | alternating d hd => exact hj.elim
  | sporadic n => exact hj.elim

theorem d4ExitAt_twE6_three (q : TauCeti.PrimePower) (hq2 : q.p = 2)
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 2) (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent))
    (h3 : ¬ 3 ∣ q.p ^ q.exponent + 1) :
    F151.D4ExitAt ↥(twistedE6RootGroup K σ) 3 := by
  intro x w hx1 hxp hwp hxw Kc hKc hCat hw hmem
  exfalso
  obtain ⟨S, a, ι, i, hSq, ⟨Fr, hFr, hΦ⟩, hT, hap, hTp, h1, hinj, hrange, hconj, hqs, hKR⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.twE6_langSetup_and_component (p := 3)
      Nat.prime_three (by norm_num) hq2 σ hK hσ x hx1 hxp Kc hKc
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcharK : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, hq2, ← pow_mul])
  haveI hcharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h3' : ¬ 3 ∣ 2 ^ q.exponent + 1 := fun hd => h3 (by rwa [hq2])
  have hq : S.D.q % 3 = 1 := by
    rw [hSq, hq2]
    exact pow_two_mod_three_of_not_dvd_succ h3'
  have hD4K : catalogIs (↥Kc ⧸ Subgroup.center ↥Kc) isD4any :=
    catalogIs_isD4any_of_lie_exists hCat
  let R := rationalComponent S.ρ S.Γ (rootCharHom a) i
  let eJ : ↥Kc ≃* ↥R := (Kc.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hKR)
  have hD4R : catalogIs (↥R ⧸ Subgroup.center ↥R) isD4any :=
    (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr
      (QuotientGroup.congr (Subgroup.center ↥Kc) (Subgroup.center ↥R) eJ
        (Subgroup.map_center_eq eJ))).1 hD4K
  exact CFSG.LocalAnalysis.GLTheoremA.T171D4.false_of_d4Rational_three_twE6 S
    (fun c => by rw [hSq]; exact hFr c) hΦ hq hT hap h1 i hqs hD4R

theorem twE6D4Inner_holds : F151.TwE6D4Inner := by
  intro q hq2 K hfield hfinite σ hK hσ p hp hp2 h3
  by_cases hp3 : p = 3
  · subst p
    exact d4ExitAt_twE6_three q hq2 K σ hK hσ (h3 rfl)
  · exact d4ExitAt_of_ne_three _ hp hp2 hp3

end CFSG.LocalAnalysis.GLTheoremA.T171D4

end
