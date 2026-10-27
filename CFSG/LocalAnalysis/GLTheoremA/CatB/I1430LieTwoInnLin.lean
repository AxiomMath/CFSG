module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnGlue
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.Assembly

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (lieSemisimpleCentLinearUnitary)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (exists_eq_scalar_of_conjAut_eq_one
  exists_primeFormP_mulEquiv_of_isUnitaryIdx)

private theorem componentsNoA6_projectiveSL {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2) {β : MulAut (LinearFlag.projectiveSL n k)}
    (hβ : β ∈ innAutDerived (LinearFlag.projectiveSL n k)) (hβ3 : β ^ 3 = 1) :
    ComponentsNoA6 β := by
  intro K hK
  refine ⟨fun ψ => ?_⟩
  obtain ⟨A, rfl⟩ := LinearFlag.mem_linearAutGroup_iff.1
    (innAutDerived_projectiveSL_le_linearAutGroup hn hβ)
  haveI : CharP k 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (le_refl 1) (by rw [hk]; norm_num)
  have hpk : ((3 : ℕ) : k) ≠ 0 := fun h0 => by
    have h23 := (CharP.cast_eq_zero_iff k 2 3).1 h0
    omega
  have hA3 : LinearFlag.conjAut n k (A ^ 3) = 1 := by rw [map_pow, hβ3]
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_conjAut_eq_one hn hA3
  obtain ⟨E, _, _, m, j, hm, hj, -, hcardE, hbig, g, hg, hker⟩ :=
    linear_inner_component_type_card hpk hc K hK
  have hbig' : m = 2 → 4 ≤ Fintype.card E := fun h2 => by
    rw [Fintype.card_eq_nat_card]
    exact hbig h2
  obtain ⟨φ⟩ :=
    nonempty_centralQuotient_mulEquiv (slFactorFacts_holds E m hm hbig').perfect g hg hker
  have h9 := (slAltSixFacts_holds E m hm ⟨φ.trans ψ⟩).2
  rw [Fintype.card_eq_nat_card, hcardE, hk] at h9
  have h2 : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
  rw [h9] at h2
  omega

private theorem componentsNoA6_primeFormP {q : TauCeti.PrimePower} {r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData q.p q.exponent K) (hr : 3 ≤ r + 1)
    (hq : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2)) (hp : q.p = 2)
    {β : MulAut (primeFormP h (idGram K (r + 1)))}
    (hβ : β ∈ innAutDerived (primeFormP h (idGram K (r + 1)))) (hβ3 : β ^ 3 = 1) :
    ComponentsNoA6 β := by
  intro T hT
  refine ⟨fun ψ => ?_⟩
  classical
  obtain ⟨A, c, -, hA, rfl⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived h isPrimeFormGram_idGram hr hq hβ hβ3
  obtain ⟨d, hd, hcase⟩ := exists_field_factor_of_component_primeFormConjHom (h := h)
    Nat.prime_three (by omega) A hA T hT
  have hev : ∀ s : ℕ, s ≠ 0 → q.p ^ s ≠ 9 := fun s hs h9 => by
    have h2 : 2 ∣ q.p ^ s := by
      rw [hp]
      exact dvd_pow_self 2 hs
    rw [h9] at h2
    omega
  have he : q.exponent * d ≠ 0 := Nat.mul_ne_zero q.exponent_pos.ne' (by omega)
  rcases hcase with ⟨F, _, _, -, hcardF, h4, g, hg, hk⟩ |
      ⟨E, _, _, m, -, hcardE, hm, hne, g, hg, hk⟩ | ⟨E, _, _, m, -, hcardE, hm, h4, g, hg, hk⟩
  · obtain ⟨φ⟩ := nonempty_centralQuotient_mulEquiv
      (slFactorFacts_holds F 2 le_rfl fun _ => h4).perfect g hg hk
    exact hev _ he (hcardF.symm.trans (slAltSixFacts_holds F 2 le_rfl ⟨φ.trans ψ⟩).2)
  · obtain ⟨φ⟩ := nonempty_centralQuotient_mulEquiv
      (suFactorFacts_holds E m _ hcardE hm hne).perfect g hg hk
    exact (suAltSixFacts_holds E m _ hcardE hm).false (φ.trans ψ)
  · obtain ⟨φ⟩ := nonempty_centralQuotient_mulEquiv
      (slFactorFacts_holds E m hm fun _ => h4).perfect g hg hk
    exact hev _ (Nat.mul_ne_zero two_ne_zero he)
      (hcardE.symm.trans (slAltSixFacts_holds E m hm ⟨φ.trans ψ⟩).2)

theorem i1430InnNoA_proved : I1430InnNoA := by
  rintro S _ _ hS hnc ⟨d, hv⟩ ⟨n, q, rfl⟩ hc hf ⟨e⟩ α hα hα3 hα1
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hk : Nat.card (GaloisField q.p q.exponent) = 2 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
    exact hf
  have hn : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  let e' : S ≃* LinearFlag.projectiveSL (n + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) _))
  refine not_compOfType_isA6 (lieSemisimpleCentLinearUnitary S hS hnc ⟨_, hv⟩ rfl ⟨e⟩ 3
    Nat.prime_three (by norm_num) (fun h3 => absurd (h3.trans hc) (by norm_num)) α hα3 hα1)
    (ComponentsNoA6.of_congr e' ?_)
  exact componentsNoA6_projectiveSL (by omega) hk ((mem_innAutDerived_congr e').2 hα)
    (by rw [← map_pow, hα3, map_one])

theorem i1430InnNoTwistedA_proved : I1430InnNoTwistedA := by
  rintro S _ _ hS hnc d ⟨_, _, hd⟩ hc - ⟨e⟩ α hα hα3 hα1
  obtain ⟨r, q, K, _, hU, hr, hdA, hne, ⟨eP⟩⟩ :=
    exists_primeFormP_mulEquiv_of_isUnitaryIdx (d := d) (by rw [hd]; exact trivial)
  have hp : q.p = 2 := by
    rw [← TauCeti.LieTypeIndex.characteristic_twistedA r q, ← hdA]
    exact hc
  have hq : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 =>
    hne ⟨h3.1, (TauCeti.PrimePower.card_def q).trans h3.2⟩
  let e' : S ≃* primeFormP hU (idGram K (r + 1)) := e.trans eP.symm
  refine not_compOfType_isA6 (lieSemisimpleCentLinearUnitary S hS hnc d
    ((congrArg CFSG.Yardstones.Md42047359a2a.lieFamily hdA).trans rfl) ⟨e⟩ 3 Nat.prime_three
    (by norm_num) (fun h3 => absurd (h3.trans hc) (by norm_num)) α hα3 hα1)
    (ComponentsNoA6.of_congr e' ?_)
  exact componentsNoA6_primeFormP hU (by omega) hq hp ((mem_innAutDerived_congr e').2 hα)
    (by rw [← map_pow, hα3, map_one])

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
