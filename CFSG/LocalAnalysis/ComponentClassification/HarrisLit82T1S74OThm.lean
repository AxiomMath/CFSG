module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74OMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ThreeDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74QF1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74QF2b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74QF4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74A1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74A4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem hyp31iOdd_of_le {G : Type} [Group G] [Finite G] [hsimple : IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog G)
    (hcat : ¬ Blueprint.Catalog G) {z : G} (hz : orderOf z = 2) {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {z})) (hzL : z ∈ L) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcov : IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L))
    (hchar : (L.subgroupOf (centralizer {z})).Characteristic)
    (hQ : centralizer {z} ⊓ coreActionKernel L =
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ zpowers z)
    (hconj : ∀ x ∈ centralizer ({z} : Set G), (∃ g : G, g * z * g⁻¹ = x) ↔
      (x ∈ L ∧ orderOf x = 2))
    (S : Sylow 2 G) (hSL : (S : Subgroup G) ≤ L) : Hyp31iOdd G z p f := by
  have hLH : L ≤ centralizer ({z} : Set G) := hL.1
  have hn : (L.subgroupOf (centralizer ({z} : Set G))).Normal := by
    have := hchar
    infer_instance
  refine ⟨hsimple, hnonab, hKP, hcat, hz, fun x hx => exists_conj_of_sylow_le hLH hconj S hSL hx,
    hp, hp2, (imageHom (L.subgroupOf (centralizer ({z} : Set G)))).range, normal_range _ hn,
    not_two_dvd_index_range hLH S hSL, isCoverOf_range hLH hn hcov,
    centralizer_range_le hLH hn ?_⟩
  rw [hQ]
  exact sup_le_sup_left ((zpowers_le).mpr hzL) _

theorem solomon74SpinSevenAsUsedOdd_of_lemma38Odd (hL38 : Lemma38Odd) (hF1 : F1Odd)
    (hF2b : F2bOdd) (hSpin : SpinFactsAllOdd) : Solomon74SpinSevenAsUsedOdd := by
  intro G _ _ _ hnonab hKP hcat z hz L hL hzL p f hp hp2 hcov hchar hQ _ hconj S hSL
  exact false_of_pPrimeCore_eq_bot hF1 hF2b hSpin hz hL hzL hp hp2 hcov
    (pow_eq_three_or_five_le_of_isCoverOf hp hp2 hcov) hchar hconj
    (hL38 G z p f (hyp31iOdd_of_le hnonab hKP hcat hz hL hzL hp hp2 hcov hchar hQ hconj S hSL))
    S hSL

theorem spinFactsAllOdd_holds : SpinFactsAllOdd :=
  spinFactsAllOdd_of f1Odd_holds f2bOdd_holds f4Odd_holds a1_holds a2_holds a3_holds a4_holds

end CFSG.ComponentClassification.HarrisLit.T1.S74
