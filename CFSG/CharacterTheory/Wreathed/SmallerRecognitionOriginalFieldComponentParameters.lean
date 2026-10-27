module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldComponentLayer
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenter

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open CFSG.Assembly.LowTwoRank DegreeThreeModelFullCenter
open scoped Classical
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem component_model_original_parameters
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index)
    (r b : ℕ) (hr : r.Prime) (hrodd : Odd r) (hb : 1 ≤ b)
    (tau : StatedLieTag) (htau : tau = .PSL ∨ tau = .PSU)
    (hmodel : StatedClassicalModel L tau 3 r b) :
    r ^ b = p ^ f ∧ r = p ∧ b = f := by
  let H_L := coveringSimpleReducedCentralizer n hn S e K hSK L hodd
  let Gamma := H_L ⧸ Subgroup.center H_L
  let P := CFSG.generalizedFitting Gamma
  have hpne : p ≠ 2 := by
    rintro rfl
    norm_num at hpodd
  obtain ⟨_, _, E, _⟩ := component_simple_full_center_layer_identification
    hnonab n hn S e hfour p f hp hpne hf hlocal K hSK hcover L hodd
  obtain ⟨hs, hab, _⟩ := original_full_center_layer_simple hnonab n hn S e hfour
  let : IsSimpleGroup (CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
    Subgroup.center (centralizerOddCoreQuotient n S e))) := hs
  let E₀ := originalFullCenterLayerEquiv hnonab n hn S e hfour
  let : IsSimpleGroup (centralizerSimpleLayer n hn S e) := E₀.symm.isSimpleGroup
  let : IsSimpleGroup P := E.isSimpleGroup
  have hab₀ : ∃ a b : centralizerSimpleLayer n hn S e, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.nonabelian_of_equiv E₀.symm hab
  have habP : ∃ a b : P, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.nonabelian_of_equiv E hab₀
  let : Group.IsPerfect P :=
    ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top P habP⟩
  have hdegree := degree_three_model_full_center_local_quotient_parameter L r b hr hrodd hb
    tau htau hmodel (coveringQuotientInvolution n hn S e K hSK L hodd)
      (coveringQuotientInvolution_order n hn S e K hSK L hodd)
  have hne3 : r ^ b ≠ 3 := by
    intro hthree
    let : Group.IsSolvable Gamma := (hdegree.1 hthree).1
    exact Group.IsPerfect.not_isSolvable P inferInstance
  have hlarge : 5 ≤ r ^ b := by
    have hr3 : 3 ≤ r := hr.odd_iff.mp hrodd
    have hq3 : 3 ≤ r ^ b := hr3.trans (Nat.le_self_pow (by omega) r)
    have hqodd : Odd (r ^ b) := hrodd.pow
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hmodelP : StatedClassicalModel P .PSL 2 p f :=
    statedPSLModel_of_equiv E.symm 2 p f hlocal
  obtain ⟨hq, heq, hbeq⟩ := (hdegree.2 hlarge).2.2.2.2.2.2 p f hp hpodd hf hmodelP
  exact ⟨hq.symm, heq.symm, hbeq.symm⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
