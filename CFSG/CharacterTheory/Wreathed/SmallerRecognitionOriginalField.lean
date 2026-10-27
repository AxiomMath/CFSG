module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldLayer
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenter

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open CFSG.Assembly.LowTwoRank DegreeThreeModelFullCenter
open scoped Classical
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem covering_model_original_parameters
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index)
    (r b : ℕ) (hr : r.Prime) (hrodd : Odd r) (hb : 1 ≤ b)
    (tau : StatedLieTag) (htau : tau = .PSL ∨ tau = .PSU)
    (hmodel : StatedClassicalModel L tau 3 r b) :
    r ^ b = p ^ f ∧ r = p ∧ b = f := by
  let H_L := coveringSimpleReducedCentralizer n hn S e K hSK L hodd
  let Gamma := H_L ⧸ Subgroup.center H_L
  let P := CFSG.generalizedFitting Gamma
  obtain ⟨_, E, _⟩ :=
    covering_simple_full_center_layer_identification hnonab n hn S e hfour K hSK hcover L hodd
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

omit [IsSimpleGroup G] in
@[expose] def CoveringOriginalFullCenterIdentification
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) : Prop :=
  let H_L := coveringSimpleReducedCentralizer n hn S e K hSK L hodd
  let i := simpleReducedCentralizerInclusion n hn S e K hSK hcover L hodd
  (Subgroup.center H_L).map i = Subgroup.center (centralizerOddCoreQuotient n S e) ∧
    ∃ E : CFSG.generalizedFitting (H_L ⧸ Subgroup.center H_L) ≃*
      centralizerSimpleLayer n hn S e,
      ∀ a : CFSG.generalizedFitting (H_L ⧸ Subgroup.center H_L),
        ∀ hcenter : (Subgroup.center H_L).map i =
          Subgroup.center (centralizerOddCoreQuotient n S e),
        (E a : centralizerFullQuotient n hn S e) =
          originalFullCenterQuotientEquiv n hn S e
            (injectiveFullCenterMap i hcenter (a : H_L ⧸ Subgroup.center H_L))

theorem smaller_recognition_identifies_covering_obstruction_over_original_field
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (hproper : K < ⊤)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (hfusion : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hindex : ∀ D : Subgroup K, D.index ≠ 2) :
    let O := CFSG.oddCore K
    let X := K ⧸ O
    let alpha := QuotientGroup.mk' O
    let T := FullSylowCoveringObstruction.subgroupSylow S K hSK
    let Sbar := T.mapSurjective (QuotientGroup.mk'_surjective O)
    let L := SimpleOddIndexQuotient.involutionClosure X
    L.Normal ∧ L ≠ ⊥ ∧
      (∀ N : Subgroup X, N.Normal → N ≤ L → N = ⊥ ∨ N = L) ∧
      (∀ N : Subgroup X, N.Normal → N ≠ ⊥ →
        (∀ M : Subgroup X, M.Normal → M ≤ N → M = ⊥ ∨ M = N) → N = L) ∧
      IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ Odd L.index ∧
      (Sbar : Subgroup X) ≤ L ∧ Subgroup.centralizer (L : Set X) = ⊥ ∧
      (∃ SL : Sylow 2 L,
        (SL : Subgroup L) = (Sbar : Subgroup X).subgroupOf L ∧
        (SL : Subgroup L).map L.subtype =
          ((S : Subgroup G).subgroupOf K).map alpha ∧
        ∃ (E : S ≃* SL) (eL : SL ≃* Wreath (2 ^ n)),
          (∀ s : S, ((E s : L) : X) = alpha (⟨(s : G), hSK s.property⟩ : K)) ∧
          ∀ s : S, eL (E s) = e s) ∧
      ((p ^ f % 4 = 1 ∧ StatedClassicalModel L .PSL 3 p f) ∨
        (p ^ f % 4 = 3 ∧ StatedClassicalModel L .PSU 3 p f)) ∧
      ∃ (hLN : L.Normal) (hodd : Odd L.index),
        letI : L.Normal := hLN
        CoveringOriginalFullCenterIdentification n hn S e K hSK hcover L hodd := by
  let O := CFSG.oddCore K
  let X := K ⧸ O
  let L := SimpleOddIndexQuotient.involutionClosure X
  let T := FullSylowCoveringObstruction.subgroupSylow S K hSK
  let eT := FullSylowCoveringObstruction.subgroupCoordinates S e K hSK
  obtain ⟨hLN, hne, hmin, hunique, hs, hab, hodd, hSL, hc, _, _, _,
    SL, hSLdef, hSLmap, fT, eL, hfT, heL⟩ :=
    SimpleOddIndexQuotient.one_involution_class_no_index_two_has_simple_odd_index_core_quotient
      n hn T eT hfusion hindex
  let : L.Normal := hLN
  let : IsSimpleGroup L := hs
  have hnoncomm : ∃ a b : L, a * b ≠ b * a := by
    by_contra h
    apply hab
    apply isMulCommutative_iff.mpr
    intro a b
    exact not_not.mp (fun hab => h ⟨a, b, hab⟩)
  obtain ⟨_, _, _, _, _, r, b, hr, hrne, hb, hmodel⟩ :=
    smaller_core_quotient_model hrec n hn S e K hSK hproper hfusion hindex
  have hrodd : Odd r := hr.odd_iff.mpr (by have hr2 := hr.two_le; omega)
  have hmodels : (p ^ f % 4 = 1 ∧ StatedClassicalModel L .PSL 3 p f) ∨
      (p ^ f % 4 = 3 ∧ StatedClassicalModel L .PSU 3 p f) := by
    rcases hmodel with ⟨hmod, hmodel⟩ | ⟨hmod, hmodel⟩
    · obtain ⟨_, rfl, rfl⟩ := covering_model_original_parameters hnonab n hn S e hfour
        p f hp hpodd hf hlocal K hSK hcover L hodd r b hr hrodd hb .PSL
          (Or.inl rfl) hmodel
      exact Or.inl ⟨hmod, hmodel⟩
    · obtain ⟨_, rfl, rfl⟩ := covering_model_original_parameters hnonab n hn S e hfour
        p f hp hpodd hf hlocal K hSK hcover L hodd r b hr hrodd hb .PSU
          (Or.inr rfl) hmodel
      exact Or.inr ⟨hmod, hmodel⟩
  refine ⟨hLN, hne, hmin, hunique, hs, hnoncomm, hodd, hSL, hc, ?_, hmodels, ?_⟩
  · let F : S ≃* T := (Subgroup.subgroupOfEquivOfLe hSK).symm
    let E := F.trans fT
    refine ⟨SL, hSLdef, hSLmap, E, eL, ?_, ?_⟩
    · intro s
      exact hfT (F s)
    · intro s
      exact heL (F s)
  · exact ⟨hLN, hodd, covering_simple_full_center_layer_identification
      hnonab n hn S e hfour K hSK hcover L hodd⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
