module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldComponentParameters

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open CFSG.Assembly.LowTwoRank
open scoped Classical
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem smaller_recognition_identifies_component_obstruction_over_original_field
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (hproper : K < ⊤)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
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
        ∃ hnormal : (ComponentCoveringLocal.originalImage n S e K).Normal,
          OriginalComponentFullCenterIdentification n hn S e K hSK hnormal L hodd := by
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
    · obtain ⟨_, rfl, rfl⟩ := component_model_original_parameters hnonab n hn S e hfour
        p f hp hpodd hf hlocal K hSK hcover L hodd r b hr hrodd hb .PSL
          (Or.inl rfl) hmodel
      exact Or.inl ⟨hmod, hmodel⟩
    · obtain ⟨_, rfl, rfl⟩ := component_model_original_parameters hnonab n hn S e hfour
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
  · have hpne : p ≠ 2 := by
      rintro rfl
      norm_num at hpodd
    exact ⟨hLN, hodd, component_simple_full_center_layer_identification
      hnonab n hn S e hfour p f hp hpne hf hlocal K hSK hcover L hodd⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
