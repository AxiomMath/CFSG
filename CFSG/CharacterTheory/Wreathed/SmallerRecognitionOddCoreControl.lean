module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOddCoreControlModels
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldCore
public import CFSG.CharacterTheory.Wreathed.OddIndexCentralCoreAction

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOddCoreControl

open ReducedCentralizerInclusion OddIndexCentralCoreAction SimpleOddIndexQuotient
open SmallerRecognitionOriginalField

theorem odd_kernel_local_two_action_commutator {K : Type*} [Group K] [Finite K]
    (O : Subgroup K) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (hcentral : ∀ v : L, orderOf v = 2 →
      CFSG.oddCore (Subgroup.centralizer ({v} : Set L)) ≤
        Subgroup.center (Subgroup.centralizer ({v} : Set L)))
    (t : K) (ht : orderOf t = 2) (A : Subgroup K) (hA : IsPGroup 2 A)
    (hAC : A ≤ Subgroup.centralizer ({t} : Set K)) :
    ⁅A, (CFSG.oddCore (Subgroup.centralizer ({t} : Set K))).map
      (Subgroup.centralizer ({t} : Set K)).subtype⁆ ≤ O := by
  let alpha := QuotientGroup.mk' O
  let u := alpha t
  have hu : orderOf u = 2 := OddNormalQuotientInvolutions.quotient_involution O hO t ht
  have huL : u ∈ L := involution_mem_normal_of_odd_index L hindex u hu
  let v : L := ⟨u, huL⟩
  have hv : orderOf v = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hAC' : A.map alpha ≤ Subgroup.centralizer ({u} : Set (K ⧸ O)) := by
    rintro a ⟨a0, ha0, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg alpha (Subgroup.mem_centralizer_singleton_iff.mp (hAC ha0)))
  have hact := odd_index_normal_subgroup_central_core_controls_local_two_action
    L hindex u huL hu (hcentral v hv) (A.map alpha) (hA.map alpha) hAC'
  let R := (CFSG.oddCore (Subgroup.centralizer ({t} : Set K))).map
    (Subgroup.centralizer ({t} : Set K)).subtype
  have hRmap : R.map alpha =
      (CFSG.oddCore (Subgroup.centralizer ({u} : Set (K ⧸ O)))).map
        (Subgroup.centralizer ({u} : Set (K ⧸ O))).subtype :=
    ambient_centralizer_oddCore_map O hO t ht
  have hzero : ⁅A.map alpha, R.map alpha⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rw [hRmap]
    exact hact
  have hmapzero : (⁅A, R⁆).map alpha = ⊥ := by
    rw [Subgroup.map_commutator, hzero]
  have hk := (Subgroup.map_eq_bot_iff (⁅A, R⁆)).mp hmapzero
  simpa only [alpha, QuotientGroup.ker_mk'] using hk

theorem smaller_simple_quotient_centralizer_core
    {G : Type} [Group G] [Finite G]
    (hrec : SmallerWreathedRecognition G) (K : Subgroup G) (hproper : K < ⊤)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 K) (e : S ≃* Wreath (2 ^ n))
    (hfusion : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hindex : ∀ D : Subgroup K, D.index ≠ 2) :
    let L := involutionClosure (K ⧸ CFSG.oddCore K)
    L.Normal ∧ Odd L.index ∧
      ∀ v : L, orderOf v = 2 →
        CFSG.oddCore (Subgroup.centralizer ({v} : Set L)) ≤
          Subgroup.center (Subgroup.centralizer ({v} : Set L)) := by
  let L := involutionClosure (K ⧸ CFSG.oddCore K)
  obtain ⟨hLN, _, _, _, hsimple, hnonab, hodd, _, _, _, _, _,
    TL, _, _, _, eL, _, _⟩ :=
    one_involution_class_no_index_two_has_simple_odd_index_core_quotient
      n hn S e hfusion hindex
  let : IsSimpleGroup L := hsimple
  have hab : ∃ a b : L, a * b ≠ b * a := by
    by_contra h
    apply hnonab
    apply isMulCommutative_iff.mpr
    intro a b
    exact not_not.mp (fun hab => h ⟨a, b, hab⟩)
  have hcard : Nat.card L < Nat.card G := proper_core_quotient_subgroup_card_lt K hproper L
  obtain ⟨p, f, hp, hpne, hf, hmodel⟩ := hrec L hab hcard n hn TL ⟨eL⟩
  refine ⟨hLN, hodd, ?_⟩
  intro v hv
  rcases hmodel with ⟨_, hlinear⟩ | ⟨_, hunitary⟩
  · exact stated_linear_three_centralizer_oddCore_central
      L p f hp (hp.odd_of_ne_two hpne) hf hlinear v hv
  · exact stated_unitary_three_centralizer_oddCore_central
      L p f hp (hp.odd_of_ne_two hpne) hunitary v hv

theorem smaller_wreathed_recognition_gives_proper_subgroup_odd_core_commutator_control
    {G : Type} [Group G] [Finite G]
    (hrec : SmallerWreathedRecognition G) (K : Subgroup G) (hproper : K < ⊤)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 K) (e : S ≃* Wreath (2 ^ n))
    (hfusion : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hindex : ∀ D : Subgroup K, D.index ≠ 2)
    (t : K) (ht : orderOf t = 2) (A : Subgroup K) (hA : IsPGroup 2 A)
    (hAC : A ≤ Subgroup.centralizer ({t} : Set K)) :
    ⁅A, (CFSG.oddCore (Subgroup.centralizer ({t} : Set K))).map
      (Subgroup.centralizer ({t} : Set K)).subtype⁆ ≤ CFSG.oddCore K := by
  let L := involutionClosure (K ⧸ CFSG.oddCore K)
  obtain ⟨hLN, hodd, hcentral⟩ :=
    smaller_simple_quotient_centralizer_core hrec K hproper n hn S e hfusion hindex
  let : L.Normal := hLN
  exact odd_kernel_local_two_action_commutator (CFSG.oddCore K)
    (actual_oddCore_odd K) L hodd hcentral t ht A hA hAC

theorem smaller_recognition_sylow_centralizer_commutator
    {G : Type} [Group G] [Finite G]
    (hrec : SmallerWreathedRecognition G) (K : Subgroup G) (hproper : K < ⊤)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 K) (e : S ≃* Wreath (2 ^ n))
    (hfusion : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hindex : ∀ D : Subgroup K, D.index ≠ 2)
    (t : K) (ht : orderOf t = 2)
    (P : Sylow 2 (Subgroup.centralizer ({t} : Set K))) :
    ⁅(P : Subgroup (Subgroup.centralizer ({t} : Set K))).map
      (Subgroup.centralizer ({t} : Set K)).subtype,
      (CFSG.oddCore (Subgroup.centralizer ({t} : Set K))).map
        (Subgroup.centralizer ({t} : Set K)).subtype⁆ ≤ CFSG.oddCore K := by
  apply smaller_wreathed_recognition_gives_proper_subgroup_odd_core_commutator_control
    hrec K hproper n hn S e hfusion hindex t ht
  · exact P.isPGroup'.map _
  · rintro a ⟨c, _, rfl⟩
    exact c.property

end CFSG.Wreathed.SmallerRecognitionOddCoreControl
