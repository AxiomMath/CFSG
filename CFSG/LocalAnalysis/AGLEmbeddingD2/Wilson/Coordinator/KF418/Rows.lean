module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Core
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofCenter
public import CFSG.RankThree.PartTwo.Sec4.Item47Close
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

noncomputable def quotCenterEquivOfEqBot {X : Type*} [Group X] (h : Subgroup.center X = ⊥) :
    X ⧸ Subgroup.center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem ker_conj_eq_center (X : Type*) [Group X] :
    (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · exact mem_center_of_conj_eq_one
  · intro hx
    ext y
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hx y).symm,
      mul_inv_cancel_right]

noncomputable def quotCenterEquivInn (X : Type*) [Group X] :
    X ⧸ Subgroup.center X ≃* (MulAut.conj : X →* MulAut X).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center X).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

theorem card_centralizer_subtype {M : Type*} [Group M] (H : Subgroup M) (y : H) :
    Nat.card (Subgroup.centralizer ({y} : Set H)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({(y : M)} : Set M)) := by
  have hmap : (Subgroup.centralizer ({y} : Set H)).map H.subtype =
      H ⊓ Subgroup.centralizer ({(y : M)} : Set M) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, congrArg Subtype.val hz⟩
    · rintro ⟨hxH, hx⟩
      exact ⟨⟨x, hxH⟩, Subtype.ext hx, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective H.subtype_injective]


theorem mem_range_conj_of_list46FourFive {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hl : Sec4.IsList46Four X ∨ Sec4.IsList46Five X) {σ : MulAut X} (hσ : σ ^ 3 = 1) :
    σ ∈ (MulAut.conj : X →* MulAut X).range := by
  rcases hl with (⟨n, hn, ⟨φ⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨φ⟩⟩ | ⟨s, hs, hext⟩)
  · by_cases h4 : n ≤ 4
    · have hs := alternatingGroup.isSolvable (α := Fin n) (by rwa [Nat.card_fin])
      exact (Sec4.false_of_isQuasisimple_of_isSolvable hq
        (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)).elim
    · have : IsSimpleGroup (alternatingGroup (Fin n)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
      have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
      have h4' := CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n (by omega)
      refine Sec13.Res5Proof.mem_range_conj_of_not_three_dvd_outer hq.1
        ((quotCenterEquivOfEqBot hZ).trans φ) (fun h3 => ?_) hσ
      have := h3.trans h4'
      omega
  · have hZ6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
    have htc := (Sec4.isTripleCover_iff_isExtOf hq hZ6).mpr hA6
    exact Sec12.KS128NotHJTC.mem_range_conj_of_isTripleCover hq.1 (Or.inl htc) hσ
  · have hZ7 : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
    have htc := (Sec4.isTripleCover_iff_isExtOf hq hZ7).mpr hA7
    exact Sec12.KS128NotHJTC.mem_range_conj_of_isTripleCover hq.1 (Or.inr (Or.inl htc)) hσ
  · have hZ := Sec13.Res5Proof.center_eq_bot_of_sporadic hq hs φ
    exact Sec13.Res5Proof.mem_range_conj_of_not_three_dvd_outer hq.1
      ((quotCenterEquivOfEqBot hZ).trans φ)
      (Sec4.not_three_dvd_card_outer_sporadic46 CFSG.Quasithin.qSporOutTwo_holds
        Sec4.inputs47Core_outON s (Or.inl hs)) hσ
  · exact (Sec13.Res5Proof.cover_facts_sporadic hq hs hext).2 σ hσ


theorem quotCenter_model_of_list46FourFive {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hl : Sec4.IsList46Four X ∨ Sec4.IsList46Five X) :
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 9 ∧
        Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n))) ∨
      ∃ s : TauCeti.SporadicName, (s ∈ Sec4.sporadics46 ∨ s ∈ Sec4.sporadicCovers46) ∧
        Nonempty (X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.Carrier s) := by
  rcases hl with (⟨n, hn, ⟨φ⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨φ⟩⟩ | ⟨s, hs, hext⟩)
  · by_cases h4 : n ≤ 4
    · have hs := alternatingGroup.isSolvable (α := Fin n) (by rwa [Nat.card_fin])
      exact (Sec4.false_of_isQuasisimple_of_isSolvable hq
        (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)).elim
    · have : IsSimpleGroup (alternatingGroup (Fin n)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
      have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
      exact Or.inl ⟨n, by omega, hn, ⟨(quotCenterEquivOfEqBot hZ).trans φ⟩⟩
  · have hZ6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
    exact Or.inl ⟨6, by norm_num, by norm_num, ((Sec4.isTripleCover_iff_isExtOf hq hZ6).mpr hA6).2⟩
  · have hZ7 : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
    exact Or.inl ⟨7, by norm_num, by norm_num, ((Sec4.isTripleCover_iff_isExtOf hq hZ7).mpr hA7).2⟩
  · have hZ := Sec13.Res5Proof.center_eq_bot_of_sporadic hq hs φ
    exact Or.inr ⟨s, Or.inl hs, ⟨(quotCenterEquivOfEqBot hZ).trans φ⟩⟩
  · exact Or.inr ⟨s, Or.inr hs,
      ((Sec4.isTripleCover_iff_isExtOf hq (Sec4.center_carrier_eq_bot_of_cover hs)).mpr hext).2⟩

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
