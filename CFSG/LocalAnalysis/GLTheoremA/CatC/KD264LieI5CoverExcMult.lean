module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5CoverExcHopf
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5FieldPieces

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.RankThree.PerfectCover CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.OuterAutomorphisms

theorem isCyclic_and_card_of_row {X : Type} [Group X] {a : ℕ} [NeZero a]
    (h : Nonempty (griessHopfMultiplier X ≃*
      (Multiplicative (ZMod a) × Multiplicative (ZMod 1)) ×
        (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)))) :
    IsCyclic (hopfMultiplier X) ∧ Nat.card (hopfMultiplier X) = a := by
  obtain ⟨eG⟩ := h
  let e : hopfMultiplier X ≃* (Multiplicative (ZMod a) × Multiplicative (ZMod 1)) ×
      (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) :=
    (hopfMultiplierEquivGriess X).symm.trans eG
  constructor
  · let g : Multiplicative (ZMod a) →* hopfMultiplier X :=
      (e.symm.toMonoidHom).comp
        ((MonoidHom.inl _ (Multiplicative (ZMod 1) × Multiplicative (ZMod 1))).comp
          (MonoidHom.inl _ (Multiplicative (ZMod 1))))
    refine isCyclic_of_surjective g fun y => ?_
    refine ⟨(e y).1.1, e.injective ?_⟩
    simp only [g, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      MonoidHom.inl_apply]
    refine Prod.ext (Prod.ext rfl (Subsingleton.elim _ _)) (Subsingleton.elim _ _)
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
    have h1 : ∀ n : ℕ, Nat.card (Multiplicative (ZMod n)) = n := fun n => by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod n) ≃ ZMod n), Nat.card_zmod]
    rw [h1, h1]
    simp

theorem isI5UniversalCover_hopfCover (e : TauCeti.ValidLieTypeIndex) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (eK : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie e).Group)
    (hcyc : IsCyclic (hopfMultiplier (K ⧸ Subgroup.center K)))
    (hcard : Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)) = i5CentreOrder e.1) :
    IsI5UniversalCover e (HopfCover (K ⧸ Subgroup.center K)) := by
  have hperfK : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  haveI hperfX : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hZ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hK
  have hc := center_hopfCover_eq hZ
  have hu : Function.Surjective (hopfCoverMap (K ⧸ Subgroup.center K)) := hopfCoverMap_surjective
  let e1 : HopfCover (K ⧸ Subgroup.center K) ⧸ Subgroup.center (HopfCover (K ⧸ Subgroup.center K)) ≃*
      K ⧸ Subgroup.center K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hu)
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  refine ⟨⟨(hopfCover_isPerfect (S := K ⧸ Subgroup.center K)).commutator_eq_top, e1.isSimpleGroup⟩,
    ⟨e1.trans eK⟩, ?_, ?_⟩
  · exact isCyclic_of_surjective (MulEquiv.subgroupCongr hc).symm.toMonoidHom
      (MulEquiv.subgroupCongr hc).symm.surjective
  · rw [Nat.card_congr (MulEquiv.subgroupCongr hc).toEquiv]
    exact hcard

theorem kd264I5CoverLift_of_multiplier (e : TauCeti.ValidLieTypeIndex) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (eK : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie e).Group) {a : ℕ} [NeZero a]
    (ha : a = i5CentreOrder e.1)
    (hrow : Nonempty (griessHopfMultiplier (K ⧸ Subgroup.center K) ≃*
      (Multiplicative (ZMod a) × Multiplicative (ZMod 1)) ×
        (Multiplicative (ZMod 1) × Multiplicative (ZMod 1))))
    (β : MulAut K) (hβ3 : β ^ 3 = 1) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (π : L →* K) (βL : MulAut L),
      Function.Surjective π ∧ (∀ x : L, π x = 1 → x ∈ Subgroup.center L) ∧
        IsI5UniversalCover e L ∧ βL ^ 3 = 1 ∧ ∀ x : L, π (βL x) = β (π x) := by
  have hperfK : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  haveI hperfX : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hZ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hK
  have hc := center_hopfCover_eq hZ
  have hγ3 : onCenterQuotient β ^ 3 = 1 := by
    have := congrArg (centerQuotientHom K) hβ3
    rwa [map_pow, map_one] at this
  obtain ⟨π, βL, hπ, -, hπk, hβL3, hβL⟩ := exists_hopf_lift hperfX hperfK (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) β (onCenterQuotient β)
    (fun k => (onCenterQuotient_apply_mk β k).symm) hγ3
  obtain ⟨hcyc, hcard⟩ := isCyclic_and_card_of_row hrow
  haveI : Finite (HopfCover (K ⧸ Subgroup.center K)) := finite_hopfCover hperfX
  refine ⟨HopfCover (K ⧸ Subgroup.center K), inferInstance, inferInstance, π, βL, hπ,
    fun x hx => hc ▸ hπk x hx, isI5UniversalCover_hopfCover e hK eK hcyc (hcard.trans ha), hβL3, hβL⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
