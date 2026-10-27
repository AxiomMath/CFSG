module

public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.GraphFixedOddComponents
public import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (isQuasisimple_congr p_component_isomorphism_transport)

section Auts

variable (t : TwistTag) {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K)

theorem map_exactEntrywiseAut_commutator_twistedFixedGroup :
    ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆.map
        (exactEntrywiseAut t.tag δ).toMonoidHom =
      ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ := by
  have e : (exactEntrywiseAut t.tag δ).toMonoidHom = Units.map (entrywiseHom δ.toRingHom) :=
    MonoidHom.ext fun _ => rfl
  rw [e]
  exact map_entrywise_commutator_twistedFixedGroup (apply_apply_comm_of_finite σ δ)

@[expose] def derivedEntrywiseAut :
    MulAut ↥⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ :=
  mulAutRestrict _ (exactEntrywiseAut t.tag δ)
    (map_exactEntrywiseAut_commutator_twistedFixedGroup t σ δ)

theorem coe_derivedEntrywiseAut
    (x : ↥⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆) :
    (derivedEntrywiseAut t σ δ x : ModGL t.tag K) = Units.map (entrywiseHom δ.toRingHom) x :=
  rfl

theorem map_center_derivedEntrywiseAut :
    (Subgroup.center ↥⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆).map
        (derivedEntrywiseAut t σ δ).toMonoidHom =
      Subgroup.center ↥⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ :=
  Subgroup.characteristic_iff_map_eq.1 inferInstance _

@[expose] def derivedQuotientEntrywiseAut :
    MulAut (↥⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ ⧸
      Subgroup.center ↥⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆) :=
  onQuotient _ (derivedEntrywiseAut t σ δ) (map_center_derivedEntrywiseAut t σ δ)

theorem derivedQuotientEntrywiseAut_mk
    (x : ↥⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆) :
    derivedQuotientEntrywiseAut t σ δ (QuotientGroup.mk x) =
      QuotientGroup.mk (derivedEntrywiseAut t σ δ x) :=
  onQuotient_mk _ _ _ x

end Auts

theorem pComponents_quasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] {p : ℕ} (hp : p.Prime) (e : A ≃* B)
    (hB : ∀ J : Subgroup B, CFSG.IsPComponent p J → CFSG.IsQuasisimple J) (J : Subgroup A)
    (hJ : CFSG.IsPComponent p J) : CFSG.IsQuasisimple J := by
  have hJ' := ((p_component_isomorphism_transport p hp e).1 J).1 hJ
  exact (isQuasisimple_congr (J.equivMapOfInjective e.toMonoidHom e.injective)).2 (hB _ hJ')

theorem odd_diagram_derived_coordinate_field_fixed_p_components
    (t : TwistTag) (K : Type)
    [Field K] [Finite K] (hK : ringChar K ≠ 2) (σ δ : K ≃+* K) :
    (∀ x : ↥⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆,
      (derivedEntrywiseAut t σ δ x : ModGL t.tag K) = Units.map (entrywiseHom δ.toRingHom) x) ∧
    (∀ x : ↥⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆,
      derivedQuotientEntrywiseAut t σ δ (QuotientGroup.mk x) =
        QuotientGroup.mk (derivedEntrywiseAut t σ δ x)) ∧
    ∀ p : ℕ, p.Prime →
      (∀ L : Subgroup (fixedSubgroup (derivedEntrywiseAut t σ δ)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
      (∀ L : Subgroup (fixedSubgroup (derivedQuotientEntrywiseAut t σ δ)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L) := by
  refine ⟨coe_derivedEntrywiseAut t σ δ, derivedQuotientEntrywiseAut_mk t σ δ, fun p hp => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  set Γ := twistedFixedGroup t K σ.toRingHom
  set D := ⁅Γ, Γ⁆
  set X := entrywiseFixedGroup t.tag δ
  set Y := Γ ⊓ X
  set k := fixSubfield δ
  set Lk := twistedFixedGroup t k (fixSubfieldRestrict σ δ).toRingHom
  set L := Lk.map (baseChangeGL k.subtype)
  have hk := ringChar_fixSubfield_ne_two hK δ
  have hLk : ∀ M : Subgroup Lk, CFSG.IsPComponent p M → CFSG.IsQuasisimple M := fun M hM =>
    ((odd_diagram_field_fixed_p_components t k hk (fixSubfieldRestrict σ δ)).2.2 p hp M hM).1
  have hL : ∀ M : Subgroup L, CFSG.IsPComponent p M → CFSG.IsQuasisimple M :=
    pComponents_quasisimple_of_mulEquiv hp
      (Subgroup.equivMapOfInjective Lk _ (baseChangeGL_injective k.subtype)).symm hLk
  have hLY : L ≤ Y := map_baseChangeGL_twistedFixedGroup_le t σ δ
  have hLYq : ∀ M : Subgroup (L.subgroupOf Y), CFSG.IsPComponent p M → CFSG.IsQuasisimple M :=
    pComponents_quasisimple_of_mulEquiv hp (Subgroup.subgroupOfEquivOfLe hLY) hL
  have : Group.IsSolvable (Y ⧸ L.subgroupOf Y) :=
    Group.isSolvable_of_comm (map_baseChangeGL_twistedFixedGroup_quotient_comm t σ δ)
  have hY : ∀ M : Subgroup Y, CFSG.IsPComponent p M → CFSG.IsQuasisimple M :=
    pComponent_quasisimple_of_normal_solvable_quotient p (L.subgroupOf Y) hLYq
  have hDY : D ⊓ X ≤ Y := fun g hg => by
    rw [Subgroup.mem_inf] at hg ⊢
    exact ⟨Subgroup.commutator_le_self Γ hg.1, hg.2⟩
  have hDn : ((D ⊓ X).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff hDY).2 fun d y hd hy => by
      rw [Subgroup.mem_inf] at hd hy ⊢
      exact ⟨conj_mem_commutator_self hy.1 hd.1, mul_mem (mul_mem hy.2 hd.2) (inv_mem hy.2)⟩
  have hfix : fixedSubgroup (derivedEntrywiseAut t σ δ) = (D ⊓ X).subgroupOf D := by
    ext d
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨d.2, ?_, congrArg Subtype.val h⟩
      exact (Subgroup.commutator_le_self Γ).trans (twistedFixedGroup_le_adjointGroup _ _ _) d.2
    · rintro ⟨-, -, h⟩
      exact Subtype.ext h
  let e : fixedSubgroup (derivedEntrywiseAut t σ δ) ≃* (D ⊓ X).subgroupOf Y :=
    (MulEquiv.subgroupCongr hfix).trans ((Subgroup.subgroupOfEquivOfLe inf_le_left).trans
      (Subgroup.subgroupOfEquivOfLe hDY).symm)
  have hW : ∀ M : Subgroup ((D ⊓ X).subgroupOf Y), CFSG.IsPComponent p M →
      CFSG.IsQuasisimple M := fun M hM => by
    have hM' := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_extend_subnormal p
      _ (Subgroup.Normal.isSubnormal hDn) M hM
    exact (isQuasisimple_congr (M.equivMapOfInjective _ (Subgroup.subtype_injective _))).2
      (hY _ hM')
  have hCD : ∀ M : Subgroup (fixedSubgroup (derivedEntrywiseAut t σ δ)),
      CFSG.IsPComponent p M → CFSG.IsQuasisimple M :=
    pComponents_quasisimple_of_mulEquiv hp e hW
  refine ⟨hCD, ?_⟩
  exact (central_quotient_fixed_p_component_transfer (Subgroup.center ↥D) le_rfl
    (derivedEntrywiseAut t σ δ) (map_center_derivedEntrywiseAut t σ δ)).2.2.2.2.2 p hp hCD

end CFSG.LieType.Chevalley
