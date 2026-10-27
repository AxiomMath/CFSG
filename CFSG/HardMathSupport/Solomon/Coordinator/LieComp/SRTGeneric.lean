module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearUnitaryComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrderSix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorDataCongr
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open scoped commutatorElement
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a

theorem LieFactorData.of_simple {q : ℕ} {N : Type} [Group N] [Finite N] [IsSimpleGroup N]
    (hnc : ∃ a b : N, a * b ≠ b * a)
    (h : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q N) : LieFactorData q N := by
  have hZ : Subgroup.center N = ⊥ := b3Lie_center_eq_bot hnc
  have hq := b3Lie_isQuasisimple_of_simple hnc
  let eZ : N ⧸ Subgroup.center N ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hq.1, isChevSimple_congr eZ.symm h, fun _ => ?_⟩
  rw [hZ, Subgroup.card_bot]
  norm_num

theorem isEmpty_quot_alternating_six_of_equiv_cat (hb : LieOrderBridge) {N : Type} [Group N]
    [Finite N] [IsSimpleGroup N] (hnc : ∃ a b : N, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (he : Nonempty (N ≃* (TauCeti.CFSGIndex.lie idx).Group)) :
    IsEmpty ((N ⧸ Subgroup.center N) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := he
  have hZ : Subgroup.center N = ⊥ := b3Lie_center_eq_bot hnc
  let eZ : N ⧸ Subgroup.center N ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  haveI : Finite (N ⧸ Subgroup.center N) := inferInstance
  exact isEmpty_mulEquiv_alternating_six hb idx ⟨eZ.trans e⟩

private theorem nontrivial_of_open_quasisimple {K : Type*} [Group K]
    (h : CFSG.Open.IsQuasisimple K) : Nontrivial K := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := h.2
  exact (QuotientGroup.mk_surjective (s := Subgroup.center K)).nontrivial

theorem false_of_open_quasisimple_of_isSolvable {K : Type*} [Group K]
    (h : CFSG.Open.IsQuasisimple K) (hs : Group.IsSolvable K) : False := by
  haveI := nontrivial_of_open_quasisimple h
  haveI : Group.IsPerfect K := ⟨h.1⟩
  exact Group.IsPerfect.not_isSolvable K hs

private theorem normal_of_commutator_le' {G : Type*} [Group G] {H : Subgroup G}
    (h : commutator G ≤ H) : H.Normal :=
  ⟨fun n hn g => by
    have h1 : ⁅g, n⁆ ∈ H :=
      h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have h2 : g * n * g⁻¹ = ⁅g, n⁆ * n := by simp [commutatorElement_def]
    rw [h2]
    exact H.mul_mem h1 hn⟩

private theorem quotient_comm_of_commutator_le {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    (h : commutator G ≤ H) : ∀ x y : G ⧸ H, x * y = y * x := by
  intro x y
  induction x using QuotientGroup.induction_on with | H x => ?_
  induction y using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
  rw [h1]
  exact h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem not_isComponentOf_of_isSolvable {S : Type} [Group S] {C K : Subgroup S}
    (hC : Group.IsSolvable ↥C) (hK : IsComponentOf K C) : False := by
  haveI : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK.1)
      (Subgroup.inclusion_injective hK.1)
  exact false_of_open_quasisimple_of_isSolvable hK.2.2 inferInstance

theorem lieCompsExport_of_isSolvable (q : ℕ) {S : Type} [Group S] (β : MulAut S)
    (h : Group.IsSolvable ↥(fixSubgroup β)) : LieCompsExport q β := by
  refine ⟨CFSG.HardMathSupport.Dickson.SuzukiReeB.perfectInLayer_of_isSolvable β h, fun K hK => ?_⟩
  exact (not_isComponentOf_of_isSolvable h hK).elim

theorem SRT.isSolvable_fixSubgroup_of_congr {S G : Type} [Group S] [Group G] (e : S ≃* G)
    (β : MulAut S) (h : Group.IsSolvable ↥(fixSubgroup (MulAut.congr e β))) :
    Group.IsSolvable ↥(fixSubgroup β) := by
  have hfix : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have e' : ↥(fixSubgroup β) ≃* ↥(fixSubgroup (MulAut.congr e β)) :=
    ((fixSubgroup β).equivMapOfInjective (e : S →* G) e.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  exact Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective

theorem lieCompsExport_of_normal {q : ℕ} {S : Type} [Group S] [Finite S] (β : MulAut S)
    {N : Subgroup S} (hNC : N ≤ fixSubgroup β)
    [hNn : (N.subgroupOf (fixSubgroup β)).Normal]
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β)))
    (hq : CFSG.Open.IsQuasisimple ↥N) (hX : LieFactorData q ↥N) :
    LieCompsExport q β ∧ ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) → K = N := by
  have hcomp : CFSG.Open.IsComponentOf N (fixSubgroup β) :=
    ⟨hNC, CFSG.Open.IsSubnormal.step hNC hNn (CFSG.Open.IsSubnormal.refl _), hq⟩
  have hperf : ∀ P : Subgroup S, P ≤ fixSubgroup β → ⁅P, P⁆ = P → P ≤ N := fun P hPC hP =>
    LieSemisimple.perfect_le_of_solvable_quotient hNC hsol hPC hP
  have hall : ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) → K = N := by
    intro K hK
    obtain ⟨-, hKN⟩ := component_mem_named_factors (ι := Unit) (fun _ => N) (fun _ => hcomp)
      (fun P hPC hP => by
        rw [iSup_const]
        exact hperf P hPC (Subgroup.isPerfect_iff.1 ⟨hP⟩)) hK
    exact hKN
  refine ⟨⟨fun P hPC hP => (hperf P hPC hP).trans (le_sSup hcomp), fun K hK => ?_⟩, hall⟩
  obtain rfl := hall K hK
  exact ⟨↥K, inferInstance, inferInstance, hX, MonoidHom.id _, Function.surjective_id,
    by simp⟩

structure SRTOut (q : ℕ) {S : Type} [Group S] (β : MulAut S) : Prop where
  comps : LieCompsExport q β
  full : LieOrderBridge → LieCompExport q β

private theorem congr_self_eq' {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

theorem SRTOut.of_congr {q : ℕ} {S G : Type} [Group S] [Group G] (e : S ≃* G) {β : MulAut S}
    (h : SRTOut q (MulAut.congr e β)) : SRTOut q β :=
  ⟨LieCompsExport.of_congr e h.comps, fun hb => LieCompExport.of_congr e (h.full hb)⟩

theorem SRTOut.of_conj {q : ℕ} {G : Type} [Group G] (δ : MulAut G) {β : MulAut G}
    (h : SRTOut q (δ * β * δ⁻¹)) : SRTOut q β :=
  SRTOut.of_congr (δ : G ≃* G) (by rw [congr_self_eq']; exact h)

theorem SRTOut.conj {q : ℕ} {G : Type} [Group G] (γ : MulAut G) {β : MulAut G}
    (h : SRTOut q β) : SRTOut q (γ * β * γ⁻¹) :=
  SRTOut.of_conj γ⁻¹ (by rw [show γ⁻¹ * (γ * β * γ⁻¹) * γ⁻¹⁻¹ = β by group]; exact h)

theorem srtOut_of_normal {q : ℕ} {S : Type} [Group S] [Finite S] (β : MulAut S)
    {N : Subgroup S} (hNC : N ≤ fixSubgroup β)
    [(N.subgroupOf (fixSubgroup β)).Normal]
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β)))
    (hq : CFSG.Open.IsQuasisimple ↥N) (hX : LieFactorData q ↥N)
    (hA6 : LieOrderBridge → IsEmpty ((↥N ⧸ Subgroup.center ↥N) ≃* alternatingGroup (Fin 6))) :
    SRTOut q β := by
  obtain ⟨hE, hall⟩ := lieCompsExport_of_normal β hNC hsol hq hX
  refine ⟨hE, fun hb => ⟨hE.layer, hE.comps, fun ⟨K, hK, ⟨e⟩⟩ => ?_⟩⟩
  obtain rfl := hall K hK
  exact ((hA6 hb).false e).elim

theorem srtOut_of_derived {q : ℕ} {S : Type} [Group S] [Finite S] (β : MulAut S)
    {N : Subgroup S} (hNC : N ≤ fixSubgroup β)
    (hCN : commutator ↥(fixSubgroup β) ≤ N.subgroupOf (fixSubgroup β))
    (hq : CFSG.Open.IsQuasisimple ↥N) (hX : LieFactorData q ↥N)
    (hA6 : LieOrderBridge → IsEmpty ((↥N ⧸ Subgroup.center ↥N) ≃* alternatingGroup (Fin 6))) :
    SRTOut q β :=
  haveI : (N.subgroupOf (fixSubgroup β)).Normal := normal_of_commutator_le' hCN
  srtOut_of_normal β hNC
    (Group.isSolvable_of_comm (quotient_comm_of_commutator_le hCN)) hq hX hA6

theorem srtOut_of_isSolvable (q : ℕ) {S : Type} [Group S] (β : MulAut S)
    (h : Group.IsSolvable ↥(fixSubgroup β)) : SRTOut q β :=
  ⟨lieCompsExport_of_isSolvable q β h, fun _ =>
    ⟨(lieCompsExport_of_isSolvable q β h).layer, (lieCompsExport_of_isSolvable q β h).comps,
      fun ⟨K, hK, _⟩ => (not_isComponentOf_of_isSolvable h hK).elim⟩⟩

theorem srtOut_of_fixed_equiv_simple {q : ℕ} {S : Type} [Group S] [Finite S] (β : MulAut S)
    {X : Type} [Group X] [IsSimpleGroup X] (hnc : ∃ x y : X, x * y ≠ y * x)
    (hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q X)
    (hA6 : LieOrderBridge → IsEmpty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)))
    (e : ↥(fixSubgroup β) ≃* X) : SRTOut q β := by
  haveI : Finite X := Finite.of_equiv _ e.toEquiv
  haveI : IsSimpleGroup ↥(fixSubgroup β) := e.isSimpleGroup
  have hnc' : ∃ x y : ↥(fixSubgroup β), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by
      rw [map_mul, map_mul]
      exact h))⟩
  have hX : LieFactorData q X := LieFactorData.of_simple hnc hchev
  refine srtOut_of_derived β (N := fixSubgroup β) le_rfl
    (by rw [Subgroup.subgroupOf_self]; exact le_top) (b3Lie_isQuasisimple_of_simple hnc')
    (LieFactorData.of_mulEquiv e.symm hX) fun hb => ?_
  have g : (↥(fixSubgroup β) ⧸ Subgroup.center ↥(fixSubgroup β)) ≃* (X ⧸ Subgroup.center X) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  exact ⟨fun f => (hA6 hb).false (g.symm.trans f)⟩

theorem srtOut_of_fixed_equiv_derived {q : ℕ} {S : Type} [Group S] [Finite S] (β : MulAut S)
    {X : Type} [Group X] (e : ↥(fixSubgroup β) ≃* X) (hs : IsSimpleGroup ↥(commutator X))
    (hnc : ∃ x y : ↥(commutator X), x * y ≠ y * x)
    (hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q ↥(commutator X))
    (hA6 : LieOrderBridge →
      IsEmpty ((↥(commutator X) ⧸ Subgroup.center ↥(commutator X)) ≃* alternatingGroup (Fin 6))) :
    SRTOut q β := by
  set C := fixSubgroup β with hC
  set D := commutator ↥C with hD
  set N := D.map C.subtype with hN
  have hNC : N ≤ C := Subgroup.map_subtype_le _
  have hNCD : N.subgroupOf C = D :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hmap : D.map e.toMonoidHom = commutator X := by
    rw [hD, commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  let eD : ↥D ≃* ↥(commutator X) :=
    (D.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hmap)
  let eN : ↥D ≃* ↥N := D.equivMapOfInjective C.subtype C.subtype_injective
  let eDN : ↥(commutator X) ≃* ↥N := eD.symm.trans eN
  haveI := hs
  haveI : Finite ↥(commutator X) := Finite.of_equiv _ eD.symm.toEquiv.symm
  haveI : IsSimpleGroup ↥N := eDN.symm.isSimpleGroup
  have hncN : ∃ x y : ↥N, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eDN x, eDN y, fun h => hxy (eDN.injective (by
      rw [map_mul, map_mul]
      exact h))⟩
  refine srtOut_of_derived β hNC (by rw [hNCD]) (b3Lie_isQuasisimple_of_simple hncN)
    (LieFactorData.of_mulEquiv eDN (LieFactorData.of_simple hnc hchev)) fun hb => ?_
  have g : (↥(commutator X) ⧸ Subgroup.center ↥(commutator X)) ≃*
      (↥N ⧸ Subgroup.center ↥N) := QuotientGroup.congr _ _ eDN (Subgroup.map_center_eq eDN)
  exact ⟨fun f => (hA6 hb).false (g.trans f)⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
