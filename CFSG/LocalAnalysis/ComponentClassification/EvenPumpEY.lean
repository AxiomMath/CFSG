module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpERed
public import CFSG.LocalAnalysis.ComponentClassification.BFailureSolvableQuotient
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34
public import CFSG.Quasithin.H13.GoldschmidtC137SQKg

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup SemidirectProduct

variable {L : Type} [Group L] (Q : Subgroup (MulAut L))

abbrev PumpY : Type := L ⋊[Q.subtype] ↥Q

abbrev pumpL : Subgroup (PumpY Q) := (inl : L →* PumpY Q).range

noncomputable def pumpLEquiv : L ≃* ↥(pumpL Q) := MonoidHom.ofInjective inl_injective

theorem pumpL_normal : (pumpL Q).Normal := by
  have h : pumpL Q = (rightHom : PumpY Q →* ↥Q).ker := range_inl_eq_ker_rightHom
  rw [h]
  infer_instance

theorem finite_pumpY [Finite L] : Finite (PumpY Q) := by
  have : Finite (MulAut L) := Finite.of_injective (fun e : MulAut L => e.toEquiv)
    fun _ _ h => MulEquiv.ext fun x => congrArg (fun f : L ≃ L => f x) h
  exact Finite.of_equiv _ equivProd.symm

theorem inr_mul_inl (q : ↥Q) (l : L) :
    (inr q : PumpY Q) * inl l = inl ((q : MulAut L) l) * inr q := by
  have h := inl_aut (φ := Q.subtype) q l
  rw [show Q.subtype q = (q : MulAut L) from rfl] at h
  rw [h, map_inv]
  group

theorem isKGroupCat_pumpY [Finite L] (hL : SectionRank.IsKGroupCat L) (hQ : IsPGroup 2 Q) :
    SectionRank.IsKGroupCat (PumpY Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut L) := Finite.of_injective (fun e : MulAut L => e.toEquiv)
    fun _ _ h => MulEquiv.ext fun x => congrArg (fun f : L ≃ L => f x) h
  let e : (rightHom : PumpY Q →* ↥Q).ker ≃* L :=
    (MulEquiv.subgroupCongr range_inl_eq_ker_rightHom.symm).trans (pumpLEquiv Q).symm
  exact Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_ker (rightHom : PumpY Q →* ↥Q)
    (hL.of_mulEquiv e) (Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_pGroup hQ)

theorem isPComponent_pumpL [Finite L] (hq : IsQuasisimple L) (hO : pPrimeCore 2 L = ⊥) :
    IsPComponent 2 (pumpL Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_pumpY Q
  have hO' : pPrimeCore 2 ↥(pumpL Q) = ⊥ := by
    rw [← pPrimeCore_map_iso 2 (pumpLEquiv Q), hO, Subgroup.map_bot]
  have hq' : IsQuasisimple ↥(pumpL Q) := LocalCores.isQuasisimple_of_mulEquiv (pumpLEquiv Q) hq
  have := pumpL_normal Q
  rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple]
  refine ⟨Subgroup.Normal.isSubnormal inferInstance,
    CatalogueBPrimeJoin.primeResidual_eq_top_of_corefree_quasisimple 2 hq' hO', ?_⟩
  exact LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot).symm hq'

theorem pumpL_inf_centralizer_range :
    pumpL Q ⊓ centralizer ((inr : ↥Q →* PumpY Q).range : Set (PumpY Q)) =
      (autFixed Q).map inl := by
  ext y
  constructor
  · rintro ⟨⟨l, rfl⟩, hc⟩
    refine ⟨l, fun q hq => ?_, rfl⟩
    have h1 := (mem_centralizer_iff.mp hc) (inr ⟨q, hq⟩) ⟨⟨q, hq⟩, rfl⟩
    rw [inr_mul_inl] at h1
    exact inl_injective (mul_right_cancel h1)
  · rintro ⟨l, hl, rfl⟩
    refine ⟨⟨l, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨q, rfl⟩
    rw [inr_mul_inl, hl q q.2]

theorem isPComponent_centralizer_range [Finite L] {Tb : Subgroup L} (hTb : Tb ≤ autFixed Q)
    (hT : IsPComponent 2 (Tb.subgroupOf (autFixed Q))) :
    Tb.map inl ≤ centralizer ((inr : ↥Q →* PumpY Q).range : Set (PumpY Q)) ∧
      IsPComponent 2 ((Tb.map inl).subgroupOf
        (centralizer ((inr : ↥Q →* PumpY Q).range : Set (PumpY Q)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_pumpY Q
  have := pumpL_normal Q
  set C := centralizer ((inr : ↥Q →* PumpY Q).range : Set (PumpY Q)) with hC
  have hle : Tb.map inl ≤ pumpL Q ⊓ C := by
    rw [pumpL_inf_centralizer_range]
    exact map_mono hTb
  refine ⟨hle.trans inf_le_right, ?_⟩
  have hker : ¬ 2 ∣ Nat.card (inl : L →* PumpY Q).ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr inl_injective, Subgroup.card_bot]
    norm_num
  have h1 : IsPComponent 2 ((Tb.map inl).subgroupOf (pumpL Q ⊓ C)) := by
    rw [pumpL_inf_centralizer_range]
    exact GSThmB.OddQuot.isPComponent_map inl hker hTb hT
  have hsub : ((pumpL Q ⊓ C).subgroupOf C).IsSubnormal := by
    have hn : ((pumpL Q ⊓ C).subgroupOf C).Normal := by
      rw [inf_subgroupOf_right]
      infer_instance
    exact Subgroup.Normal.isSubnormal hn
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hle inf_le_right hsub).mpr h1

theorem nonempty_pumpL_fusionZStar_equiv [Finite L] (hO : pPrimeCore 2 L = ⊥) :
    Nonempty (↥(pumpL Q) ⧸ Open.fusionZStar ↥(pumpL Q) ≃* L ⧸ center L) := by
  have := finite_pumpY Q
  obtain ⟨e₁⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (pumpLEquiv Q).symm
  obtain ⟨e₂⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar L
  let e₃ : L ⧸ pPrimeCore 2 L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  exact ⟨e₁.trans (e₂.symm.trans (Sol78.centerQuotCongr e₃))⟩

theorem le_pumpL_of_isPerfect [Finite L] (hQ : IsPGroup 2 Q) (J : Subgroup (PumpY Q))
    [Group.IsPerfect J] : J ≤ pumpL Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut L) := Finite.of_injective (fun e : MulAut L => e.toEquiv)
    fun _ _ h => MulEquiv.ext fun x => congrArg (fun f : L ≃ L => f x) h
  have := pumpL_normal Q
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  let e : PumpY Q ⧸ pumpL Q ≃* ↥Q :=
    (QuotientGroup.quotientMulEquivOfEq range_inl_eq_ker_rightHom).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ rightHom_surjective)
  exact CatalogueBPrimeJoin.le_of_isPerfect_of_isSolvable_quotient
    (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

theorem orderOf_inr {q : ↥Q} (hq : (q : MulAut L) * q = 1) (hne : (q : MulAut L) ≠ 1) :
    orderOf (inr q : PumpY Q) = 2 := by
  rw [orderOf_injective _ inr_injective q]
  refine orderOf_eq_prime ?_ fun h => hne (by rw [h]; rfl)
  rw [sq]
  exact Subtype.ext hq

end CFSG.ComponentClassification.EvenPump
