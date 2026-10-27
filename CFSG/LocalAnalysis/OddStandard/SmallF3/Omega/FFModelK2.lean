module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ff_K2_exists_E (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {α : ℤˣ} {t : OGroup Q} (htt : t * t = 1)
    (htype : invType t = (1, α)) :
    ∃ (E : Subgroup ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t)))) (_ : E.Normal),
      LieModel ↥E .PSp 2 3 1 ∧
      IsPGroup 2 (↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) ⧸ E) := by
  have htdim : invDim t = 1 := congrArg Prod.fst htype
  have hcdim : Module.finrank (ZMod 3) (commSp t) = 1 := htdim
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 5 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    rw [hcdim, hdim] at h
    omega
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp t) := by omega
  have hR := nondegenerate_restrict_fixSp hQ htt
  let C : Subgroup (OGroup Q) :=
    omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))
  let φ : OGroup (Q.restrict (fixSp t)) →* OGroup Q :=
    (blockHom htt).comp (MonoidHom.inl _ _)
  let Eimg : Subgroup (OGroup Q) := (omegaGroup hR).map φ
  let E : Subgroup ↥C := Eimg.subgroupOf C
  have hφinj : Function.Injective φ := fun a b hab =>
    congrArg Prod.fst (blockHom_injective htt hab)
  have hEle : Eimg ≤ C := by
    rintro xD ⟨a, ha, rfl⟩
    refine ⟨blockHom_left_mem_omegaGroup hQ htt hW ha, ?_⟩
    rw [← range_blockHom hQ htt]
    exact MonoidHom.mem_range.mpr ⟨(a, 1), rfl⟩
  have hEnorm : E.Normal := by
    constructor
    intro xD hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    obtain ⟨p, hp⟩ := (show (g : OGroup Q) ∈ (blockHom htt).range from by
      rw [range_blockHom hQ htt]; exact g.2.2)
    have hcalc : (g : OGroup Q) * (xD : OGroup Q) * (g : OGroup Q)⁻¹ =
        φ (p.1 * a * p.1⁻¹) := by
      rw [← hax, ← hp]
      change blockHom htt p * blockHom htt (a, 1) * (blockHom htt p)⁻¹ =
        blockHom htt (p.1 * a * p.1⁻¹, 1)
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext rfl (by simp)
    exact Subgroup.mem_map.mpr ⟨p.1 * a * p.1⁻¹,
      (omegaGroup_normal hR).conj_mem _ ha p.1, hcalc.symm⟩
  haveI : E.Normal := hEnorm
  have hfileModelR : LieModel (omegaGroup hR) .PSp 2 3 1 := by
    have hZ : Subgroup.center (omegaGroup hR) = ⊥ :=
      Subgroup.eq_bot_of_card_eq (Subgroup.center (omegaGroup hR))
        (natCard_center_omegaGroup_five hR hUdim)
    exact LieModel.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot) (lieModel_quotient_center_omegaGroup_five hR hUdim)
  have hLieE : LieModel ↥E .PSp 2 3 1 :=
    hfileModelR.of_mulEquiv
      ((Subgroup.equivMapOfInjective _ φ hφinj).trans
        (Subgroup.subgroupOfEquivOfLe hEle).symm)
  have hPE : IsPGroup 2 (↥C ⧸ E) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E x
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨p, hp⟩ := (show (g : OGroup Q) ∈ (blockHom htt).range from by
      rw [range_blockHom hQ htt]; exact g.2.2)
    have hWfin : Nat.card (OGroup (Q.restrict (commSp t))) = 2 :=
      natCard_oGroup_one (nondegenerate_restrict_commSp hQ htt) hcdim
    have hp2 : p.2 * p.2 = 1 := by
      have hdvd : orderOf p.2 ∣ 2 := by
        rw [← hWfin]
        exact orderOf_dvd_natCard p.2
      rw [orderOf_dvd_iff_pow_eq_one] at hdvd
      simpa [pow_two] using hdvd
    have hpp : p * p = (p.1 * p.1, p.2 * p.2) := rfl
    have hcoe : ((g * g : ↥C) : OGroup Q) = blockHom htt p * blockHom htt p := by
      rw [Subgroup.coe_mul, hp]
    have hsq : blockHom htt p * blockHom htt p = blockHom htt (p.1 * p.1, 1) := by
      rw [← map_mul, hpp, hp2]
    rw [hcoe, hsq]
    exact Subgroup.mem_map.mpr
      ⟨p.1 * p.1, mul_self_mem_omegaGroup hR p.1, rfl⟩
  obtain ⟨eC, -⟩ := ff_fixEquiv hQ hdim hsgn htt
  let E' : Subgroup ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) :=
    E.map eC.toMonoidHom
  have hEnorm' : E'.Normal := hEnorm.map _ eC.surjective
  haveI : E'.Normal := hEnorm'
  have hLieE' : LieModel ↥E' .PSp 2 3 1 :=
    hLieE.of_mulEquiv (Subgroup.equivMapOfInjective E eC.toMonoidHom eC.injective)
  have hPE' : IsPGroup 2 (↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) ⧸ E') :=
    hPE.of_equiv (QuotientGroup.congr E E' eC (by rfl))
  exact ⟨E', hEnorm', hLieE', hPE'⟩

theorem ff_K2_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (hx : KM2 x) :
    LayerModel ↥(ffFix hQ (by omega) x) .PSp 2 1 := by
  obtain ⟨α, y, hy, -, t, htt, htype, htoProj⟩ := hx
  have hxeq : x = projOrthToProjSim Q (toProj Q t) := by rw [← hy, htoProj]
  rw [hxeq]
  obtain ⟨E, hEn, hLie, hP⟩ := ff_K2_exists_E hQ hdim hsgn (by omega) htt htype
  exact ⟨E, hEn, hLie, hP⟩

end CFSG.OddStandard.SmallF3.Omega
