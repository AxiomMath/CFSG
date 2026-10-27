module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFixHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCentralProj
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_blockHom_inl_ne_piOrth_pos {t : OGroup Q} (htt : t * t = 1)
    (hpos : 0 < Module.finrank (ZMod 3) (commSp t))
    (a : OGroup (Q.restrict (fixSp t))) :
    blockHom htt (a, 1) ≠ piOrth Q := by
  intro h
  have h1 : (a, 1) = (piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) := by
    apply blockHom_injective htt
    rw [h, blockHom_piOrth_piOrth htt]
  have h2 : (1 : OGroup (Q.restrict (commSp t))) = piOrth (Q.restrict (commSp t)) :=
    congrArg Prod.snd h1
  exact piOrth_ne_one (Q := Q.restrict (commSp t)) hpos h2.symm

theorem ff6m_K2_exists_E (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    {α : ℤˣ} {t : OGroup Q} (htt : t * t = 1) (htype : invType t = (1, α)) :
    ∃ (E : Subgroup ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t)))) (_ : E.Normal),
      LieModel ↥E .PSp 2 3 1 ∧
      IsPGroup 2 (↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) ⧸ E) ∧
      (∀ (a : OGroup (Q.restrict (fixSp t)))
        (_ : a ∈ omegaGroup (nondegenerate_restrict_fixSp hQ htt))
        (hm : blockHom htt (a, 1) ∈ omegaGroup hQ),
        omegaToProj hQ ⟨blockHom htt (a, 1), hm⟩ ∈
          E.map (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))).subtype) := by
  have htdim : invDim t = 1 := congrArg Prod.fst htype
  have htsgn : invSign t = α := congrArg Prod.snd htype
  have hcdim : Module.finrank (ZMod 3) (commSp t) = 1 := htdim
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 5 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    rw [hcdim, hdim] at h
    omega
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp t) := by omega
  have hQU : (Q.restrict (fixSp t)).Nondegenerate := nondegenerate_restrict_fixSp hQ htt
  have hUsign : quadSign (Q.restrict (fixSp t)) = α := by
    have h := quadSign_fixSp_eq hQ htt
    rw [hsgn, htsgn, htdim, hdim] at h
    have h1 : (-1 : ℤˣ) ^ (1 * (6 - 1)) = -1 := by decide
    rw [h1] at h
    have h2 : (-1 : ℤˣ) * α * (-1) = α := by
      rw [mul_comm ((-1 : ℤˣ) * α) (-1), ← mul_assoc,
        show (-1 : ℤˣ) * (-1) = 1 by decide, one_mul]
    rwa [h2] at h
  have hnc : ¬ IsConj (piOrth Q * t) t := by
    rw [isConj_piOrth_mul_iff hQ htt]
    rintro ⟨h2r, -⟩
    rw [htdim] at h2r
    omega
  have hfileModelU : LieModel (omegaGroup hQU) .PSp 2 3 1 := by
    have hZ : Subgroup.center (omegaGroup hQU) = ⊥ :=
      Subgroup.eq_bot_of_card_eq (Subgroup.center (omegaGroup hQU))
        (natCard_center_omegaGroup_five hQU hUdim)
    exact LieModel.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot) (lieModel_quotient_center_omegaGroup_five hQU hUdim)
  let C : Subgroup (OGroup Q) :=
    omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))
  let φ : OGroup (Q.restrict (fixSp t)) →* OGroup Q := (blockHom htt).comp (MonoidHom.inl _ _)
  let Eimg : Subgroup (OGroup Q) := (omegaGroup hQU).map φ
  let E0 : Subgroup ↥C := Eimg.subgroupOf C
  have hφinj : Function.Injective φ := fun a b hab =>
    congrArg Prod.fst (blockHom_injective htt hab)
  have hEle : Eimg ≤ C := by
    rintro x ⟨a, ha, rfl⟩
    exact ⟨blockHom_left_mem_omegaGroup hQ htt hW ha,
      Subgroup.mem_centralizer_singleton_iff.mpr (ff_blockHom_inl_commute htt a)⟩
  have hE0norm : E0.Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    obtain ⟨p, hp⟩ := (show (g : OGroup Q) ∈ (blockHom htt).range from by
      rw [range_blockHom hQ htt]; exact g.2.2)
    have hcalc : (g : OGroup Q) * (x : OGroup Q) * (g : OGroup Q)⁻¹ = φ (p.1 * a * p.1⁻¹) := by
      rw [← hax, ← hp]
      change blockHom htt p * blockHom htt (a, 1) * (blockHom htt p)⁻¹ =
        blockHom htt (p.1 * a * p.1⁻¹, 1)
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext rfl (by simp)
    exact Subgroup.mem_map.mpr
      ⟨p.1 * a * p.1⁻¹, (omegaGroup_normal hQU).conj_mem _ ha p.1, hcalc.symm⟩
  have hLie0 : LieModel ↥E0 .PSp 2 3 1 :=
    hfileModelU.of_mulEquiv
      ((Subgroup.equivMapOfInjective _ φ hφinj).trans
        (Subgroup.subgroupOfEquivOfLe hEle).symm)
  have hP0 : IsPGroup 2 (↥C ⧸ E0) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E0 x
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
      ⟨p.1 * p.1, mul_self_mem_omegaGroup hQU p.1, rfl⟩
  let ψ : ↥C →* ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) :=
    ff6mFixHom hQ hdim hsgn htt hnc
  have hψsurj : Function.Surjective ψ := ff6mFixHom_surjective hQ hdim hsgn htt hnc
  let E : Subgroup ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) := E0.map ψ
  have hEnorm : E.Normal := hE0norm.map ψ hψsurj
  have hinj : ∀ g ∈ E0, ψ g = 1 → g = 1 := by
    intro g hg hg1
    rcases (ff6mFixHom_eq_one_iff hQ hdim hsgn htt hnc g).mp hg1 with h1 | h1
    · exact Subtype.ext h1
    · exfalso
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hg)
      have hpi : blockHom htt (a, 1) = piOrth Q := hae.trans h1
      exact ff6m_blockHom_inl_ne_piOrth_pos htt (by omega) a hpi
  have hinj' : Function.Injective (ψ.comp E0.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hinj g.1 g.2 hg)
  let ψcod : ↥E0 →* ↥E :=
    (ψ.comp E0.subtype).codRestrict E (fun g => ⟨g.1, g.2, rfl⟩)
  have hψcod : Function.Bijective ψcod := by
    constructor
    · intro a b hab
      exact hinj' (congrArg Subtype.val hab)
    · rintro ⟨y, g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hLieE : LieModel ↥E .PSp 2 3 1 :=
    LieModel.of_mulEquiv (MulEquiv.ofBijective ψcod hψcod) hLie0
  have hPE : IsPGroup 2 (↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) ⧸ E) :=
    hP0.of_surjective (QuotientGroup.map E0 (E0.map ψ) ψ
      (fun x hx => Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)) (fun y => by
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨a, rfl⟩ := hψsurj b
        exact ⟨QuotientGroup.mk a, rfl⟩)
  have hcont : ∀ (a : OGroup (Q.restrict (fixSp t)))
      (_ : a ∈ omegaGroup (nondegenerate_restrict_fixSp hQ htt))
      (hm : blockHom htt (a, 1) ∈ omegaGroup hQ),
      omegaToProj hQ ⟨blockHom htt (a, 1), hm⟩ ∈
        E.map (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))).subtype := by
    intro a ha hm
    have hmemC : blockHom htt (a, 1) ∈ C :=
      ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr (ff_blockHom_inl_commute htt a)⟩
    have hE0 : (⟨blockHom htt (a, 1), hmemC⟩ : ↥C) ∈ E0 :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    have hxE : ψ ⟨blockHom htt (a, 1), hmemC⟩ ∈ E :=
      Subgroup.mem_map.mpr ⟨⟨blockHom htt (a, 1), hmemC⟩, hE0, rfl⟩
    have hmemE : (ψ ⟨blockHom htt (a, 1), hmemC⟩ : ↥(omegaProj hQ)) ∈
        E.map (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))).subtype :=
      Subgroup.mem_map.mpr ⟨ψ ⟨blockHom htt (a, 1), hmemC⟩, hxE, rfl⟩
    have heq : (ψ ⟨blockHom htt (a, 1), hmemC⟩ : ↥(omegaProj hQ)) =
        omegaToProj hQ ⟨blockHom htt (a, 1), hm⟩ := by
      apply Subtype.ext
      rw [ff6mFixHom_coe, coe_omegaToProj]
    rw [heq] at hmemE
    exact hmemE
  exact ⟨E, hEnorm, hLieE, hPE, hcont⟩

end CFSG.OddStandard.SmallF3.Omega
