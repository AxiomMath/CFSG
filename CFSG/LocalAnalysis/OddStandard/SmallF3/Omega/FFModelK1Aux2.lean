module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38Four
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreDim2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenDelta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}
theorem ff_K1_exists_E (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    {t : OGroup Q} (htt : t * t = 1) (htype : invType t = (2, -1)) :
    ∃ (E : Subgroup ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))))
      (_ : E.Normal),
      LieModel ↥E .PSL 2 3 2 ∧
      IsPGroup 2 (↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) ⧸ E) ∧
      (twoPrimeRes (twoRes (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t)))) ≤
        E.map (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))).subtype) ∧
      (∀ w : ↥(omegaProj hQ), w ∈ E.map (ffFix hQ h2
          (projOrthToProjSim Q (toProj Q t))).subtype → orderOf w = 2 →
        ∃ a : OGroup (Q.restrict (fixSp t)),
          a ∈ omegaGroup (nondegenerate_restrict_fixSp hQ htt) ∧
          (w : ProjOrth Q) = toProj Q (blockHom htt (a, 1)) ∧
          blockHom htt (a, 1) * blockHom htt (a, 1) = 1 ∧
          invType (blockHom htt (a, 1)) = (2, -1)) := by
  have htdim : invDim t = 2 := congrArg Prod.fst htype
  have htsgn : invSign t = -1 := congrArg Prod.snd htype
  have hcdim : Module.finrank (ZMod 3) (commSp t) = 2 := htdim
  have hcsign : quadSign (Q.restrict (commSp t)) = -1 := htsgn
  have hmem : t ∈ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ htt]
    exact ⟨by rw [htdim]; norm_num, by rw [htdim, htsgn]; decide⟩
  have hpiQ : piOrth Q ∉ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ]
    rintro ⟨-, hh⟩
    rw [hdim, hsgn] at hh
    exact absurd hh (by decide)
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 4 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    rw [hcdim, hdim] at h
    omega
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp t) := by omega
  have hWU : 2 ≤ Module.finrank (ZMod 3) (commSp t) := by omega
  have hQU : (Q.restrict (fixSp t)).Nondegenerate := nondegenerate_restrict_fixSp hQ htt
  have hQW : (Q.restrict (commSp t)).Nondegenerate := nondegenerate_restrict_commSp hQ htt
  have hUsign : quadSign (Q.restrict (fixSp t)) = -1 := by
    have h := quadSign_eq_fixSp_commSp hQ htt
    rw [hsgn, hcsign, hcdim, hUdim] at h
    have h1 : ((-1 : ℤˣ)) ^ (4 * 2) = 1 := by decide
    rw [h1, mul_one] at h
    have h2 : (-1 : ℤˣ) * (-1) = 1 := by decide
    calc quadSign (Q.restrict (fixSp t))
        = quadSign (Q.restrict (fixSp t)) * ((-1 : ℤˣ) * (-1)) := by rw [h2, mul_one]
      _ = (quadSign (Q.restrict (fixSp t)) * (-1)) * (-1) := by group
      _ = (1 : ℤˣ) * (-1) := by rw [← h]
      _ = -1 := one_mul _
  have hfileModelU : LieModel (omegaGroup (nondegenerate_restrict_fixSp hQ htt)) .PSL 2 3 2 :=
    lieModel_omegaGroup_four_minus hQU hUdim hUsign
  have hpiU : piOrth (Q.restrict (fixSp t)) ∉ omegaGroup (nondegenerate_restrict_fixSp hQ htt) := by
    rw [piOrth_mem_omegaGroup_iff hQU]
    rintro ⟨-, h⟩
    rw [hUdim, hUsign] at h
    exact absurd h (by decide)
  let C : Subgroup (OGroup Q) :=
    omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))
  let φ : OGroup (Q.restrict (fixSp t)) →* OGroup Q := (blockHom htt).comp (MonoidHom.inl _ _)
  let Eimg : Subgroup (OGroup Q) := (omegaGroup (nondegenerate_restrict_fixSp hQ htt)).map φ
  let E : Subgroup ↥C := Eimg.subgroupOf C
  have hφinj : Function.Injective φ := fun a b hab =>
    congrArg Prod.fst (blockHom_injective htt hab)
  have hEle : Eimg ≤ C := by
    rintro xD ⟨a, ha, rfl⟩
    refine ⟨blockHom_left_mem_omegaGroup hQ htt hW ha, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (ff_blockHom_inl_commute htt a)
  have hEnorm : E.Normal := by
    constructor
    intro xD hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    obtain ⟨p, hp⟩ := (show (g : OGroup Q) ∈ (blockHom htt).range from by
      rw [range_blockHom hQ htt]; exact g.2.2)
    have hcalc : (g : OGroup Q) * (xD : OGroup Q) * (g : OGroup Q)⁻¹ = φ (p.1 * a * p.1⁻¹) := by
      rw [← hax, ← hp]
      change blockHom htt p * blockHom htt (a, 1) * (blockHom htt p)⁻¹ =
        blockHom htt (p.1 * a * p.1⁻¹, 1)
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext rfl (by simp)
    exact Subgroup.mem_map.mpr ⟨p.1 * a * p.1⁻¹,
      (omegaGroup_normal _).conj_mem _ ha p.1, hcalc.symm⟩
  have hLieE : LieModel ↥E .PSL 2 3 2 :=
    hfileModelU.of_mulEquiv
      ((Subgroup.equivMapOfInjective _ φ hφinj).trans (Subgroup.subgroupOfEquivOfLe hEle).symm)
  have hPE : IsPGroup 2 (↥C ⧸ E) := by
    classical
    have hψC_mem : ∀ b : omegaGroup hQW,
        blockInr htt (b : OGroup (Q.restrict (commSp t))) ∈ C := by
      intro b
      refine ⟨blockInr_mem_omegaGroup hQ htt hWU b.2, ?_⟩
      exact blockInr_mem_centralizer hQ htt (b : OGroup (Q.restrict (commSp t)))
    let ψC : omegaGroup hQW →* ↥C :=
      ((blockInr htt).comp (omegaGroup hQW).subtype).codRestrict C hψC_mem
    let ψ : omegaGroup hQW →* ↥C ⧸ E := (QuotientGroup.mk' E).comp ψC
    have hψinj : Function.Injective ψ := by
      intro b b' hbb'
      have h1 : ψ (b⁻¹ * b') = 1 := by rw [map_mul, map_inv, hbb', inv_mul_cancel]
      have h2 : (ψC (b⁻¹ * b') : ↥C) ∈ E := by
        have h3 : QuotientGroup.mk' E (ψC (b⁻¹ * b')) = 1 := h1
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      have hE2 : (ψC (b⁻¹ * b') : OGroup Q) ∈ Eimg := Subgroup.mem_subgroupOf.mp h2
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hE2
      have heq : (a, 1) = (1, ((b⁻¹ * b' : omegaGroup hQW) :
          OGroup (Q.restrict (commSp t)))) :=
        blockHom_injective htt (by
          have h4 : blockHom htt (a, 1) = (ψC (b⁻¹ * b') : OGroup Q) := hae
          rwa [show (ψC (b⁻¹ * b') : OGroup Q) = blockInr htt (b⁻¹ * b') from rfl,
            blockInr_apply] at h4)
      have hb1 : b⁻¹ * b' = 1 := Subtype.ext (by simpa using (congrArg Prod.snd heq).symm)
      exact inv_mul_eq_one.mp hb1
    have hΩW : IsPGroup 2 (omegaGroup hQW) :=
      (isPGroup_two_oGroup_of_finrank_two hQW hcdim).to_subgroup _
    have hK : IsPGroup 2 ψ.range := hΩW.of_equiv (MonoidHom.ofInjective hψinj)
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E x
    obtain ⟨p, hp⟩ := (show (g : OGroup Q) ∈ (blockHom htt).range from by
      rw [range_blockHom hQ htt]; exact g.2.2)
    have he1E : (⟨φ (p.1 * p.1), hEle (Subgroup.mem_map.mpr
        ⟨p.1 * p.1, mul_self_mem_omegaGroup hQU p.1, rfl⟩)⟩ : ↥C) ∈ E :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr
        ⟨p.1 * p.1, mul_self_mem_omegaGroup hQU p.1, rfl⟩)
    let e1 : ↥C := ⟨φ (p.1 * p.1), hEle (Subgroup.mem_map.mpr
      ⟨p.1 * p.1, mul_self_mem_omegaGroup hQU p.1, rfl⟩)⟩
    let bW : omegaGroup hQW := ⟨p.2 * p.2, mul_self_mem_omegaGroup hQW p.2⟩
    have hgg : (g : OGroup Q) * g = blockHom htt (p * p) := by rw [← hp, ← map_mul]
    have hdecomp : g * g = e1 * ψC bW := by
      apply Subtype.ext
      show (g : OGroup Q) * g = φ (p.1 * p.1) * blockInr htt (bW : OGroup (Q.restrict (commSp t)))
      rw [hgg]
      change blockHom htt (p * p) = blockHom htt (p.1 * p.1, 1) * blockHom htt (1, p.2 * p.2)
      rw [← map_mul]
      congr 1
    have hsq : (QuotientGroup.mk' E g) ^ 2 = ψ bW := by
      rw [pow_two, ← map_mul, hdecomp, map_mul,
        show QuotientGroup.mk' E e1 = 1 from by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact he1E, one_mul]
      rfl
    have hsq_mem : (QuotientGroup.mk' E g) ^ 2 ∈ ψ.range := ⟨bW, hsq.symm⟩
    obtain ⟨k, hk⟩ := hK ⟨(QuotientGroup.mk' E g) ^ 2, hsq_mem⟩
    refine ⟨k + 1, ?_⟩
    have hk' : (((⟨(QuotientGroup.mk' E g) ^ 2, hsq_mem⟩ : ψ.range)) ^ (2 ^ k) :
        ↥C ⧸ E) = 1 := congrArg Subtype.val hk
    rw [Nat.pow_succ, mul_comm (2 ^ k) 2, pow_mul]
    simpa using hk'
  obtain ⟨eC, heC⟩ := ff_fixEquiv hQ hdim hsgn htt
  let E' : Subgroup ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) :=
    E.map eC.toMonoidHom
  have hEnorm' : E'.Normal := hEnorm.map _ eC.surjective
  have hLieE' : LieModel ↥E' .PSL 2 3 2 :=
    hLieE.of_mulEquiv (Subgroup.equivMapOfInjective E eC.toMonoidHom eC.injective)
  have hPE' : IsPGroup 2 (↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) ⧸ E') :=
    hPE.of_equiv (QuotientGroup.congr E E' eC (by rfl))
  have htwoRes : twoRes (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) ≤
      E'.map (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))).subtype := by
    rw [twoRes]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, hodd⟩
    by_contra hnot
    let g' : ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) := ⟨g, hg⟩
    have hne : QuotientGroup.mk' E' g' ≠ 1 := by
      intro h
      apply hnot
      refine Subgroup.mem_map.mpr ⟨g', ?_, rfl⟩
      exact (QuotientGroup.eq_one_iff g').mp h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2dvd : 2 ∣ orderOf (QuotientGroup.mk' E' g') := hPE'.dvd_orderOf hne
    have hdvd : orderOf (QuotientGroup.mk' E' g') ∣ orderOf g := by
      rw [← Subgroup.orderOf_mk g hg]
      exact orderOf_map_dvd _ g'
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat hdvd)) (even_iff_two_dvd.mpr h2dvd)
  have hXle : twoPrimeRes (twoRes (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t)))) ≤
      E'.map (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))).subtype :=
    ((Subgroup.closure_le _).mpr (fun g hg => hg.1)).trans htwoRes
  have hdesc : ∀ w : ↥(omegaProj hQ), w ∈ E'.map (ffFix hQ h2
      (projOrthToProjSim Q (toProj Q t))).subtype → orderOf w = 2 →
      ∃ a : OGroup (Q.restrict (fixSp t)),
        a ∈ omegaGroup (nondegenerate_restrict_fixSp hQ htt) ∧
        (w : ProjOrth Q) = toProj Q (blockHom htt (a, 1)) ∧
        blockHom htt (a, 1) * blockHom htt (a, 1) = 1 ∧
        invType (blockHom htt (a, 1)) = (2, -1) := by
    rintro w hw hw2'
    obtain ⟨w', hw'E, hw'w⟩ := Subgroup.mem_map.mp hw
    obtain ⟨z, hzE, hz⟩ := Subgroup.mem_map.mp hw'E
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hzE)
    have hwa : (w : ProjOrth Q) = toProj Q (blockHom htt (a, 1)) := by
      calc (w : ProjOrth Q) = (w' : ProjOrth Q) :=
            congrArg (fun x : ↥(omegaProj hQ) => (x : ProjOrth Q)) hw'w.symm
        _ = (eC z : ProjOrth Q) :=
            (congrArg (fun x : ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) =>
              ((x : ↥(omegaProj hQ)) : ProjOrth Q)) hz).symm
        _ = toProj Q (z : OGroup Q) := heC z
        _ = toProj Q (blockHom htt (a, 1)) := by rw [← haz]; rfl
    have hww : w * w = 1 := by rw [← pow_two, ← hw2', pow_orderOf_eq_one]
    have hbmem : blockHom htt (a, 1) ∈ omegaGroup hQ :=
      blockHom_left_mem_omegaGroup hQ htt hW ha
    have hb2 : blockHom htt (a, 1) * blockHom htt (a, 1) = 1 := by
      have h2 : ((w : ↥(omegaProj hQ)) : ProjOrth Q) *
          ((w : ↥(omegaProj hQ)) : ProjOrth Q) = 1 := by
        have := congrArg (fun u : ↥(omegaProj hQ) => (u : ProjOrth Q)) hww
        simpa using this
      have h1 : toProj Q (blockHom htt (a, 1) * blockHom htt (a, 1)) = 1 := by
        rw [map_mul, ← hwa]; exact h2
      have hmem2 : blockHom htt (a, 1) * blockHom htt (a, 1) ∈ omegaGroup hQ :=
        (omegaGroup hQ).mul_mem hbmem hbmem
      have h3 : omegaToProj hQ ⟨_, hmem2⟩ = 1 := by
        apply Subtype.ext; rw [coe_omegaToProj]; exact h1
      rcases (omegaToProj_eq_one_iff hQ _).mp h3 with hh | hh
      · exact hh
      · exact absurd (hh ▸ (⟨_, hmem2⟩ : omegaGroup hQ).2) hpiQ
    have haa : a * a = 1 := by
      apply hφinj
      rw [map_mul, map_one]
      change blockHom htt (a, 1) * blockHom htt (a, 1) = 1
      exact hb2
    have hwne : w ≠ 1 := fun h => by
      rw [h, orderOf_one] at hw2'
      exact (by decide : (1 : ℕ) ≠ 2) hw2'
    have ha1 : a ≠ 1 := by
      intro ha1'
      apply hwne
      apply Subtype.ext
      rw [hwa, ha1']
      have hb1 : blockHom htt ((1 : OGroup (Q.restrict (fixSp t))), 1) = 1 :=
        map_one (blockHom htt)
      rw [hb1, map_one]
      rfl
    have hane : a ≠ piOrth (Q.restrict (fixSp t)) := fun h => hpiU (h ▸ ha)
    have htypeb : invType (blockHom htt (a, 1)) = (2, -1) := by
      rw [ff_invType_blockHom_inl hQ htt haa, invType_eq_two_minus hQU hUdim haa ha ha1 hane]
    exact ⟨a, ha, hwa, hb2, htypeb⟩
  exact ⟨E', hEnorm', hLieE', hPE', hXle, hdesc⟩


end CFSG.OddStandard.SmallF3.Omega
