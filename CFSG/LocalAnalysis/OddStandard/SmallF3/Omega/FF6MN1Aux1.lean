module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFixHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2BlockInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38Four
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreDim2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCentralProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_blockHom_inl_ne_piOrth {t : OGroup Q} (htt : t * t = 1)
    (hcdim : Module.finrank (ZMod 3) (commSp t) = 2)
    (a : OGroup (Q.restrict (fixSp t))) :
    blockHom htt (a, 1) ≠ piOrth Q := by
  intro h
  have h1 : (a, 1) = (piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) := by
    apply blockHom_injective htt
    rw [h, blockHom_piOrth_piOrth htt]
  have h2 : (1 : OGroup (Q.restrict (commSp t))) = piOrth (Q.restrict (commSp t)) :=
    congrArg Prod.snd h1
  exact piOrth_ne_one (Q := Q.restrict (commSp t)) (by rw [hcdim]; norm_num) h2.symm

theorem ff6m_N1_exists_E (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    {t : OGroup Q} (htt : t * t = 1) (htype : invType t = (2, 1)) :
    ∃ (E : Subgroup ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t)))) (_ : E.Normal),
      LieModel ↥E .PSL 2 3 2 ∧
      IsPGroup 2 (↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) ⧸ E) ∧
      (∀ (a : OGroup (Q.restrict (fixSp t)))
        (_ : a ∈ omegaGroup (nondegenerate_restrict_fixSp hQ htt))
        (hm : blockHom htt (a, 1) ∈ omegaGroup hQ),
        omegaToProj hQ ⟨blockHom htt (a, 1), hm⟩ ∈
          E.map (ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))).subtype) := by
  have htdim : invDim t = 2 := congrArg Prod.fst htype
  have htsgn : invSign t = 1 := congrArg Prod.snd htype
  have hcdim : Module.finrank (ZMod 3) (commSp t) = 2 := htdim
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 4 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    rw [hcdim, hdim] at h
    omega
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp t) := by omega
  have hWU : 2 ≤ Module.finrank (ZMod 3) (commSp t) := by omega
  have hQU : (Q.restrict (fixSp t)).Nondegenerate := nondegenerate_restrict_fixSp hQ htt
  have hQW : (Q.restrict (commSp t)).Nondegenerate := nondegenerate_restrict_commSp hQ htt
  have hUsign : quadSign (Q.restrict (fixSp t)) = -1 := by
    have h := quadSign_fixSp_eq hQ htt
    rw [hsgn, htsgn, htdim, hdim] at h
    have h1 : ((-1 : ℤˣ)) ^ (2 * (6 - 2)) = 1 := by decide
    rw [h1, mul_one, mul_one] at h
    exact h
  have hnc : ¬ IsConj (piOrth Q * t) t := by
    rw [isConj_piOrth_mul_iff hQ htt]
    rintro ⟨h2r, -⟩
    rw [htdim] at h2r
    omega
  have hfileModelU : LieModel (omegaGroup hQU) .PSL 2 3 2 :=
    lieModel_omegaGroup_four_minus hQU hUdim hUsign
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
  have hLie0 : LieModel ↥E0 .PSL 2 3 2 :=
    hfileModelU.of_mulEquiv
      ((Subgroup.equivMapOfInjective _ φ hφinj).trans
        (Subgroup.subgroupOfEquivOfLe hEle).symm)
  have hP0 : IsPGroup 2 (↥C ⧸ E0) := by
    classical
    have hψC_mem : ∀ b : omegaGroup hQW,
        blockInr htt (b : OGroup (Q.restrict (commSp t))) ∈ C := by
      intro b
      refine ⟨blockInr_mem_omegaGroup hQ htt hWU b.2, ?_⟩
      exact blockInr_mem_centralizer hQ htt (b : OGroup (Q.restrict (commSp t)))
    let ψC : omegaGroup hQW →* ↥C :=
      ((blockInr htt).comp (omegaGroup hQW).subtype).codRestrict C hψC_mem
    let ψ : omegaGroup hQW →* ↥C ⧸ E0 := (QuotientGroup.mk' E0).comp ψC
    have hψinj : Function.Injective ψ := by
      intro b b' hbb'
      have h1 : ψ (b⁻¹ * b') = 1 := by rw [map_mul, map_inv, hbb', inv_mul_cancel]
      have h2 : (ψC (b⁻¹ * b') : ↥C) ∈ E0 := by
        have h3 : QuotientGroup.mk' E0 (ψC (b⁻¹ * b')) = 1 := h1
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
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E0 x
    obtain ⟨p, hp⟩ := (show (g : OGroup Q) ∈ (blockHom htt).range from by
      rw [range_blockHom hQ htt]; exact g.2.2)
    have he1E : (⟨φ (p.1 * p.1), hEle (Subgroup.mem_map.mpr
        ⟨p.1 * p.1, mul_self_mem_omegaGroup hQU p.1, rfl⟩)⟩ : ↥C) ∈ E0 :=
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
    have hsq : (QuotientGroup.mk' E0 g) ^ 2 = ψ bW := by
      rw [pow_two, ← map_mul, hdecomp, map_mul,
        show QuotientGroup.mk' E0 e1 = 1 from by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact he1E, one_mul]
      rfl
    have hsq_mem : (QuotientGroup.mk' E0 g) ^ 2 ∈ ψ.range := ⟨bW, hsq.symm⟩
    obtain ⟨k, hk⟩ := hK ⟨(QuotientGroup.mk' E0 g) ^ 2, hsq_mem⟩
    refine ⟨k + 1, ?_⟩
    have hk' : (((⟨(QuotientGroup.mk' E0 g) ^ 2, hsq_mem⟩ : ψ.range)) ^ (2 ^ k) :
        ↥C ⧸ E0) = 1 := congrArg Subtype.val hk
    rw [Nat.pow_succ, mul_comm (2 ^ k) 2, pow_mul]
    simpa using hk'
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
      exact ff6m_blockHom_inl_ne_piOrth htt hcdim a hpi
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
  have hLieE : LieModel ↥E .PSL 2 3 2 :=
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
