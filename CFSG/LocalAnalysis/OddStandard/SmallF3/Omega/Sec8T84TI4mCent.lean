module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MClassModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec8t84t_aux_center_eq_bot {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  haveI := hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnc
    exact absurd ((mem_center_iff.mp (h ▸ mem_top b)) a) hab

theorem sec8t84t_centB_eq_one (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {x : ProjSim Q} (E : Subgroup ↥(ffFix hQ (by omega) x)) [E.Normal]
    (hE : IsSimpleGroup ↥E) (hnc : ∃ a b : ↥E, a * b ≠ b * a)
    (h2 : IsPGroup 2 (↥(ffFix hQ (by omega) x) ⧸ E)) {c : ↥(ffFix hQ (by omega) x)}
    (hc : ∀ e ∈ E, c * e = e * c) : c = 1 := by
  haveI := hE
  have hcen : center ↥E = ⊥ := sec8t84t_aux_center_eq_bot hE hnc
  obtain ⟨j, hj⟩ := h2 (QuotientGroup.mk c)
  have hcE : c ^ (2 ^ j) ∈ E := by
    refine (QuotientGroup.eq_one_iff (N := E) (c ^ (2 ^ j))).mp ?_
    rw [QuotientGroup.mk_pow]
    exact hj
  have hmemc : (⟨c ^ (2 ^ j), hcE⟩ : ↥E) ∈ center ↥E := by
    rw [mem_center_iff]
    intro e
    apply Subtype.ext
    exact ((show Commute c (e : ↥(ffFix hQ (by omega) x)) from
      hc (e : ↥(ffFix hQ (by omega) x)) e.2).pow_left (2 ^ j)).eq.symm
  have hzp : c ^ (2 ^ j) = 1 := by
    have h1 : (⟨c ^ (2 ^ j), hcE⟩ : ↥E) ∈ (⊥ : Subgroup ↥E) := hcen ▸ hmemc
    have h2' : (⟨c ^ (2 ^ j), hcE⟩ : ↥E) = 1 := Subgroup.mem_bot.mp h1
    simpa using
      congrArg (fun z : ↥E => (z : ↥(ffFix hQ (by omega) x))) h2'
  by_contra hc1
  have hdvd : orderOf c ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hzp
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hc1 (orderOf_eq_one_iff.mp hm)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have h2dvd : 2 ∣ orderOf c := by
    rw [hm, pow_succ]
    exact ⟨2 ^ k, by ring⟩
  let w : ↥(ffFix hQ (by omega) x) := c ^ (orderOf c / 2)
  have hx0 : orderOf c ≠ 0 :=
    orderOf_ne_zero_iff.mpr
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 ^ j, by positivity, hzp⟩)
  have hword : orderOf w = 2 := by
    simpa [w] using orderOf_pow_orderOf_div hx0 h2dvd
  have hw2 : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hword] at h
    rwa [pow_two] at h
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hword
    omega
  have hwΩ2 : ((w : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)) *
      ((w : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)) = 1 := by
    simpa using
      congrArg (fun z : ↥(ffFix hQ (by omega) x) => (z : ↥(omegaProj hQ))) hw2
  have hwΩ1 : ((w : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)) ≠ 1 :=
    fun h => hw1 (Subtype.ext h)
  have hKM0 : KM0 (projOrthToProjSim Q ((w : ↥(omegaProj hQ)) : ProjOrth Q)) :=
    ff6m_involution_kind hQ hdim hsgn hwΩ2 hwΩ1
  have hsol : Group.IsSolvable
      ↥(ffFix hQ (by omega) (projOrthToProjSim Q ((w : ↥(omegaProj hQ)) : ProjOrth Q))) :=
    ff6m_K0_solvable hQ hdim hsgn hKM0
  have hceq : ∀ e : ↥E,
      ((c ^ (orderOf c / 2)) * (e : ↥(ffFix hQ (by omega) x)) =
        (e : ↥(ffFix hQ (by omega) x)) * (c ^ (orderOf c / 2))) :=
    fun e => ((show Commute c (e : ↥(ffFix hQ (by omega) x)) from
      hc (e : ↥(ffFix hQ (by omega) x)) e.2).pow_left (orderOf c / 2)).eq
  have hcommΩ : ∀ e : ↥E,
      ((w : ↥(omegaProj hQ)) * (((e : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ))) =
        (((e : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ))) * (w : ↥(omegaProj hQ))) := by
    intro e
    simpa [w] using
      congrArg (fun z : ↥(ffFix hQ (by omega) x) => (z : ↥(omegaProj hQ))) (hceq e)
  have hconj : ∀ e : ↥E,
      ((w : ↥(omegaProj hQ)) : ProjOrth Q) *
        (((e : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)) : ProjOrth Q) *
        (((w : ↥(omegaProj hQ)) : ProjOrth Q))⁻¹ =
      (((e : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)) : ProjOrth Q) := by
    intro e
    have h1 : ((w : ↥(omegaProj hQ)) * (((e : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)))) *
        (w : ↥(omegaProj hQ))⁻¹ =
        (((e : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ))) := by
      rw [hcommΩ e]
      group
    simpa using
      congrArg (fun z : ↥(omegaProj hQ) => (z : ProjOrth Q)) h1
  let f : ↥E →* ↥(ffFix hQ (by omega)
      (projOrthToProjSim Q ((w : ↥(omegaProj hQ)) : ProjOrth Q))) :=
    { toFun := fun e =>
        ⟨((e : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)), by
          rw [show ffFix hQ (by omega)
              (projOrthToProjSim Q ((w : ↥(omegaProj hQ)) : ProjOrth Q)) =
              fixSub (ffSimOmegaAct hQ (by omega)
                (projOrthToProjSim Q ((w : ↥(omegaProj hQ)) : ProjOrth Q))) from rfl,
            mem_fixSub_iff]
          apply Subtype.ext
          rw [ffSimOmegaAct_projOrthToProjSim, MulAut.conjNormal_apply]
          exact hconj e⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h3 : ((a : ↥E) : ↥(omegaProj hQ)) = ((b : ↥E) : ↥(omegaProj hQ)) :=
      congrArg (fun z : ↥(ffFix hQ (by omega)
          (projOrthToProjSim Q ((w : ↥(omegaProj hQ)) : ProjOrth Q))) =>
            (z : ↥(omegaProj hQ))) hab
    exact Subtype.ext (Subtype.ext h3)
  haveI : Group.IsSolvable ↥(ffFix hQ (by omega)
      (projOrthToProjSim Q ((w : ↥(omegaProj hQ)) : ProjOrth Q))) := hsol
  haveI : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (f := f) hf_inj
  haveI : Group.IsPerfect ↥E := (ff_isQuasisimple_of_simple hE hnc).1
  exact (Group.IsPerfect.not_isSolvable ↥E) inferInstance

end CFSG.OddStandard.SmallF3.Omega
