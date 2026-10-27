module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1Aux2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_K1_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (hx : KM1 x) :
    LayerModel ↥(ffFix hQ (by omega) x) .PSL 2 2 := by
  obtain ⟨y, hy, -, t, htt, htype, ht⟩ := hx
  have hxeq : x = projOrthToProjSim Q (toProj Q t) := by rw [← hy, ← ht]
  rw [hxeq]
  obtain ⟨E, hEn, hLie, hP, -, -⟩ := ff_K1_exists_E hQ hdim hsgn (by omega) htt htype
  exact ⟨E, hEn, hLie, hP⟩

theorem ff_K1_invol (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (hx : KM1 x) {w : ↥(omegaProj hQ)}
    (hw : w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) x))) (hw2 : orderOf w = 2) :
    KM1 (projOrthToProjSim Q (w : ProjOrth Q)) := by
  obtain ⟨y, hy, -, t, htt, htype, ht⟩ := hx
  have hxeq : x = projOrthToProjSim Q (toProj Q t) := by rw [← hy, ← ht]
  rw [hxeq] at hw
  obtain ⟨_E, _hEn, _hLie, _hP, hXle, hdesc⟩ := ff_K1_exists_E hQ hdim hsgn (by omega) htt htype
  obtain ⟨a, ha, hwa, hb2, htypeb⟩ := hdesc w (hXle hw) hw2
  refine ⟨(w : ProjOrth Q), rfl, ?_, blockHom htt (a, 1), hb2, htypeb, hwa.symm⟩
  intro hw1
  have hw1' : w = 1 := Subtype.ext hw1
  rw [hw1', orderOf_one] at hw2
  exact (by decide : (1 : ℕ) ≠ 2) hw2

theorem ff_K1_prod (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {y : ↥(omegaProj hQ)}
    (hy : KM1 (projOrthToProjSim Q (y : ProjOrth Q))) {w : ↥(omegaProj hQ)}
    (hw : w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) (projOrthToProjSim Q (y : ProjOrth Q)))))
    (hw2 : orderOf w = 2) :
    orderOf (w * y) = 2 ∧ KM0 (projOrthToProjSim Q ((w * y : ↥(omegaProj hQ)) : ProjOrth Q)) := by
  obtain ⟨y', hy', -, t, htt, htype, ht⟩ := hy
  have hyt : toProj Q t = (y : ProjOrth Q) := by
    rw [ht]; exact projOrthToProjSim_injective hy'
  have htdim : invDim t = 2 := congrArg Prod.fst htype
  have htsgn : invSign t = -1 := congrArg Prod.snd htype
  have hcdim : Module.finrank (ZMod 3) (commSp t) = 2 := htdim
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 4 := by
    have hh := finrank_fixSp_add_finrank_commSp (Q := Q) t
    rw [hcdim, hdim] at hh
    omega
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp t) := by omega
  have htmem : t ∈ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ htt]
    exact ⟨by rw [htdim]; norm_num, by rw [htdim, htsgn]; decide⟩
  rw [← hyt] at hw
  obtain ⟨_E, _hEn, _hLie, _hP, hXle, hdesc⟩ := ff_K1_exists_E hQ hdim hsgn (by omega) htt htype
  obtain ⟨a, ha, hwa, hb2, htypeb⟩ := hdesc w (hXle hw) hw2
  have hbcomm : commSp (blockHom htt (a, 1)) ≤ fixSp t := by
    rw [ff_commSp_blockHom_inl htt a]
    rintro x ⟨v, -, rfl⟩
    exact v.2
  have horth : ∀ v ∈ commSp (blockHom htt (a, 1)), ∀ u ∈ commSp t,
      QuadraticMap.polar Q v u = 0 :=
    fun v hv u hu => polar_fixSp_commSp htt (hbcomm hv) hu
  have hb1 : invDim (blockHom htt (a, 1)) = 2 := congrArg Prod.fst htypeb
  have hb2s : invSign (blockHom htt (a, 1)) = -1 := congrArg Prod.snd htypeb
  have htype_mul : invType (blockHom htt (a, 1) * t) = (4, 1) := by
    rw [invType_mul_of_orth hQ hb2 htt horth, hb1, htdim, hb2s, htsgn]
    decide
  have hmul2 : (blockHom htt (a, 1) * t) * (blockHom htt (a, 1) * t) = 1 :=
    mul_mul_self_of_orth hQ hb2 htt horth
  have hcoe : ((w * y : ↥(omegaProj hQ)) : ProjOrth Q) =
      toProj Q (blockHom htt (a, 1) * t) := by
    rw [Subgroup.coe_mul, hwa, ← hyt, ← map_mul]
  have hwy2 : (w * y) * (w * y) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hcoe, ← map_mul, hmul2, map_one]
    rfl
  have hwyne : w * y ≠ 1 := by
    intro h1
    have h2 : toProj Q (blockHom htt (a, 1) * t) = 1 := by rw [← hcoe, h1]; rfl
    have hmem : blockHom htt (a, 1) * t ∈ omegaGroup hQ :=
      (omegaGroup hQ).mul_mem (blockHom_left_mem_omegaGroup hQ htt hW ha) htmem
    have h3 : omegaToProj hQ ⟨_, hmem⟩ = 1 := by
      apply Subtype.ext; rw [coe_omegaToProj]; exact h2
    rcases (omegaToProj_eq_one_iff hQ _).mp h3 with hh | hh
    · have hh' : blockHom htt (a, 1) * t = 1 := hh
      rw [hh', invType_one] at htype_mul
      exact absurd htype_mul (by decide)
    · have hh' : blockHom htt (a, 1) * t = piOrth Q := hh
      have hpi : invType (piOrth Q) = (6, 1) := by rw [invType_piOrth hQ, hdim, hsgn]
      rw [hh', hpi] at htype_mul
      exact absurd htype_mul (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horder : orderOf (w * y) = 2 :=
    orderOf_eq_prime (p := 2) (by rwa [pow_two]) hwyne
  refine ⟨horder, ?_⟩
  exact ⟨((w * y : ↥(omegaProj hQ)) : ProjOrth Q), rfl,
    (fun h => hwyne (Subtype.ext h)), blockHom htt (a, 1) * t, hmul2, htype_mul, hcoe.symm⟩

end CFSG.OddStandard.SmallF3.Omega
