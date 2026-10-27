module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TI4mBlk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFixHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MKinds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCentralProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma sec8t84t_aux_descend {S B : Type*} [Group S] [Group B] (ψ : S →* B)
    (hψ : Function.Surjective ψ) (ε : S →* (ZMod 3)ˣ)
    (hker : ∀ s, ψ s = 1 → ε s = 1) :
    ∃ ε' : B →* (ZMod 3)ˣ, ∀ s, ε' (ψ s) = ε s := by
  have hk : ψ.ker ≤ ε.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    exact hker s hs
  refine ⟨MonoidHom.liftOfRightInverse ψ (Function.surjInv hψ)
    (Function.rightInverse_surjInv hψ) ⟨ε, hk⟩, ?_⟩
  intro s
  exact MonoidHom.liftOfRightInverse_comp_apply ψ (Function.surjInv hψ)
    (Function.rightInverse_surjInv hψ) ⟨ε, hk⟩ s

theorem sec8t84t_N1_char (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V) {t : OGroup Q}
    (htt : t * t = 1) (htype : invType t = (2, 1)) :
    ∃ (ε : ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) →* (ZMod 3)ˣ)
      (u : ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t)))), u * u = 1 ∧ ε u = -1 := by
  have htdim : invDim t = 2 := congrArg Prod.fst htype
  have hcdim : Module.finrank (ZMod 3) (commSp t) = 2 := htdim
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 4 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    rw [hcdim, hdim] at h
    omega
  have hnc : ¬ IsConj (piOrth Q * t) t := by
    rw [isConj_piOrth_mul_iff hQ htt]
    rintro ⟨h2r, -⟩
    rw [htdim] at h2r
    omega
  obtain ⟨p, hp2, hpΩ, hpdet⟩ :=
    sec8t84t_exists_block_involution hQ hdim htt htype
  let P := OGroup (Q.restrict (fixSp t)) × OGroup (Q.restrict (commSp t))
  let S : Subgroup P := (omegaGroup hQ).comap (blockHom htt)
  let C : Subgroup (OGroup Q) :=
    omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))
  let toC : ↥S →* ↥C := ((blockHom htt).comp S.subtype).codRestrict C (fun q =>
    ⟨(Subgroup.mem_comap).mp q.2, by
      rw [← range_blockHom hQ htt]
      exact ⟨q.1, rfl⟩⟩)
  let ψ : ↥S →* ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))) :=
    (ff6mFixHom hQ hdim hsgn htt hnc).comp toC
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨c, hc⟩ := ff6mFixHom_surjective hQ hdim hsgn htt hnc b
    obtain ⟨q, hq⟩ := (show (c : OGroup Q) ∈ (blockHom htt).range from by
      rw [range_blockHom hQ htt]
      exact c.2.2)
    have hqS : q ∈ S := by
      rw [Subgroup.mem_comap, hq]
      exact c.2.1
    refine ⟨⟨q, hqS⟩, ?_⟩
    rw [show ψ ⟨q, hqS⟩ = ff6mFixHom hQ hdim hsgn htt hnc (toC ⟨q, hqS⟩) from rfl,
      show toC ⟨q, hqS⟩ = c from Subtype.ext hq, hc]
  let ε0 : ↥S →* (ZMod 3)ˣ :=
    (QuadraticMap.orthogonalDet (Q.restrict (fixSp t))).comp
      ((MonoidHom.fst _ _).comp S.subtype)
  have hker : ∀ q : ↥S, ψ q = 1 → ε0 q = 1 := by
    intro q hq
    have h1 := (ff6mFixHom_eq_one_iff hQ hdim hsgn htt hnc (toC q)).mp hq
    rcases h1 with h1 | h1
    · have hq1 : (q : P) = 1 :=
        blockHom_injective htt (h1.trans (map_one (blockHom htt)).symm)
      rw [show q = 1 from Subtype.ext hq1, map_one]
    · have hpair : (q : P) = (piOrth (Q.restrict (fixSp t)),
          piOrth (Q.restrict (commSp t))) :=
        blockHom_injective htt (h1.trans (blockHom_piOrth_piOrth htt).symm)
      have hfst : (q : P).1 = piOrth (Q.restrict (fixSp t)) := congrArg Prod.fst hpair
      change QuadraticMap.orthogonalDet (Q.restrict (fixSp t)) (q : P).1 = 1
      rw [hfst, orthogonalDet_piOrth (V := fixSp t) (Q := Q.restrict (fixSp t)), hUdim]
      decide
  obtain ⟨ε', hε'⟩ := sec8t84t_aux_descend ψ hψ ε0 hker
  let s0 : ↥S := ⟨p, (Subgroup.mem_comap).mpr hpΩ⟩
  refine ⟨ε', ψ s0, ?_, ?_⟩
  · rw [← map_mul, show s0 * s0 = 1 from Subtype.ext hp2, map_one]
  · rw [hε' s0]
    change QuadraticMap.orthogonalDet (Q.restrict (fixSp t)) p.1 = -1
    exact hpdet

theorem sec8t84t_KN1_char (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {x : ProjSim Q} (hx : KN1 x) :
    ∃ (ε : ↥(ffFix hQ (by omega) x) →* (ZMod 3)ˣ) (u : ↥(ffFix hQ (by omega) x)),
      u * u = 1 ∧ ε u = -1 := by
  obtain ⟨y, hyx, htype⟩ := hx
  obtain ⟨-, t, htt, hty, hto⟩ := htype
  have htt' : (piOrth Q * t) * (piOrth Q * t) = 1 := piOrth_mul_mul_self htt
  have htype' : invType (piOrth Q * t) = (2, 1) := by
    rw [invType_piOrth_mul hQ htt, hdim, hsgn,
      show invDim t = 4 from congrArg Prod.fst hty,
      show invSign t = -1 from congrArg Prod.snd hty]
    decide
  have hx' : x = projOrthToProjSim Q (toProj Q (piOrth Q * t)) := by
    rw [← hyx, ← hto, map_mul, toProj_piOrth, one_mul]
  subst hx'
  exact sec8t84t_N1_char hQ hdim hsgn (by omega) htt' htype'

end CFSG.OddStandard.SmallF3.Omega
