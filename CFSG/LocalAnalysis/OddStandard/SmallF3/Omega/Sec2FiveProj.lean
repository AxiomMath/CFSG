module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCentralProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCenter

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem piOrth_not_mem_omegaGroup_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) : piOrth Q ∉ omegaGroup hQ := by
  rw [piOrth_mem_omegaGroup_iff hQ, hdim]
  exact fun h => (by decide : ¬ Even (5 : ℕ)) h.1

theorem natCard_omegaProj_five (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5) :
    Nat.card (omegaProj hQ) = 25920 := by
  have h := card_omegaProj_mul hQ (by rw [hdim]; norm_num)
  rw [if_neg (piOrth_not_mem_omegaGroup_five hQ hdim), mul_one,
    natCard_omegaGroup_five hQ hdim] at h
  exact h

theorem natCard_projOrth_five (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5) :
    Nat.card (ProjOrth Q) = 51840 := by
  have h := Subgroup.card_mul_index (omegaProj hQ)
  rw [index_omegaProj_of_odd hQ (by rw [hdim]; norm_num) (by rw [hdim]; decide),
    natCard_omegaProj_five hQ hdim] at h
  omega

theorem natCard_centralizer_toProj_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) {t : OGroup Q} (htt : t * t = 1)
    (hr : invDim t = 2 ∨ invDim t = 4) :
    Nat.card (Subgroup.centralizer ({toProj Q t} : Set (ProjOrth Q))) * 2 =
      Nat.card (OGroup (Q.restrict (fixSp t))) * Nat.card (OGroup (Q.restrict (commSp t))) := by
  have hnc : ¬ IsConj (piOrth Q * t) t := by
    intro h
    have h1 := ((isConj_piOrth_mul_iff hQ htt).mp h).1
    rw [hdim] at h1
    omega
  have hπ : piOrth Q ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_piOrth_comm t).symm
  rw [centralizer_toProj_eq_map hQ htt hnc,
    natCard_map_toProj_mul _ hπ (by rw [hdim]; norm_num), natCard_centralizer_involution hQ htt]

private theorem finrank_split_five (hdim : Module.finrank (ZMod 3) V = 5) (t : OGroup Q)
    {r : ℕ} (hr : invDim t = r) :
    Module.finrank (ZMod 3) (commSp t) = r ∧ Module.finrank (ZMod 3) (fixSp t) = 5 - r := by
  have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have h1 : Module.finrank (ZMod 3) (commSp t) = r := hr
  omega

theorem natCard_centralizer_hasType_four_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) {x : ProjOrth Q} (hx : HasType x 4 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 1152 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 4 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = 1 := congrArg Prod.snd hty
  obtain ⟨hU, hW⟩ := finrank_split_five hdim t hr
  have h := natCard_centralizer_toProj_five hQ hdim htt (Or.inr hr)
  rw [natCard_oGroup_one (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_four_plus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

theorem natCard_centralizer_hasType_two_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) {x : ProjOrth Q} (hx : HasType x 2 (-1)) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 192 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 2 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = -1 := congrArg Prod.snd hty
  obtain ⟨hU, hW⟩ := finrank_split_five hdim t hr
  have h := natCard_centralizer_toProj_five hQ hdim htt (Or.inl hr)
  rw [natCard_oGroup_three (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_two_minus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

theorem natCard_centralizer_hasType_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) {x : ProjOrth Q} (hx : HasType x 4 (-1)) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 1440 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 4 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = -1 := congrArg Prod.snd hty
  obtain ⟨hU, hW⟩ := finrank_split_five hdim t hr
  have h := natCard_centralizer_toProj_five hQ hdim htt (Or.inr hr)
  rw [natCard_oGroup_one (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_four_minus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

theorem natCard_centralizer_hasType_two_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) {x : ProjOrth Q} (hx : HasType x 2 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 96 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 2 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = 1 := congrArg Prod.snd hty
  obtain ⟨hU, hW⟩ := finrank_split_five hdim t hr
  have h := natCard_centralizer_toProj_five hQ hdim htt (Or.inl hr)
  rw [natCard_oGroup_three (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_two_plus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

end CFSG.OddStandard.SmallF3.Omega
