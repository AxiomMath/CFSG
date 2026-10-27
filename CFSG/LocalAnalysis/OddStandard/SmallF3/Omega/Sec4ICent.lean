module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCentralProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IOrd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem natCard_centralizer_toProj_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) {t : OGroup Q} (htt : t * t = 1) :
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

theorem natCard_centralizer_hasType_two_plus_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) {x : ProjOrth Q} (hx : HasType x 2 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 207360 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 2 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = 1 := congrArg Prod.snd hty
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have hU : Module.finrank (ZMod 3) (commSp t) = 2 := hr
  have hW : Module.finrank (ZMod 3) (fixSp t) = 5 := by omega
  have h := natCard_centralizer_toProj_seven hQ hdim htt
  rw [natCard_oGroup_five (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_two_plus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

theorem natCard_centralizer_hasType_two_minus_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) {x : ProjOrth Q} (hx : HasType x 2 (-1)) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 414720 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 2 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = -1 := congrArg Prod.snd hty
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have hU : Module.finrank (ZMod 3) (commSp t) = 2 := hr
  have hW : Module.finrank (ZMod 3) (fixSp t) = 5 := by omega
  have h := natCard_centralizer_toProj_seven hQ hdim htt
  rw [natCard_oGroup_five (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_two_minus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

theorem natCard_centralizer_hasType_four_plus_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) {x : ProjOrth Q} (hx : HasType x 4 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 27648 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 4 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = 1 := congrArg Prod.snd hty
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have hU : Module.finrank (ZMod 3) (commSp t) = 4 := hr
  have hW : Module.finrank (ZMod 3) (fixSp t) = 3 := by omega
  have h := natCard_centralizer_toProj_seven hQ hdim htt
  rw [natCard_oGroup_three (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_four_plus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

theorem natCard_centralizer_hasType_four_minus_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) {x : ProjOrth Q} (hx : HasType x 4 (-1)) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 34560 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 4 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = -1 := congrArg Prod.snd hty
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have hU : Module.finrank (ZMod 3) (commSp t) = 4 := hr
  have hW : Module.finrank (ZMod 3) (fixSp t) = 3 := by omega
  have h := natCard_centralizer_toProj_seven hQ hdim htt
  rw [natCard_oGroup_three (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_four_minus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

theorem natCard_centralizer_hasType_six_plus_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) {x : ProjOrth Q} (hx : HasType x 6 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 24261120 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 6 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = 1 := congrArg Prod.snd hty
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have hU : Module.finrank (ZMod 3) (commSp t) = 6 := hr
  have hW : Module.finrank (ZMod 3) (fixSp t) = 1 := by omega
  have h := natCard_centralizer_toProj_seven hQ hdim htt
  rw [natCard_oGroup_one (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_six_plus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

theorem natCard_centralizer_hasType_six_minus_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) {x : ProjOrth Q} (hx : HasType x 6 (-1)) :
    Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 26127360 := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  have hr : invDim t = 6 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = -1 := congrArg Prod.snd hty
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have hU : Module.finrank (ZMod 3) (commSp t) = 6 := hr
  have hW : Module.finrank (ZMod 3) (fixSp t) = 1 := by omega
  have h := natCard_centralizer_toProj_seven hQ hdim htt
  rw [natCard_oGroup_one (nondegenerate_restrict_fixSp hQ htt) hW,
    natCard_oGroup_six_minus (nondegenerate_restrict_commSp hQ htt) hU hs] at h
  omega

theorem natCard_centralizer_lt_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hσ : quadSign Q = 1) {x : ProjOrth Q}
    (hxx : x * x = 1) (hx1 : x ≠ 1) :
    0 < Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) ∧
      Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) < Nat.card (omegaProj hQ) := by
  rw [natCard_omegaProj_seven hQ hdim]
  rcases hasType_of_involution_seven hQ hdim hσ hxx hx1 with h | h | h | h | h | h
  · rw [natCard_centralizer_hasType_two_plus_seven hQ hdim h]
    norm_num
  · rw [natCard_centralizer_hasType_two_minus_seven hQ hdim h]
    norm_num
  · rw [natCard_centralizer_hasType_four_plus_seven hQ hdim h]
    norm_num
  · rw [natCard_centralizer_hasType_four_minus_seven hQ hdim h]
    norm_num
  · rw [natCard_centralizer_hasType_six_plus_seven hQ hdim h]
    norm_num
  · rw [natCard_centralizer_hasType_six_minus_seven hQ hdim h]
    norm_num

private theorem natCard_centralizer_table (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hσ : quadSign Q = 1) {x : ProjOrth Q}
    (hxx : x * x = 1) (hx1 : x ≠ 1) :
    (HasType x 2 1 ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 207360) ∨
      (HasType x 2 (-1) ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 414720) ∨
      (HasType x 4 1 ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 27648) ∨
      (HasType x 4 (-1) ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 34560) ∨
      (HasType x 6 1 ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 24261120) ∨
      (HasType x 6 (-1) ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 26127360) := by
  rcases hasType_of_involution_seven hQ hdim hσ hxx hx1 with h | h | h | h | h | h
  · exact Or.inl ⟨h, natCard_centralizer_hasType_two_plus_seven hQ hdim h⟩
  · exact Or.inr (Or.inl ⟨h, natCard_centralizer_hasType_two_minus_seven hQ hdim h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, natCard_centralizer_hasType_four_plus_seven hQ hdim h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h, natCard_centralizer_hasType_four_minus_seven hQ hdim h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h, natCard_centralizer_hasType_six_plus_seven hQ hdim h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h, natCard_centralizer_hasType_six_minus_seven hQ hdim h⟩))))

variable {V' : Type} [AddCommGroup V'] [Module (ZMod 3) V'] [FiniteDimensional (ZMod 3) V']
  {Q' : QuadraticForm (ZMod 3) V'}

theorem hasType_of_natCard_eq_seven (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hdim' : Module.finrank (ZMod 3) V' = 7)
    (hσ : quadSign Q = 1) (hσ' : quadSign Q' = 1) {x : ProjOrth Q} {x' : ProjOrth Q'}
    (hxx : x * x = 1) (hx1 : x ≠ 1) (hxx' : x' * x' = 1) (hx1' : x' ≠ 1)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) =
      Nat.card (Subgroup.centralizer ({x'} : Set (ProjOrth Q'))))
    {r : ℕ} {α : ℤˣ} (hr : r = 2 ∨ r = 4 ∨ r = 6) (h : HasType x r α) : HasType x' r α := by
  rcases natCard_centralizer_table hQ hdim hσ hxx hx1 with
      ⟨h1, c1⟩ | ⟨h1, c1⟩ | ⟨h1, c1⟩ | ⟨h1, c1⟩ | ⟨h1, c1⟩ | ⟨h1, c1⟩ <;>
    rcases natCard_centralizer_table hQ' hdim' hσ' hxx' hx1' with
      ⟨h2, c2⟩ | ⟨h2, c2⟩ | ⟨h2, c2⟩ | ⟨h2, c2⟩ | ⟨h2, c2⟩ | ⟨h2, c2⟩ <;>
    first
    | (exfalso; omega)
    | (obtain ⟨rfl, rfl⟩ := eq_of_hasType_seven hQ hdim h h1 hr (by simp); exact h2)

end CFSG.OddStandard.SmallF3.Omega
