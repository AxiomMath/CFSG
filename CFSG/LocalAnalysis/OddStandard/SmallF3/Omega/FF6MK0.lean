module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFixHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCentralProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem isSolvable_of_natCard {G : Type*} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G := by
  haveI := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

private noncomputable def auxProdEquiv (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    (OGroup (Q.restrict (fixSp t)) × OGroup (Q.restrict (commSp t))) ≃*
      ↥(Subgroup.centralizer ({t} : Set (OGroup Q))) := by
  classical
  let φ : (OGroup (Q.restrict (fixSp t)) × OGroup (Q.restrict (commSp t))) →*
      ↥(Subgroup.centralizer ({t} : Set (OGroup Q))) :=
    { toFun := fun p => ⟨blockHom htt p, by
        rw [← range_blockHom hQ htt]
        exact MonoidHom.mem_range.mpr ⟨p, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun p q => Subtype.ext (map_mul _ p q) }
  exact MulEquiv.ofBijective φ (by
    constructor
    · intro p q hpq
      exact blockHom_injective htt (Subtype.ext_iff.mp hpq)
    · intro y
      have hy : (y : OGroup Q) ∈ (blockHom htt).range := by
        rw [range_blockHom hQ htt]
        exact y.2
      obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hy
      exact ⟨p, Subtype.ext hp⟩)

private noncomputable def auxHom (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))) →*
      OGroup (Q.restrict (fixSp t)) × OGroup (Q.restrict (commSp t)) :=
  (auxProdEquiv hQ htt).symm.toMonoidHom.comp (Subgroup.inclusion inf_le_right)

private theorem auxHom_injective (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    Function.Injective (auxHom hQ htt) := by
  intro a b hab
  exact Subgroup.inclusion_injective inf_le_right ((auxProdEquiv hQ htt).symm.injective hab)

private theorem aux_finrank_commSp_eq {t : OGroup Q} {r : ℕ} {α : ℤˣ}
    (hty : invType t = (r, α)) : Module.finrank (ZMod 3) (commSp t) = r := by
  have h := congrArg Prod.fst hty
  simpa only [invType, invDim] using h

private theorem aux_quadSign_commSp_eq {t : OGroup Q} {r : ℕ} {α : ℤˣ}
    (hty : invType t = (r, α)) : quadSign (Q.restrict (commSp t)) = α := by
  have h := congrArg Prod.snd hty
  simpa only [invType, invSign] using h

private theorem aux_quadSign_fixSp_eq (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {t : OGroup Q}
    (htt : t * t = 1) (hty : invType t = (4, 1)) :
    quadSign (Q.restrict (fixSp t)) = -1 := by
  have h := quadSign_fixSp_eq hQ htt
  have hr : invDim t = 4 := congrArg Prod.fst hty
  have hα : invSign t = 1 := congrArg Prod.snd hty
  have hpow : ((-1 : ℤˣ) ^ (4 * (6 - 4))) = 1 := by
    rw [show 4 * (6 - 4) = 2 * 4 by norm_num, pow_mul]
    have h2 : (-1 : ℤˣ) ^ 2 = 1 := by norm_num
    rw [h2, one_pow]
  rw [hsgn, hα, hr, hdim] at h
  simpa [hpow] using h

theorem ff6m_K0_solvable (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KM0 x) : Group.IsSolvable ↥(ffFix hQ (by omega) x) := by
  obtain ⟨y, hyx, htype⟩ := hx
  obtain ⟨_, t, htt, hty, hto⟩ := htype
  have hyx' : projOrthToProjSim Q (toProj Q t) = x := by rw [hto]; exact hyx
  have hnc : ¬ IsConj (piOrth Q * t) t := by
    intro h
    have h' := (isConj_piOrth_mul_iff hQ htt).mp h
    have hr : invDim t = 4 := congrArg Prod.fst hty
    rw [hr, hdim] at h'
    norm_num at h'
  have hdimC : Module.finrank (ZMod 3) (commSp t) = 4 := aux_finrank_commSp_eq hty
  have hsgnC : quadSign (Q.restrict (commSp t)) = 1 := aux_quadSign_commSp_eq hty
  have hdimU : Module.finrank (ZMod 3) (fixSp t) = 2 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    omega
  have hsgnU := aux_quadSign_fixSp_eq hQ hdim hsgn htt hty
  haveI hsolU : Group.IsSolvable (OGroup (Q.restrict (fixSp t))) :=
    isSolvable_of_natCard (p := 2) (q := 3) (a := 3) (b := 0)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [natCard_oGroup_two_minus (nondegenerate_restrict_fixSp hQ htt) hdimU hsgnU]
          norm_num)
  haveI hsolW : Group.IsSolvable (OGroup (Q.restrict (commSp t))) :=
    isSolvable_of_natCard (p := 2) (q := 3) (a := 7) (b := 2)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [natCard_oGroup_four_plus (nondegenerate_restrict_commSp hQ htt) hdimC hsgnC]
          norm_num)
  haveI hsolC : Group.IsSolvable ↥(Subgroup.centralizer ({t} : Set (OGroup Q))) :=
    ff_solvable_congr (auxProdEquiv hQ htt) inferInstance
  haveI hsolA :
      Group.IsSolvable ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))) :=
    Group.isSolvable_of_isSolvable_injective (f := auxHom hQ htt) (auxHom_injective hQ htt)
  rw [← hyx']
  exact Group.isSolvable_of_surjective (f := ff6mFixHom hQ hdim hsgn htt hnc)
    (ff6mFixHom_surjective hQ hdim hsgn htt hnc)

end CFSG.OddStandard.SmallF3.Omega
