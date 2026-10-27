module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG.GroupTheory

open Subgroup

private theorem center_specialLinearGroup_eq_bot_ql2 {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr2, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2' : r ^ 2 = 1 := by simpa using hr2
  have hr1 : r = 1 := by
    have hsq : (r - 1) ^ 2 = 0 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      calc (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
        _ = 1 - 2 * r + 1 := by rw [hr2']
        _ = 0 := by linear_combination (1 - r) * h2
    have h0 : r - 1 = 0 := sq_eq_zero_iff.mp hsq
    exact sub_eq_zero.mp h0
  apply Subtype.ext
  rw [← hrA, hr1]
  ext i j
  simp [Matrix.scalar_apply]

private theorem not_sq_dvd_sixty_ql2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ 60 := by
  intro hd
  have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hd
  have hp8 : p < 8 := by
    by_contra h
    have : 8 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (not_lt.mp h) 2
    omega
  interval_cases p <;> revert hp hp2 hd <;> norm_num

private noncomputable def specialLinearGroupMulEquivOfRingEquiv_ql2
    {R S : Type*} [Field R] [Field S] (f : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map f.toRingHom
  invFun := Matrix.SpecialLinearGroup.map f.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext i j
    change f.symm (f ((A : Matrix (Fin 2) (Fin 2) R) i j)) =
      (A : Matrix (Fin 2) (Fin 2) R) i j
    exact f.symm_apply_apply _
  right_inv B := by
    apply Subtype.ext
    ext i j
    change f (f.symm ((B : Matrix (Fin 2) (Fin 2) S) i j)) =
      (B : Matrix (Fin 2) (Fin 2) S) i j
    exact f.apply_symm_apply _
  map_mul' A B := map_mul (Matrix.SpecialLinearGroup.map f.toRingHom) A B

private theorem center_eq_bot_of_card_quotient_sixty_ql2 {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] (hcard : Nat.card (L ⧸ Subgroup.center L) = 60)
    (hL : CFSG.pCore 2 L = ⊥) : Subgroup.center L = ⊥ := by
  have h2 : IsPGroup 2 (Subgroup.center L) := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
      (Nat.card_pos (α := Subgroup.center L)).ne' fun {q} hq hqd => ?_)
    by_contra hq2
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) q hqd
    have hzo : orderOf z = q := by rw [← hz, Subgroup.orderOf_mk]
    have hZ'c : Subgroup.zpowers z ≤ Subgroup.center L := Subgroup.zpowers_le.mpr hzZ
    have : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hZ'c
    have hZ' : Subgroup.zpowers z = ⊥ := by
      refine CFSG.RankThree.PartTwo.KFacts.KS14.eq_bot_of_isPerfect_of_sylow_comm hZ'c ?_
      intro p hp hpZ P
      have : Fact p.Prime := ⟨hp⟩
      have hpq : p = q := by
        rw [Nat.card_zpowers, hzo] at hpZ
        exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpZ
      subst hpq
      refine CFSG.RankThree.PartTwo.KFacts.KS14.sylow_comm_of_not_sq_dvd
        (Z := Subgroup.center L) le_rfl ?_ P
      rw [hcard]
      exact not_sq_dvd_sixty_ql2 hp hq2
    have hz1 : z = 1 := by
      have hmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
      rwa [hZ', Subgroup.mem_bot] at hmem
    rw [hz1, orderOf_one] at hzo
    exact hq.one_lt.ne hzo
  have hle : Subgroup.center L ≤ CFSG.pCore 2 L := by
    rw [CFSG.pCore]
    exact le_sSup ⟨Subgroup.normal_of_le_center le_rfl, h2⟩
  rw [hL] at hle
  exact le_bot_iff.mp hle

theorem nonempty_mulEquiv_specialLinearGroup_of_isPerfect {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 8 ≤ Nat.card K)
    (e : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
    Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hm
  have hm3 : 3 ≤ (m : ℕ) := by
    by_contra h
    have hle : 2 ^ (m : ℕ) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hcard] at hle
    omega
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
    center_specialLinearGroup_eq_bot_ql2
  let psl : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let π : L →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (e.trans psl).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π :=
    (e.trans psl).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    rw [show π = (e.trans psl).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
        from rfl,
      MonoidHom.ker_comp_of_injective _ _ (e.trans psl).injective, QuotientGroup.ker_mk']
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardGF : Nat.card (GaloisField 2 (m : ℕ)) = 2 ^ (m : ℕ) :=
    GaloisField.card 2 (m : ℕ) (by omega)
  have : Fintype (GaloisField 2 (m : ℕ)) := Fintype.ofFinite _
  have hfcard : Fintype.card K = Fintype.card (GaloisField 2 (m : ℕ)) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardGF]
    exact hcard
  let f : K ≃+* GaloisField 2 (m : ℕ) := FiniteField.ringEquivOfCardEq hfcard
  let sl2e : Matrix.SpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (m : ℕ)) :=
    specialLinearGroupMulEquivOfRingEquiv_ql2 f
  let π' : L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (m : ℕ)) :=
    sl2e.toMonoidHom.comp π
  have hπ' : Function.Surjective π' := sl2e.surjective.comp hπ
  have hker' : π'.ker = π.ker := by
    rw [show π' = sl2e.toMonoidHom.comp π from rfl]
    exact MonoidHom.ker_comp_of_injective π sl2e.toMonoidHom sl2e.injective
  have hbot' : π'.ker = ⊥ :=
    CFSG.LocalAnalysis.EvenBN.Common.ker_eq_bot_of_perfect_central_sl2_two_pow
      (k := GaloisField 2 (m : ℕ)) (E := L) hm3 hcardGF hπ' (by rw [hker', hker])
  have hbot : π.ker = ⊥ := by rw [← hker']; exact hbot'
  exact ⟨MulEquiv.ofBijective π ⟨π.ker_eq_bot_iff.mp hbot, hπ⟩⟩

theorem nonempty_mulEquiv_alternatingGroup_five_of_pCore_eq_bot {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] (hL : CFSG.pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 5)) :
    Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  have hcard : Nat.card (L ⧸ Subgroup.center L) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num
  have hZ : Subgroup.center L = ⊥ := center_eq_bot_of_card_quotient_sixty_ql2 hcard hL
  exact ⟨(QuotientGroup.quotientBot.symm).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).symm.trans e)⟩

end CFSG.GroupTheory
