module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Supp
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceLp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.Classical CFSG.LocalAnalysis.GLTheoremA.HDescUniRes
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU blockSUOn_injective)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp (statedSU_eq_gramSU)

section Group

variable {K₀ : Type} [Field K₀]

private theorem three_dvd_card_gramSU_four (h₀ : UnitaryFieldData 2 1 K₀) :
    3 ∣ Nat.card (gramSU h₀ (idGram K₀ 4)) := by
  have := h₀.finite
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.CTP.exists_primitiveRoot_of_dvd (F := K₀)
    Nat.prime_three (by rw [h₀.card]; norm_num)
  obtain ⟨u, hu⟩ : ∃ u : K₀ˣ, (u : K₀) = ζ := ⟨Units.mk0 ζ (hζ.ne_zero (by norm_num)), rfl⟩
  have hu3 : u ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hu, Units.val_one]; exact hζ.pow_eq_one)
  have hu1 : (u : K₀) ≠ 1 := by
    rw [hu]
    exact hζ.ne_one (by norm_num)
  let dv : Fin 4 → K₀ˣ := ![u, u, u, 1]
  have hdv3 : ∀ i, dv i ^ 3 = 1 := by
    intro i
    fin_cases i
    exacts [hu3, hu3, hu3, one_pow 3]
  have hnorm : ∀ i, h₀.norm ((dv i : K₀ˣ) : K₀) = 1 := fun i =>
    (pow_succ_eq_one_iff_norm h₀ (dv i)).1 (hdv3 i)
  have hprod : ∏ i, ((dv i : K₀ˣ) : K₀) = 1 := by
    rw [Fin.prod_univ_four]
    show (u : K₀) * u * u * ((1 : K₀ˣ) : K₀) = 1
    rw [Units.val_one, mul_one, ← pow_three', ← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  let d : gramSU h₀ (idGram K₀ 4) := ⟨unitaryDiagGL dv, unitaryDiagGL_mem_gramSU h₀ hnorm hprod⟩
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
    show (diagonal fun i => ((dv i : K₀ˣ) : K₀)) ^ 3 = 1
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    show ((dv i : K₀ˣ) : K₀) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, hdv3, Units.val_one]
  have hd1 : d ≠ 1 := by
    intro h1
    have h1' := congrArg
      (fun A : gramSU h₀ (idGram K₀ 4) => ((A : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) 0 0) h1
    have h2 : (u : K₀) = 1 := h1'
    exact hu1 h2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← orderOf_eq_prime hd3 hd1]
  exact orderOf_dvd_natCard d

theorem simple_coordBlockSU_of_card_four [Finite K₀] [CharP K₀ 2] (h₀ : UnitaryFieldData 2 1 K₀)
    {n : ℕ} {J : Finset (Fin n)} (hJ : J.card = 4) :
    IsSimpleGroup (coordBlockSU K₀ 2 1 J) ∧ (∃ a b : coordBlockSU K₀ 2 1 J, a * b ≠ b * a) ∧
      3 ∣ Nat.card (coordBlockSU K₀ 2 1 J) := by
  let eB : Su K₀ 2 1 J.card ≃* coordBlockSU K₀ 2 1 J :=
    MonoidHom.ofInjective (blockSUOn_injective (K := K₀) (p := 2) (f := 1) J)
  suffices H : IsSimpleGroup (Su K₀ 2 1 J.card) ∧ (∃ a b : Su K₀ 2 1 J.card, a * b ≠ b * a) ∧
      3 ∣ Nat.card (Su K₀ 2 1 J.card) by
    obtain ⟨hs, ⟨a, b, hab⟩, h3⟩ := H
    haveI := hs
    refine ⟨eB.symm.isSimpleGroup, ⟨eB a, eB b, fun h' => hab (eB.injective ?_)⟩, ?_⟩
    · rw [map_mul, map_mul]
      exact h'
    · rw [← Nat.card_congr eB.toEquiv]
      exact h3
  rw [hJ]
  have heq₀ : SUid (unitaryInvolution K₀ 2 1) 4 = gramSU h₀ (idGram K₀ 4) :=
    (SUid_eq_statedSU (h₀.card.trans (by norm_num)) 4).trans (statedSU_eq_gramSU h₀ 4)
  haveI : IsSimpleGroup (primeFormP h₀ (idGram K₀ 4)) :=
    isSimpleGroup_primeFormP_one h₀ (n := 4) (by norm_num) (by norm_num)
  let e : Su K₀ 2 1 4 ≃* primeFormP h₀ (idGram K₀ 4) := (MulEquiv.subgroupCongr heq₀).trans
    (MulEquiv.ofBijective (QuotientGroup.mk' _)
      ⟨primeFormP_mk_injective_four h₀, QuotientGroup.mk'_surjective _⟩)
  refine ⟨e.isSimpleGroup, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    exact not_commute_primeFormP_one h₀ (n := 4) (by norm_num) (by norm_num) fun x y =>
      e.symm.injective (by rw [map_mul, map_mul]; exact hcon _ _)
  · rw [Nat.card_congr (MulEquiv.subgroupCongr heq₀).toEquiv]
    exact three_dvd_card_gramSU_four h₀

end Group

section Matrix

variable {K : Type} [Field K]

theorem eq_one_of_mul_diagonal_eq_smul {n : ℕ} {e : Fin n → K} {J : Finset (Fin n)}
    (hJe : ∀ l, l ∈ J ↔ e l = 1) (hJ : Jᶜ.card < J.card) {Y : Matrix (Fin n) (Fin n) K}
    (hY : Y.det ≠ 0) {ν : K} (h : Y * diagonal e = ν • (diagonal e * Y)) : ν = 1 := by
  classical
  by_contra hν
  obtain ⟨π, hπ⟩ := exists_perm_of_support hY (a := e) (a' := fun l => ν * e l)
    (fun l k hlk => by
      have e1 := congrFun (congrFun h l) k
      rw [mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul] at e1
      show ν * e l = e k
      apply mul_left_cancel₀ hlk
      linear_combination -e1)
  have hsub : J.map π.toEmbedding ⊆ Jᶜ := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hl
    rw [Finset.mem_compl, hJe]
    intro h1
    have e2 : ν * e (π k) = e k := hπ k
    rw [Equiv.toEmbedding_apply] at h1
    rw [h1, mul_one, (hJe k).1 hk] at e2
    exact hν e2
  have := Finset.card_le_card hsub
  rw [Finset.card_map] at this
  omega

end Matrix

theorem mul_conj_eq_of_mul_eq {R : Type*} [Ring R] {P U U' B : R} (hUU : U * U' = 1)
    (hU'U : U' * U = 1) (hPU : P * U = U * P) (hPB : P * B = P) (hBP : B * P = P) :
    P * (U * B * U') = P ∧ U * B * U' * P = P := by
  have hPU' : P * U' = U' * P :=
    calc P * U' = U' * U * P * U' := by rw [hU'U, one_mul]
      _ = U' * (U * P) * U' := by simp only [mul_assoc]
      _ = U' * (P * U) * U' := by rw [hPU]
      _ = U' * P * (U * U') := by simp only [mul_assoc]
      _ = U' * P := by rw [hUU, mul_one]
  constructor
  · calc P * (U * B * U') = U * (P * B) * U' := by
          rw [← mul_assoc, ← mul_assoc, hPU, mul_assoc U P B]
      _ = P := by rw [hPB, mul_assoc, hPU', ← mul_assoc, hUU, one_mul]
  · calc U * B * U' * P = U * (B * P) * U' := by
          rw [mul_assoc, hPU'.symm, ← mul_assoc, mul_assoc U B P]
      _ = P := by rw [hBP, ← hPU, mul_assoc, hUU, mul_one]

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
