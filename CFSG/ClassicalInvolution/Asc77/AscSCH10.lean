module

public import CFSG.ClassicalInvolution.Asc77.AscSCH08
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ClassicalInvolution.Asc77.AscSCH07

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {r : ℕ} {k : Type} [Field k]

theorem lam_eq_one {i : Fin r} {g : SpecialLinearGroup (Fin 2) k} (h : lam i g = 1) :
    g = 1 := by
  have hm : pairMat (Sum.inl i : Fin r ⊕ Fin r) (Sum.inr i) (g : Matrix (Fin 2) (Fin 2) k) =
      (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
    have := congrArg (fun x : StatedSp r k =>
      ((x : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) h
    simpa [coe_lam] using this
  obtain ⟨h00, h01, h10, h11⟩ :=
    pairMat_apply_pair (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i)
    (g : Matrix (Fin 2) (Fin 2) k)
  rw [hm] at h00 h01 h10 h11
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  fin_cases a <;> fin_cases b <;> simp_all

theorem lam_disj {i j : Fin r} (hij : i ≠ j) {a b : SpecialLinearGroup (Fin 2) k}
    (h : lam i a = lam j b) : lam i a = 1 := by
  suffices ha : a = 1 by rw [ha, map_one]
  have hm : pairMat (Sum.inl i : Fin r ⊕ Fin r) (Sum.inr i) (a : Matrix (Fin 2) (Fin 2) k) =
      pairMat (Sum.inl j : Fin r ⊕ Fin r) (Sum.inr j) (b : Matrix (Fin 2) (Fin 2) k) := by
    have := congrArg (fun x : StatedSp r k =>
      ((x : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) h
    simpa [coe_lam] using this
  have hinl : ∀ x : Fin r ⊕ Fin r, x = Sum.inl i ∨ x = Sum.inr i →
      x ≠ Sum.inl j ∧ x ≠ Sum.inr j := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨fun h => hij (Sum.inl_injective h), Sum.inl_ne_inr⟩
    · exact ⟨Sum.inr_ne_inl, fun h => hij (Sum.inr_injective h)⟩
  obtain ⟨h00, h01, h10, h11⟩ := pairMat_apply_pair
    (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i) (a : Matrix (Fin 2) (Fin 2) k)
  have e1 := congrFun (congrFun hm (Sum.inl i)) (Sum.inl i)
  have e2 := congrFun (congrFun hm (Sum.inl i)) (Sum.inr i)
  have e3 := congrFun (congrFun hm (Sum.inr i)) (Sum.inl i)
  have e4 := congrFun (congrFun hm (Sum.inr i)) (Sum.inr i)
  rw [pairMat_apply_of_ne (hinl _ (Or.inl rfl)).1 (hinl _ (Or.inl rfl)).2, h00] at e1
  rw [pairMat_apply_of_ne (hinl _ (Or.inl rfl)).1 (hinl _ (Or.inl rfl)).2, h01] at e2
  rw [pairMat_apply_of_ne (hinl _ (Or.inr rfl)).1 (hinl _ (Or.inr rfl)).2, h10] at e3
  rw [pairMat_apply_of_ne (hinl _ (Or.inr rfl)).1 (hinl _ (Or.inr rfl)).2, h11] at e4
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  fin_cases x <;> fin_cases y <;> simp_all

theorem not_three_dvd_sq_add_one {q : ℕ} (hq : ¬ 3 ∣ q) : ¬ 3 ∣ q ^ 2 + 1 := by
  have h : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h with h | h <;> simp [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod, Nat.add_mod, h]

theorem sp_two_factorization_le {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) :
    (Nat.card (StatedSp 2 K)).factorization 3 ≤
      2 * (Nat.card (SpecialLinearGroup (Fin 2) K)).factorization 3 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  set q := Nat.card K with hqdef
  have hsq : 1 < q ^ 2 := by nlinarith
  have hq4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [Nat.one_le_pow 2 q (by omega), Nat.one_le_pow 4 q (by omega)]
    ring
  have h3q : ∀ n : ℕ, (q ^ n).factorization 3 = 0 := fun n =>
    Nat.factorization_eq_zero_of_not_dvd (fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h))
  have h3q2 : (q ^ 2 + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_three_dvd_sq_add_one h3)
  have hne1 : q ^ 2 - 1 ≠ 0 := by omega
  have hne2 : q ^ 2 + 1 ≠ 0 := by omega
  have hne3 : q ≠ 0 := by omega
  have hne4 : q ^ 4 ≠ 0 := pow_ne_zero 4 hne3
  have e : Nat.card (StatedSp 2 K) = q ^ 4 * ((q ^ 2 - 1) * ((q ^ 2 - 1) * (q ^ 2 + 1))) := by
    rw [SymplecticFlag.card_statedSp, ← hqdef, show Finset.Icc 1 2 = {1, 2} by decide,
      Finset.prod_pair (by norm_num), ← hq4]
    norm_num
  rw [e, card_sl2, ← hqdef, Nat.factorization_mul hne4 (mul_ne_zero hne1 (mul_ne_zero hne1 hne2)),
    Nat.factorization_mul hne1 (mul_ne_zero hne1 hne2), Nat.factorization_mul hne1 hne2,
    Nat.factorization_mul hne3 hne1]
  simp only [Finsupp.add_apply, h3q, h3q2]
  omega

theorem statedSp_two_perfect_ker_eq_bot_cross {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = ℓ ^ f) {E : Type*} [Group E]
    [Finite E] [Group.IsPerfect E] (π : E →* StatedSp 2 K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  obtain ⟨t, ht⟩ := exists_zpowers_sylow_sl2 hℓ2 hK (r := 3) (by norm_num) (Ne.symm hℓ3)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  refine ker_eq_bot_of_blocks (by norm_num) π hπ hC hCp (lam 0) (lam 1)
    ?_ ?_ (fun a b => (commute_lam_lam h01 a b).eq) (fun a b h => lam_disj h01 h)
    (rho 0 1 h01 sl2W) (fun a => ?_) (fun a => ?_) t
    ((sp_two_factorization_le h3).trans (Nat.mul_le_mul_left 2 ht))
  · rw [injective_iff_map_eq_one]; exact fun a ha => lam_eq_one ha
  · rw [injective_iff_map_eq_one]; exact fun a ha => lam_eq_one ha
  · simpa using DFunLike.congr_fun (conj_rho_sl2W_comp_lam_fst (k := K) h01) a
  · simpa using DFunLike.congr_fun (conj_rho_sl2W_comp_lam_snd (k := K) h01) a

end CFSG.ClassicalInvolution.Asc77.SCH
