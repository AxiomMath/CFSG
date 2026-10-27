module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Blueprint.Catalog

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticFour
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def tauS (b c d : K) : StatedSp 2 K := tau (sym2_transpose b c d)

theorem coe_tauS (b c d : K) :
    (((tauS b c d : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 1 (sym2 b c d) 0 1 :=
  coe_tau _

theorem tauS_mul_tauS (b c d b' c' d' : K) :
    tauS b c d * tauS b' c' d' = tauS (b + b') (c + c') (d + d') := by
  rw [tauS, tauS, tau_mul_tau]
  refine tau_congr _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym2]

theorem tauS_zero : tauS (0 : K) 0 0 = 1 := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauS, show sym2 (0 : K) 0 0 = 0 by ext i j; fin_cases i <;> fin_cases j <;> rfl,
    fromBlocks_one]
  rfl

theorem tauS_inv (b c d : K) : (tauS b c d)⁻¹ = tauS (-b) (-c) (-d) :=
  inv_eq_of_mul_eq_one_right (by rw [tauS_mul_tauS, add_neg_cancel, add_neg_cancel,
    add_neg_cancel, tauS_zero])

theorem tauS_mem_unipotent (b c d : K) : tauS b c d ∈ unipotent 2 K :=
  tau_mem_unipotent _

theorem tau_eq_tauS {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    tau hC = tauS (C 0 0) (C 0 1) (C 1 1) :=
  tau_congr _ _ (eq_sym2 hC)

theorem torusHom_mul_tauS (s : Fin 2 → Kˣ) (b c d : K) :
    SymplecticTorusWeyl.torusHom s * tauS b c d =
      tauS ((s 0 : K) ^ 2 * b) ((s 0 : K) * (s 1 : K) * c) ((s 1 : K) ^ 2 * d) *
        SymplecticTorusWeyl.torusHom s := by
  apply SymplecticTorusWeyl.statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, SymplecticTorusWeyl.coe_torusHom, coe_tauS]
  have h0 := (s 0).ne_zero
  have h1 := (s 1).ne_zero
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [sym2] <;> field_simp

theorem torusHom_mul_lam (s : Fin 2 → Kˣ) (a : K) :
    SymplecticTorusWeyl.torusHom s * lam a =
      lam ((s 0 : K) * (s 1 : K)⁻¹ * a) * SymplecticTorusWeyl.torusHom s := by
  apply SymplecticTorusWeyl.statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, SymplecticTorusWeyl.coe_torusHom, coe_lam]
  have h0 := (s 0).ne_zero
  have h1 := (s 1).ne_zero
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [unitri] <;> field_simp

theorem torusHom_const_conj_tauS (u : Kˣ) (b c d : K) :
    SymplecticTorusWeyl.torusHom (fun _ => u) * tauS b c d *
      (SymplecticTorusWeyl.torusHom (fun _ => u))⁻¹ =
      tauS ((u : K) ^ 2 * b) ((u : K) ^ 2 * c) ((u : K) ^ 2 * d) := by
  rw [mul_inv_eq_iff_eq_mul, torusHom_mul_tauS, sq]

theorem torusHom_const_conj_lam (u : Kˣ) (a : K) :
    SymplecticTorusWeyl.torusHom (fun _ => u) * lam a *
      (SymplecticTorusWeyl.torusHom (fun _ => u))⁻¹ = lam a := by
  rw [mul_inv_eq_iff_eq_mul, torusHom_mul_lam, mul_inv_cancel₀ u.ne_zero, one_mul]

theorem torusHom_first_conj_tauS (u : Kˣ) (b c d : K) :
    SymplecticTorusWeyl.torusHom ![u, 1] * tauS b c d *
      (SymplecticTorusWeyl.torusHom ![u, 1])⁻¹ = tauS ((u : K) ^ 2 * b) ((u : K) * c) d := by
  rw [mul_inv_eq_iff_eq_mul, torusHom_mul_tauS]
  simp

theorem torusHom_first_conj_lam (u : Kˣ) (a : K) :
    SymplecticTorusWeyl.torusHom ![u, 1] * lam a * (SymplecticTorusWeyl.torusHom ![u, 1])⁻¹ =
      lam ((u : K) * a) := by
  rw [mul_inv_eq_iff_eq_mul, torusHom_mul_lam]
  simp

variable (K) in
@[expose] def swapGL : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

variable (K) in
@[expose] def weylD : StatedSp 2 K := SymplecticTorusWeyl.leviSp (swapGL K)

theorem weylD_mul_tauS (d : K) : weylD K * tauS 0 0 d = tauS d 0 0 * weylD K := by
  apply SymplecticTorusWeyl.statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, weylD, SymplecticTorusWeyl.coe_leviSp, coe_tauS]
  change fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0]ᵀ * _ =
    _ * fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0]ᵀ
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply, sym2]

variable (K) in
@[expose] def weylAMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1] !![0, 0; 0, 1] !![1, 0; 0, 0]

theorem weylAMat_mul_self : weylAMat K * weylAMat K = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [weylAMat, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply]

section CharTwo

variable [CharP K 2]

theorem weylAMat_symplectic :
    (weylAMat K)ᵀ * fromBlocks 0 1 (-1) 0 * weylAMat K = fromBlocks 0 1 (-1) 0 := by
  have h2 : (-1 : K) = 1 := CharTwo.neg_eq 1
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [weylAMat, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply, h2]

variable (K) in
@[expose] def weylA : StatedSp 2 K :=
  ⟨⟨weylAMat K, weylAMat K, weylAMat_mul_self, weylAMat_mul_self⟩,
    SymplecticTorusWeyl.mem_statedSp_iff.mpr weylAMat_symplectic⟩

theorem weylA_mul_lam (a : K) : weylA K * lam a = tauS 0 a 0 * weylA K := by
  apply SymplecticTorusWeyl.statedSp_ext
  have h2 : (-a : K) = a := CharTwo.neg_eq a
  simp only [Subgroup.coe_mul, Units.val_mul, coe_lam, coe_tauS]
  change weylAMat K * _ = _ * weylAMat K
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [weylAMat, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply, unitri, sym2,
      h2]

theorem lam_mul_tauS_mul_inv (a b c d : K) :
    lam a * tauS b c d * (lam a)⁻¹ = tauS (b + a ^ 2 * d) (c + a * d) d := by
  rw [tauS, lam_mul_tau_mul_inv]
  exact tau_congr _ _ (unitri_mul_sym2_mul_transpose a b c d)

theorem commutatorElement_lam_tauS (a b c d : K) :
    ⁅lam a, tauS b c d⁆ = tauS (a ^ 2 * d) (a * d) 0 := by
  rw [commutatorElement_def, lam_mul_tauS_mul_inv, tauS_inv, tauS_mul_tauS]
  congr 1
  · ring
  · ring
  · exact add_neg_cancel d

theorem lam_mul_tauS_zero (a b c : K) : lam a * tauS b c 0 = tauS b c 0 * lam a := by
  have h := lam_mul_tauS_mul_inv a b c 0
  simp only [mul_zero, add_zero] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem tauS_zero_mul_comm {g : StatedSp 2 K} (hg : g ∈ unipotent 2 K) (b c : K) :
    tauS b c 0 * g = g * tauS b c 0 := by
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.mp hg
  rw [← mul_assoc, tauS, tau_comm _ hC, mul_assoc, ← tauS, ← lam_mul_tauS_zero, mul_assoc]

theorem sq_add_self_ne_zero_of_charTwo {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) : t ^ 2 + t ≠ 0 := by
  intro h
  have h' : t * (t + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h₁ | h₁
  · exact ht0 h₁
  · exact ht1 (by linear_combination h₁ - CharP.cast_eq_zero K 2)

theorem sq_ne_one_of_charTwo {t : K} (ht1 : t ≠ 1) : t ^ 2 ≠ 1 := by
  intro h
  have h' : (t + 1) ^ 2 = 0 := by linear_combination h + (t + 1) * (CharP.cast_eq_zero K 2)
  have h'' : t + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h'
  exact ht1 (by linear_combination h'' - CharP.cast_eq_zero K 2)

theorem statedScalars_subgroupOf_eq_bot (n : ℕ) [NeZero n] :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot

end CharTwo

theorem exists_mulEquiv_statedSp_of_lieModel {J : Type} [Group J] {f : ℕ}
    (hJ : CFSG.Blueprint.LieModel J .PSp 2 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (J ≃* StatedSp 2 K) := by
  rcases hJ with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    have := finite_field_prime_power_characteristic (K := K) Nat.prime_two hf hK
    exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_eq_bot 2)).trans QuotientGroup.quotientBot)⟩⟩
  all_goals exact absurd h0 (by decide)

end CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
