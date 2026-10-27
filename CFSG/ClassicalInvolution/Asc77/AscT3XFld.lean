module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIExact
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfg
public import CFSG.ClassicalInvolution.Asc77.AscT3RAct
public import CFSG.ClassicalInvolution.Asc77.AscT3WStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T3CII.T3R CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Pure

variable {F : Type} [Field F]

theorem x_trace_inv_sl2 (A : SL(2, F)) :
    ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      (A : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.trace_fin_two]
  simp [add_comm]

theorem x_mul_self_eq_neg_one_of_trace_eq_zero (A : SL(2, F))
    (h : (A : Matrix (Fin 2) (Fin 2) F).trace = 0) : A * A = -1 := by
  have hdet := A.det_coe
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at h
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination (↑A : Matrix (Fin 2) (Fin 2) F) 0 0 * h
    | linear_combination (↑A : Matrix (Fin 2) (Fin 2) F) 0 1 * h
    | linear_combination (↑A : Matrix (Fin 2) (Fin 2) F) 1 0 * h
    | linear_combination (↑A : Matrix (Fin 2) (Fin 2) F) 1 1 * h
    | linear_combination (↑A : Matrix (Fin 2) (Fin 2) F) 0 0 * h - hdet
    | linear_combination (↑A : Matrix (Fin 2) (Fin 2) F) 1 1 * h - hdet

theorem x_trace_semilinHom_one (G : GL (Fin 2) F) (A : SL(2, F)) :
    ((semilinHom G (1 : F ≃+* F) A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      (A : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [coe_semilinHom]
  have hmap : (A : Matrix (Fin 2) (Fin 2) F).map (1 : F ≃+* F) = (A : Matrix (Fin 2) (Fin 2) F) :=
    rfl
  rw [hmap, Matrix.trace_mul_comm]
  have hGG : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← Matrix.mul_assoc, hGG, Matrix.one_mul]

theorem x_not_conj_modular (h2 : (2 : F) ≠ 0) (G : GL (Fin 2) F) {A : SL(2, F)} {k : ℕ}
    (hk : 2 ≤ k) (hAo : orderOf A = 2 ^ (k + 1)) {r : ℤ}
    (hr : r = 2 ^ k + 1 ∨ r = 2 ^ k - 1) (h : semilinHom G (1 : F ≃+* F) A = A ^ r) :
    False := by
  have hA2k : A ^ (2 ^ k) * A ^ (2 ^ k) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    exact pow_eq_one_iff_modEq.mpr (by simp [hAo])
  have hA2k1 : A ^ (2 ^ k) ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hAo] at this
    have := Nat.le_of_dvd (by positivity) this
    have : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hneg : A ^ (2 ^ k) = -1 := by
    rcases sl2_sq_eq_one h2 hA2k with h' | h'
    · exact absurd h' hA2k1
    · exact h'
  have htr : (A : Matrix (Fin 2) (Fin 2) F).trace = -(A : Matrix (Fin 2) (Fin 2) F).trace := by
    have h1 := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F).trace) h
    simp only [x_trace_semilinHom_one] at h1
    refine h1.trans ?_
    rcases hr with rfl | rfl
    · rw [zpow_add_one, show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, hneg]
      have : ((-1 * A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
          -(A : Matrix (Fin 2) (Fin 2) F) := by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        simp
      rw [this, Matrix.trace_neg]
    · rw [zpow_sub_one, show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, hneg]
      have : ((-1 * A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
          -((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        simp
      rw [this, Matrix.trace_neg, x_trace_inv_sl2]
  have h0 : (A : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
    have : (2 : F) * (A : Matrix (Fin 2) (Fin 2) F).trace = 0 := by linear_combination htr
    exact (mul_eq_zero.mp this).resolve_left h2
  have hsq := x_mul_self_eq_neg_one_of_trace_eq_zero A h0
  have h4 : A ^ 4 = 1 := by
    have : A ^ 4 = (A * A) * (A * A) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this, hsq]
    simp
  have := orderOf_dvd_of_pow_eq_one h4
  rw [hAo] at this
  have := Nat.le_of_dvd (by norm_num) this
  have : 2 ^ 3 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Pure

section Gen

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F]

theorem x_orderOf_eta_of_two_pow (L : Subgroup G)
    (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)) {x : G} (hx : x ∈ L) {n : ℕ}
    (hxo : orderOf x = 2 ^ n) : orderOf (eta L e ⟨x, hx⟩) = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y := eta L e ⟨x, hx⟩ with hy
  have h1 : y ^ (2 ^ n) = 1 := by
    rw [hy, ← map_pow]
    have : (⟨x, hx⟩ : ↥L) ^ (2 ^ n) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← hxo]; exact pow_orderOf_eq_one x)
    rw [this, map_one]
  obtain ⟨j, hj, hyj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  rw [hyj]
  have h2 : y ^ (2 ^ j) = 1 := by rw [← hyj]; exact pow_orderOf_eq_one y
  have h3 : (⟨x, hx⟩ : ↥L) ^ (2 ^ j) ∈ classicalInvolutionOddCore ↥L := by
    rw [← eta_eq_one_iff L e, map_pow]
    exact h2
  have h4 : x ^ (2 ^ j) ∈ oddCoreOf L := ⟨_, h3, rfl⟩
  have h5 : IsPGroup 2 (Subgroup.zpowers (x ^ (2 ^ j))) := by
    have h6 : orderOf (x ^ (2 ^ j)) ∣ 2 ^ n := hxo ▸ orderOf_pow_dvd _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h6
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have h7 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) h4 h5
  have h8 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h7
  rw [hxo] at h8
  have h9 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h8
  have h10 : j ≤ n := by
    have := Nat.le_of_dvd (by positivity) (hyj ▸ orderOf_dvd_of_pow_eq_one h1)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  congr 1
  omega

end Gen

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.x_fieldData (d : Std20 p f K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) :
    b ∈ Subgroup.normalizer (K : Set G) ∧ b ∈ Subgroup.normalizer (K' : Set G) ∧
      ∃ (e₀ : ℕ) (eK : ↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField p f))
        (g : GL (Fin 2) (GaloisField p f)) (σ : GaloisField p f ≃+* GaloisField p f),
        f = 2 * e₀ ∧ σ * σ = 1 ∧ σ ≠ 1 ∧ (∀ a, σ a = a ^ p ^ e₀) ∧
          ∀ x, phiG K eK b x = semilinHom g σ x := by
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hFodd
  have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
    (c9 h8).2.2 b hb.mem (by rw [hb.sq]; exact Subgroup.one_mem _)
  have hbN' : b ∈ Subgroup.normalizer (K' : Set G) := by
    have h1 := (d.late_conj_iff (d.hSz hb.mem)).mp (mem_normalizer_iff_conjSub_eq.mp hbN)
    exact mem_normalizer_iff_conjSub_eq.mpr h1
  obtain ⟨eK⟩ := d.hyp.nonempty_equiv_sl2 d.late_mem_K
  have hφ2 : phiG K eK b * phiG K eK b = 1 := by
    rw [← phiG_mul hbN hbN, hb.sq, phiG_one]
  obtain ⟨g, σ, hg, hσ2⟩ := mulAut_involution_structure hp hq (phiG K eK b) hφ2
  have hσ1 : σ ≠ 1 := by
    intro hσ
    subst hσ
    obtain ⟨u, k, hk2, hu, huo, hact⟩ := hb.modular
    have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
    have huK : u ∈ K := huKW.1
    have hA := x_orderOf_eta_of_two_pow K eK huK huo
    obtain ⟨r, hr, hrb⟩ : ∃ r : ℤ, (r = 2 ^ k + 1 ∨ r = 2 ^ k - 1) ∧ b * u * b⁻¹ = u ^ r := by
      rcases hact with h | h
      · exact ⟨_, Or.inl rfl, h u huKW⟩
      · exact ⟨_, Or.inr rfl, h u huKW⟩
    refine x_not_conj_modular h2 g hk2 hA hr ?_
    have h1 := phiG_apply_eta hbN (L := K) (e := eK) ⟨u, huK⟩
    rw [hg] at h1
    rw [h1]
    have : (⟨b * u * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbN u).mp huK⟩ : ↥K) =
        (⟨u, huK⟩ : ↥K) ^ r := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hrb)
    rw [this, map_zpow]
  obtain ⟨e₀, hfe, hfrob⟩ := eq_frobenius_of_sq_eq_one hf hσ2 hσ1
  exact ⟨hbN, hbN', e₀, eK, g, σ, hfe, hσ2, hσ1, hfrob, hg⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
