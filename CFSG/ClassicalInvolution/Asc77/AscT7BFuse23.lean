module

public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE23
public import CFSG.ClassicalInvolution.Asc77.AscT7ATwin
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenBurnside
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement MatrixGroups

namespace T7B

section SL2

open Matrix

variable {F : Type*} [Field F]

theorem sl2_sq_entries (x : Matrix.SpecialLinearGroup (Fin 2) F) (hx : x * x = -1) :
    x.1 0 0 * x.1 0 0 + x.1 0 1 * x.1 1 0 = -1 ∧ x.1 0 0 * x.1 0 1 + x.1 0 1 * x.1 1 1 = 0 ∧
    x.1 1 0 * x.1 0 0 + x.1 1 1 * x.1 1 0 = 0 ∧ x.1 1 0 * x.1 0 1 + x.1 1 1 * x.1 1 1 = -1 := by
  have h := fun i j => congrArg
    (fun y : Matrix.SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F) i j) hx
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem sl2_trace_eq_zero (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x * x = -1) : x.1 1 1 = -x.1 0 0 := by
  obtain ⟨e00, e01, e10, e11⟩ := sl2_sq_entries x hx
  have hdet := x.2
  rw [Matrix.det_fin_two] at hdet
  by_contra hne
  have hs : x.1 0 0 + x.1 1 1 ≠ 0 := fun h => hne (by linear_combination h)
  have hb : x.1 0 1 = 0 := by
    have : x.1 0 1 * (x.1 0 0 + x.1 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right hs
  have hc : x.1 1 0 = 0 := by
    have : x.1 1 0 * (x.1 0 0 + x.1 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right hs
  rw [hb, hc] at e00 e11 hdet
  have had : x.1 0 0 = x.1 1 1 := by
    have : (x.1 0 0 - x.1 1 1) * (x.1 0 0 + x.1 1 1) = 0 := by linear_combination e00 - e11
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hs)
  apply h2
  rw [← had] at hdet
  linear_combination e00 - hdet

theorem sl2_exists_vec_det_ne_zero (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x * x = -1) :
    ∃ v : Fin 2 → F, v 0 * (x.1 *ᵥ v) 1 - (x.1 *ᵥ v) 0 * v 1 ≠ 0 := by
  obtain ⟨e00, e01, e10, e11⟩ := sl2_sq_entries x hx
  have htr := sl2_trace_eq_zero h2 x hx
  by_cases hc : x.1 1 0 = 0
  · by_cases hb : x.1 0 1 = 0
    · refine ⟨![1, 1], ?_⟩
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hb, hc, htr]
      intro h
      have ha : x.1 0 0 = 0 := by
        have : (2 : F) * x.1 0 0 = 0 := by linear_combination -h
        exact (mul_eq_zero.1 this).resolve_left h2
      rw [ha, hb, hc] at e00
      simp at e00
    · refine ⟨![0, 1], ?_⟩
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hb]
  · refine ⟨![1, 0], ?_⟩
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc]

theorem sl2_exists_matrix_conj_J (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x * x = -1) :
    ∃ M : Matrix (Fin 2) (Fin 2) F, M.det ≠ 0 ∧ x.1 * M = M * !![0, -1; 1, 0] := by
  obtain ⟨v, hv⟩ := sl2_exists_vec_det_ne_zero h2 x hx
  obtain ⟨e00, e01, e10, e11⟩ := sl2_sq_entries x hx
  refine ⟨!![v 0, (x.1 *ᵥ v) 0; v 1, (x.1 *ᵥ v) 1], ?_, ?_⟩
  · simpa [Matrix.det_fin_two_of] using hv
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
    · linear_combination v 0 * e00 + v 1 * e01
    · linear_combination v 0 * e10 + v 1 * e11

theorem exists_sq_add_sq_eq [Finite F] (h2 : (2 : F) ≠ 0) (d : F) :
    ∃ a b : F, a ^ 2 + b ^ 2 = d := by
  have := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := fun h => h2 (by
    have h' := CharP.cast_eq_zero F (ringChar F)
    rw [h] at h'
    simpa using h')
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 - Polynomial.C d) (g := Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by norm_num) d) (Polynomial.degree_X_pow 2) hodd
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

theorem sl2_exists_conj_of_sq_eq_neg_one [Finite F] (h2 : (2 : F) ≠ 0)
    {x y : Matrix.SpecialLinearGroup (Fin 2) F} (hx : x * x = -1) (hy : y * y = -1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g * x * g⁻¹ = y := by
  obtain ⟨M, hM, hxM⟩ := sl2_exists_matrix_conj_J h2 x hx
  obtain ⟨N, hN, hyN⟩ := sl2_exists_matrix_conj_J h2 y hy
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq h2 (N.det / M.det)
  set T : Matrix (Fin 2) (Fin 2) F := !![a, -b; b, a] with hTdef
  have hT : T * !![0, -1; 1, 0] = !![0, -1; 1, 0] * T := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two]
  have hTdet : T.det = N.det / M.det := by
    simp [T, Matrix.det_fin_two_of]
    linear_combination hab
  set M' : Matrix (Fin 2) (Fin 2) F := M * T with hM'def
  have hM'det : M'.det = N.det := by
    rw [hM'def, Matrix.det_mul, hTdet]
    field_simp
  have hxM' : x.1 * M' = M' * !![0, -1; 1, 0] := by
    calc x.1 * (M * T) = (x.1 * M) * T := by rw [Matrix.mul_assoc]
      _ = (M * !![0, -1; 1, 0]) * T := by rw [hxM]
      _ = M * (!![0, -1; 1, 0] * T) := by rw [Matrix.mul_assoc]
      _ = M * (T * !![0, -1; 1, 0]) := by rw [hT]
      _ = (M * T) * !![0, -1; 1, 0] := by rw [Matrix.mul_assoc]
  have hunit : IsUnit M'.det := by
    rw [hM'det]
    exact isUnit_iff_ne_zero.2 hN
  have hinv1 : M'⁻¹ * M' = 1 := Matrix.nonsing_inv_mul M' hunit
  have hinv2 : M' * M'⁻¹ = 1 := Matrix.mul_nonsing_inv M' hunit
  have hxinv : M'⁻¹ * x.1 = !![0, -1; 1, 0] * M'⁻¹ := by
    calc M'⁻¹ * x.1 = M'⁻¹ * x.1 * (M' * M'⁻¹) := by rw [hinv2, Matrix.mul_one]
      _ = M'⁻¹ * (x.1 * M') * M'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M'⁻¹ * (M' * !![0, -1; 1, 0]) * M'⁻¹ := by rw [hxM']
      _ = (M'⁻¹ * M') * !![0, -1; 1, 0] * M'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = !![0, -1; 1, 0] * M'⁻¹ := by rw [hinv1, Matrix.one_mul]
  have hgdet : (N * M'⁻¹).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hM'det]
    exact mul_inv_cancel₀ hN
  set g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨N * M'⁻¹, hgdet⟩ with hg
  refine ⟨g, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show N * M'⁻¹ * x.1 = y.1 * (N * M'⁻¹)
  calc N * M'⁻¹ * x.1 = N * (M'⁻¹ * x.1) := by rw [Matrix.mul_assoc]
    _ = N * (!![0, -1; 1, 0] * M'⁻¹) := by rw [hxinv]
    _ = (N * !![0, -1; 1, 0]) * M'⁻¹ := by rw [Matrix.mul_assoc]
    _ = (y.1 * N) * M'⁻¹ := by rw [hyN]
    _ = y.1 * (N * M'⁻¹) := by rw [Matrix.mul_assoc]

end SL2

section Lift

variable {G : Type} [Group G]

theorem exists_pow_conj_of_sq_eq {a x : G} (hsq : a * a = x * x)
    (hodd : Odd (orderOf (a⁻¹ * x))) : ∃ j : ℕ, (a⁻¹ * x) ^ j * a * ((a⁻¹ * x) ^ j)⁻¹ = x := by
  set n := a⁻¹ * x with hn
  have hxn : x = a * n := by rw [hn]; group
  have hnan : n * a * n = a := by
    have : a * (n * a * n) = a * a := by
      calc a * (n * a * n) = (a * n) * (a * n) := by group
        _ = x * x := by rw [← hxn]
        _ = a * a := hsq.symm
    exact mul_left_cancel this
  have hinv : a⁻¹ * n * a = n⁻¹ := by
    have h : a⁻¹ * n * a * n = 1 := by
      calc a⁻¹ * n * a * n = a⁻¹ * (n * a * n) := by group
        _ = a⁻¹ * a := by rw [hnan]
        _ = 1 := by group
    exact mul_eq_one_iff_eq_inv.mp h
  obtain ⟨s, hs⟩ := hodd
  have hpow : n ^ (2 * s) = n⁻¹ := by
    have h1 : n ^ (2 * s + 1) = 1 := by rw [← hs]; exact pow_orderOf_eq_one n
    rw [pow_succ] at h1
    exact mul_eq_one_iff_eq_inv.mp h1
  refine ⟨s, ?_⟩
  have hconj : a⁻¹ * n ^ s * a = (n⁻¹) ^ s := by
    have := conj_pow (a := a⁻¹) (b := n) (i := s)
    rw [inv_inv, hinv] at this
    exact this.symm
  calc n ^ s * a * (n ^ s)⁻¹ = a * (a⁻¹ * n ^ s * a) * (n ^ s)⁻¹ := by group
    _ = a * (n⁻¹) ^ s * (n ^ s)⁻¹ := by rw [hconj]
    _ = a * (n ^ (2 * s))⁻¹ := by
      rw [inv_pow, two_mul, pow_add, mul_inv_rev, mul_assoc]
    _ = a * n := by rw [hpow, inv_inv]
    _ = x := hxn.symm

end Lift

section Member

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_conj_of_sq_eq (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {z : G} (hz : IsUniqueInvolution L z) {a x : G} (ha : a ∈ L) (hx : x ∈ L)
    (ha2 : a * a = z) (hx2 : x * x = z) : ∃ k ∈ L, k * a * k⁻¹ = x := by
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (GaloisField p f) p 2).1 (by exact_mod_cast h0)
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)
  obtain ⟨φ, hφs, hφk⟩ := hΩ.exists_chart hL
  set zL : ↥L := ⟨z, hz.mem⟩ with hzL
  have hzL2 : zL * zL = 1 := Subtype.ext hz.sq
  have hφz : φ zL = -1 := by
    rcases sl2_sq_eq_one h2 (by rw [← map_mul, hzL2, map_one] : φ zL * φ zL = 1) with h | h
    · exfalso
      have hmem : zL ∈ classicalInvolutionOddCore ↥L := (hφk zL).mp h
      have hdvd : orderOf zL ∣ Nat.card ↥(classicalInvolutionOddCore ↥L) :=
        Subgroup.orderOf_dvd_natCard _ hmem
      have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥L)) :=
        CFSG.ComponentClassification.OddCore.odd_card ↥L
      have hord : orderOf zL = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzL2) (by
        intro h1
        exact hz.ne_one (congrArg Subtype.val h1))
      rw [hord] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
    · exact h
  set aL : ↥L := ⟨a, ha⟩ with haL
  set xL : ↥L := ⟨x, hx⟩ with hxL
  have haφ : φ aL * φ aL = -1 := by
    rw [← map_mul, show aL * aL = zL from Subtype.ext ha2, hφz]
  have hxφ : φ xL * φ xL = -1 := by
    rw [← map_mul, show xL * xL = zL from Subtype.ext hx2, hφz]
  obtain ⟨g, hg⟩ := sl2_exists_conj_of_sq_eq_neg_one h2 haφ hxφ
  obtain ⟨k₀, rfl⟩ := hφs g
  set a'L : ↥L := k₀ * aL * k₀⁻¹ with ha'L
  set a' : G := (a'L : G) with ha'
  have ha'e : a' = (k₀ : G) * a * (k₀ : G)⁻¹ := rfl
  have ha'2 : a' * a' = z := by
    have e : a' * a' = (k₀ : G) * (a * a) * (k₀ : G)⁻¹ := by rw [ha'e]; group
    rw [e, ha2]
    have := hz.commute_of_mem k₀.2
    calc (k₀ : G) * z * (k₀ : G)⁻¹ = (z * (k₀ : G)) * (k₀ : G)⁻¹ := by rw [this]
      _ = z := by group
  have hn : a'L⁻¹ * xL ∈ classicalInvolutionOddCore ↥L := by
    rw [← hφk, map_mul, map_inv]
    have : φ a'L = φ xL := by
      rw [ha'L, map_mul, map_mul, map_inv]
      exact hg
    rw [this, inv_mul_cancel]
  have hnG : a'⁻¹ * x ∈ oddCoreOf L := mem_oddCoreOf_iff.mpr ⟨L.mul_mem (L.inv_mem a'L.2) hx, hn⟩
  have hodd : Odd (orderOf (a'⁻¹ * x)) := by
    have hdvd : orderOf (a'⁻¹ * x) ∣ Nat.card ↥(oddCoreOf L) := Subgroup.orderOf_dvd_natCard _ hnG
    exact (oddCoreOf_odd_natCard L).of_dvd_nat hdvd
  obtain ⟨j, hj⟩ := exists_pow_conj_of_sq_eq (a := a') (x := x) (by rw [ha'2, hx2]) hodd
  have hnL : a'⁻¹ * x ∈ L := oddCoreOf_le_self L hnG
  refine ⟨(a'⁻¹ * x) ^ j * (k₀ : G), L.mul_mem (L.pow_mem hnL j) k₀.2, ?_⟩
  calc (a'⁻¹ * x) ^ j * (k₀ : G) * a * ((a'⁻¹ * x) ^ j * (k₀ : G))⁻¹
      = (a'⁻¹ * x) ^ j * ((k₀ : G) * a * (k₀ : G)⁻¹) * ((a'⁻¹ * x) ^ j)⁻¹ := by group
    _ = x := by rw [← ha'e]; exact hj

omit [Finite G] in
theorem conj_mem_oddCoreOf_of_mem_normalizer {H : Subgroup G} {g n : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (hn : n ∈ oddCoreOf H) :
    g * n * g⁻¹ ∈ oddCoreOf H := by
  have h1 : conjSub g H = H := mem_normalizer_iff_conjSub_eq.mp hg
  have h2 := Thompson.oddCoreOf_conjSub_eq g H
  rw [h1] at h2
  rw [h2]
  exact conj_mem_conjSub hn

theorem exists_centralizing_conj (hΩ : HypOmegaMod p f Ω) {L L' : Subgroup G} (hL : L ∈ Ω)
    (hL' : L' ∈ Ω) (hne : L' ≠ L) {z : G} (hzL : IsUniqueInvolution L z)
    (hzL' : IsUniqueInvolution L' z) {x b y ℓ : G} (hx : x ∈ L)
    (hx2 : IsPGroup 2 ↥(Subgroup.zpowers x)) (hℓ : ℓ ∈ L') (hxb : x * b = b * x)
    (hxy : x * y = y * x) (hℓb : ℓ * b * ℓ⁻¹ = y) :
    ∃ ℓ' ∈ L', ℓ' * b * ℓ'⁻¹ = y ∧ ℓ' * x = x * ℓ' := by
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    hΩ.le_normalizer_of_twin hL hL' hne.symm hzL hzL'
  have hcomm := hΩ.comm_le_oddCore_of_twin hL hL' hne.symm hzL hzL'
  set S : Subgroup G := oddCoreOf L' ⊓ Subgroup.centralizer ({b} : Set G) with hS
  set C : Set G := (fun n => ℓ * n) '' (S : Set G) with hC
  have hSodd : Odd (Nat.card ↥S) :=
    (oddCoreOf_odd_natCard L').of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hCodd : Odd (Nat.card ↥C) := by
    have : Nat.card ↥C = Nat.card ↥(S : Set G) :=
      Nat.card_image_of_injective (mul_right_injective ℓ) (S : Set G)
    rw [this]
    exact hSodd
  have hCmem : ∀ c ∈ C, c ∈ L' ∧ c * b * c⁻¹ = y ∧ ℓ⁻¹ * c ∈ oddCoreOf L' := by
    rintro _ ⟨n, hn, rfl⟩
    have hnO : n ∈ oddCoreOf L' := hn.1
    have hnb : n * b = b * n := Subgroup.mem_centralizer_singleton_iff.mp hn.2
    refine ⟨L'.mul_mem hℓ (oddCoreOf_le_self L' hnO), ?_, ?_⟩
    · calc ℓ * n * b * (ℓ * n)⁻¹ = ℓ * (n * b * n⁻¹) * ℓ⁻¹ := by group
        _ = y := by rw [hnb]; simpa using hℓb
    · simpa using hnO
  have hinv : ∀ v ∈ Subgroup.zpowers x, ∀ c ∈ C, v * c * v⁻¹ ∈ C := by
    intro v hv c hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hvL : x ^ j ∈ L := L.zpow_mem hx j
    have hvb : x ^ j * b = b * x ^ j := (Commute.zpow_left (show Commute x b from hxb) j).eq
    have hvy : x ^ j * y = y * x ^ j := (Commute.zpow_left (show Commute x y from hxy) j).eq
    obtain ⟨hcL', hcb, hcO⟩ := hCmem c hc
    set c' := x ^ j * c * (x ^ j)⁻¹ with hc'
    have hc'b : c' * b * c'⁻¹ = y := by
      calc c' * b * c'⁻¹ = x ^ j * (c * ((x ^ j)⁻¹ * b * x ^ j) * c⁻¹) * (x ^ j)⁻¹ := by
            rw [hc']; group
        _ = x ^ j * (c * b * c⁻¹) * (x ^ j)⁻¹ := by
            rw [show (x ^ j)⁻¹ * b * x ^ j = b by rw [mul_assoc, ← hvb]; group]
        _ = y := by rw [hcb, hvy]; group
    have hc'L' : ℓ⁻¹ * c' ∈ oddCoreOf L' := by
      have hvN : x ^ j ∈ Subgroup.normalizer (L' : Set G) := hLN hvL
      have hℓN : ℓ ∈ Subgroup.normalizer (L' : Set G) := Subgroup.le_normalizer hℓ
      have hcomm' : ⁅x ^ j, ℓ⁆ ∈ oddCoreOf L' :=
        (hcomm (Subgroup.commutator_mem_commutator hvL hℓ)).2
      have h1 : ℓ⁻¹ * ⁅x ^ j, ℓ⁆ * ℓ ∈ oddCoreOf L' := by
        have := conj_mem_oddCoreOf_of_mem_normalizer (Subgroup.inv_mem _ hℓN) hcomm'
        simpa using this
      have h2 : x ^ j * (ℓ⁻¹ * c) * (x ^ j)⁻¹ ∈ oddCoreOf L' :=
        conj_mem_oddCoreOf_of_mem_normalizer hvN hcO
      have e : ℓ⁻¹ * c' = (ℓ⁻¹ * ⁅x ^ j, ℓ⁆ * ℓ) * (x ^ j * (ℓ⁻¹ * c) * (x ^ j)⁻¹) := by
        rw [hc']
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (oddCoreOf L').mul_mem h1 h2
    refine ⟨ℓ⁻¹ * c', ⟨hc'L', ?_⟩, by simp⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have : (ℓ⁻¹ * c') * b * (ℓ⁻¹ * c')⁻¹ = b := by
      calc (ℓ⁻¹ * c') * b * (ℓ⁻¹ * c')⁻¹ = ℓ⁻¹ * (c' * b * c'⁻¹) * ℓ := by group
        _ = ℓ⁻¹ * y * ℓ := by rw [hc'b]
        _ = b := by rw [← hℓb]; group
    exact mul_inv_eq_iff_eq_mul.mp this
  obtain ⟨c, hcC, hfix⟩ := Thompson.exists_fixed_mem_of_odd hx2 hinv hCodd
  obtain ⟨hcL', hcb, -⟩ := hCmem c hcC
  refine ⟨c, hcL', hcb, ?_⟩
  exact (mul_inv_eq_iff_eq_mul.mp (hfix x (Subgroup.mem_zpowers x))).symm

omit [Finite G] in
theorem mul_self_eq_of_orderOf_four {L : Subgroup G} {z x : G} (hz : IsUniqueInvolution L z)
    (hx : x ∈ L) (h4 : orderOf x = 4) : x * x = z := by
  have h1 : (x * x) * (x * x) = 1 := by
    have : x ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one x
    calc (x * x) * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  rcases hz.unique (x * x) (L.mul_mem hx hx) h1 with h | h
  · exfalso
    have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h4] at this
    omega
  · exact h

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf_four {x : G} (h4 : orderOf x = 4) :
    IsPGroup 2 ↥(Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, h4]; norm_num)

end Member

end T7B

variable {p f : ℕ} [Fact p.Prime]

theorem c23_2_fuse : C23_2_fuse p f := by
  intro G _ _ _ Ω K K' z hs _ _ _ u hu _ hu1 huz hu2 L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy
    ox oy
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hp : p ≠ 2 := hs.stand.odd
  have hLΩ : L ∈ Ω := hL.1
  have hL'Ω : L' ∈ Ω := hL'.1
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hs.hz hL
  have hzL' : IsUniqueInvolution L' z := isUniqueInvolution_of_mem_twinSet hs.hz hL'
  have hM : K ⊔ K' = L ⊔ L' := by
    have hLm : L ∈ ({K, K'} : Set (Subgroup G)) := hs.twinSet_eq ▸ hL
    have hL'm : L' ∈ ({K, K'} : Set (Subgroup G)) := hs.twinSet_eq ▸ hL'
    rcases hLm with rfl | rfl <;> rcases hL'm with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact sup_comm _ _
    · exact absurd rfl hne
  have huM : u ∈ L ⊔ L' := hM ▸ hu
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    hΩ.le_normalizer_of_twin hLΩ hL'Ω hne.symm hzL hzL'
  have hLC : L ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hw).symm
  have hL'C : L' ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL'.commute_of_mem hw).symm
  have hMC : L ⊔ L' ≤ Subgroup.centralizer ({z} : Set G) := sup_le hLC hL'C
  have hQ : IsSylow2In (R₁ ⊔ R₂) (L ⊔ L') :=
    T7A.isSylow2In_sup_of_twin hp hΩ hLΩ hL'Ω hne hzL hzL' hR₁ hR₂ hc
  have hu2' : IsPGroup 2 ↥(Subgroup.zpowers u) := isPGroup_zpowers_of_mul_self_eq_one hu2 hu1
  obtain ⟨V, hV, huV⟩ := IsSylow2In.exists_ge hu2' (Subgroup.zpowers_le.mpr huM)
  obtain ⟨m, hmM, hmV⟩ := exists_conjSub_eq_of_isSylow2In hV hQ
  have hu'mem : m * u * m⁻¹ ∈ R₁ ⊔ R₂ := by
    rw [← hmV]
    exact conj_mem_conjSub (huV (Subgroup.mem_zpowers u))
  obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc hu'mem
  have hmz : m * z * m⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMC hmM)
    calc m * z * m⁻¹ = (z * m) * m⁻¹ := by rw [this]
      _ = z := by group
  have hu'2 : (a * b) * (a * b) = 1 := by
    rw [hab]
    calc m * u * m⁻¹ * (m * u * m⁻¹) = m * (u * u) * m⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hcab : a * b = b * a := hc a ha b hb
  have hsq : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := hu'2
  have haL : a ∈ L := hR₁.1 ha
  have hbL' : b ∈ L' := hR₂.1 hb
  have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
    hΩ.card_le_two_of_le_inf hLΩ hL'Ω hne.symm (hR₁.2.1.to_le inf_le_left)
      (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
  have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
    intro e he
    have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
    have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
    have h2 : orderOf e ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have haaA : a * a ∈ R₁ ⊓ R₂ := by
    refine ⟨R₁.mul_mem ha ha, ?_⟩
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R₂.inv_mem (R₂.mul_mem hb hb)
  have haa2 : (a * a) * (a * a) = 1 := hA _ haaA
  have haa : a * a = z := by
    rcases hzL.unique (a * a) (L.mul_mem haL haL) haa2 with h | h
    · exfalso
      have hbb : b * b = 1 := by rwa [h, one_mul] at hsq
      have ha1 : a = 1 ∨ a = z := hzL.unique a haL h
      have hb1 : b = 1 ∨ b = z := hzL'.unique b hbL' hbb
      have hu'z : m * u * m⁻¹ = 1 ∨ m * u * m⁻¹ = z := by
        rw [← hab]
        rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2
        · left; rw [h1, h2, one_mul]
        · right; rw [h1, h2, one_mul]
        · right; rw [h1, h2, mul_one]
        · left; rw [h1, h2]; exact hzL.sq
      have hu : u = m⁻¹ * (m * u * m⁻¹) * m := by group
      rcases hu'z with h' | h'
      · exact hu1 (by rw [hu, h']; group)
      · exact huz (by
          rw [hu, h']
          calc m⁻¹ * z * m = m⁻¹ * (m * z * m⁻¹) * m := by rw [hmz]
            _ = z := by group)
    · exact h
  have hbb : b * b = z := by
    have h1 : b * b = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [haa] at hsq)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hzL.sq
  have hx2 : x * x = z := T7B.mul_self_eq_of_orderOf_four hzL (hR₁.1 hx) ox
  have hy2 : y * y = z := T7B.mul_self_eq_of_orderOf_four hzL' (hR₂.1 hy) oy
  obtain ⟨k, hkL, hk⟩ := T7B.exists_conj_of_sq_eq hp hΩ hLΩ hzL haL (hR₁.1 hx) haa hx2
  set b₁ := k * b * k⁻¹ with hb₁
  have hb₁L' : b₁ ∈ L' := (Subgroup.mem_normalizer_iff.mp (hLN hkL) b).mp hbL'
  have hb₁2 : b₁ * b₁ = z := by
    have e : b₁ * b₁ = k * (b * b) * k⁻¹ := by rw [hb₁]; group
    rw [e, hbb]
    have := hzL.commute_of_mem hkL
    calc k * z * k⁻¹ = (z * k) * k⁻¹ := by rw [this]
      _ = z := by group
  have hxb₁ : x * b₁ = b₁ * x := by
    rw [← hk, hb₁]
    calc k * a * k⁻¹ * (k * b * k⁻¹) = k * (a * b) * k⁻¹ := by group
      _ = k * (b * a) * k⁻¹ := by rw [hcab]
      _ = k * b * k⁻¹ * (k * a * k⁻¹) := by group
  have hxy : x * y = y * x := hc x hx y hy
  obtain ⟨ℓ, hℓL', hℓ⟩ := T7B.exists_conj_of_sq_eq hp hΩ hL'Ω hzL' hb₁L' (hR₂.1 hy) hb₁2 hy2
  obtain ⟨ℓ', hℓ'L', hℓ'b, hℓ'x⟩ := T7B.exists_centralizing_conj hΩ hLΩ hL'Ω hne hzL hzL'
    (hR₁.1 hx) (T7B.isPGroup_zpowers_of_orderOf_four ox) hℓL' hxb₁ hxy hℓ
  refine ⟨ℓ' * k * m, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hL'C hℓ'L') (hLC hkL))
    (hMC hmM), ?_⟩
  have hℓ'x' : ℓ' * x * ℓ'⁻¹ = x := by
    rw [hℓ'x]
    group
  calc ℓ' * k * m * u * (ℓ' * k * m)⁻¹ = ℓ' * k * (m * u * m⁻¹) * k⁻¹ * ℓ'⁻¹ := by group
    _ = ℓ' * k * (a * b) * k⁻¹ * ℓ'⁻¹ := by rw [hab]
    _ = ℓ' * ((k * a * k⁻¹) * (k * b * k⁻¹)) * ℓ'⁻¹ := by group
    _ = ℓ' * (x * b₁) * ℓ'⁻¹ := by rw [hk]
    _ = (ℓ' * x * ℓ'⁻¹) * (ℓ' * b₁ * ℓ'⁻¹) := by group
    _ = x * y := by rw [hℓ'x', hℓ'b]

end CFSG.ClassicalInvolution.Asc77
