module

public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.GH74.GLS.IVK.Lifted.QuatAut

public section

open Matrix CFSG.Semidihedral.OddFieldSL2

namespace CFSG.GH74.GLS.LU.Local.SL2

variable {F : Type} [Field F]

theorem scalar_of_comm_anticomm (h2 : (2 : F) ≠ 0) (A B X : Matrix (Fin 2) (Fin 2) F)
    (hAd : A.det = 1) (hBd : B.det = 1) (hA : A * A = -1) (hB : B * B = -1)
    (hBA : B * A = -(A * B)) (hXA : X * A = A * X) (hXB : X * B = B * X) :
    X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 0 0 = X 1 1 := by
  have trace0 : ∀ M : Matrix (Fin 2) (Fin 2) F, M.det = 1 → M * M = -1 → M 1 1 = -M 0 0 := by
    intro M hd hM
    have e01 := congrFun (congrFun hM 0) 1
    have e10 := congrFun (congrFun hM 1) 0
    have e00 := congrFun (congrFun hM 0) 0
    have e11 := congrFun (congrFun hM 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10 e00 e11
    rw [Matrix.det_fin_two] at hd
    by_contra hne
    have hs : M 0 0 + M 1 1 ≠ 0 := fun h => hne (by linear_combination h)
    have hb : M 0 1 = 0 := by
      have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : M 1 0 = 0 := by
      have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hb, hc] at e00 e11
    simp at e00 e11
    rw [hb, hc] at hd
    simp at hd
    have : M 0 0 = M 1 1 := by
      have h3 : (M 0 0 - M 1 1) * (M 0 0 + M 1 1) = 0 := by linear_combination e00 - e11
      have := (mul_eq_zero.1 h3).resolve_right hs
      linear_combination this
    rw [← this] at hd
    have h4 : (M 0 0) ^ 2 = 1 := by linear_combination hd
    have h5 : (M 0 0) ^ 2 = -1 := by linear_combination e00
    apply h2
    linear_combination h5 - h4
  have hA11 := trace0 A hAd hA
  have hB11 := trace0 B hBd hB
  have eA := fun i j => congrFun (congrFun hA i) j
  have eB := fun i j => congrFun (congrFun hB i) j
  have eBA := fun i j => congrFun (congrFun hBA i) j
  have eXA := fun i j => congrFun (congrFun hXA i) j
  have eXB := fun i j => congrFun (congrFun hXB i) j
  have hA00 := eA 0 0
  have hB00 := eB 0 0
  have hBA00 := eBA 0 0
  have hXA00 := eXA 0 0
  have hXA01 := eXA 0 1
  have hXA10 := eXA 1 0
  have hXB00 := eXB 0 0
  have hXB01 := eXB 0 1
  have hXB10 := eXB 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq] at hA00 hB00 hBA00 hXA00 hXA01 hXA10 hXB00 hXB01 hXB10
  simp only [hA11, hB11] at hA00 hB00 hBA00 hXA00 hXA01 hXA10 hXB00 hXB01 hXB10
  generalize A 0 0 = p at *
  generalize A 0 1 = r at *
  generalize A 1 0 = s at *
  generalize B 0 0 = p' at *
  generalize B 0 1 = r' at *
  generalize B 1 0 = s' at *
  generalize X 0 0 = x at *
  generalize X 0 1 = y at *
  generalize X 1 0 = w at *
  generalize X 1 1 = v at *
  have hA' : p ^ 2 + r * s = -1 := by linear_combination hA00
  have hB' : p' ^ 2 + r' * s' = -1 := by linear_combination hB00
  have hW : 2 * p * p' + r * s' + r' * s = 0 := by linear_combination hBA00
  have hA1 : y * s = r * w := by linear_combination hXA00
  have hA2 : r * (x - v) = 2 * p * y := by linear_combination hXA01
  have hA3 : 2 * p * w = s * (x - v) := by linear_combination hXA10
  have hB1 : y * s' = r' * w := by linear_combination hXB00
  have hB2 : r' * (x - v) = 2 * p' * y := by linear_combination hXB01
  have hB3 : 2 * p' * w = s' * (x - v) := by linear_combination hXB10
  have key : (r * s' - r' * s) ^ 2 - 4 * (p * r' - p' * r) * (p * s' - p' * s) = -4 := by
    linear_combination (4 - 4 * (p' ^ 2 + r' * s' + 1)) * hA' + 4 * hB' + (2 * p * p' + r * s' + r' * s) * hW
  have L1 : (p * r' - p' * r) * (x - v) = 0 := by linear_combination p * hB2 - p' * hA2
  have L2 : (p * s' - p' * s) * (x - v) = 0 := by linear_combination p' * hA3 - p * hB3
  have L3 : (p * r' - p' * r) * y = 0 := by
    have : 2 * ((p * r' - p' * r) * y) = 0 := by linear_combination r * hB2 - r' * hA2
    exact (mul_eq_zero.mp this).resolve_left h2
  have L4 : (p * s' - p' * s) * w = 0 := by
    have : 2 * ((p * s' - p' * s) * w) = 0 := by linear_combination s' * hA3 - s * hB3
    exact (mul_eq_zero.mp this).resolve_left h2
  have L5 : (r * s' - r' * s) * w = 0 := by linear_combination s * hB1 - s' * hA1
  have L6 : (r * s' - r' * s) * y = 0 := by linear_combination r * hB1 - r' * hA1
  by_cases hD3 : r * s' - r' * s = 0
  · rw [hD3] at key
    have h4 : (4 : F) ≠ 0 := by
      intro h
      apply h2
      have : (2 : F) * 2 = 0 := by linear_combination h
      exact mul_self_eq_zero.mp this
    have hprod : (p * r' - p' * r) * (p * s' - p' * s) = 1 := by
      have h5 : 4 * ((p * r' - p' * r) * (p * s' - p' * s) - 1) = 0 := by linear_combination -key
      have := (mul_eq_zero.mp h5).resolve_left h4
      linear_combination this
    have hD1 : p * r' - p' * r ≠ 0 := fun h => by rw [h, zero_mul] at hprod; exact zero_ne_one hprod
    have hD2 : p * s' - p' * s ≠ 0 := fun h => by rw [h, mul_zero] at hprod; exact zero_ne_one hprod
    refine ⟨(mul_eq_zero.mp L3).resolve_left hD1, (mul_eq_zero.mp L4).resolve_left hD2, ?_⟩
    have := (mul_eq_zero.mp L1).resolve_left hD1
    linear_combination this
  · have hy : y = 0 := (mul_eq_zero.mp L6).resolve_left hD3
    have hw : w = 0 := (mul_eq_zero.mp L5).resolve_left hD3
    refine ⟨hy, hw, ?_⟩
    by_contra hne
    have hδ : x - v ≠ 0 := fun h => hne (by linear_combination h)
    rw [hy] at hA2 hB2
    rw [hw] at hA3 hB3
    have hr : r = 0 := (mul_eq_zero.mp (by linear_combination hA2 : r * (x - v) = 0)).resolve_right hδ
    have hs : s = 0 := (mul_eq_zero.mp (by linear_combination -hA3 : s * (x - v) = 0)).resolve_right hδ
    have hr' : r' = 0 := (mul_eq_zero.mp (by linear_combination hB2 : r' * (x - v) = 0)).resolve_right hδ
    have hs' : s' = 0 := (mul_eq_zero.mp (by linear_combination -hB3 : s' * (x - v) = 0)).resolve_right hδ
    apply hD3
    rw [hr, hs, hr', hs']; ring


section Fin
variable [Finite F]

theorem orderOf_a_n {n : ℕ} [NeZero n] : orderOf (QuaternionGroup.a (n : ZMod (2 * n)) : QuaternionGroup n) = 2 := by
  have h1 : (QuaternionGroup.xa (0 : ZMod (2 * n)) : QuaternionGroup n) ^ 2 = QuaternionGroup.a (n : ZMod (2 * n)) :=
    QuaternionGroup.xa_sq 0
  rw [← h1, orderOf_pow' _ (by norm_num), QuaternionGroup.orderOf_xa]
  norm_num

theorem exists_anticomm_pair (hodd : Odd (Nat.card F)) (P : Sylow 2 (SpecialLinearGroup (Fin 2) F)) :
    ∃ α β : SpecialLinearGroup (Fin 2) F, α ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) ∧
      β ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) ∧ α * α = minusIdentity F ∧
      β * β = minusIdentity F ∧ β * α = α * β * minusIdentity F := by
  have h2 := two_ne_zero_of_odd_card F hodd
  obtain ⟨m, hm, ⟨φ⟩⟩ := sylow_two_quaternion F hodd P
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hN : (2 : ℕ) ^ (k + 3 - 2) = 2 * 2 ^ k := by
    rw [show k + 3 - 2 = k + 1 by omega, pow_succ]; ring
  set N := 2 ^ (k + 3 - 2) with hNdef
  have : NeZero N := ⟨by positivity⟩
  let a₁ : QuaternionGroup N := QuaternionGroup.a ((2 ^ k : ℕ) : ZMod (2 * N))
  let b₁ : QuaternionGroup N := QuaternionGroup.xa 0
  have ha₁ : a₁ * a₁ = QuaternionGroup.a (N : ZMod (2 * N)) := by
    simp only [a₁, QuaternionGroup.a_mul_a]
    congr 1
    rw [← Nat.cast_add, hN]; push_cast; ring_nf
  have hb₁ : b₁ * b₁ = QuaternionGroup.a (N : ZMod (2 * N)) := by
    simp only [b₁]; rw [← sq]; exact QuaternionGroup.xa_sq 0
  have hba : b₁ * a₁ = a₁ * b₁ * QuaternionGroup.a (N : ZMod (2 * N)) := by
    simp only [a₁, b₁, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
    congr 1
    have : (N : ZMod (2 * N)) = ((2 ^ k : ℕ) : ZMod (2 * N)) + ((2 ^ k : ℕ) : ZMod (2 * N)) := by
      rw [← Nat.cast_add, hN]; push_cast; ring_nf
    rw [this]; ring
  have hz₀ : ((φ.symm (QuaternionGroup.a (N : ZMod (2 * N))) : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) :
      SpecialLinearGroup (Fin 2) F) = minusIdentity F := by
    apply (orderOf_eq_two_iff F h2 _).mp
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_a_n
  refine ⟨((φ.symm a₁ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) : SpecialLinearGroup (Fin 2) F),
    ((φ.symm b₁ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) : SpecialLinearGroup (Fin 2) F),
    (φ.symm a₁).2, (φ.symm b₁).2, ?_, ?_, ?_⟩
  · rw [← hz₀, ← ha₁, map_mul]; rfl
  · rw [← hz₀, ← hb₁, map_mul]; rfl
  · have h := congrArg (fun w : QuaternionGroup N =>
      ((φ.symm w : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) : SpecialLinearGroup (Fin 2) F)) hba
    simp only [map_mul, Subgroup.coe_mul] at h
    rw [← hz₀]; exact h


theorem cent_sylow_le_center (hodd : Odd (Nat.card F)) (P : Sylow 2 (SpecialLinearGroup (Fin 2) F))
    {x : SpecialLinearGroup (Fin 2) F}
    (hx : ∀ y ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)), x * y = y * x) :
    x ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  have h2 := two_ne_zero_of_odd_card F hodd
  obtain ⟨α, β, hα, hβ, hαα, hββ, hβα⟩ := exists_anticomm_pair hodd P
  have hneg : ((minusIdentity F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [minusIdentity_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  have hA : (α : Matrix (Fin 2) (Fin 2) F) * α = -1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hαα
    simpa [hneg] using this
  have hB : (β : Matrix (Fin 2) (Fin 2) F) * β = -1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hββ
    simpa [hneg] using this
  have hBA : (β : Matrix (Fin 2) (Fin 2) F) * α = -((α : Matrix (Fin 2) (Fin 2) F) * β) := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hβα
    simpa [hneg] using this
  have hXA : (x : Matrix (Fin 2) (Fin 2) F) * α = α * x := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (hx α hα)
    simpa using this
  have hXB : (x : Matrix (Fin 2) (Fin 2) F) * β = β * x := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (hx β hβ)
    simpa using this
  obtain ⟨h01, h10, h00⟩ := scalar_of_comm_anticomm h2 _ _ _ α.2 β.2 hA hB hBA hXA hXB
  refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨(x : Matrix (Fin 2) (Fin 2) F) 0 0, ?_, ?_⟩
  · have hd := x.2
    rw [Matrix.det_fin_two, h01, h10, ← h00] at hd
    simpa [pow_two] using (by linear_combination hd : (x : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 = 1)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]


end Fin

section Res

variable {M : Type} [Group M]

@[expose] def resAut (Q : Subgroup M) (α : MulAut M) (h : ∀ x, x ∈ Q ↔ α x ∈ Q) : MulAut ↥Q where
  toFun x := ⟨α x, (h x).mp x.2⟩
  invFun y := ⟨α.symm y, by rw [h]; simp⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp

theorem resAut_apply (Q : Subgroup M) (α : MulAut M) (h : ∀ x, x ∈ Q ↔ α x ∈ Q) (x : ↥Q) :
    ((resAut Q α h x : ↥Q) : M) = α x := rfl

theorem resAut_pow_apply (Q : Subgroup M) (α : MulAut M) (h : ∀ x, x ∈ Q ↔ α x ∈ Q) (n : ℕ) (x : ↥Q) :
    ((((resAut Q α h) ^ n) x : ↥Q) : M) = (α ^ n) (x : M) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
    rfl

theorem resAut_orderOf_dvd (Q : Subgroup M) (α : MulAut M) (h : ∀ x, x ∈ Q ↔ α x ∈ Q) [Finite M] :
    orderOf (resAut Q α h) ∣ orderOf α := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [resAut_pow_apply, pow_orderOf_eq_one]
  simp

end Res


section QuatOdd

open CFSG.GH74.GLS.IVK.Lifted.QuatAut

theorem aut_odd_eq_one {j : ℕ} (hj : 2 ≤ j) (ρ : MulAut (QuaternionGroup (2 ^ j))) {m : ℕ}
    (hm : Odd m) (hρ : ρ ^ m = 1) : ρ = 1 := by
  have hN : 3 ≤ 2 ^ j := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have : NeZero (2 ^ j) := ⟨by positivity⟩
  have kpow : ∀ n : ℕ, kOf (ρ ^ n) = (kOf ρ) ^ n := by
    intro n
    induction n with
    | zero => simpa using kOf_one
    | succ n ih => rw [pow_succ, kOf_mul hN, ih, pow_succ]
  have hk : (kOf ρ) ^ m = 1 := by
    rw [← kpow, hρ, kOf_one]
  have hk1 : kOf ρ = 1 := by
    obtain ⟨u, hu⟩ := isUnit_kOf hN ρ
    have hum : u ^ m = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, hu, Units.val_one]
      exact hk
    have hdvd : orderOf u ∣ 2 ^ j := by
      have h1 : orderOf u ∣ Nat.card (ZMod (2 * 2 ^ j))ˣ := orderOf_dvd_natCard u
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h1
      have h2 : 2 * 2 ^ j = 2 ^ (j + 1) := by ring
      have ht : (2 * 2 ^ j).totient = 2 ^ j := by
        rw [h2, Nat.totient_prime_pow Nat.prime_two (by omega)]; simp
      rw [ht] at h1
      exact h1
    have hdvd2 : orderOf u ∣ m := orderOf_dvd_of_pow_eq_one hum
    have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
    have : orderOf u ∣ 1 := by
      have := Nat.dvd_gcd hdvd hdvd2
      rwa [hcop.gcd_eq_one] at this
    have h1 : orderOf u = 1 := Nat.dvd_one.mp this
    have : u = 1 := orderOf_eq_one_iff.mp h1
    rw [← hu, this]; simp
  have kpow1 : ∀ n : ℕ, kOf (ρ ^ n) = 1 := fun n => by rw [kpow, hk1, one_pow]
  have jpow : ∀ n : ℕ, jOf (ρ ^ n) = (n : ZMod (2 * 2 ^ j)) * jOf ρ := by
    intro n
    induction n with
    | zero => simpa using jOf_one
    | succ n ih =>
      rw [pow_succ, jOf_mul hN, ih, kpow1]
      push_cast; ring
  have hj0 : jOf ρ = 0 := by
    have h1 : jOf (ρ ^ m) = 0 := by rw [hρ, jOf_one]
    rw [jpow] at h1
    have hunit : IsUnit (m : ZMod (2 * 2 ^ j)) := by
      rw [ZMod.isUnit_iff_coprime]
      have h2 : 2 * 2 ^ j = 2 ^ (j + 1) := by ring
      rw [h2]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
    exact (hunit.mul_right_eq_zero).mp h1
  ext x
  rcases x with i | i
  · rw [aut_a hN, hk1, one_mul]; rfl
  · rw [aut_xa hN, hk1, hj0, one_mul, zero_add]; rfl

end QuatOdd

end CFSG.GH74.GLS.LU.Local.SL2
