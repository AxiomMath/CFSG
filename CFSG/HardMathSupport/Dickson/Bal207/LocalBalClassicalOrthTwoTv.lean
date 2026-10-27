module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Quad

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

theorem card_two_cases' {K : Type*} [Field K] (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 :=
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.card_two_cases hK c

section Tv

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem add_self_vec (K : Type*) [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
    (v : V) : v + v = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [← two_smul K, h2, zero_smul]

noncomputable def tvMap (Q : QuadraticForm K V) (a : V) : V →ₗ[K] V :=
  LinearMap.id + (QuadraticMap.polarBilin Q a).smulRight a

theorem tvMap_apply (Q : QuadraticForm K V) (a v : V) :
    tvMap Q a v = v + polar Q a v • a := by
  simp [tvMap, QuadraticMap.polarBilin_apply_apply]

theorem tvMap_tvMap (Q : QuadraticForm K V) (a v : V) : tvMap Q a (tvMap Q a v) = v := by
  rw [tvMap_apply, tvMap_apply, polar_add_right, polar_smul_right, polar_self_eq_zero,
    smul_eq_mul, mul_zero, add_zero, add_assoc, add_self_vec K, add_zero]

noncomputable def tv (Q : QuadraticForm K V) (a : V) : V ≃ₗ[K] V :=
  LinearEquiv.ofInvolutive (tvMap Q a) (tvMap_tvMap Q a)

theorem tv_apply (Q : QuadraticForm K V) (a v : V) : tv Q a v = v + polar Q a v • a :=
  tvMap_apply Q a v

theorem tv_mul_self (Q : QuadraticForm K V) (a : V) : tv Q a * tv Q a = 1 := by
  ext v
  exact tvMap_tvMap Q a v

theorem tv_inv (Q : QuadraticForm K V) (a : V) : (tv Q a)⁻¹ = tv Q a :=
  inv_eq_of_mul_eq_one_right (tv_mul_self Q a)

theorem tv_isometry {a : V} (ha : Q a = 1) (v : V) : Q (tv Q a v) = Q v := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [tv_apply, map_add_eq, QuadraticMap.map_smul, ha, polar_smul_right, polar_comm Q v a]
  simp only [smul_eq_mul, mul_one]
  linear_combination (polar Q a v * polar Q a v) * h2

theorem tv_mem {a : V} (ha : Q a = 1) : tv Q a ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (tv_isometry ha)

theorem tv_conj {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (a : V) :
    g * tv Q a * g⁻¹ = tv Q (g a) := by
  ext v
  have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg a (g.symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  change g (tv Q a (g.symm v)) = tv Q (g a) v
  rw [tv_apply, map_add, map_smul, LinearEquiv.apply_symm_apply, tv_apply, h]

theorem tv_comm_of_fixed {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {a : V} (hga : g a = a) : g * tv Q a = tv Q a * g := by
  have h := tv_conj hg a
  rw [hga] at h
  calc g * tv Q a = g * tv Q a * g⁻¹ * g := by group
    _ = tv Q a * g := by rw [h]

theorem tv_braid {a b : V} (hab : polar Q a b = 1) :
    tv Q a * tv Q b * tv Q a = tv Q b * tv Q a * tv Q b := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hba : polar Q b a = 1 := by rw [polar_comm]; exact hab
  ext v
  simp only [LinearEquiv.mul_apply, tv_apply, map_add, map_smul, polar_add_right,
    polar_smul_right, smul_eq_mul, hab, hba, polar_self_eq_zero, mul_zero, add_zero, mul_one]
  match_scalars <;>
    first
      | ring1
      | linear_combination (polar Q a v) * h2
      | linear_combination (polar Q b v) * h2
      | linear_combination (-(polar Q a v)) * h2
      | linear_combination (-(polar Q b v)) * h2

@[expose] noncomputable def rot (Q : QuadraticForm K V) (a b : V) : V ≃ₗ[K] V := tv Q a * tv Q b

theorem rot_apply {a b : V} (hab : polar Q a b = 1) (v : V) :
    rot Q a b v = v + polar Q a v • a + polar Q b v • (a + b) := by
  simp only [rot, LinearEquiv.mul_apply, tv_apply, map_add, map_smul, polar_add_right,
    polar_smul_right, smul_eq_mul, hab, mul_one]
  module

theorem rot_a {a b : V} (hab : polar Q a b = 1) : rot Q a b a = b := by
  have hba : polar Q b a = 1 := by rw [polar_comm]; exact hab
  rw [rot_apply hab, polar_self_eq_zero, hba, zero_smul, add_zero, one_smul, ← add_assoc,
    add_self_vec K, zero_add]

theorem rot_b {a b : V} (hab : polar Q a b = 1) : rot Q a b b = a + b := by
  rw [rot_apply hab, hab, polar_self_eq_zero, zero_smul, add_zero, one_smul, add_comm]

theorem rot_eq_mul (Q : QuadraticForm K V) (a b : V) : rot Q a b = tv Q a * tv Q b := rfl

theorem rot_cube {a b : V} (hab : polar Q a b = 1) : rot Q a b ^ 3 = 1 := by
  have hbr := tv_braid hab
  have ha := tv_mul_self Q a
  have hb := tv_mul_self Q b
  rw [rot_eq_mul]
  calc (tv Q a * tv Q b) ^ 3 = (tv Q a * tv Q b * tv Q a) * (tv Q b * tv Q a * tv Q b) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (tv Q b * tv Q a * tv Q b) * (tv Q b * tv Q a * tv Q b) := by rw [hbr]
    _ = tv Q b * tv Q a * (tv Q b * tv Q b) * tv Q a * tv Q b := by simp only [mul_assoc]
    _ = tv Q b * (tv Q a * tv Q a) * tv Q b := by rw [hb, mul_one]; simp only [mul_assoc]
    _ = 1 := by rw [ha, mul_one, hb]

theorem rot_swap (Q : QuadraticForm K V) (a b : V) : rot Q b a = (rot Q a b)⁻¹ := by
  rw [rot_eq_mul, rot_eq_mul, mul_inv_rev, tv_inv, tv_inv]

theorem tv_add_eq {a b : V} (ha : Q a = 1) (hab : polar Q a b = 1) :
    tv Q (a + b) = tv Q a * tv Q b * tv Q a := by
  have h := tv_conj (tv_mem ha) b
  rw [tv_inv, tv_apply, hab, one_smul, add_comm] at h
  exact h.symm

theorem rot_cyc {a b : V} (ha : Q a = 1) (hab : polar Q a b = 1) :
    rot Q b (a + b) = rot Q a b ∧ rot Q (a + b) a = rot Q a b := by
  have hbr := tv_braid hab
  have haa := tv_mul_self Q a
  have hbb := tv_mul_self Q b
  have hc := tv_add_eq ha hab
  refine ⟨?_, ?_⟩
  · rw [rot_eq_mul, rot_eq_mul, hc, hbr]
    calc tv Q b * (tv Q b * tv Q a * tv Q b) = (tv Q b * tv Q b) * tv Q a * tv Q b := by
          simp only [mul_assoc]
      _ = tv Q a * tv Q b := by rw [hbb, one_mul]
  · rw [rot_eq_mul, rot_eq_mul, hc]
    calc tv Q a * tv Q b * tv Q a * tv Q a = tv Q a * tv Q b * (tv Q a * tv Q a) := by
          simp only [mul_assoc]
      _ = tv Q a * tv Q b := by rw [haa, mul_one]

theorem rot_mem {a b : V} (ha : Q a = 1) (hb : Q b = 1) :
    rot Q a b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (tv_mem ha) (tv_mem hb)

theorem rot_conj {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (a b : V) :
    g * rot Q a b * g⁻¹ = rot Q (g a) (g b) := by
  rw [rot_eq_mul, rot_eq_mul, ← tv_conj hg a, ← tv_conj hg b]
  group

theorem rot_comm_of_fixed {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {a b : V} (hga : g a = a) (hgb : g b = b) : g * rot Q a b = rot Q a b * g := by
  rw [rot_eq_mul, ← mul_assoc, tv_comm_of_fixed hg hga, mul_assoc, tv_comm_of_fixed hg hgb,
    mul_assoc]

theorem rot_apply_add_self {a b : V} (hab : polar Q a b = 1) (v : V) :
    rot Q a b v + v = polar Q a v • a + polar Q b v • (a + b) := by
  rw [rot_apply hab]
  calc v + polar Q a v • a + polar Q b v • (a + b) + v
      = (v + v) + (polar Q a v • a + polar Q b v • (a + b)) := by abel
    _ = _ := by rw [add_self_vec K, zero_add]

theorem three_dvd_of_rot_pow_apply_eq {a b : V} (hab : polar Q a b = 1) {m : ℕ}
    (h : (rot Q a b ^ m) a = a) : 3 ∣ m := by
  have h3 := rot_cube hab
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.polar_zero_right] at hab
    exact zero_ne_one hab
  have hab' : a ≠ b := by
    rintro rfl
    rw [polar_self_eq_zero] at hab
    exact zero_ne_one hab
  have hm : rot Q a b ^ m = rot Q a b ^ (m % 3) := by
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [hm] at h
  obtain h0 | h1 | h2 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  · omega
  · rw [h1, pow_one, rot_a hab] at h
    exact absurd h.symm hab'
  · rw [h2, pow_two, LinearEquiv.mul_apply, rot_a hab, rot_b hab] at h
    exact absurd (by simpa using h) hb0

end Tv

section FixesOfCommute

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem fixes_of_commute_rot (hK : Nat.card K = 2) {a b : V} (hab : polar Q a b = 1)
    {G : V ≃ₗ[K] V} (hGρ : G * rot Q a b = rot Q a b * G) {k : ℕ} (hk : Nat.Coprime 3 k)
    (hGk : G ^ k = 1) : G a = a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.polar_zero_left] at hab
    exact zero_ne_one hab
  have hρa : rot Q a b a = b := rot_a hab
  have hρb : rot Q a b b = a + b := rot_b hab
  have hcomm : ∀ v, G (rot Q a b v) = rot Q a b (G v) := fun v => by
    have := congrArg (fun e : V ≃ₗ[K] V => e v) hGρ
    simpa using this
  have hGa : G a = rot Q a b (G b) + G b := by
    have : a = rot Q a b b + b := by
      rw [hρb, add_assoc, add_self_vec K, add_zero]
    conv_lhs => rw [this]
    rw [map_add, hcomm]
  have hmem : G a ∈ Submodule.span K ({a, b} : Set V) := by
    rw [hGa, rot_apply_add_self hab]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))))
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 hmem
  obtain ⟨j, hj3, hGj⟩ : ∃ j : ℕ, j < 3 ∧ G a = ((rot Q a b) ^ j) a := by
    rcases card_two_cases' hK c with rfl | rfl <;> rcases card_two_cases' hK d with rfl | rfl
    · exfalso
      apply ha0
      have : G a = 0 := by simpa using hcd.symm
      exact (LinearEquiv.map_eq_zero_iff G).1 this
    · exact ⟨1, by norm_num, by rw [pow_one, hρa]; simpa using hcd.symm⟩
    · exact ⟨0, by norm_num, by rw [pow_zero]; simpa using hcd.symm⟩
    · exact ⟨2, by norm_num, by rw [pow_two, LinearEquiv.mul_apply, hρa, hρb]; simpa using hcd.symm⟩
  have hGpow : ∀ m : ℕ, ∀ v, G ((rot Q a b ^ m) v) = (rot Q a b ^ m) (G v) := fun m v => by
    have := congrArg (fun e : V ≃ₗ[K] V => e v) ((Commute.pow_right hGρ m).eq)
    simpa using this
  have hpow : ∀ n : ℕ, (G ^ n) a = ((rot Q a b) ^ (j * n)) a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, hGpow, hGj, mul_add, mul_one, pow_add,
        LinearEquiv.mul_apply]
  have h1 : ((rot Q a b) ^ (j * k)) a = a := by
    rw [← hpow k, hGk]
    rfl
  have h3j : 3 ∣ j := Nat.Coprime.dvd_of_dvd_mul_right hk (three_dvd_of_rot_pow_apply_eq hab h1)
  have hj0 : j = 0 := by omega
  rw [hGj, hj0, pow_zero]
  rfl

end FixesOfCommute

end CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

end
