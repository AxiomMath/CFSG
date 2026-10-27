module

public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LinearAlgebra

open Matrix

private abbrev elem {n : ℕ} (i j : Fin n) (hij : i ≠ j) : GL (Fin n) (ZMod 2) :=
  Matrix.GeneralLinearGroup.transvection i j hij 1

@[simp] private lemma coe_elem {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (elem i j hij : Matrix (Fin n) (Fin n) (ZMod 2)) =
      1 + Matrix.single i j (1 : ZMod 2) := rfl

private lemma elem_mul_self {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    elem i j hij * elem i j hij = 1 := by
  ext a b
  simp [elem, Matrix.GeneralLinearGroup.transvection, Matrix.transvection,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one,
    Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne, Matrix.single_mul_single_same,
    Matrix.one_apply, Matrix.single_apply, hij, hij.symm]
  split_ifs <;> decide

private lemma elem_mul_comm {n : ℕ} (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hil : i ≠ l) :
    elem i j hij * elem k l hkl = elem k l hkl * elem i j hij := by
  ext a b
  simp [elem, Matrix.GeneralLinearGroup.transvection, Matrix.transvection,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one,
    Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne, Matrix.single_mul_single_same,
    Matrix.one_apply, Matrix.single_apply, hjk, hjk.symm, hil, hil.symm]
  split_ifs <;> decide

private lemma elem_steinberg {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    elem i j hij * elem j k hjk * elem i j hij = elem i k hik * elem j k hjk := by
  ext a b
  simp [elem, Matrix.GeneralLinearGroup.transvection, Matrix.transvection,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one,
    Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne, Matrix.single_mul_single_same,
    Matrix.one_apply, Matrix.single_apply, hij, hij.symm, hjk, hjk.symm, hik, hik.symm]
  split_ifs <;> decide

private lemma elem_mulVec {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (u : Fin n → ZMod 2) :
    (elem i j hij : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u =
      u + (u j) • Pi.single i (1 : ZMod 2) := by
  rw [coe_elem, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  simp

private lemma elem_mulVec_sub {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (a : Fin n → ZMod 2) :
    (elem i j hij : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a - a =
      (a j) • Pi.single i (1 : ZMod 2) := by
  rw [elem_mulVec, add_sub_cancel_left]

private lemma cocycle_eq_of_rho_eq {n : ℕ} {Γ : Type*} [Group Γ]
    (ρ : Γ →* GL (Fin n) (ZMod 2)) (c : Γ → Fin n → ZMod 2)
    (hc : ∀ g h : Γ, c (g * h) = c g +
      (ρ g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ c h)
    (hker : ∀ g : Γ, ρ g = 1 → c g = 0) {g g' : Γ} (hgg' : ρ g = ρ g') :
    c g = c g' := by
  have h0 : ρ (g'⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hgg', inv_mul_cancel]
  have h := hc g' (g'⁻¹ * g)
  rw [hker _ h0, Matrix.mulVec_zero, add_zero] at h
  rw [show g = g' * (g'⁻¹ * g) by simp]
  exact h

private lemma cocycle_one {n : ℕ} {Γ : Type*} [Group Γ]
    (ρ : Γ →* GL (Fin n) (ZMod 2)) (c : Γ → Fin n → ZMod 2)
    (hker : ∀ g : Γ, ρ g = 1 → c g = 0) : c 1 = 0 :=
  hker 1 (map_one ρ)

theorem exists_eq_mulVec_sub_of_cocycle {n : ℕ} (hn : 4 ≤ n) {Γ : Type*} [Group Γ]
    (ρ : Γ →* GL (Fin n) (ZMod 2))
    (hρ : ∀ i j : Fin n, i ≠ j → ∃ γ : Γ,
      (ρ γ : Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.transvection i j 1)
    (c : Γ → Fin n → ZMod 2)
    (hc : ∀ g h : Γ, c (g * h) = c g +
      (ρ g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ c h)
    (hker : ∀ g : Γ, ρ g = 1 → c g = 0) :
    ∃ a : Fin n → ZMod 2, ∀ g : Γ,
      c g = (ρ g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a - a := by
  classical
  let γ : (i j : Fin n) → (hij : i ≠ j) → Γ := fun i j hij =>
    Classical.choose (hρ i j hij)
  have hγ : ∀ (i j : Fin n) (hij : i ≠ j), ρ (γ i j hij) = elem i j hij := by
    intro i j hij
    apply Units.ext
    change (ρ (γ i j hij) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      Matrix.transvection i j 1
    simpa [γ] using Classical.choose_spec (hρ i j hij)
  let v : (i j : Fin n) → (hij : i ≠ j) → Fin n → ZMod 2 := fun i j hij =>
    c (γ i j hij)
  have hv_sq : ∀ (i j : Fin n) (hij : i ≠ j),
      v i j hij + (elem i j hij : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v i j hij = 0 := by
    intro i j hij
    have h0 : ρ (γ i j hij * γ i j hij) = 1 := by
      rw [map_mul, hγ i j hij, elem_mul_self]
    have h := hc (γ i j hij) (γ i j hij)
    rw [hker _ h0, hγ i j hij] at h
    simpa [v] using h.symm
  have hv_second : ∀ (i j : Fin n) (hij : i ≠ j), v i j hij j = 0 := by
    intro i j hij
    have h := hv_sq i j hij
    rw [elem_mulVec, ← add_assoc, ZModModule.add_self, zero_add] at h
    have hi := congrFun h i
    simpa using hi
  have hv_off : ∀ {i j : Fin n} (hij : i ≠ j) {q : Fin n}, q ≠ i → q ≠ j →
      v i j hij q = 0 := by
    intro i j hij q hqi hqj
    have hcard :
        Finset.card ({q, i, j} : Finset (Fin n)) <
          Finset.card (Finset.univ : Finset (Fin n)) := by
      rw [Finset.card_univ, Fintype.card_fin]
      have hle : Finset.card ({q, i, j} : Finset (Fin n)) ≤ 3 := Finset.card_le_three
      omega
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hpq : p ≠ q := by intro h; exact hp (by simp [h])
    have hpi : p ≠ i := by intro h; exact hp (by simp [h])
    have hpj : p ≠ j := by intro h; exact hp (by simp [h])
    have hcomm : elem p q hpq * elem i j hij = elem i j hij * elem p q hpq :=
      elem_mul_comm p q i j hpq hij hqi hpj
    have hρeq : ρ (γ p q hpq * γ i j hij) = ρ (γ i j hij * γ p q hpq) := by
      rw [map_mul, map_mul, hγ p q hpq, hγ i j hij, hcomm]
    have heq := cocycle_eq_of_rho_eq ρ c hc hker hρeq
    rw [hc (γ p q hpq) (γ i j hij), hc (γ i j hij) (γ p q hpq),
      hγ p q hpq, hγ i j hij] at heq
    rw [elem_mulVec, elem_mulVec] at heq
    have hp_eval := congrFun heq p
    simp [Pi.add_apply, Pi.smul_apply, hpq, hpi, hpj] at hp_eval
    abel_nf at hp_eval
    have h1 := add_left_cancel hp_eval
    change c (γ i j hij) q = 0
    have h2 : c (γ i j hij) p + c (γ i j hij) q = c (γ i j hij) p + 0 := by
      simpa using h1
    exact add_left_cancel h2
  have hv_coeff : ∀ {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      v j k hjk j = v i k hik i := by
    intro i j k hij hjk hik
    have hρeq : ρ (γ i j hij * γ j k hjk * γ i j hij) =
        ρ (γ i k hik * γ j k hjk) := by
      rw [map_mul, map_mul, map_mul, hγ i j hij, hγ j k hjk, hγ i k hik,
        elem_steinberg i j k hij hjk hik]
    have heq := cocycle_eq_of_rho_eq ρ c hc hker hρeq
    rw [hc (γ i j hij * γ j k hjk) (γ i j hij),
      hc (γ i j hij) (γ j k hjk),
      hc (γ i k hik) (γ j k hjk)] at heq
    simp only [map_mul, hγ i j hij, hγ j k hjk, hγ i k hik,
      Matrix.GeneralLinearGroup.coe_mul] at heq
    have hv_jk_k : v j k hjk k = 0 := hv_second j k hjk
    have hv_ij_k : v i j hij k = 0 := hv_off hij hik.symm hjk.symm
    have hv_ij_j : v i j hij j = 0 := hv_second i j hij
    rw [← Matrix.mulVec_mulVec] at heq
    simp only [v, elem_mulVec, hv_jk_k, hv_ij_k, hv_ij_j,
      zero_smul, add_zero, ZModModule.add_self] at heq
    have hi := congrFun heq i
    change c (γ j k hjk) j = c (γ i k hik) i
    have hv_jk_i : c (γ j k hjk) i = 0 := by simpa [v] using hv_off hjk hij hik
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, hv_jk_i] at hi
    abel_nf at hi
    simpa [two_mul, ZModModule.add_self] using hi
  have hn1 : 1 < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  let j0 : Fin n → Fin n := fun k => Classical.choose (Fintype.exists_ne_of_one_lt_card hn1 k)
  have hj0 : ∀ k : Fin n, j0 k ≠ k := fun k =>
    Classical.choose_spec (Fintype.exists_ne_of_one_lt_card hn1 k)
  let a : Fin n → ZMod 2 := fun k => v (j0 k) k (hj0 k) (j0 k)
  have hv_a : ∀ {i k : Fin n} (hik : i ≠ k),
      v i k hik = (elem i k hik : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a - a := by
    intro i k hik
    rw [elem_mulVec_sub]
    funext q
    by_cases hqi : q = i
    · subst q
      have hcoeff : v i k hik i = a k := by
        by_cases hji : i = j0 k
        · subst i
          rfl
        · exact (hv_coeff hji (hj0 k) hik).symm
      rw [hcoeff]
      simp
    · have hvz : v i k hik q = 0 := by
        by_cases hqk : q = k
        · subst q
          exact hv_second i k hik
        · exact hv_off hik hqi hqk
      rw [hvz]
      simp [Pi.smul_apply, Pi.single_eq_of_ne hqi]
  let d : Γ → Fin n → ZMod 2 := fun g =>
    c g - ((ρ g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a - a)
  have hd_cocycle : ∀ g h : Γ, d (g * h) = d g +
      (ρ g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ d h := by
    intro g h
    simp only [d, hc g h, map_mul, Matrix.GeneralLinearGroup.coe_mul]
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    simp only [Matrix.mulVec_mulVec]
    abel_nf
  have hd_eq : ∀ {g h : Γ}, ρ g = ρ h → d g = d h := by
    intro g h hgh
    have hcgh := cocycle_eq_of_rho_eq ρ c hc hker hgh
    simp [d, hcgh, hgh]
  have hd_one : d 1 = 0 := by
    simp [d, cocycle_one ρ c hker]
  have hd_trans : ∀ (i j : Fin n) (hij : i ≠ j), d (γ i j hij) = 0 := by
    intro i j hij
    have hv := hv_a hij
    simp [d, hγ i j hij, v, hv]
  have hd_lift : ∀ (i j : Fin n) (hij : i ≠ j) (r : ZMod 2),
      ∃ g : Γ, (ρ g : Matrix (Fin n) (Fin n) (ZMod 2)) =
        Matrix.transvection i j r ∧ d g = 0 := by
    intro i j hij r
    have hr01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
    rcases hr01 r with rfl | rfl
    · refine ⟨1, ?_, hd_one⟩
      simp
    · refine ⟨γ i j hij, ?_, hd_trans i j hij⟩
      rw [hγ i j hij]
      rfl
  have hP : ∀ M : Matrix (Fin n) (Fin n) (ZMod 2), M.det ≠ 0 →
      ∃ g : Γ, (ρ g : Matrix (Fin n) (Fin n) (ZMod 2)) = M ∧ d g = 0 := by
    intro M hM
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (P := fun N => ∃ g : Γ,
        (ρ g : Matrix (Fin n) (Fin n) (ZMod 2)) = N ∧ d g = 0) M hM ?_ ?_ ?_
    · intro D hD
      have hprod : (Finset.univ.prod D : ZMod 2) ≠ 0 := by
        simpa [Matrix.det_diagonal] using hD
      have hDnz : ∀ i, D i ≠ 0 := by
        intro i
        exact (Finset.prod_ne_zero_iff (s := Finset.univ) (f := D)).mp
          (by simpa using hprod) i (Finset.mem_univ i)
      have hD1 : D = 1 := by
        funext i
        have h01 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
        exact h01 (D i) (hDnz i)
      refine ⟨1, ?_, hd_one⟩
      simp [hD1]
    · intro t
      obtain ⟨g, hg, hdg⟩ := hd_lift t.i t.j t.hij t.c
      refine ⟨g, ?_, hdg⟩
      simpa [Matrix.TransvectionStruct.toMatrix] using hg
    · intro A B hA hB hPA hPB
      obtain ⟨g, hg, hdg⟩ := hPA
      obtain ⟨h, hh, hdh⟩ := hPB
      refine ⟨g * h, ?_, ?_⟩
      · simp [map_mul, hg, hh]
      · rw [hd_cocycle, hdg, hdh, Matrix.mulVec_zero, add_zero]
  refine ⟨a, ?_⟩
  intro g
  obtain ⟨g', hg', hdg'⟩ := hP (ρ g : Matrix (Fin n) (Fin n) (ZMod 2))
    (Matrix.GeneralLinearGroup.det_ne_zero (ρ g))
  have hρgg' : ρ g = ρ g' := Units.ext hg'.symm
  have hdg : d g = d g' := hd_eq hρgg'
  have hzero : d g = 0 := by rw [hdg, hdg']
  exact sub_eq_zero.mp hzero

end CFSG.LinearAlgebra
