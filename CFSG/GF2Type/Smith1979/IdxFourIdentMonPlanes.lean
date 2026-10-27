module

public import CFSG.GF2Type.Smith1979.IdxFourIdentMonDefs

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

namespace MonAux

@[expose] def pr (x : V12) (i : Fin 6) : ZMod 2 × ZMod 2 := (x (lo i), x (hi i))

@[expose] def nrm (p : ZMod 2 × ZMod 2) : ZMod 2 := p.1 + p.1 * p.2 + p.2

@[expose] def thPair (p : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := (p.2, p.1 + p.2)

@[expose] def frPair (p : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := (p.1 + p.2, p.2)

theorem ext_pr {x y : V12} (h : ∀ i, pr x i = pr y i) : x = y :=
  ext_lo_hi (fun i => congrArg Prod.fst (h i)) (fun i => congrArg Prod.snd (h i))

theorem q0_eq_sum (x : V12) : q0 x = ∑ i : Fin 6, nrm (pr x i) := rfl

theorem pr_add (x y : V12) (i : Fin 6) : pr (x + y) i = pr x i + pr y i := rfl

theorem pr_zero (i : Fin 6) : pr (0 : V12) i = 0 := rfl

theorem pr_diagE (c : Fin 6 → ZMod 3) (x : V12) (i : Fin 6) :
    pr (diagE c x) i = omegaPow (c i) (pr x i) := by
  unfold pr
  rw [diagE_apply, diagFun_lo, diagFun_hi]

theorem pr_permE (π : Equiv.Perm (Fin 6)) (x : V12) (i : Fin 6) :
    pr (permE π x) i = pr x (π.symm i) := by
  unfold pr
  rw [permE_apply, permFun_lo, permFun_hi]

theorem pr_frobE (x : V12) (i : Fin 6) : pr (frobE x) i = frPair (pr x i) := by
  unfold pr frPair
  rw [frobE_apply, frobFun_lo, frobFun_hi]

theorem pr_theta0 (x : V12) (i : Fin 6) : pr (theta0 x) i = thPair (pr x i) := by
  unfold pr thPair
  rw [theta0_lo, theta0_hi]

theorem mem_plane_iff_pr {x : V12} {i : Fin 6} :
    x ∈ plane i ↔ ∀ j, j ≠ i → pr x j = 0 := by
  refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩
  · obtain ⟨h1, h2⟩ := h j hj
    exact Prod.ext h1 h2
  · have := h j hj
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem omegaPow_one : ∀ p : ZMod 2 × ZMod 2, omegaPow 1 p = thPair p := by decide

theorem omegaPow_thPair : ∀ (k : ZMod 3) (p : ZMod 2 × ZMod 2),
    omegaPow k (thPair p) = thPair (omegaPow k p) := by decide

theorem omegaPow_frPair : ∀ (k : ZMod 3) (p : ZMod 2 × ZMod 2),
    frPair (omegaPow k p) = omegaPow (-k) (frPair p) := by decide

theorem nrm_omegaPow : ∀ (k : ZMod 3) (p : ZMod 2 × ZMod 2), nrm (omegaPow k p) = nrm p := by
  decide

theorem nrm_thPair : ∀ p : ZMod 2 × ZMod 2, nrm (thPair p) = nrm p := by decide

theorem nrm_frPair : ∀ p : ZMod 2 × ZMod 2, nrm (frPair p) = nrm p := by decide

theorem frPair_thPair : ∀ p : ZMod 2 × ZMod 2, frPair (thPair p) = thPair (thPair (frPair p)) := by
  decide

theorem omegaPow_zero_pair (k : ZMod 3) : omegaPow k (0 : ZMod 2 × ZMod 2) = 0 :=
  (omegaPow_eq_zero_iff k 0).2 rfl

theorem omegaPow_injective_one : ∀ a b : ZMod 3, omegaPow a (1, 0) = omegaPow b (1, 0) → a = b := by
  decide

theorem exists_omegaPow_of_ne_zero :
    ∀ p : ZMod 2 × ZMod 2, p ≠ 0 → ∃ k : ZMod 3, omegaPow k (1, 0) = p := by decide

theorem omegaPow_ne_zero (k : ZMod 3) : omegaPow k (1, 0) ≠ 0 :=
  fun h => absurd ((omegaPow_eq_zero_iff k (1, 0)).1 h) (by decide)

theorem nrm_eq_one : ∀ p : ZMod 2 × ZMod 2, p ≠ 0 → nrm p = 1 := by decide

theorem nrm_zero : nrm (0 : ZMod 2 × ZMod 2) = 0 := by decide

theorem zmod2_cases : ∀ ε : ZMod 2, ε = 0 ∨ ε = 1 := by decide

theorem omegaPow_unit_hi : ∀ k : ZMod 3, omegaPow k (0, 1) = thPair (omegaPow k (1, 0)) := by
  decide

theorem omegaPow_one_one :
    ∀ k : ZMod 3, omegaPow k (1, 1) = thPair (thPair (omegaPow k (1, 0))) := by decide

theorem omegaPow_clash : ∀ (m : ZMod 3) (p q : ZMod 2 × ZMod 2), p ≠ 0 → q ≠ 0 →
    omegaPow 1 p = omegaPow m p → omegaPow 2 q = omegaPow m q → False := by decide

theorem sum_clash : ∀ j l : Fin 6, j ≠ l →
    ∑ t : Fin 6, (if t = j then (1 : ZMod 3) else if t = l then 2 else 0) = 0 := by decide

@[expose] def pairVec (i : Fin 6) (p : ZMod 2 × ZMod 2) : V12 :=
  Fin.append (fun j => if j = i then p.1 else 0) (fun j => if j = i then p.2 else 0)

theorem pr_pairVec (i j : Fin 6) (p : ZMod 2 × ZMod 2) :
    pr (pairVec i p) j = if j = i then p else 0 := by
  unfold pr pairVec
  rw [Fin.append_left, Fin.append_right]
  split_ifs <;> rfl

theorem pr_pairVec_self (i : Fin 6) (p : ZMod 2 × ZMod 2) : pr (pairVec i p) i = p := by
  rw [pr_pairVec, if_pos rfl]

theorem pr_pairVec_ne {i j : Fin 6} (h : j ≠ i) (p : ZMod 2 × ZMod 2) :
    pr (pairVec i p) j = 0 := by
  rw [pr_pairVec, if_neg h]

theorem pairVec_mem_plane (i : Fin 6) (p : ZMod 2 × ZMod 2) : pairVec i p ∈ plane i :=
  mem_plane_iff_pr.2 fun _ hj => pr_pairVec_ne hj p

theorem eq_pairVec_of_mem_plane {i : Fin 6} {x : V12} (hx : x ∈ plane i) :
    x = pairVec i (pr x i) :=
  ext_pr fun j => by
    by_cases hj : j = i
    · subst hj
      rw [pr_pairVec_self]
    · rw [pr_pairVec_ne hj, mem_plane_iff_pr.1 hx j hj]

theorem pairVec_zero (i : Fin 6) : pairVec i 0 = 0 :=
  ext_pr fun j => by
    rw [pr_pairVec, pr_zero]
    split_ifs <;> rfl

theorem pairVec_add (i : Fin 6) (p q : ZMod 2 × ZMod 2) :
    pairVec i (p + q) = pairVec i p + pairVec i q :=
  ext_pr fun j => by
    rw [pr_add, pr_pairVec, pr_pairVec, pr_pairVec]
    split_ifs <;> simp

theorem pairVec_eq_zero_iff {i : Fin 6} {p : ZMod 2 × ZMod 2} : pairVec i p = 0 ↔ p = 0 :=
  ⟨fun h => by rw [← pr_pairVec_self i p, h]; rfl, fun h => h ▸ pairVec_zero i⟩

theorem pairVec_ne_zero (i : Fin 6) {p : ZMod 2 × ZMod 2} (hp : p ≠ 0) : pairVec i p ≠ 0 :=
  fun h => hp (pairVec_eq_zero_iff.1 h)

theorem eq_zero_of_mem_plane_of_pr {i : Fin 6} {x : V12} (hx : x ∈ plane i) (h : pr x i = 0) :
    x = 0 := by
  rw [eq_pairVec_of_mem_plane hx, h, pairVec_zero]

theorem pairVec_inj {a b : Fin 6} {p q : ZMod 2 × ZMod 2} (h : pairVec a p = pairVec b q)
    (hp : p ≠ 0) : a = b ∧ p = q := by
  have h1 : pr (pairVec a p) a = pr (pairVec b q) a := by rw [h]
  rw [pr_pairVec_self, pr_pairVec] at h1
  by_cases hab : a = b
  · rw [if_pos hab] at h1
    exact ⟨hab, h1⟩
  · rw [if_neg hab] at h1
    exact absurd h1 hp

theorem eq_of_mem_plane_of_mem_plane {i j : Fin 6} {x : V12} (hi : x ∈ plane i)
    (hj : x ∈ plane j) (h0 : x ≠ 0) : i = j := by
  by_contra hij
  exact h0 (eq_zero_of_mem_plane_of_pr hi (mem_plane_iff_pr.1 hj i hij))

theorem diagE_pairVec (c : Fin 6 → ZMod 3) (i : Fin 6) (p : ZMod 2 × ZMod 2) :
    diagE c (pairVec i p) = pairVec i (omegaPow (c i) p) :=
  ext_pr fun j => by
    rw [pr_diagE, pr_pairVec, pr_pairVec]
    split_ifs with h
    · subst h
      rfl
    · exact omegaPow_zero_pair _

theorem permE_pairVec (π : Equiv.Perm (Fin 6)) (i : Fin 6) (p : ZMod 2 × ZMod 2) :
    permE π (pairVec i p) = pairVec (π i) p :=
  ext_pr fun j => by
    rw [pr_permE, pr_pairVec, pr_pairVec]
    simp only [Equiv.symm_apply_eq]

theorem frobE_pairVec (i : Fin 6) (p : ZMod 2 × ZMod 2) :
    frobE (pairVec i p) = pairVec i (frPair p) :=
  ext_pr fun j => by
    rw [pr_frobE, pr_pairVec, pr_pairVec]
    split_ifs <;> rfl

theorem theta0_pairVec (i : Fin 6) (p : ZMod 2 × ZMod 2) :
    theta0 (pairVec i p) = pairVec i (thPair p) :=
  ext_pr fun j => by
    rw [pr_theta0, pr_pairVec, pr_pairVec]
    split_ifs <;> rfl

theorem theta0e_pairVec (i : Fin 6) (p : ZMod 2 × ZMod 2) :
    theta0e (pairVec i p) = pairVec i (thPair p) := theta0_pairVec i p

theorem pr_sum (s : Finset (Fin 6)) (v : Fin 6 → V12) (j : Fin 6) :
    pr (∑ i ∈ s, v i) j = ∑ i ∈ s, pr (v i) j := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add, ih]

theorem sum_pairVec (x : V12) : ∑ i : Fin 6, pairVec i (pr x i) = x :=
  ext_pr fun j => by
    rw [pr_sum]
    simp only [pr_pairVec]
    rw [Finset.sum_ite_eq]
    simp

theorem ext_pairVec {f g : G12} (h₁ : ∀ i, f (pairVec i (1, 0)) = g (pairVec i (1, 0)))
    (h₂ : ∀ i, f (pairVec i (0, 1)) = g (pairVec i (0, 1))) : f = g := by
  refine LinearEquiv.ext fun x => ?_
  rw [← sum_pairVec x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp : ∀ p : ZMod 2 × ZMod 2, p = 0 ∨ p = (1, 0) ∨ p = (0, 1) ∨ p = (1, 1) := by decide
  rcases hp (pr x i) with h | h | h | h <;> rw [h]
  · rw [pairVec_zero, map_zero, map_zero]
  · exact h₁ i
  · exact h₂ i
  · have e : ((1 : ZMod 2), (1 : ZMod 2)) = (1, 0) + (0, 1) := by decide
    rw [e, pairVec_add, map_add, map_add, h₁ i, h₂ i]

end MonAux

open MonAux

theorem diagE_zero : diagE 0 = 1 := LinearEquiv.ext fun x => LinearMap.congr_fun diagLin_zero x

theorem diagE_add (c c' : Fin 6 → ZMod 3) : diagE (c + c') = diagE c * diagE c' :=
  LinearEquiv.ext fun x => LinearMap.congr_fun (diagLin_add c c') x

theorem diagE_injective : Function.Injective diagE := by
  intro c c' h
  funext i
  have h1 := congrArg (fun g : G12 => pr (g (pairVec i (1, 0))) i) h
  simp only [pr_diagE, pr_pairVec_self] at h1
  exact omegaPow_injective_one _ _ h1

theorem diagE_const_one : diagE (fun _ => (1 : ZMod 3)) = theta0e :=
  LinearEquiv.ext fun x => ext_pr fun i => by
    rw [pr_diagE, theta0e_apply, pr_theta0]
    exact omegaPow_one (pr x i)

theorem permE_one : permE 1 = 1 := LinearEquiv.ext fun x => LinearMap.congr_fun permLin_one x

theorem permE_mul (π π' : Equiv.Perm (Fin 6)) : permE (π * π') = permE π * permE π' :=
  LinearEquiv.ext fun x => LinearMap.congr_fun (permLin_mul π π') x

theorem frobE_mul_self : frobE * frobE = 1 :=
  LinearEquiv.ext fun x => LinearMap.congr_fun frobLin_frobLin x

theorem permE_mul_diagE_mul_inv (π : Equiv.Perm (Fin 6)) (c : Fin 6 → ZMod 3) :
    permE π * diagE c * (permE π)⁻¹ = diagE (fun i => c (π.symm i)) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact LinearEquiv.ext fun x => ext_pr fun i => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, pr_permE, pr_diagE, pr_diagE, pr_permE]

theorem frobE_mul_diagE_mul_inv (c : Fin 6 → ZMod 3) :
    frobE * diagE c * frobE⁻¹ = diagE (-c) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact LinearEquiv.ext fun x => ext_pr fun i => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, pr_frobE, pr_diagE, pr_diagE, pr_frobE]
    exact omegaPow_frPair (c i) (pr x i)

theorem frobE_mul_permE (π : Equiv.Perm (Fin 6)) : frobE * permE π = permE π * frobE :=
  LinearEquiv.ext fun x => ext_pr fun i => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, pr_frobE, pr_permE, pr_permE, pr_frobE]

theorem diagE_mem_gammaU (c : Fin 6 → ZMod 3) : diagE c ∈ gammaU :=
  mem_gammaU.2 ⟨fun x => by
    rw [q0_eq_sum, q0_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pr_diagE]; exact nrm_omegaPow _ _,
    Or.inl fun x => ext_pr fun i => by
      rw [pr_diagE, pr_theta0, pr_theta0, pr_diagE]
      exact omegaPow_thPair _ _⟩

theorem permE_mem_gammaU (π : Equiv.Perm (Fin 6)) : permE π ∈ gammaU :=
  mem_gammaU.2 ⟨fun x => by
    rw [q0_eq_sum, q0_eq_sum]
    simp only [pr_permE]
    exact Equiv.sum_comp π.symm (fun i => nrm (pr x i)),
    Or.inl fun x => ext_pr fun i => by
      rw [pr_permE, pr_theta0, pr_theta0, pr_permE]⟩

theorem frobE_mem_gammaU : frobE ∈ gammaU :=
  mem_gammaU.2 ⟨fun x => by
    rw [q0_eq_sum, q0_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pr_frobE]; exact nrm_frPair _,
    Or.inr fun x => ext_pr fun i => by
      rw [pr_frobE, pr_theta0, pr_theta0, pr_theta0, pr_frobE]
      exact frPair_thPair _⟩

theorem theta0e_mem_gammaU : theta0e ∈ gammaU :=
  mem_gammaU.2 ⟨fun x => by
    rw [q0_eq_sum, q0_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [theta0e_apply, pr_theta0]; exact nrm_thPair _,
    Or.inl fun x => rfl⟩

theorem diagE_mul_theta0e (c : Fin 6 → ZMod 3) : diagE c * theta0e = theta0e * diagE c :=
  LinearEquiv.ext fun x => ext_pr fun i => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, theta0e_apply, theta0e_apply, pr_diagE,
      pr_theta0, pr_theta0, pr_diagE]
    exact omegaPow_thPair _ _

theorem permE_mul_theta0e (π : Equiv.Perm (Fin 6)) : permE π * theta0e = theta0e * permE π :=
  LinearEquiv.ext fun x => ext_pr fun i => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, theta0e_apply, theta0e_apply, pr_permE,
      pr_theta0, pr_theta0, pr_permE]

theorem diagE_mem_plane {i : Fin 6} {x : V12} (hx : x ∈ plane i) (c : Fin 6 → ZMod 3) :
    diagE c x ∈ plane i :=
  mem_plane_iff_pr.2 fun j hj => by
    rw [pr_diagE, mem_plane_iff_pr.1 hx j hj]
    exact omegaPow_zero_pair _

theorem permE_mem_plane {i : Fin 6} {x : V12} (hx : x ∈ plane i) (π : Equiv.Perm (Fin 6)) :
    permE π x ∈ plane (π i) :=
  mem_plane_iff_pr.2 fun j hj => by
    rw [pr_permE]
    exact mem_plane_iff_pr.1 hx _ fun h => hj (by rw [← h]; simp)

theorem frobE_mem_plane {i : Fin 6} {x : V12} (hx : x ∈ plane i) : frobE x ∈ plane i :=
  mem_plane_iff_pr.2 fun j hj => by
    rw [pr_frobE, mem_plane_iff_pr.1 hx j hj]
    rfl

theorem theta0_mem_plane {i : Fin 6} {x : V12} (hx : x ∈ plane i) : theta0 x ∈ plane i :=
  mem_plane_iff_pr.2 fun j hj => by
    rw [pr_theta0, mem_plane_iff_pr.1 hx j hj]
    rfl

theorem q0_eq_one_of_mem_plane {i : Fin 6} {x : V12} (hx : x ∈ plane i) (h0 : x ≠ 0) :
    q0 x = 1 := by
  rw [q0_eq_sum, Finset.sum_eq_single i]
  · exact nrm_eq_one _ fun h => h0 (eq_zero_of_mem_plane_of_pr hx h)
  · intro j _ hj
    rw [mem_plane_iff_pr.1 hx j hj]
    exact nrm_zero
  · intro h
    exact absurd (Finset.mem_univ i) h

namespace MonAux

theorem frobPow_zero : frobE ^ (0 : ZMod 2).val = 1 := pow_zero _

theorem frobPow_one : frobE ^ (1 : ZMod 2).val = frobE := pow_one _

theorem frobE_inv : frobE⁻¹ = frobE := inv_eq_of_mul_eq_one_right frobE_mul_self

theorem frobPow_inv (n : ℕ) : (frobE ^ n)⁻¹ = frobE ^ n := by rw [← inv_pow, frobE_inv]

theorem diagE_inv (c : Fin 6 → ZMod 3) : (diagE c)⁻¹ = diagE (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [← diagE_add, add_neg_cancel, diagE_zero])

theorem permE_inv (π : Equiv.Perm (Fin 6)) : (permE π)⁻¹ = permE π⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← permE_mul, mul_inv_cancel, permE_one])

theorem frobPow_mem_gammaU (n : ℕ) : frobE ^ n ∈ gammaU :=
  Subgroup.pow_mem _ frobE_mem_gammaU n

theorem frobPow_mem_plane {i : Fin 6} (n : ℕ) :
    ∀ {x : V12}, x ∈ plane i → (frobE ^ n) x ∈ plane i := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero]
    exact hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, LinearEquiv.mul_apply]
    exact ih (frobE_mem_plane hx)

theorem mon_mem_gammaU (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) (ε : ZMod 2) :
    diagE c * permE π * frobE ^ ε.val ∈ gammaU :=
  mul_mem (mul_mem (diagE_mem_gammaU c) (permE_mem_gammaU π)) (frobPow_mem_gammaU _)

theorem mon_mem_plane (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) (ε : ZMod 2) {i : Fin 6}
    {x : V12} (hx : x ∈ plane i) : (diagE c * permE π * frobE ^ ε.val) x ∈ plane (π i) := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact diagE_mem_plane (permE_mem_plane (frobPow_mem_plane _ hx) π) c

theorem mon_inv_mem_plane (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) (ε : ZMod 2) {i : Fin 6}
    {x : V12} (hx : x ∈ plane i) : (diagE c * permE π * frobE ^ ε.val)⁻¹ x ∈ plane (π⁻¹ i) := by
  rw [mul_inv_rev, mul_inv_rev, frobPow_inv, permE_inv, diagE_inv, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply]
  exact frobPow_mem_plane _ (permE_mem_plane (diagE_mem_plane hx _) _)

theorem exists_diag_perm_aux {g : G12} (hg : g ∈ gammaU) {π : Equiv.Perm (Fin 6)}
    (h : ∀ i, ∀ x ∈ plane i, g x ∈ plane (π i)) :
    ∃ (c : Fin 6 → ZMod 3) (ε : ZMod 2), g = diagE c * permE π * frobE ^ ε.val := by
  have hq : ∀ i, ∃ k : ZMod 3, g (pairVec i (1, 0)) = pairVec (π i) (omegaPow k (1, 0)) := by
    intro i
    have hmem := h i _ (pairVec_mem_plane i (1, 0))
    have hne : pr (g (pairVec i (1, 0))) (π i) ≠ 0 := by
      intro h0
      have h00 : pairVec i (1, 0) = 0 :=
        g.injective ((eq_zero_of_mem_plane_of_pr hmem h0).trans (map_zero g).symm)
      exact absurd (pairVec_eq_zero_iff.1 h00) (by decide)
    obtain ⟨k, hk⟩ := exists_omegaPow_of_ne_zero _ hne
    exact ⟨k, by rw [hk]; exact eq_pairVec_of_mem_plane hmem⟩
  choose cc hcc using hq
  have e01 : ((0 : ZMod 2), (1 : ZMod 2)) = thPair (1, 0) := by decide
  have f10 : frPair ((1 : ZMod 2), (0 : ZMod 2)) = (1, 0) := by decide
  have f01 : frPair ((0 : ZMod 2), (1 : ZMod 2)) = (1, 1) := by decide
  rcases (mem_gammaU.1 hg).2 with hu | hu
  · refine ⟨fun j => cc (π.symm j), 0, ext_pairVec (fun i => ?_) (fun i => ?_)⟩
    · rw [frobPow_zero, mul_one, LinearEquiv.mul_apply, permE_pairVec, diagE_pairVec,
        Equiv.symm_apply_apply, hcc]
    · have h1 : g (pairVec i (0, 1)) = pairVec (π i) (thPair (omegaPow (cc i) (1, 0))) := by
        rw [e01, ← theta0_pairVec, hu, hcc, theta0_pairVec]
      rw [h1, frobPow_zero, mul_one, LinearEquiv.mul_apply, permE_pairVec, diagE_pairVec,
        Equiv.symm_apply_apply, omegaPow_unit_hi]
  · refine ⟨fun j => cc (π.symm j), 1, ext_pairVec (fun i => ?_) (fun i => ?_)⟩
    · rw [frobPow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply, frobE_pairVec, f10,
        permE_pairVec, diagE_pairVec, Equiv.symm_apply_apply, hcc]
    · have h1 : g (pairVec i (0, 1)) =
          pairVec (π i) (thPair (thPair (omegaPow (cc i) (1, 0)))) := by
        rw [e01, ← theta0_pairVec, hu, hcc, theta0_pairVec, theta0_pairVec]
      rw [h1, frobPow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply, frobE_pairVec, f01,
        permE_pairVec, diagE_pairVec, Equiv.symm_apply_apply, omegaPow_one_one]

theorem mon_comm_theta0e (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) :
    theta0e * (diagE c * permE π) = diagE c * permE π * theta0e :=
  calc theta0e * (diagE c * permE π) = (theta0e * diagE c) * permE π := (mul_assoc _ _ _).symm
    _ = (diagE c * theta0e) * permE π := by rw [diagE_mul_theta0e]
    _ = diagE c * (theta0e * permE π) := mul_assoc _ _ _
    _ = diagE c * (permE π * theta0e) := by rw [permE_mul_theta0e]
    _ = diagE c * permE π * theta0e := (mul_assoc _ _ _).symm

theorem frobE_not_comm : frobE * theta0e ≠ theta0e * frobE := by
  intro h
  have h1 := congrArg (fun g : G12 => g (pairVec 0 (1, 0))) h
  simp only [LinearEquiv.mul_apply, theta0e_pairVec, frobE_pairVec] at h1
  exact absurd (pairVec_inj h1 (by decide)).2 (by decide)

theorem frobE_ne_one : frobE ≠ 1 := by
  intro h
  have h1 : frobE (pairVec 0 (0, 1)) = pairVec 0 (0, 1) := by rw [h]; rfl
  rw [frobE_pairVec] at h1
  exact absurd (pairVec_inj h1 (by decide)).2 (by decide)

theorem mon_inj {c c' : Fin 6 → ZMod 3} {π π' : Equiv.Perm (Fin 6)} {ε ε' : ZMod 2}
    (h : diagE c * permE π * frobE ^ ε.val = diagE c' * permE π' * frobE ^ ε'.val) :
    c = c' ∧ π = π' ∧ ε = ε' := by
  have hF : ∀ (e : ZMod 2) (i : Fin 6), (frobE ^ e.val) (pairVec i (1, 0)) = pairVec i (1, 0) := by
    intro e i
    rcases zmod2_cases e with rfl | rfl
    · rw [frobPow_zero]
      rfl
    · rw [frobPow_one, frobE_pairVec]
      rfl
  have key : ∀ i, π i = π' i ∧ omegaPow (c (π i)) (1, 0) = omegaPow (c' (π' i)) (1, 0) := by
    intro i
    have h1 := congrArg (fun g : G12 => g (pairVec i (1, 0))) h
    simp only [LinearEquiv.mul_apply, hF, permE_pairVec, diagE_pairVec] at h1
    exact pairVec_inj h1 (omegaPow_ne_zero _)
  have hπ : π = π' := Equiv.ext fun i => (key i).1
  subst hπ
  have hc : c = c' := by
    funext j
    have h2 := (key (π.symm j)).2
    rw [Equiv.apply_symm_apply] at h2
    exact omegaPow_injective_one _ _ h2
  subst hc
  refine ⟨rfl, rfl, ?_⟩
  have h2 := mul_left_cancel h
  rcases zmod2_cases ε with rfl | rfl <;> rcases zmod2_cases ε' with rfl | rfl
  · rfl
  · rw [frobPow_zero, frobPow_one] at h2
    exact absurd h2.symm frobE_ne_one
  · rw [frobPow_zero, frobPow_one] at h2
    exact absurd h2 frobE_ne_one
  · rfl

theorem diagE_eq_const_of_mem_plane {i : Fin 6} {x : V12} (hx : x ∈ plane i)
    (c : Fin 6 → ZMod 3) : diagE c x = diagE (fun _ => c i) x :=
  ext_pr fun j => by
    rw [pr_diagE, pr_diagE]
    by_cases hj : j = i
    · subst hj
      rfl
    · rw [mem_plane_iff_pr.1 hx j hj, omegaPow_zero_pair, omegaPow_zero_pair]

theorem g_diag_const {g : G12} (hg : g ∈ gammaU) : ∃ e : ZMod 3, ∀ (k : ZMod 3) (x : V12),
    g (diagE (fun _ => k) x) = diagE (fun _ => e * k) (g x) := by
  have h2 : diagE (fun _ => (2 : ZMod 3)) = theta0e * theta0e := by
    rw [← diagE_const_one, ← diagE_add]
    rfl
  have h0 : diagE (fun _ => (0 : ZMod 3)) = 1 := diagE_zero
  have hk3 : ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases (mem_gammaU.1 hg).2 with hu | hu
  · refine ⟨1, fun k x => ?_⟩
    rcases hk3 k with rfl | rfl | rfl
    · rw [one_mul, h0]
      rfl
    · rw [one_mul, diagE_const_one]
      exact hu x
    · rw [one_mul, h2]
      exact (hu (theta0 x)).trans (congrArg theta0 (hu x))
  · refine ⟨2, fun k x => ?_⟩
    rcases hk3 k with rfl | rfl | rfl
    · rw [mul_zero, h0]
      rfl
    · rw [mul_one, h2, diagE_const_one]
      exact hu x
    · have h4 : (2 : ZMod 3) * 2 = 1 := by decide
      rw [h4, diagE_const_one, h2]
      calc g (theta0 (theta0 x)) = theta0 (theta0 (g (theta0 x))) := hu (theta0 x)
        _ = theta0 (theta0 (theta0 (theta0 (g x)))) := by rw [hu x]
        _ = theta0 (g x) := theta0_theta0_theta0 (theta0 (g x))

theorem conj_mon_zero (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) (c' : Fin 6 → ZMod 3) :
    diagE c * permE π * diagE c' * (diagE c * permE π)⁻¹ = diagE (fun i => c' (π.symm i)) := by
  have h1 : diagE c * permE π * diagE c' * (diagE c * permE π)⁻¹ =
      diagE c * (permE π * diagE c' * (permE π)⁻¹) * (diagE c)⁻¹ := by group
  rw [h1, permE_mul_diagE_mul_inv, mul_inv_eq_iff_eq_mul, ← diagE_add, ← diagE_add, add_comm]

theorem conj_mon_one (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) (c' : Fin 6 → ZMod 3) :
    diagE c * permE π * frobE * diagE c' * (diagE c * permE π * frobE)⁻¹ =
      diagE (fun i => (-c') (π.symm i)) := by
  have h1 : diagE c * permE π * frobE * diagE c' * (diagE c * permE π * frobE)⁻¹ =
      diagE c * (permE π * (frobE * diagE c' * frobE⁻¹) * (permE π)⁻¹) * (diagE c)⁻¹ := by group
  rw [h1, frobE_mul_diagE_mul_inv, permE_mul_diagE_mul_inv, mul_inv_eq_iff_eq_mul, ← diagE_add,
    ← diagE_add, add_comm]

end MonAux

end CFSG.GF2Type.Smith1979.IdxFour
