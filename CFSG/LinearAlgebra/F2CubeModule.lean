module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankCount
public import CFSG.LinearAlgebra.F2QuadraticModule

public section

namespace CFSG.LinearAlgebra.F2Cube

abbrev C3 : Type := Fin 3 × Fin 3 × Fin 3

@[expose] def dot (f t : C3) : Fin 3 := f.1 * t.1 + f.2.1 * t.2.1 + f.2.2 * t.2.2

@[expose] def forms : Fin 13 → C3
  | 0 => (0, 0, 1)
  | 1 => (0, 1, 0)
  | 2 => (0, 1, 1)
  | 3 => (0, 1, 2)
  | 4 => (1, 0, 0)
  | 5 => (1, 0, 1)
  | 6 => (1, 0, 2)
  | 7 => (1, 1, 0)
  | 8 => (1, 1, 1)
  | 9 => (1, 1, 2)
  | 10 => (1, 2, 0)
  | 11 => (1, 2, 1)
  | 12 => (1, 2, 2)

@[expose] def allC3 : List C3 :=
  (List.finRange 3).flatMap fun a => (List.finRange 3).flatMap fun b =>
    (List.finRange 3).map fun c => (a, b, c)

theorem mem_allC3 (t : C3) : t ∈ allC3 := by
  revert t
  decide

theorem nodup_allC3 : allC3.Nodup := by decide

theorem sum_univ_eq_list {M : Type*} [AddCommMonoid M] (f : C3 → M) :
    ∑ s, f s = (allC3.map f).sum := by
  have h : (Finset.univ : Finset C3) = allC3.toFinset := by
    ext x
    simp [mem_allC3]
  rw [h, List.sum_toFinset f nodup_allC3]

@[expose] def indN (i : Fin 13) (t : C3) : ℕ := if dot (forms i) t = 0 then 1 else 0

@[expose] def conv (c c' : C3 → ℕ) (t : C3) : ℕ := ∑ s, c s * c' (t - s)

theorem conv_eq (c c' : C3 → ℕ) (t : C3) :
    conv c c' t = (allC3.map fun s => c s * c' (t - s)).sum := sum_univ_eq_list _

theorem conv_ind : ∀ i j : Fin 13, ∀ t : C3,
    conv (indN i) (indN j) t % 2 = if i = j then indN i t else 1 := by
  intro i j t
  rw [conv_eq]
  revert i j t
  decide +kernel

theorem indN_lt (i : Fin 13) (t : C3) : indN i t < 2 := by
  unfold indN
  split_ifs <;> decide

theorem sum_indN : ∀ t : C3, (∑ i, indN i t) % 2 = if t = 0 then 1 else 0 := by decide +kernel

theorem indN_sub : ∀ (i : Fin 13) (g t : C3), dot (forms i) g = 0 → indN i (t - g) = indN i t := by
  decide +kernel

@[expose] def delta (g t : C3) : ℕ := if t = g then 1 else 0

@[expose] def lineN (g t : C3) : ℕ := if t = 0 ∨ t = g ∨ t = g + g then 1 else 0

theorem lineN_eq_delta : ∀ g : C3, g ≠ 0 → ∀ t : C3,
    lineN g t = delta 0 t + delta g t + delta (g + g) t := by
  decide +kernel

theorem triple_eq_zero : ∀ g : C3, g + g + g = 0 := by decide

theorem sum_indN_filter : ∀ g : C3, g ≠ 0 → ∀ t : C3,
    (∑ i ∈ Finset.univ.filter fun i : Fin 13 => dot (forms i) g = 0, indN i t) % 2 =
      (1 + lineN g t) % 2 := by
  decide +kernel

theorem card_hyperplane : ∀ i : Fin 13,
    (Finset.univ.filter fun g : C3 => g ≠ 0 ∧ dot (forms i) g = 0).card = 8 := by decide +kernel

theorem card_hyperplane_inter : ∀ i φ : Fin 13,
    ((Finset.univ.filter fun g : C3 => g ≠ 0 ∧ dot (forms i) g = 0).filter
      fun g => dot (forms φ) g = 0).card = if φ = i then 8 else 2 := by decide +kernel

theorem linesum_closed (x : Fin 13 → ℕ) (i : Fin 13) :
    ∑ g ∈ Finset.univ.filter (fun g : C3 => g ≠ 0 ∧ dot (forms i) g = 0),
      ∑ φ ∈ Finset.univ.filter (fun φ : Fin 13 => dot (forms φ) g = 0), x φ =
    2 * ∑ φ, x φ + 6 * x i := by
  have h1 : ∀ g : C3, ∑ φ ∈ Finset.univ.filter (fun φ : Fin 13 => dot (forms φ) g = 0), x φ =
      ∑ φ, if dot (forms φ) g = 0 then x φ else 0 := fun g => by
    rw [Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ φ : Fin 13, ∑ g ∈ Finset.univ.filter (fun g : C3 => g ≠ 0 ∧ dot (forms i) g = 0),
      (if dot (forms φ) g = 0 then x φ else 0) = (if φ = i then 8 else 2) * x φ := by
    intro φ
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, card_hyperplane_inter i φ]
  simp_rw [h2]
  have h3 : ∀ φ : Fin 13, (if φ = i then 8 else 2) * x φ =
      2 * x φ + (if φ = i then 6 * x φ else 0) := fun φ => by
    split_ifs <;> ring
  simp_rw [h3]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ i]
  simp

theorem c_unique (x y : Fin 13 → ℕ)
    (h : ∀ g : C3, g ≠ 0 →
      ∑ i ∈ Finset.univ.filter (fun i : Fin 13 => dot (forms i) g = 0), x i =
        ∑ i ∈ Finset.univ.filter (fun i : Fin 13 => dot (forms i) g = 0), y i)
    (hs : ∑ i, x i = ∑ i, y i) : x = y := by
  funext i
  have h1 := linesum_closed x i
  have h2 := linesum_closed y i
  have h3 : ∑ g ∈ Finset.univ.filter (fun g : C3 => g ≠ 0 ∧ dot (forms i) g = 0),
      ∑ φ ∈ Finset.univ.filter (fun φ : Fin 13 => dot (forms φ) g = 0), x φ =
      ∑ g ∈ Finset.univ.filter (fun g : C3 => g ≠ 0 ∧ dot (forms i) g = 0),
      ∑ φ ∈ Finset.univ.filter (fun φ : Fin 13 => dot (forms φ) g = 0), y φ :=
    Finset.sum_congr rfl fun g hg => h g (Finset.mem_filter.1 hg).2.1
  omega

theorem sum_lines (f : Fin 13 → ℕ) :
    ∑ g ∈ Finset.univ.filter (fun g : C3 => g ≠ 0),
      ∑ i ∈ Finset.univ.filter (fun i : Fin 13 => dot (forms i) g = 0), f i = 8 * ∑ i, f i := by
  have h1 : ∀ g : C3, ∑ i ∈ Finset.univ.filter (fun i : Fin 13 => dot (forms i) g = 0), f i =
      ∑ i, if dot (forms i) g = 0 then f i else 0 := fun g => by
    rw [Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have : (Finset.univ.filter fun g : C3 => g ≠ 0).filter (fun g => dot (forms i) g = 0) =
      Finset.univ.filter (fun g : C3 => g ≠ 0 ∧ dot (forms i) g = 0) := by
    ext g
    simp
  rw [this, card_hyperplane i]

@[expose] def gen : Fin 13 → C3
  | 0 => (0, 0, 1)
  | 1 => (0, 1, 0)
  | 2 => (0, 1, 0)
  | 3 => (0, 1, 0)
  | 4 => (1, 0, 0)
  | 5 => (1, 0, 0)
  | 6 => (1, 0, 0)
  | 7 => (1, 0, 0)
  | 8 => (1, 0, 0)
  | 9 => (1, 0, 0)
  | 10 => (1, 0, 0)
  | 11 => (1, 0, 0)
  | 12 => (1, 0, 0)

theorem gen_ne_zero : ∀ i : Fin 13, gen i ≠ 0 := by decide

theorem dot_sub_gen : ∀ (i : Fin 13) (t : C3),
    dot (forms i) (t - (dot (forms i) t).val • gen i) = 0 := by decide +kernel

theorem conv_line_ind : ∀ (i : Fin 13) (t : C3), conv (lineN (gen i)) (indN i) t % 2 = 1 := by
  intro i t
  rw [conv_eq]
  revert i t
  decide +kernel

section Assemble

variable {K W W' ι : Type*} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W']
  [Module K W'] [Fintype ι] [DecidableEq ι]

theorem sum_comp_sum (π : ι → Module.End K W) (π' : ι → Module.End K W') (F : ι → W →ₗ[K] W')
    (G : ι → W' →ₗ[K] W) (hπ0' : ∀ i j, i ≠ j → π' i * π' j = 0) (hs : ∑ i, π i = 1)
    (hFb : ∀ i w, π' i (F i w) = F i w) (hGa : ∀ i w, G i (π' i w) = G i w)
    (hGF : ∀ i w, G i (F i w) = π i w) (w : W) :
    (∑ j, G j) ((∑ i, F i) w) = w := by
  have h1 : ∀ i j, G j (F i w) = if i = j then π i w else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hGF]
    · have h2 : π' j (F i w) = 0 := by
        have h3 := congrArg (fun f : Module.End K W' => f (F i w)) (hπ0' j i (Ne.symm hij))
        simp only [Module.End.mul_apply, LinearMap.zero_apply] at h3
        rw [hFb] at h3
        exact h3
      rw [if_neg hij, ← hGa j (F i w), h2, map_zero]
  simp only [LinearMap.sum_apply, map_sum, h1]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h4 := congrArg (fun f : Module.End K W => f w) hs
  simpa only [LinearMap.sum_apply, Module.End.one_apply] using h4

end Assemble

section Rep

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

structure CubeRep (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] where
  toFun : C3 → Module.End (ZMod 2) W
  map_zero : toFun 0 = 1
  map_add : ∀ s t, toFun (s + t) = toFun s * toFun t

instance : CoeFun (CubeRep W) (fun _ => C3 → Module.End (ZMod 2) W) := ⟨CubeRep.toFun⟩

variable (ρ : CubeRep W)

@[expose] def CubeRep.eval (c : C3 → ℕ) : Module.End (ZMod 2) W := ∑ t, c t • ρ t

theorem CubeRep.comm (s t : C3) : ρ s * ρ t = ρ t * ρ s := by
  rw [← ρ.map_add, ← ρ.map_add, add_comm]

theorem nsmul_two_eq_zero {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    (2 : ℕ) • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  have h : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h, zero_smul]

theorem nsmul_mod_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (n : ℕ) (x : M) :
    n • x = (n % 2) • x := by
  conv_lhs => rw [← Nat.mod_add_div n 2, add_smul, mul_smul, nsmul_two_eq_zero, add_zero]

theorem CubeRep.eval_congr {c c' : C3 → ℕ} (h : ∀ t, c t % 2 = c' t % 2) :
    ρ.eval c = ρ.eval c' := by
  unfold CubeRep.eval
  apply Finset.sum_congr rfl
  intro t _
  rw [nsmul_mod_two (c t), h t, ← nsmul_mod_two]

theorem CubeRep.eval_add (c c' : C3 → ℕ) : ρ.eval (c + c') = ρ.eval c + ρ.eval c' := by
  unfold CubeRep.eval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [Pi.add_apply, add_smul]

theorem CubeRep.eval_sum {ι : Type*} (I : Finset ι) (c : ι → C3 → ℕ) :
    ρ.eval (fun t => ∑ i ∈ I, c i t) = ∑ i ∈ I, ρ.eval (c i) := by
  unfold CubeRep.eval
  simp_rw [Finset.sum_smul]
  exact Finset.sum_comm

theorem CubeRep.eval_mul (c c' : C3 → ℕ) : ρ.eval c * ρ.eval c' = ρ.eval (conv c c') := by
  have h1 : ρ.eval c * ρ.eval c' = ∑ s, ∑ u, (c s * c' u) • ρ (s + u) := by
    unfold CubeRep.eval
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro u _
    rw [smul_mul_smul_comm, ← ρ.map_add]
  have h2 : ρ.eval (conv c c') = ∑ s, ∑ u, (c s * c' u) • ρ (s + u) := by
    unfold CubeRep.eval conv
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    refine (Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun u => ?_)).symm
    simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [h1, h2]

theorem CubeRep.eval_delta (g : C3) : ρ.eval (delta g) = ρ g := by
  unfold CubeRep.eval delta
  simp [ite_smul]

theorem conv_delta (g : C3) (c : C3 → ℕ) (t : C3) : conv (delta g) c t = c (t - g) := by
  unfold conv delta
  simp

theorem CubeRep.mul_eval (g : C3) (c : C3 → ℕ) : ρ g * ρ.eval c = ρ.eval (fun t => c (t - g)) := by
  have h := ρ.eval_mul (delta g) c
  rw [ρ.eval_delta] at h
  rw [h, show conv (delta g) c = fun t => c (t - g) from funext (conv_delta g c)]

theorem CubeRep.eval_comm (g : C3) (c : C3 → ℕ) : ρ g * ρ.eval c = ρ.eval c * ρ g := by
  unfold CubeRep.eval
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_smul_comm, smul_mul_assoc, ρ.comm]

@[expose] def CubeRep.pi (i : Fin 13) : Module.End (ZMod 2) W := ρ.eval (indN i)

@[expose] def CubeRep.eps : Module.End (ZMod 2) W := ρ.eval fun _ => 1

theorem CubeRep.mul_eps (g : C3) : ρ g * ρ.eps = ρ.eps := by
  unfold CubeRep.eps
  rw [ρ.mul_eval]

theorem CubeRep.eps_eq_zero (h : ∀ v : W, (∀ t, ρ t v = v) → v = 0) : ρ.eps = 0 := by
  ext v
  apply h
  intro t
  have h1 := congrArg (fun f : Module.End (ZMod 2) W => f v) (ρ.mul_eps t)
  simpa only [Module.End.mul_apply] using h1

theorem CubeRep.pi_mul_pi (i j : Fin 13) :
    ρ.pi i * ρ.pi j = if i = j then ρ.pi i else ρ.eps := by
  unfold CubeRep.pi CubeRep.eps
  rw [ρ.eval_mul]
  split_ifs with h
  · apply ρ.eval_congr
    intro t
    have h1 := conv_ind i j t
    rw [if_pos h] at h1
    rw [h1, Nat.mod_eq_of_lt (indN_lt i t)]
  · apply ρ.eval_congr
    intro t
    have h1 := conv_ind i j t
    rw [if_neg h] at h1
    rw [h1]

theorem CubeRep.sum_pi : ∑ i, ρ.pi i = 1 := by
  unfold CubeRep.pi
  rw [← ρ.eval_sum]
  have h : ρ.eval (delta 0) = 1 := by rw [ρ.eval_delta, ρ.map_zero]
  rw [← h]
  apply ρ.eval_congr
  intro t
  rw [sum_indN t]
  unfold delta
  split_ifs <;> simp

theorem CubeRep.pi_comm (g : C3) (i : Fin 13) : ρ g * ρ.pi i = ρ.pi i * ρ g := ρ.eval_comm g _

theorem CubeRep.mul_pi (g : C3) (i : Fin 13) (h : dot (forms i) g = 0) :
    ρ g * ρ.pi i = ρ.pi i := by
  unfold CubeRep.pi
  rw [ρ.mul_eval, show (fun t => indN i (t - g)) = indN i from funext fun t => indN_sub i g t h]

theorem CubeRep.pow_three (g : C3) : ρ g ^ 3 = 1 := by
  rw [pow_succ, pow_two, ← ρ.map_add, ← ρ.map_add, triple_eq_zero, ρ.map_zero]

theorem CubeRep.eval_lineN {g : C3} (hg : g ≠ 0) : ρ.eval (lineN g) = 1 + ρ g + ρ g ^ 2 := by
  have h1 : ρ.eval (lineN g) = ρ.eval (delta 0 + delta g + delta (g + g)) := by
    apply ρ.eval_congr
    intro t
    rw [lineN_eq_delta g hg t]
    rfl
  rw [h1, ρ.eval_add, ρ.eval_add, ρ.eval_delta, ρ.eval_delta, ρ.eval_delta, ρ.map_zero,
    ρ.map_add, pow_two]

theorem CubeRep.sum_pi_filter {g : C3} (hg : g ≠ 0) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin 13 => dot (forms i) g = 0), ρ.pi i =
      ρ.eps + (1 + ρ g + ρ g ^ 2) := by
  unfold CubeRep.pi CubeRep.eps
  rw [← ρ.eval_sum, ← ρ.eval_lineN hg, ← ρ.eval_add]
  apply ρ.eval_congr
  intro t
  rw [sum_indN_filter g hg t]
  simp [Pi.add_apply]

theorem CubeRep.pi_idem (i : Fin 13) : ρ.pi i * ρ.pi i = ρ.pi i := by
  rw [ρ.pi_mul_pi, if_pos rfl]

theorem CubeRep.pi_orth (hε : ρ.eps = 0) {i j : Fin 13} (h : i ≠ j) : ρ.pi i * ρ.pi j = 0 := by
  rw [ρ.pi_mul_pi, if_neg h, hε]

open CFSG.StandardType.D4Rank in
theorem CubeRep.fixDim_eq_sum [FiniteDimensional (ZMod 2) W] (hε : ρ.eps = 0) {g : C3}
    (hg : g ≠ 0) :
    fixDim (ρ g) = ∑ i ∈ Finset.univ.filter (fun i : Fin 13 => dot (forms i) g = 0),
      rk (ρ.pi i) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h1 : fixDim (ρ g) = rk (fp (ρ g)) := by
    unfold rk fixDim
    rw [range_fixProj h2 (ρ.pow_three g)]
  have h3 : fp (ρ g) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin 13 => dot (forms i) g = 0), ρ.pi i := by
    rw [ρ.sum_pi_filter hg, hε, zero_add]
  rw [h1, h3]
  exact rk_sum_of_orth _ ρ.pi (fun i _ => ρ.pi_idem i)
    (fun i _ j _ hij => ρ.pi_orth hε hij)

open CFSG.StandardType.D4Rank in
theorem CubeRep.finrank_eq_sum [FiniteDimensional (ZMod 2) W] (hε : ρ.eps = 0) :
    Module.finrank (ZMod 2) W = ∑ i, rk (ρ.pi i) := by
  have h := rk_sum_of_orth Finset.univ ρ.pi (fun i _ => ρ.pi_idem i)
    (fun i _ j _ hij => ρ.pi_orth hε hij)
  rw [ρ.sum_pi] at h
  rw [← h]
  unfold rk
  rw [Module.End.one_eq_id, LinearMap.range_id, finrank_top]

theorem CubeRep.map_nsmul (g : C3) (n : ℕ) : ρ (n • g) = ρ g ^ n := by
  induction n with
  | zero => rw [zero_smul, ρ.map_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, ρ.map_add, ih, pow_succ]

theorem CubeRep.line_mul_pi (i : Fin 13) :
    (1 + ρ (gen i) + ρ (gen i) ^ 2) * ρ.pi i = ρ.eps := by
  rw [← ρ.eval_lineN (gen_ne_zero i)]
  unfold CubeRep.pi CubeRep.eps
  rw [ρ.eval_mul]
  apply ρ.eval_congr
  intro t
  rw [conv_line_ind i t]

theorem CubeRep.mul_pi_pow (i : Fin 13) (t : C3) :
    ρ t * ρ.pi i = ρ (gen i) ^ (dot (forms i) t).val * ρ.pi i := by
  have h1 : t = (dot (forms i) t).val • gen i + (t - (dot (forms i) t).val • gen i) := by
    rw [add_sub_cancel]
  have h2 : ρ t = ρ ((dot (forms i) t).val • gen i) * ρ (t - (dot (forms i) t).val • gen i) := by
    conv_lhs => rw [h1, ρ.map_add]
  rw [h2, mul_assoc, ρ.mul_pi _ i (dot_sub_gen i t), ρ.map_nsmul]

theorem CubeRep.mul_pi_apply (t : C3) (i : Fin 13) (w : W) : ρ t (ρ.pi i w) = ρ.pi i (ρ t w) := by
  have h := congrArg (fun f : Module.End (ZMod 2) W => f w) (ρ.pi_comm t i)
  simpa only [Module.End.mul_apply] using h

@[expose] def CubeRep.restr (i : Fin 13) (t : C3) :
    Module.End (ZMod 2) ↥(LinearMap.range (ρ.pi i)) :=
  (ρ t).restrict (p := LinearMap.range (ρ.pi i)) (q := LinearMap.range (ρ.pi i))
    (fun v hv => by
      obtain ⟨w, rfl⟩ := hv
      exact ⟨ρ t w, (ρ.mul_pi_apply t i w).symm⟩)

theorem CubeRep.coe_restr (i : Fin 13) (t : C3) (v : ↥(LinearMap.range (ρ.pi i))) :
    ((ρ.restr i t v : ↥(LinearMap.range (ρ.pi i))) : W) = ρ t v := rfl

theorem CubeRep.mem_range_pi {i : Fin 13} {v : W} (hv : v ∈ LinearMap.range (ρ.pi i)) :
    ρ.pi i v = v := by
  obtain ⟨w, rfl⟩ := hv
  rw [← Module.End.mul_apply, ρ.pi_idem]

theorem CubeRep.restr_quad (hε : ρ.eps = 0) (i : Fin 13) :
    ρ.restr i (gen i) * ρ.restr i (gen i) + ρ.restr i (gen i) + 1 = 0 := by
  ext v
  have h1 := congrArg (fun f : Module.End (ZMod 2) W => f (v : W)) (ρ.line_mul_pi i)
  simp only [Module.End.mul_apply, hε, LinearMap.add_apply, Module.End.one_apply, pow_two,
    LinearMap.zero_apply] at h1
  rw [ρ.mem_range_pi v.2] at h1
  have h2 : ρ (gen i) (ρ (gen i) (v : W)) + ρ (gen i) (v : W) + (v : W) = 0 := by
    rw [← h1]
    abel
  simpa [CubeRep.restr] using h2

theorem CubeRep.restr_pow (i : Fin 13) (t : C3) :
    ρ.restr i t = ρ.restr i (gen i) ^ (dot (forms i) t).val := by
  have h1 : ∀ (n : ℕ) (v : ↥(LinearMap.range (ρ.pi i))),
      (((ρ.restr i (gen i) ^ n) v : ↥(LinearMap.range (ρ.pi i))) : W) = (ρ (gen i) ^ n) v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ih, ρ.coe_restr]
  ext v
  rw [h1, ρ.coe_restr]
  obtain ⟨w, hw⟩ := v.2
  have h2 := congrArg (fun f : Module.End (ZMod 2) W => f w) (ρ.mul_pi_pow i t)
  simp only [Module.End.mul_apply] at h2
  rw [← hw]
  exact h2

variable {W' : Type*} [AddCommGroup W'] [Module (ZMod 2) W']

open CFSG.StandardType.D4Rank in
theorem CubeRep.sum_fixDim [FiniteDimensional (ZMod 2) W] (hε : ρ.eps = 0) :
    ∑ g ∈ Finset.univ.filter (fun g : C3 => g ≠ 0), fixDim (ρ g) =
      8 * Module.finrank (ZMod 2) W := by
  rw [Finset.sum_congr rfl (fun g hg => ρ.fixDim_eq_sum hε (Finset.mem_filter.1 hg).2),
    sum_lines (fun i => rk (ρ.pi i)), ρ.finrank_eq_sum hε]

theorem CubeRep.exists_piece [FiniteDimensional (ZMod 2) W] [FiniteDimensional (ZMod 2) W']
    (σ : CubeRep W') (hρ : ρ.eps = 0) (hσ : σ.eps = 0) (i : Fin 13)
    (hr : Module.finrank (ZMod 2) ↥(LinearMap.range (ρ.pi i)) =
      Module.finrank (ZMod 2) ↥(LinearMap.range (σ.pi i))) :
    ∃ F : W →ₗ[ZMod 2] W', ∃ G : W' →ₗ[ZMod 2] W,
      (∀ w, F (ρ.pi i w) = F w) ∧ (∀ w, σ.pi i (F w) = F w) ∧
      (∀ w, G (σ.pi i w) = G w) ∧ (∀ w, ρ.pi i (G w) = G w) ∧
      (∀ w, G (F w) = ρ.pi i w) ∧ (∀ w, F (G w) = σ.pi i w) ∧
      ∀ t w, F (ρ t w) = σ t (F w) := by
  obtain ⟨e, he⟩ := CFSG.LinearAlgebra.F2Quadratic.exists_equiv_of_quadratic
    (ρ.restr i (gen i)) (σ.restr i (gen i)) (ρ.restr_quad hρ i) (σ.restr_quad hσ i) hr
  have hpow : ∀ (n : ℕ) (v : ↥(LinearMap.range (ρ.pi i))),
      e ((ρ.restr i (gen i) ^ n) v) = (σ.restr i (gen i) ^ n) (e v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, he, pow_succ, Module.End.mul_apply]
  have hrestr : ∀ (t : C3) (v : ↥(LinearMap.range (ρ.pi i))),
      e (ρ.restr i t v) = σ.restr i t (e v) := by
    intro t v
    rw [ρ.restr_pow i t, σ.restr_pow i t, hpow]
  have hidem : ∀ w, ρ.pi i (ρ.pi i w) = ρ.pi i w := by
    intro w
    have h := congrArg (fun f : Module.End (ZMod 2) W => f w) (ρ.pi_idem i)
    simpa only [Module.End.mul_apply] using h
  have hidem' : ∀ w, σ.pi i (σ.pi i w) = σ.pi i w := by
    intro w
    have h := congrArg (fun f : Module.End (ZMod 2) W' => f w) (σ.pi_idem i)
    simpa only [Module.End.mul_apply] using h
  obtain ⟨F, hF⟩ : ∃ F : W →ₗ[ZMod 2] W', ∀ w,
      F w = ((e ⟨ρ.pi i w, ⟨w, rfl⟩⟩ : ↥(LinearMap.range (σ.pi i))) : W') :=
    ⟨(LinearMap.range (σ.pi i)).subtype ∘ₗ (e : _ →ₗ[ZMod 2] _) ∘ₗ (ρ.pi i).rangeRestrict,
      fun w => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : W' →ₗ[ZMod 2] W, ∀ w,
      G w = ((e.symm ⟨σ.pi i w, ⟨w, rfl⟩⟩ : ↥(LinearMap.range (ρ.pi i))) : W) :=
    ⟨(LinearMap.range (ρ.pi i)).subtype ∘ₗ (e.symm : _ →ₗ[ZMod 2] _) ∘ₗ (σ.pi i).rangeRestrict,
      fun w => rfl⟩
  have hFr : ∀ w, σ.pi i (F w) = F w := fun w => by
    rw [hF]
    exact σ.mem_range_pi (e _).2
  have hGr : ∀ w, ρ.pi i (G w) = G w := fun w => by
    rw [hG]
    exact ρ.mem_range_pi (e.symm _).2
  refine ⟨F, G, fun w => ?_, hFr, fun w => ?_, hGr, fun w => ?_, fun w => ?_, fun t w => ?_⟩
  · rw [hF, hF]
    exact congrArg (fun x : ↥(LinearMap.range (ρ.pi i)) =>
      ((e x : ↥(LinearMap.range (σ.pi i))) : W')) (Subtype.ext (hidem w))
  · rw [hG, hG]
    exact congrArg (fun x : ↥(LinearMap.range (σ.pi i)) =>
      ((e.symm x : ↥(LinearMap.range (ρ.pi i))) : W)) (Subtype.ext (hidem' w))
  · have h3 : (⟨σ.pi i (F w), ⟨F w, rfl⟩⟩ : ↥(LinearMap.range (σ.pi i))) =
        e ⟨ρ.pi i w, ⟨w, rfl⟩⟩ := Subtype.ext ((hFr w).trans (hF w))
    rw [hG, h3, e.symm_apply_apply]
  · have h3 : (⟨ρ.pi i (G w), ⟨G w, rfl⟩⟩ : ↥(LinearMap.range (ρ.pi i))) =
        e.symm ⟨σ.pi i w, ⟨w, rfl⟩⟩ := Subtype.ext ((hGr w).trans (hG w))
    rw [hF, h3, e.apply_symm_apply]
  · have h3 : (⟨ρ.pi i (ρ t w), ⟨ρ t w, rfl⟩⟩ : ↥(LinearMap.range (ρ.pi i))) =
        ρ.restr i t ⟨ρ.pi i w, ⟨w, rfl⟩⟩ := Subtype.ext (ρ.mul_pi_apply t i w).symm
    rw [hF, hF, h3, hrestr, σ.coe_restr]

open CFSG.StandardType.D4Rank in
theorem CubeRep.exists_equiv [FiniteDimensional (ZMod 2) W] [FiniteDimensional (ZMod 2) W']
    (σ : CubeRep W') (hρ : ρ.eps = 0) (hσ : σ.eps = 0)
    (hdim : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) W')
    (hfix : ∀ g : C3, g ≠ 0 → fixDim (ρ g) = fixDim (σ g)) :
    ∃ e : W ≃ₗ[ZMod 2] W', ∀ t w, e (ρ t w) = σ t (e w) := by
  have hrk : ∀ i, rk (ρ.pi i) = rk (σ.pi i) := by
    have h := c_unique (fun i => rk (ρ.pi i)) (fun i => rk (σ.pi i))
      (fun g hg => by
        rw [← ρ.fixDim_eq_sum hρ hg, ← σ.fixDim_eq_sum hσ hg]
        exact hfix g hg)
      (by rw [← ρ.finrank_eq_sum hρ, ← σ.finrank_eq_sum hσ]; exact hdim)
    exact fun i => congrFun h i
  choose F G hFa hFb hGa hGb hGF hFG hFt using fun i => ρ.exists_piece σ hρ hσ i (hrk i)
  have hπ0 : ∀ i j, i ≠ j → ρ.pi i * ρ.pi j = 0 := fun i j h => ρ.pi_orth hρ h
  have hπ0' : ∀ i j, i ≠ j → σ.pi i * σ.pi j = 0 := fun i j h => σ.pi_orth hσ h
  have h1 := sum_comp_sum ρ.pi σ.pi F G hπ0' ρ.sum_pi hFb hGa hGF
  have h2 := sum_comp_sum σ.pi ρ.pi G F hπ0 σ.sum_pi hGb hFa hFG
  refine ⟨LinearEquiv.ofLinear (∑ i, F i) (∑ i, G i) (LinearMap.ext h2) (LinearMap.ext h1),
    fun t w => ?_⟩
  show (∑ i, F i) (ρ t w) = σ t ((∑ i, F i) w)
  simp only [LinearMap.sum_apply, map_sum, hFt]

end Rep

end CFSG.LinearAlgebra.F2Cube
