module

public import CFSG.LargeExtraspecial.AS35ZSStab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap Matrix
open CFSG.Blueprint.Fischer (K)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem mat_two_spec : ∀ M N : Matrix (Fin 2) (Fin 2) (ZMod 2), M * M * M = 1 →
    N * N * N = 1 → N * (M * M) * N = M → M = N := by
  decide

theorem eq_on_plane {A : Submodule (ZMod 2) V} (hA : finrank (ZMod 2) A = 2)
    {α β : V →ₗ[ZMod 2] V} (hαA : ∀ a ∈ A, α a ∈ A) (hβA : ∀ a ∈ A, β a ∈ A)
    (hα3 : ∀ a ∈ A, α (α (α a)) = a) (hβ3 : ∀ a ∈ A, β (β (β a)) = a)
    (hγ : ∀ a ∈ A, β (α (α (β a))) = α a) : ∀ a ∈ A, α a = β a := by
  set b := Module.finBasisOfFinrankEq (ZMod 2) A hA
  set fα : A →ₗ[ZMod 2] A := α.restrict hαA
  set fβ : A →ₗ[ZMod 2] A := β.restrict hβA
  have hfα : fα ∘ₗ fα ∘ₗ fα = LinearMap.id := LinearMap.ext fun a => Subtype.ext (hα3 a a.2)
  have hfβ : fβ ∘ₗ fβ ∘ₗ fβ = LinearMap.id := LinearMap.ext fun a => Subtype.ext (hβ3 a a.2)
  have hfγ : fβ ∘ₗ (fα ∘ₗ fα) ∘ₗ fβ = fα := LinearMap.ext fun a => Subtype.ext (hγ a a.2)
  have key := mat_two_spec (LinearMap.toMatrix b b fα) (LinearMap.toMatrix b b fβ)
    (by rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, LinearMap.comp_assoc, hfα,
      LinearMap.toMatrix_id])
    (by rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, LinearMap.comp_assoc, hfβ,
      LinearMap.toMatrix_id])
    (by rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp,
      LinearMap.comp_assoc, hfγ])
  have heq : fα = fβ := (LinearMap.toMatrix b b).injective key
  intro a ha
  have := congrArg (fun f : A →ₗ[ZMod 2] A => (f ⟨a, ha⟩ : V)) heq
  exact this

variable {n : ℕ}

@[expose] noncomputable def diagSU (d : Fin n → K) (hd : ∀ i, frob (d i) * d i = 1)
    (hdet : ∏ i, d i = 1) : SUid frob n :=
  mkSU frob (Matrix.diagonal d) (by rw [Matrix.det_diagonal]; exact hdet) (fun x y => by
    simp only [herm_def, Matrix.mulVec_diagonal, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show frob (d i) * frob (x i) * (d i * y i) = (frob (d i) * d i) * (frob (x i) * y i) by
      ring, hd, one_mul])

theorem diagSU_smul (d : Fin n → K) (hd : ∀ i, frob (d i) * d i = 1) (hdet : ∏ i, d i = 1)
    (v : Fin n → K) : diagSU d hd hdet • v = fun i => d i * v i := by
  rw [diagSU, mkSU_smul]
  funext i
  rw [Matrix.mulVec_diagonal]

noncomputable abbrev sd (n : ℕ) : Fin n → K := fun i => if (i : ℕ) < 3 then ω else 1

theorem frob_sd (i : Fin n) : frob (sd n i) * sd n i = 1 := by
  simp only [sd]
  split_ifs
  · exact frob_mul_self omega_ne_zero
  · rw [map_one, one_mul]

theorem prod_sd (hn : 3 ≤ n) : ∏ i, sd n i = 1 := by
  have e : ∏ i : Fin n, sd n i = ∏ i ∈ Finset.range n, (if i < 3 then ω else 1) :=
    Fin.prod_univ_eq_prod_range (fun i => if i < 3 then ω else 1) n
  have h2 : ∏ i ∈ Finset.Ico 3 n, (if i < 3 then ω else (1 : K)) = 1 :=
    Finset.prod_eq_one fun i hi => by
      rw [Finset.mem_Ico] at hi
      simp [show ¬ i < 3 by omega]
  have h3 : ω * ω * ω = 1 := by
    have := frob_mul_self omega_ne_zero
    rw [frob_omega] at this
    have e2 : ω * ω = ω + 1 := by rw [← frob_omega, frob_apply, _root_.sq]
    linear_combination ω * e2 + this
  rw [e, ← Finset.prod_range_mul_prod_Ico _ hn, h2, mul_one]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  simpa using h3

@[expose] noncomputable def s₀ (hn : 3 ≤ n) : SUid frob n := diagSU (sd n) frob_sd (prod_sd hn)

theorem s₀_smul (hn : 3 ≤ n) (v : Fin n → K) : s₀ hn • v = fun i => sd n i * v i :=
  diagSU_smul _ _ _ v

theorem s₀_cube (hn : 3 ≤ n) : s₀ hn ^ 3 = 1 := by
  refine ext_smul _ fun v => ?_
  rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul, s₀_smul, s₀_smul, s₀_smul, one_smul]
  funext i
  simp only [sd]
  split_ifs
  · have := frob_mul_self omega_ne_zero
    rw [frob_omega] at this
    have e2 : ω * ω = ω + 1 := by rw [← frob_omega, frob_apply, _root_.sq]
    linear_combination (ω * v i) * e2 + v i * this
  · ring

theorem s₀_smul_of_supp {m : ℕ} (hn : 3 ≤ m + 2) {v : Fin (m + 2) → K}
    (hv : ∀ i : Fin m, v i.succ.succ = 0) : s₀ hn • v = ω • v := by
  rw [s₀_smul]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, sd]
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
    cases j using Fin.cases with
    | zero => simp
    | succ k => rw [hv k, mul_zero, mul_zero]

theorem s₀_smul_v₀ {m : ℕ} (hn : 3 ≤ m + 2) : s₀ hn • v₀ m = ω • v₀ m :=
  s₀_smul_of_supp hn fun i => wd.hypA_succ_succ i

theorem s₀_smul_u₀ {m : ℕ} (hn : 3 ≤ m + 2) : s₀ hn • u₀ m = ω • u₀ m :=
  s₀_smul_of_supp hn fun i => wd.hypB_succ_succ i

theorem exists_s_pair (hn : 3 ≤ n) {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy : herm frob y y = 0) (hxy : herm frob x y ≠ 0) :
    ∃ s : SUid frob n, s ^ 3 = 1 ∧ s • x = ω • x ∧ s • y = ω • y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set y' := (herm frob x y)⁻¹ • y with hy'
  have hy'y' : herm frob y' y' = 0 := herm_smul_smul_self hy _
  have hxy' : herm frob x y' = 1 := by rw [hy', herm_smul_right, inv_mul_cancel₀ hxy]
  obtain ⟨g, hgx, hgy⟩ := exists_smul_eq_hyp (n := m) (by omega) hx0 hx hy'y' hxy'
  refine ⟨g⁻¹ * s₀ hn * g, ?_, ?_, ?_⟩
  · rw [show (g⁻¹ * s₀ hn * g) ^ 3 = g⁻¹ * s₀ hn ^ 3 * g by
        simp only [pow_succ, pow_zero, one_mul]; group, s₀_cube, mul_one, inv_mul_cancel]
  · rw [mul_smul, mul_smul, hgx, s₀_smul_v₀, smul_comm, ← hgx, inv_smul_smul]
  · have e : y = herm frob x y • y' := by rw [hy', smul_smul, mul_inv_cancel₀ hxy, one_smul]
    have hsy' : (g⁻¹ * s₀ hn * g) • y' = ω • y' := by
      rw [mul_smul, mul_smul, hgy, s₀_smul_u₀, smul_comm, ← hgy, inv_smul_smul]
    rw [e, smul_comm (g⁻¹ * s₀ hn * g) (herm frob x y) y', hsy', smul_comm (herm frob x y) ω y']

theorem exists_s (hn : 3 ≤ n) {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) :
    ∃ s : SUid frob n, s ^ 3 = 1 ∧ s • x = ω • x := by
  obtain ⟨u, -, hu, hxu⟩ := exists_partner_frob hx0 hx
  obtain ⟨s, hs3, hsx, -⟩ := exists_s_pair hn hx0 hx hu (by rw [hxu]; exact one_ne_zero)
  exact ⟨s, hs3, hsx⟩

variable {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V}

open Classical in
@[expose] noncomputable def oLine (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) (x : Fin n → K) :
    V →ₗ[ZMod 2] V :=
  if h : ∃ s : SUid frob n, s ^ 3 = 1 ∧ s • x = ω • x then
    (rs ρ (Classical.choose h) : V →ₗ[ZMod 2] V)
  else 0

omit [FiniteDimensional (ZMod 2) V] in
theorem oLine_eq (hn : 3 ≤ n) {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) :
    ∃ s : SUid frob n, s ^ 3 = 1 ∧ s • x = ω • x ∧ oLine ρ x = (rs ρ s : V →ₗ[ZMod 2] V) := by
  have he := exists_s hn hx0 hx
  refine ⟨Classical.choose he, (Classical.choose_spec he).1, (Classical.choose_spec he).2, ?_⟩
  rw [oLine, dite_eq_left he]

omit [FiniteDimensional (ZMod 2) V] in
theorem cube_apply_rs {s : SUid frob n} (hs3 : s ^ 3 = 1) (v : V) :
    rs ρ s (rs ρ s (rs ρ s v)) = v := by
  have := congrArg (fun g => rs ρ g v) hs3
  simp only [pow_succ, pow_zero, one_mul, map_mul, LinearEquiv.mul_apply, map_one] at this
  exact this.trans rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_lineA_of_s {x : Fin n → K} (hx : herm frob x x = 0) {s : SUid frob n}
    (hsx : s • x = ω • x) {a : V} (ha : a ∈ lineA ρ x) : rs ρ s a ∈ lineA ρ x := by
  have := apply_mem_lineA s hx ha
  rwa [hsx, lineA_smul hx omega_ne_zero] at this

namespace ZSHyp

variable (h : ZSHyp n q ρ)
include h

theorem apply_eq_oLine {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) {s : SUid frob n}
    (hs3 : s ^ 3 = 1) (hsx : s • x = ω • x) {a : V} (ha : a ∈ lineA ρ x) :
    rs ρ s a = oLine ρ x a := by
  obtain ⟨s', hs'3, hs'x, he⟩ := oLine_eq (ρ := ρ) h.three_le hx0 hx
  rw [he]
  refine (eq_on_plane (h.finrank_lineA hx0 hx) (α := (rs ρ s' : V →ₗ[ZMod 2] V))
    (β := (rs ρ s : V →ₗ[ZMod 2] V)) (fun b hb => mem_lineA_of_s hx hs'x hb)
    (fun b hb => mem_lineA_of_s hx hsx hb) (fun b _ => cube_apply_rs hs'3 b)
    (fun b _ => cube_apply_rs hs3 b) ?_ a ha).symm
  intro b hb
  have hg : (s'⁻¹ * s) • x = x := by rw [mul_smul, hsx, ← hs'x, inv_smul_smul]
  have hsq := h.sq_apply_eq_self_of_fix hx0 hx hg hb
  have hc : s' * (s' * s') = 1 := by rw [← hs'3, pow_succ, pow_succ, pow_one, mul_assoc]
  have hinv : s'⁻¹ = s' * s' := inv_eq_of_mul_eq_one_right hc
  rw [hinv, show (s' * s' * s) ^ 2 = s' * s' * s * (s' * s' * s) by rw [_root_.sq]] at hsq
  simp only [map_mul, LinearEquiv.mul_apply] at hsq
  have e := congrArg (rs ρ s') hsq
  rw [cube_apply_rs hs'3] at e
  exact e

theorem oLine_mem {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) {a : V}
    (ha : a ∈ lineA ρ x) : oLine ρ x a ∈ lineA ρ x := by
  obtain ⟨s, hs3, hsx, -⟩ := oLine_eq (ρ := ρ) h.three_le hx0 hx
  rw [← h.apply_eq_oLine hx0 hx hs3 hsx ha]
  exact mem_lineA_of_s hx hsx ha

theorem oLine_ne_zero {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) {a : V}
    (ha : a ∈ lineA ρ x) (ha0 : a ≠ 0) : oLine ρ x a ≠ 0 := by
  obtain ⟨s, hs3, hsx, -⟩ := oLine_eq (ρ := ρ) h.three_le hx0 hx
  rw [← h.apply_eq_oLine hx0 hx hs3 hsx ha]
  exact (LinearEquiv.map_ne_zero_iff _).2 ha0

theorem oLine_smul (g : SUid frob n) {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    {a : V} (ha : a ∈ lineA ρ x) : oLine ρ (g • x) (rs ρ g a) = rs ρ g (oLine ρ x a) := by
  obtain ⟨s, hs3, hsx, -⟩ := oLine_eq (ρ := ρ) h.three_le hx0 hx
  have hgx0 : g • x ≠ 0 := (smul_ne_zero_iff_ne g).2 hx0
  have hgx : herm frob (g • x) (g • x) = 0 := by rw [herm_smul_smul, hx]
  have h3 : (g * s * g⁻¹) ^ 3 = 1 := by
    rw [show (g * s * g⁻¹) ^ 3 = g * s ^ 3 * g⁻¹ by
      simp only [pow_succ, pow_zero, one_mul]; group, hs3, mul_one, mul_inv_cancel]
  have hsgx : (g * s * g⁻¹) • (g • x) = ω • (g • x) := by
    rw [mul_smul, mul_smul, inv_smul_smul, hsx, smul_comm]
  rw [← h.apply_eq_oLine hgx0 hgx h3 hsgx (apply_mem_lineA g hx ha),
    ← h.apply_eq_oLine hx0 hx hs3 hsx ha, map_mul, map_mul, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, ← LinearEquiv.mul_apply (rs ρ g⁻¹), ← map_mul, inv_mul_cancel,
    map_one]
  rfl

theorem polar_oLine {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) (hy0 : y ≠ 0)
    (hy : herm frob y y = 0) {a b : V} (ha : a ∈ lineA ρ x) (hb : b ∈ lineA ρ y) :
    polar q (oLine ρ x a) (oLine ρ y b) = polar q a b := by
  by_cases hxy : herm frob x y = 0
  · rw [h.polar_eq_zero_of_perp hx0 hx hy0 hy hxy (h.oLine_mem hx0 hx ha) (h.oLine_mem hy0 hy hb),
      h.polar_eq_zero_of_perp hx0 hx hy0 hy hxy ha hb]
  · obtain ⟨s, hs3, hsx, hsy⟩ := exists_s_pair h.three_le hx0 hx hy hxy
    rw [← h.apply_eq_oLine hx0 hx hs3 hsx ha, ← h.apply_eq_oLine hy0 hy hs3 hsy hb]
    exact h.polar_apply _ a b

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
