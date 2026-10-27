module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix Module CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LinearThreeKit

variable {K : Type*} [Field K]

theorem one_add_omega_add_sq {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    1 + ω + ω ^ 2 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hω1
  · exact h0

theorem three_ne_zero_of_omega {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) : (3 : K) ≠ 0 := by
  intro h3
  have h := one_add_omega_add_sq hω1 hω3
  have h' : (ω - 1) ^ 3 = 0 := by
    have : (ω - 1) ^ 3 = ω ^ 3 - 3 * ω ^ 2 + 3 * ω - 1 := by ring
    rw [this, h3, hω3]; ring
  exact hω1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h'))

theorem mul_eigen {s : Matrix (Fin 3) (Fin 3) K} {r l : K} (hr : r ^ 3 = l ^ 3)
    (hs : s ^ 3 = (l ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K)) :
    s * (s ^ 2 + r • s + (r ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K)) =
      r • (s ^ 2 + r • s + (r ^ 2) • 1) := by
  have h3 : s * s ^ 2 = s ^ 3 := (pow_succ' s 2).symm
  have h2 : s * s = s ^ 2 := (pow_two s).symm
  have : s * (s ^ 2 + r • s + (r ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K)) =
      s ^ 3 + r • s ^ 2 + (r ^ 2) • s := by
    rw [mul_add, mul_add, h3, mul_smul_comm, mul_smul_comm, mul_one, h2]
  rw [this, hs, ← hr]
  module

theorem exists_basis_subfamily {ι : Type*} (v : ι → (Fin 3 → K))
    (hv : ⊤ ≤ Submodule.span K (Set.range v)) :
    ∃ a : Fin 3 → ι, LinearIndependent K (v ∘ a) := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K v
  have htop : ⊤ ≤ Submodule.span K (Set.range (v ∘ a)) := hsp ▸ hv
  let B : Basis κ K (Fin 3 → K) := Basis.mk hli htop
  have : Finite κ := Module.Finite.finite_basis B
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = 3 := by
    have := Module.finrank_eq_card_basis B
    simpa using this.symm
  let e : κ ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  refine ⟨a ∘ e.symm, ?_⟩
  exact hli.comp e.symm e.symm.injective

theorem exists_eigenbasis_of_cube {s : Matrix (Fin 3) (Fin 3) K} {l ω : K} (hl : l ≠ 0)
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) (hs : s ^ 3 = (l ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ (b : Fin 3 → Fin 3 → K) (j : Fin 3 → Fin 3), LinearIndependent K b ∧
      ∀ i, s *ᵥ b i = (l * ω ^ (j i : ℕ)) • b i := by
  have h1 := one_add_omega_add_sq hω1 hω3
  have h3 := three_ne_zero_of_omega hω1 hω3
  set r : Fin 3 → K := fun j => l * ω ^ (j : ℕ) with hr
  have hr3 : ∀ j, r j ^ 3 = l ^ 3 := fun j => by
    have : (l * ω ^ (j : ℕ)) ^ 3 = l ^ 3 * (ω ^ 3) ^ (j : ℕ) := by ring
    simp only [hr]
    rw [this, hω3, one_pow, mul_one]
  let u : Fin 3 → Matrix (Fin 3) (Fin 3) K := fun j =>
    s ^ 2 + r j • s + (r j ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K)
  let v : Fin 3 × Fin 3 → (Fin 3 → K) := fun p => u p.1 *ᵥ Pi.single p.2 1
  have hsum : ∑ j, r j • u j = (3 * l ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    simp only [Fin.sum_univ_three, hr, u]
    have e4 : ω ^ 4 = ω := by rw [show ω ^ 4 = ω ^ 3 * ω by ring, hω3, one_mul]
    have e6 : ω ^ 6 = 1 := by rw [show ω ^ 6 = (ω ^ 3) ^ 2 by ring, hω3, one_pow]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
    have c2 : l + l * ω + l * ω ^ 2 = 0 := by linear_combination l * h1
    have c1 : l ^ 2 + (l * ω) ^ 2 + (l * ω ^ 2) ^ 2 = 0 := by
      linear_combination l ^ 2 * h1 + l ^ 2 * ω * hω3
    have c0 : l ^ 3 + (l * ω) ^ 3 + (l * ω ^ 2) ^ 3 = 3 * l ^ 3 := by
      linear_combination (l ^ 3 * (2 + ω ^ 3)) * hω3
    have key : l • (s ^ 2 + l • s + l ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K)) +
        (l * ω) • (s ^ 2 + (l * ω) • s + (l * ω) ^ 2 • 1) +
        (l * ω ^ 2) • (s ^ 2 + (l * ω ^ 2) • s + (l * ω ^ 2) ^ 2 • 1) =
        (l + l * ω + l * ω ^ 2) • s ^ 2 + (l ^ 2 + (l * ω) ^ 2 + (l * ω ^ 2) ^ 2) • s +
        (l ^ 3 + (l * ω) ^ 3 + (l * ω ^ 2) ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K) := by module
    rw [key, c2, c1, c0]; simp
  have heig : ∀ p, s *ᵥ v p = r p.1 • v p := fun p => by
    simp only [v]
    rw [Matrix.mulVec_mulVec, show u p.1 = s ^ 2 + r p.1 • s + (r p.1 ^ 2) • 1 from rfl,
      mul_eigen (hr3 p.1) hs, Matrix.smul_mulVec]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    have hbasis := (Pi.basisFun K (Fin 3)).span_eq
    rw [← hbasis]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, rfl⟩
    have hmem : (3 * l ^ 3) • (Pi.basisFun K (Fin 3) m) =
        ∑ j, r j • v (j, m) := by
      have := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A *ᵥ (Pi.single m 1 : Fin 3 → K)) hsum
      simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
      rw [Pi.basisFun_apply]
      exact this.symm
    have hne : (3 * l ^ 3 : K) ≠ 0 := mul_ne_zero h3 (pow_ne_zero 3 hl)
    have : Pi.basisFun K (Fin 3) m = (3 * l ^ 3)⁻¹ • ∑ j, r j • v (j, m) := by
      rw [← hmem, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, m), rfl⟩))
  obtain ⟨a, ha⟩ := exists_basis_subfamily v hspan
  exact ⟨v ∘ a, fun i => (a i).1, ha, fun i => heig (a i)⟩

theorem exists_det_sub_eq_zero {d : ℕ} (hd : d = 1 ∨ d = 2) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ stabilizer (flagSpace 3 K d)) :
    ∃ x : K, ((g : Matrix (Fin 3) (Fin 3) K) - x • 1).det = 0 := by
  rcases hd with rfl | rfl
  · refine ⟨(g : Matrix (Fin 3) (Fin 3) K) 0 0, ?_⟩
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Pi.single 0 1, ?_, ?_⟩
    · exact Pi.single_ne_zero_iff.mpr one_ne_zero
    · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        mulVec_single_zero_of_mem_stabilizer_one hg, sub_self]
  · refine ⟨(g : Matrix (Fin 3) (Fin 3) K) 2 2, ?_⟩
    refine Matrix.det_eq_zero_of_row_eq_zero 2 fun k => ?_
    by_cases hk : k = 2
    · subst hk
      simp
    · simp [apply_two_eq_zero_of_mem_stabilizer_two hg hk, Matrix.one_apply_ne (Ne.symm hk)]

theorem exists_eigenvector_of_mem_stabilizer {d : ℕ} (hd : d = 1 ∨ d = 2)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ stabilizer (flagSpace 3 K d)) :
    ∃ (x : K) (v : Fin 3 → K), v ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = x • v := by
  obtain ⟨x, hx⟩ := exists_det_sub_eq_zero hd hg
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hx
  refine ⟨x, v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv

theorem exists_order_three_commute_of_repeated [CharP K 2] {s : SpecialLinearGroup (Fin 3) K}
    {b₀ b₁ b₂ : Fin 3 → K} (hb : LinearIndependent K ![b₀, b₁, b₂]) {ν ν' : K}
    (h0 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b₀ = ν • b₀)
    (h1 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b₁ = ν • b₁)
    (h2 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b₂ = ν' • b₂) :
    ∃ v : SpecialLinearGroup (Fin 3) K, v ∉ scalars 3 K ∧ v ^ 3 = 1 ∧ v * s = s * v := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  set M : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 1, 0; 0, 0, 1] with hM
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 3) (Fin 3) K, ∀ j, A *ᵥ ![b₀, b₁, b₂] j =
      ∑ i, M i j • ![b₀, b₁, b₂] i := exists_mulVec_eq_sum hb M
  have hA0 : A *ᵥ b₀ = b₁ := by simpa [hM, Fin.sum_univ_three] using hA 0
  have hA1 : A *ᵥ b₁ = b₀ + b₁ := by simpa [hM, Fin.sum_univ_three] using hA 1
  have hA2 : A *ᵥ b₂ = b₂ := by simpa [hM, Fin.sum_univ_three] using hA 2
  have hdet : A.det = 1 := by
    rw [det_eq_of_mulVec_eq_sum hb hA, hM, Matrix.det_fin_three]
    simp [CharTwo.neg_eq]
  have hbb : b₁ + b₁ = 0 := by rw [← two_smul K b₁, h2K, zero_smul]
  have e3 : ∀ x, (A ^ 3) *ᵥ x = A *ᵥ (A *ᵥ (A *ᵥ x)) := fun x => by
    rw [pow_succ, pow_two, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hb0 : b₀ + b₀ = 0 := by rw [← two_smul K b₀, h2K, zero_smul]
  have hA01 : A *ᵥ (b₀ + b₁) = b₁ + (b₀ + b₁) := by
    rw [Matrix.mulVec_add, hA0, hA1]
  have hA3 : A ^ 3 = 1 := by
    refine eq_of_mulVec_eq hb (forall_fin_three ?_ ?_ ?_)
    · show A ^ 3 *ᵥ b₀ = 1 *ᵥ b₀
      rw [e3, Matrix.one_mulVec, hA0, hA1, hA01]
      calc b₁ + (b₀ + b₁) = b₀ + (b₁ + b₁) := by abel
        _ = b₀ := by rw [hbb, add_zero]
    · show A ^ 3 *ᵥ b₁ = 1 *ᵥ b₁
      rw [e3, Matrix.one_mulVec, hA1, hA01, Matrix.mulVec_add, hA1, hA01]
      calc b₀ + b₁ + (b₁ + (b₀ + b₁)) = (b₀ + b₀) + (b₁ + b₁) + b₁ := by abel
        _ = b₁ := by rw [hb0, hbb]; simp
    · show A ^ 3 *ᵥ b₂ = 1 *ᵥ b₂
      rw [e3, Matrix.one_mulVec, hA2, hA2, hA2]
  have hsA : (s : Matrix (Fin 3) (Fin 3) K) * A = A * (s : Matrix (Fin 3) (Fin 3) K) := by
    refine eq_of_mulVec_eq hb (forall_fin_three ?_ ?_ ?_)
    · show ((s : Matrix (Fin 3) (Fin 3) K) * A) *ᵥ b₀ = (A * (s : Matrix (Fin 3) (Fin 3) K)) *ᵥ b₀
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA0, h0, Matrix.mulVec_smul, hA0, h1]
    · show ((s : Matrix (Fin 3) (Fin 3) K) * A) *ᵥ b₁ = (A * (s : Matrix (Fin 3) (Fin 3) K)) *ᵥ b₁
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA1, h1, Matrix.mulVec_smul, hA1,
        Matrix.mulVec_add, h0, h1, smul_add]
    · show ((s : Matrix (Fin 3) (Fin 3) K) * A) *ᵥ b₂ = (A * (s : Matrix (Fin 3) (Fin 3) K)) *ᵥ b₂
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA2, h2, Matrix.mulVec_smul, hA2]
  let V : SpecialLinearGroup (Fin 3) K := ⟨A, hdet⟩
  have hVA : (V : Matrix (Fin 3) (Fin 3) K) = A := rfl
  refine ⟨V, ?_, ?_, ?_⟩
  · rintro ⟨c, -, hc⟩
    have hc' : A = Matrix.scalar (Fin 3) (c : K) := hc
    have h := hA0
    rw [hc', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h
    have hi := Fintype.linearIndependent_iff.mp hb ![(c : K), -1, 0] (by
      simp [Fin.sum_univ_three, h])
    simpa using hi 1
  · refine Subtype.ext ?_
    rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one, hVA]
    exact hA3
  · refine Subtype.ext ?_
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hVA]
    exact hsA.symm

theorem exists_comm_order_three [CharP K 2] {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {d : ℕ}
    (hd : d = 1 ∨ d = 2) {s : SpecialLinearGroup (Fin 3) K} (hs : s ∉ scalars 3 K)
    (hs3 : s ^ 3 ∈ scalars 3 K) (hsJ : s ∈ stabilizer (flagSpace 3 K d)) :
    ∃ v : SpecialLinearGroup (Fin 3) K, v ∉ scalars 3 K ∧ v ^ 3 = 1 ∧ v * s = s * v := by
  by_cases h1 : s ^ 3 = 1
  · exact ⟨s, hs, h1, rfl⟩
  obtain ⟨c, -, hcs⟩ := hs3
  have hS3 : (s : Matrix (Fin 3) (Fin 3) K) ^ 3 = (c : K) • 1 := by
    rw [← SpecialLinearGroup.coe_pow, hcs, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  have hc1 : (c : K) ≠ 1 := fun hc => h1 (Subtype.ext (by
    rw [SpecialLinearGroup.coe_pow, hS3, hc, one_smul, SpecialLinearGroup.coe_one]))
  obtain ⟨x, v₀, hv0, hxv⟩ := exists_eigenvector_of_mem_stabilizer hd hsJ
  have hxc : x ^ 3 = (c : K) := by
    have h3 := pow_mulVec_of_mulVec_eq_smul hxv 3
    rw [hS3, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have := congrFun h3 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_right_cancel₀ hi this).symm
  have hx0 : x ≠ 0 := fun hx => by
    rw [hx] at hxc
    exact c.ne_zero (by rw [← hxc]; norm_num)
  have hSx : (s : Matrix (Fin 3) (Fin 3) K) ^ 3 = (x ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hxc]; exact hS3
  obtain ⟨b, j, hli, hbj⟩ := exists_eigenbasis_of_cube hx0 hω1 hω3 hSx
  have hnj : ¬ Function.Injective j := by
    intro hinj
    have hbij : Function.Bijective j := (Finite.injective_iff_bijective).mp hinj
    have hdet : (s : Matrix (Fin 3) (Fin 3) K).det =
        (Matrix.diagonal fun i => x * ω ^ (j i : ℕ)).det := by
      refine det_eq_of_mulVec_eq_sum hli fun i => ?_
      rw [hbj i]
      simp [Matrix.diagonal_apply]
    rw [s.2, Matrix.det_diagonal] at hdet
    have hprod : ∏ i : Fin 3, x * ω ^ (j i : ℕ) = ∏ i : Fin 3, x * ω ^ (i : ℕ) :=
      Equiv.prod_comp (Equiv.ofBijective j hbij) (fun i : Fin 3 => x * ω ^ (i : ℕ))
    rw [hprod, Fin.prod_univ_three] at hdet
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one] at hdet
    apply hc1
    rw [← hxc]
    linear_combination (-x ^ 3) * hω3 + hdet.symm
  obtain ⟨i₀, i₁, hij, hne⟩ := Function.not_injective_iff.mp hnj
  have hthird : ∀ a b : Fin 3, ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide
  obtain ⟨i₂, hi20, hi21⟩ := hthird i₀ i₁
  have hinj3 : Function.Injective ![i₀, i₁, i₂] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hli' : LinearIndependent K ![b i₀, b i₁, b i₂] := by
    have := hli.comp _ hinj3
    convert this using 1
    ext a
    fin_cases a <;> rfl
  refine exists_order_three_commute_of_repeated hli' (ν := x * ω ^ (j i₀ : ℕ))
    (ν' := x * ω ^ (j i₂ : ℕ)) (hbj i₀) ?_ (hbj i₂)
  rw [hbj i₁, hij]

end CFSG.HardMathSupport.Curtis.Coordinator
