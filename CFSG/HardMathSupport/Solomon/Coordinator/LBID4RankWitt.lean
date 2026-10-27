module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankFrame
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LBID4

open QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_eq_zero_of_mem_span {s : Set V} (hs : ∀ x ∈ s, ∀ y ∈ s, polar Q x y = 0) :
    ∀ x ∈ Submodule.span K s, ∀ y ∈ Submodule.span K s, polar Q x y = 0 := by
  have h1 : ∀ x ∈ Submodule.span K s, ∀ y ∈ s, polar Q x y = 0 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem z hz => exact hs z hz y hy
    | zero => exact polar_zero_left Q y
    | add a b _ _ ha hb => rw [polar_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [polar_smul_left, ha, smul_zero]
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem z hz => exact h1 x hx z hz
  | zero => exact polar_zero_right Q x
  | add a b _ _ ha hb => rw [polar_add_right, ha, hb, add_zero]
  | smul c a _ ha => rw [polar_smul_right, ha, smul_zero]

theorem q_eq_zero_of_mem_span {s : Set V} (hq : ∀ x ∈ s, Q x = 0)
    (hs : ∀ x ∈ s, ∀ y ∈ s, polar Q x y = 0) : ∀ x ∈ Submodule.span K s, Q x = 0 := by
  have hp := polar_eq_zero_of_mem_span hs
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz => exact hq z hz
  | zero => exact QuadraticMap.map_zero Q
  | add a b ha' hb' ha hb => rw [q_add, ha, hb, hp a ha' b hb']; ring
  | smul c a _ ha => rw [q_smul, ha, mul_zero]

theorem polar_eq_zero_of_singular' {S : Submodule K V} (hS : ∀ x ∈ S, Q x = 0) {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) : polar Q x y = 0 := by
  rw [polar, hS _ (S.add_mem hx hy), hS x hx, hS y hy, sub_zero, sub_zero]

variable (Q) in
@[expose] noncomputable def orth (U : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) U

theorem mem_orth {U : Submodule K V} {m : V} : m ∈ orth Q U ↔ ∀ n ∈ U, polar Q n m = 0 := by
  simp [orth, LinearMap.BilinForm.mem_orthogonal_iff, polarBilin_apply_apply]

theorem orth_sup (A C : Submodule K V) : orth Q (A ⊔ C) = orth Q A ⊓ orth Q C := by
  ext m
  rw [Submodule.mem_inf, mem_orth, mem_orth, mem_orth]
  constructor
  · intro h
    exact ⟨fun n hn => h n (Submodule.mem_sup_left hn), fun n hn => h n (Submodule.mem_sup_right hn)⟩
  · rintro ⟨hA, hC⟩ n hn
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hn
    rw [polar_add_left, hA a ha, hC c hc, add_zero]

theorem le_orth_of_singular {U : Submodule K V} (hU : ∀ u ∈ U, Q u = 0) : U ≤ orth Q U :=
  fun _ hu => mem_orth.mpr fun _ hn => polar_eq_zero_of_singular' hU hn hu

variable [FiniteDimensional K V] (hB : (polarBilin Q).Nondegenerate)
include hB

omit [FiniteDimensional K V] hB in
theorem isRefl_polarBilin : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rw [polar_comm]
  exact h

theorem finrank_orth (U : Submodule K V) : finrank K ↥(orth Q U) = finrank K V - finrank K U :=
  LinearMap.BilinForm.finrank_orthogonal hB U

theorem orth_orth (U : Submodule K V) : orth Q (orth Q U) = U :=
  LinearMap.BilinForm.orthogonal_orthogonal hB isRefl_polarBilin U

theorem finrank_inf_orth_add {W U : Submodule K V} (hW : ∀ w ∈ W, Q w = 0)
    (hWdim : 2 * finrank K W = finrank K V) :
    finrank K ↥(W ⊓ orth Q U) + finrank K U = finrank K ↥(W ⊓ U) + finrank K W := by
  have hWW : orth Q W = W := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq (le_orth_of_singular hW)
    rw [finrank_orth hB]
    omega
  have hsup : orth Q (W ⊔ orth Q U) = W ⊓ U := by
    rw [orth_sup, hWW, orth_orth hB]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (orth Q U)
  have h2 := finrank_orth hB (W ⊔ orth Q U)
  have h3 := finrank_orth hB U
  rw [hsup] at h2
  have h4 := Submodule.finrank_le (W ⊔ orth Q U)
  have h5 := Submodule.finrank_le U
  omega

theorem exists_mem_inf_orth_not_mem {W U : Submodule K V} (hW : ∀ w ∈ W, Q w = 0)
    (hWdim : 2 * finrank K W = finrank K V)
    (hlt : finrank K U < finrank K W) : ∃ w ∈ W, w ∈ orth Q U ∧ w ∉ U := by
  have hA := finrank_inf_orth_add (U := U) hB hW hWdim
  by_contra h
  push Not at h
  have hle : W ⊓ orth Q U ≤ W ⊓ U := fun w hw => ⟨hw.1, h w hw.1 hw.2⟩
  have := Submodule.finrank_mono hle
  omega

omit hB in
theorem finrank_map_add_finrank_inf_ker {M₂ : Type*} [AddCommGroup M₂] [Module K M₂]
    (f : V →ₗ[K] M₂) (N : Submodule K V) :
    finrank K ↥(N.map f) + finrank K ↥(N ⊓ LinearMap.ker f) = finrank K N := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict N)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  have e : (LinearMap.ker f).comap N.subtype = (N ⊓ LinearMap.ker f).comap N.subtype := by
    ext x
    simp
  rw [e, (Submodule.comapSubtypeEquivOfLe (inf_le_left : N ⊓ LinearMap.ker f ≤ N)).finrank_eq]
    at h1
  exact h1

end CFSG.HardMathSupport.Solomon.Coordinator.LBID4

namespace CFSG.HardMathSupport.Solomon.Coordinator.LBID4.EFrame

open QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (F : EFrame Q)

theorem q_comb (α β : K) : Q (α • F.b + β • F.b') = F.c * (α ^ 2 - α * β + β ^ 2) := by
  simp only [q_add, q_smul, F.q_b, F.q_b', polar_smul_left, polar_smul_right, F.polar_bb',
    smul_eq_mul]
  ring

theorem polar_comb_b (α β : K) : polar Q (α • F.b + β • F.b') F.b = F.c * (2 * α - β) := by
  rw [polar_add_left, polar_smul_left, polar_smul_left, F.polar_bb, F.polar_b'b, smul_eq_mul,
    smul_eq_mul]
  ring

theorem polar_comb_b' (α β : K) : polar Q (α • F.b + β • F.b') F.b' = F.c * (2 * β - α) := by
  rw [polar_add_left, polar_smul_left, polar_smul_left, F.polar_bb', F.polar_b'b', smul_eq_mul,
    smul_eq_mul]
  ring

theorem eq_zero_of_norm_eq_zero (hω : ∀ y : K, y ^ 2 + y + 1 ≠ 0) {α β : K}
    (h : α ^ 2 - α * β + β ^ 2 = 0) : α = 0 ∧ β = 0 := by
  by_cases hβ : β = 0
  · subst hβ
    refine ⟨?_, rfl⟩
    have : α ^ 2 = 0 := by linear_combination h
    exact (pow_eq_zero_iff two_ne_zero).mp this
  · exfalso
    apply hω (-α / β)
    field_simp
    linear_combination h

theorem orth_proj_of_perp {G : EFrame Q} (h : F.Perp G) (v : V) : F.Orth (G.proj v) := by
  rw [proj_apply]
  exact (h.1.smul _).add (h.2.smul _)

theorem orth_of_proj_eq_zero (h3 : (3 : K) ≠ 0) {y : V} (hy : F.proj y = 0) : F.Orth y := by
  have := F.orth_sub_proj h3 y
  rwa [hy, sub_zero] at this

end CFSG.HardMathSupport.Solomon.Coordinator.LBID4.EFrame
