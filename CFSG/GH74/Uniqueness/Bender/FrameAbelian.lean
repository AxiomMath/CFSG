module

public import CFSG.GH74.Uniqueness.Bender.FrameDefs
import CFSG.LinearAlgebra.LinearGroups.UnitaryTransitivity
import CFSG.LinearAlgebra.OddSolvableUnitary.HomologyMonomial
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.Uniqueness.Bender.Frame

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {E : Type} [Field E]

namespace A2

noncomputable abbrev hform (hU : UnitaryFieldData p f E) :
    (Fin 3 → E) →ₛₗ[hU.bar] (Fin 3 → E) →ₗ[E] E :=
  gramForm hU (1 : Matrix (Fin 3) (Fin 3) E)

theorem hform_apply (hU : UnitaryFieldData p f E) (v w : Fin 3 → E) :
    hform hU v w = herm hU v w := by
  simp [hform, gramForm_apply, herm, dotProduct]

theorem hform_isSymm (hU : UnitaryFieldData p f E) : (hform hU).IsSymm :=
  gramForm_isSymm hU (by
    rw [Matrix.map_one _ (map_zero hU.bar) (map_one hU.bar), Matrix.transpose_one])

theorem hform_symm (hU : UnitaryFieldData p f E) (v w : Fin 3 → E) :
    hform hU w v = hU.bar (hform hU v w) :=
  ((hform_isSymm hU).eq v w).symm

theorem hform_separatingLeft (hU : UnitaryFieldData p f E) : (hform hU).SeparatingLeft :=
  gramForm_separatingLeft hU (by rw [Matrix.det_one]; exact one_ne_zero)

theorem hform_mulVec {hU : UnitaryFieldData p f E} {g : GL (Fin 3) E}
    (hg : g ∈ gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) (v w : Fin 3 → E) :
    hform hU ((g : Matrix (Fin 3) (Fin 3) E) *ᵥ v) ((g : Matrix (Fin 3) (Fin 3) E) *ᵥ w) =
      hform hU v w :=
  (mem_gramSU_iff_isometry.1 hg).1 v w

noncomputable def hermRefl (hU : UnitaryFieldData p f E) :
    CFSG.LieType.BorelTits.ReflForm E (Fin 3 → E) where
  σ := RingEquiv.ofBijective hU.bar (Function.Involutive.bijective hU.bar_bar)
  β v w := hform hU v w
  add_left u u' v := by simp
  smul_left c u v := by
    change hform hU (c • u) v = hU.bar c * hform hU u v
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
  add_right u v v' := by simp
  smul_right c u v := by simp
  refl u v h := by rw [hform_symm hU u v, h, map_zero]
  nondeg u h := hform_separatingLeft hU u h

theorem not_totallyIsotropic_two (hU : UnitaryFieldData p f E) {U : Submodule E (Fin 3 → E)}
    (hU2 : finrank E U = 2) (hiso : ∀ y ∈ U, ∀ w ∈ U, hform hU y w = 0) : False := by
  have h := (hermRefl hU).finrank_perp U
  have hle : U ≤ (hermRefl hU).perp U := fun y hy w hw => hiso w hw y hy
  have h2 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h
  omega

theorem inv_mulVec_mulVec (g : GL (Fin 3) E) (v : Fin 3 → E) :
    ((g⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ ((g : Matrix (Fin 3) (Fin 3) E) *ᵥ v) =
      v := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mulVec_injective (g : GL (Fin 3) E) {v w : Fin 3 → E}
    (h : (g : Matrix (Fin 3) (Fin 3) E) *ᵥ v = (g : Matrix (Fin 3) (Fin 3) E) *ᵥ w) : v = w := by
  rw [← inv_mulVec_mulVec g v, h, inv_mulVec_mulVec]

theorem mulVec_ne_zero (g : GL (Fin 3) E) {v : Fin 3 → E} (hv : v ≠ 0) :
    (g : Matrix (Fin 3) (Fin 3) E) *ᵥ v ≠ 0 := fun h =>
  hv (mulVec_injective g (by rw [h, mulVec_zero]))

theorem mulVec_conj (g b : GL (Fin 3) E) (v : Fin 3 → E) :
    (b : Matrix (Fin 3) (Fin 3) E) *ᵥ ((g : Matrix (Fin 3) (Fin 3) E) *ᵥ v) =
      (g : Matrix (Fin 3) (Fin 3) E) *ᵥ
        (((g⁻¹ * b * g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ v) := by
  simp only [mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem isScalarMat_of_forall {g : GL (Fin 3) E} {μ : E}
    (h : ∀ v : Fin 3 → E, (g : Matrix (Fin 3) (Fin 3) E) *ᵥ v = μ • v) : IsScalarMat g :=
  ⟨μ, Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, smul_mulVec, one_mulVec])⟩

theorem eigen_unique {M : Matrix (Fin 3) (Fin 3) E} {v : Fin 3 → E} (hv : v ≠ 0) {μ ν : E}
    (h1 : M *ᵥ v = μ • v) (h2 : M *ᵥ v = ν • v) : μ = ν := by
  have : (μ - ν) • v = 0 := by rw [sub_smul, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hv)

theorem pow_mulVec_of_eigen {M : Matrix (Fin 3) (Fin 3) E} {v : Fin 3 → E} {μ : E}
    (h : M *ᵥ v = μ • v) (n : ℕ) : M ^ n *ᵥ v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul, pow_succ]

theorem add_self_vec [CharP E 2] (x : Fin 3 → E) : x + x = 0 := by
  rw [← two_smul E x, CharTwo.two_eq_zero, zero_smul]

theorem linearIndependent_pair_of_not_smul {y z : Fin 3 → E} (hy : y ≠ 0)
    (hz : ∀ μ : E, z ≠ μ • y) : LinearIndependent E ![y, z] := by
  rw [LinearIndependent.pair_iff]
  intro s r h
  by_cases hr : r = 0
  · subst hr
    rw [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.1 h).resolve_right hy, rfl⟩
  · exfalso
    apply hz (-(r⁻¹ * s))
    calc z = r⁻¹ • (r • z) := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
      _ = r⁻¹ • (-(s • y)) := by rw [eq_neg_of_add_eq_zero_right h]
      _ = -(r⁻¹ * s) • y := by rw [smul_neg, smul_smul, neg_smul]

theorem linearIndependent_pair_symm {y z : Fin 3 → E} (h : LinearIndependent E ![y, z]) :
    LinearIndependent E ![z, y] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s r hsr
  have := h r s (by rw [add_comm]; exact hsr)
  exact ⟨this.2, this.1⟩

theorem exists_eq_add_of_pair {U : Submodule E (Fin 3 → E)} (hU2 : finrank E U = 2)
    {y z : Fin 3 → E} (hy : y ∈ U) (hz : z ∈ U) (hli : LinearIndependent E ![y, z]) :
    ∀ w ∈ U, ∃ α γ : E, α • y + γ • z = w := by
  have hrange : Set.range ![y, z] = {y, z} := by
    ext x
    simp [eq_comm, or_comm]
  have hle : Submodule.span E {y, z} ≤ U := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    exacts [hy, hz]
  have hrk : finrank E (Submodule.span E {y, z}) = 2 := by
    rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hrk, hU2])
  intro w hw
  rw [← heq] at hw
  exact Submodule.mem_span_pair.1 hw

theorem linearIndependent_cons3 {U : Submodule E (Fin 3 → E)} {x y z : Fin 3 → E} (hx : x ∉ U)
    (hy : y ∈ U) (hz : z ∈ U) (hyz : LinearIndependent E ![y, z]) :
    LinearIndependent E ![x, y, z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have h0 : g 0 = 0 := by
    by_contra h
    apply hx
    have hx' : g 0 • x = -(g 1 • y + g 2 • z) :=
      eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact hg)
    have hmem : g 0 • x ∈ U := by
      rw [hx']
      exact U.neg_mem (U.add_mem (U.smul_mem _ hy) (U.smul_mem _ hz))
    exact (U.smul_mem_iff h).1 hmem
  rw [h0, zero_smul, zero_add] at hg
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hyz _ _ hg
  intro i
  fin_cases i
  exacts [h0, h1, h2]

theorem exists_coeffs {x : Fin 3 → Fin 3 → E} (hli : LinearIndependent E x) (y : Fin 3 → E) :
    ∃ a : Fin 3 → E, ∑ l, a l • x l = y := by
  have htop : Submodule.span E (Set.range x) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fin_fun]
  have hy : y ∈ Submodule.span E (Set.range x) := by rw [htop]; exact Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun E).1 hy

theorem coeffs_eq {x : Fin 3 → Fin 3 → E} (hli : LinearIndependent E x) {a a' : Fin 3 → E}
    (h : ∑ l, a l • x l = ∑ l, a' l • x l) : a = a' := by
  funext l
  have := Fintype.linearIndependent_iff.1 hli (fun l => a l - a' l)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
  exact sub_eq_zero.1 (this l)

theorem eq_zero_of_hform_basis (hU : UnitaryFieldData p f E) {x : Fin 3 → Fin 3 → E}
    (hli : LinearIndependent E x) {y : Fin 3 → E} (hy : ∀ l, hform hU y (x l) = 0) : y = 0 := by
  refine hform_separatingLeft hU y fun v => ?_
  obtain ⟨a, rfl⟩ := exists_coeffs hli v
  simp [map_sum, map_smul, hy]

theorem pair_of_linearIndependent {x : Fin 3 → Fin 3 → E} (hli : LinearIndependent E x)
    {i j : Fin 3} (hij : i ≠ j) : LinearIndependent E ![x i, x j] := by
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b
    all_goals first
      | rfl
      | (exfalso; simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
          Matrix.cons_val_one] at hab; first | exact hij hab | exact hij hab.symm)
  have := hli.comp _ hinj
  convert this using 1
  funext a
  fin_cases a <;> rfl

theorem false_of_three_mem_span_pair {y₁ y₂ : Fin 3 → E} {u : Fin 3 → Fin 3 → E}
    (hli : LinearIndependent E u) (hu : ∀ i, u i ∈ Submodule.span E {y₁, y₂}) : False := by
  have hrange : Set.range ![y₁, y₂] = {y₁, y₂} := by
    ext x
    simp [eq_comm, or_comm]
  have h1 : finrank E (Submodule.span E {y₁, y₂}) ≤ 2 := by
    have := finrank_range_le_card (R := E) ![y₁, y₂]
    rw [hrange, Fintype.card_fin] at this
    exact this
  have hli' : LinearIndependent E (fun i => (⟨u i, hu i⟩ : Submodule.span E {y₁, y₂})) :=
    LinearIndependent.of_comp (Submodule.span E {y₁, y₂}).subtype hli
  have := hli'.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  omega

theorem eq_sq_pow_of_odd {G : Type*} [Monoid G] {x : G} {m : ℕ} (hm : Odd m) (hx : x ^ m = 1) :
    ∃ k : ℕ, x = (x * x) ^ (k + 1) := by
  obtain ⟨k, rfl⟩ := hm
  refine ⟨k, ?_⟩
  rw [← sq, ← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hx, one_mul]

theorem odd_orderOf_of_mem {G : Type*} [Group G] {C : Subgroup G} (hodd : Odd (Nat.card C))
    {c : G} (hc : c ∈ C) : Odd (orderOf c) := by
  have : Finite C := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have h := orderOf_dvd_natCard (⟨c, hc⟩ : C)
  rw [Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat hodd h

theorem val_pow_eq_one {g : GL (Fin 3) E} {m : ℕ} (h : g ^ m = 1) :
    (g : Matrix (Fin 3) (Fin 3) E) ^ m = 1 := by
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem eq_zero_of_odd_pow [CharP E 2] {M : Matrix (Fin 3) (Fin 3) E} {m : ℕ} (hm : Odd m)
    (hM : M ^ m = 1) {c : E} {v w : Fin 3 → E} (hw : M *ᵥ w = c • w)
    (hv : M *ᵥ v = c • v + w) : w = 0 := by
  obtain ⟨k, hk⟩ := eq_sq_pow_of_odd hm hM
  have h2v : (M * M) *ᵥ v = (c * c) • v := by
    rw [← mulVec_mulVec, hv, mulVec_add, mulVec_smul, hv, hw, smul_add, smul_smul, add_assoc,
      add_self_vec, add_zero]
  have h2w : (M * M) *ᵥ w = (c * c) • w := by
    rw [← mulVec_mulVec, hw, mulVec_smul, hw, smul_smul]
  have hMv : M *ᵥ v = (c * c) ^ (k + 1) • v := by
    calc M *ᵥ v = (M * M) ^ (k + 1) *ᵥ v := by rw [← hk]
      _ = _ := pow_mulVec_of_eigen h2v _
  have hMw : M *ᵥ w = (c * c) ^ (k + 1) • w := by
    calc M *ᵥ w = (M * M) ^ (k + 1) *ᵥ w := by rw [← hk]
      _ = _ := pow_mulVec_of_eigen h2w _
  have hw' : w = ((c * c) ^ (k + 1) - c) • v := by
    rw [sub_smul, ← hMv, hv]
    abel
  have hcd : (c - (c * c) ^ (k + 1)) • w = 0 := by
    rw [sub_smul, ← hw, ← hMw, sub_self]
  rcases smul_eq_zero.1 hcd with h | h
  · rw [hw', show (c * c) ^ (k + 1) - c = 0 by rw [← neg_sub, h, neg_zero], zero_smul]
  · exact h

section Involution

variable [CharP E 2] {t : GL (Fin 3) E}

theorem exists_rank_one (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ u : Fin 3 → E, u ≠ 0 ∧ (∀ y, ∃ κ : E, ((t : Matrix (Fin 3) (Fin 3) E) - 1) *ᵥ y = κ • u) ∧
      ∃ y₀, ((t : Matrix (Fin 3) (Fin 3) E) - 1) *ᵥ y₀ ≠ 0 := by
  have htt : (t : Matrix (Fin 3) (Fin 3) E) * t = 1 := by
    rw [← Units.val_mul, ht2, Units.val_one]
  have h2 : ∀ X : Matrix (Fin 3) (Fin 3) E, X + X = 0 := fun X => by
    rw [← two_smul E X, CharTwo.two_eq_zero, zero_smul]
  obtain ⟨N, hNdef⟩ : ∃ N, N = (t : Matrix (Fin 3) (Fin 3) E) - 1 := ⟨_, rfl⟩
  rw [← hNdef]
  have hNN : N * N = 0 := by
    rw [hNdef, sub_mul, mul_sub, mul_sub, htt, mul_one, one_mul, mul_one]
    calc (1 : Matrix (Fin 3) (Fin 3) E) - t - (t - 1) = (1 + 1) - (t + t) := by abel
      _ = 0 := by rw [h2, h2, sub_zero]
  have hN0 : ∃ y₀, N *ᵥ y₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply ht1
    have hN : N = 0 := Matrix.toLin'.injective (LinearMap.ext fun y => by
      rw [Matrix.toLin'_apply, h y, map_zero, LinearMap.zero_apply])
    apply Units.ext
    rw [Units.val_one, ← sub_eq_zero, ← hNdef, hN]
  have hrange : finrank E (LinearMap.range (Matrix.toLin' N)) ≤ 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' N)
    have h2 : LinearMap.range (Matrix.toLin' N) ≤ LinearMap.ker (Matrix.toLin' N) := by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, hNN,
        zero_mulVec]
    have h3 := Submodule.finrank_mono h2
    rw [Module.finrank_fin_fun] at h1
    omega
  obtain ⟨u', hu'⟩ := finrank_le_one_iff.1 hrange
  obtain ⟨y₀, hy₀⟩ := hN0
  have hall : ∀ y, ∃ κ : E, N *ᵥ y = κ • (u' : Fin 3 → E) := by
    intro y
    obtain ⟨κ, hκ⟩ := hu' ⟨N *ᵥ y, ⟨y, Matrix.toLin'_apply N y⟩⟩
    exact ⟨κ, (congrArg Subtype.val hκ).symm⟩
  refine ⟨u', ?_, hall, y₀, hy₀⟩
  intro hu0
  obtain ⟨κ, hκ⟩ := hall y₀
  rw [hu0, smul_zero] at hκ
  exact hy₀ hκ

theorem exists_eigen_of_commute (ht2 : t * t = 1) (ht1 : t ≠ 1) {M : Matrix (Fin 3) (Fin 3) E}
    (hMt : M * (t : Matrix (Fin 3) (Fin 3) E) = (t : Matrix (Fin 3) (Fin 3) E) * M) :
    ∃ y : Fin 3 → E, y ≠ 0 ∧ ∃ μ : E, M *ᵥ y = μ • y := by
  obtain ⟨u, -, hall, y₀, hy₀⟩ := exists_rank_one ht2 ht1
  have hMN : M * ((t : Matrix (Fin 3) (Fin 3) E) - 1) =
      ((t : Matrix (Fin 3) (Fin 3) E) - 1) * M := by
    rw [mul_sub, sub_mul, hMt, mul_one, one_mul]
  obtain ⟨κ₀, hκ₀⟩ := hall y₀
  obtain ⟨κ₁, hκ₁⟩ := hall (M *ᵥ y₀)
  have hκ₀0 : κ₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hκ₀
    exact hy₀ hκ₀
  refine ⟨_, hy₀, κ₁ / κ₀, ?_⟩
  rw [mulVec_mulVec, hMN, ← mulVec_mulVec, hκ₁, hκ₀, smul_smul, div_mul_cancel₀ _ hκ₀0]

theorem exists_fixed_pair (ht2 : t * t = 1) (ht1 : t ≠ 1) (a : Matrix (Fin 3) (Fin 3) E) :
    ∃ x : Fin 3 → E, x ≠ 0 ∧ (t : Matrix (Fin 3) (Fin 3) E) *ᵥ x = x ∧
      (t : Matrix (Fin 3) (Fin 3) E) *ᵥ (a *ᵥ x) = a *ᵥ x := by
  obtain ⟨u, hu0, hall, -⟩ := exists_rank_one ht2 ht1
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  let Φ : (Fin 3 → E) →ₗ[E] E × E :=
    (LinearMap.proj i₀ ∘ₗ Matrix.toLin' ((t : Matrix (Fin 3) (Fin 3) E) - 1)).prod
      (LinearMap.proj i₀ ∘ₗ Matrix.toLin' (((t : Matrix (Fin 3) (Fin 3) E) - 1) * a))
  have hker : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
    norm_num)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hx
  have hx' := Prod.ext_iff.1 hx
  simp only [Φ, LinearMap.prod_apply, LinearMap.coe_comp,
    LinearMap.coe_proj, Prod.fst_zero, Prod.snd_zero] at hx'
  have key : ∀ y, (((t : Matrix (Fin 3) (Fin 3) E) - 1) *ᵥ y) i₀ = 0 →
      (t : Matrix (Fin 3) (Fin 3) E) *ᵥ y = y := by
    intro y hy
    obtain ⟨κ, hκ⟩ := hall y
    rw [hκ, Pi.smul_apply, smul_eq_mul] at hy
    have : ((t : Matrix (Fin 3) (Fin 3) E) - 1) *ᵥ y = 0 := by
      rw [hκ, (mul_eq_zero.1 hy).resolve_right hi₀, zero_smul]
    rwa [sub_mulVec, one_mulVec, sub_eq_zero] at this
  refine ⟨x, hx0, key x hx'.1, key _ ?_⟩
  rw [mulVec_mulVec]
  exact hx'.2

end Involution

theorem exists_nonscalar_eigen [CharP E 2] {A : Subgroup (GL (Fin 3) E)} {t : GL (Fin 3) E}
    (hAodd : ∀ a ∈ A, ∃ m, Odd m ∧ a ^ m = 1) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hAt : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAns : ∃ a ∈ A, ¬ IsScalarMat a) :
    ∃ a ∈ A, ¬ IsScalarMat a ∧ ∃ x : Fin 3 → E, x ≠ 0 ∧ ∃ μ : E,
      (a : Matrix (Fin 3) (Fin 3) E) *ᵥ x = μ • x := by
  by_contra H
  have Hsc : ∀ a ∈ A, ∀ x : Fin 3 → E, x ≠ 0 → ∀ μ : E,
      (a : Matrix (Fin 3) (Fin 3) E) *ᵥ x = μ • x → IsScalarMat a := by
    intro a ha x hx μ h
    by_contra hns
    exact H ⟨a, ha, hns, x, hx, μ, h⟩
  obtain ⟨a₀, ha₀, hns⟩ := hAns
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_left ht2).symm
  have hbA : t * a₀ * t ∈ A := by
    have := hAt a₀ ha₀
    rwa [htinv] at this
  have hcA : a₀ * (t * a₀ * t) ∈ A := A.mul_mem ha₀ hbA
  have hab := hAab a₀ ha₀ _ hbA
  have hct : ((a₀ * (t * a₀ * t) : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
      (t : Matrix (Fin 3) (Fin 3) E) =
      (t : Matrix (Fin 3) (Fin 3) E) *
        ((a₀ * (t * a₀ * t) : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    calc a₀ * (t * a₀ * t) * t = t * a₀ * t * a₀ * t := by rw [hab]
      _ = t * (a₀ * (t * a₀ * t)) := by simp only [mul_assoc]
  obtain ⟨y, hy0, μ, hy⟩ := exists_eigen_of_commute ht2 ht1 hct
  obtain ⟨c, hc⟩ := Hsc _ hcA y hy0 μ hy
  obtain ⟨x, hx0, htx, htax⟩ := exists_fixed_pair ht2 ht1 (a₀ : Matrix (Fin 3) (Fin 3) E)
  have hx : ((a₀ * a₀ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x = c • x := by
    have h1 : ((a₀ * (t * a₀ * t) : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x = c • x := by
      rw [hc, smul_mulVec, one_mulVec]
    rw [← h1]
    simp only [Units.val_mul, ← mulVec_mulVec, htx, htax]
  obtain ⟨ν, hν⟩ := Hsc _ (A.mul_mem ha₀ ha₀) x hx0 c hx
  obtain ⟨m, hm, ha₀m⟩ := hAodd a₀ ha₀
  obtain ⟨k, hk⟩ := eq_sq_pow_of_odd hm ha₀m
  apply hns
  refine ⟨ν ^ (k + 1), ?_⟩
  rw [hk, Units.val_pow_eq_pow_val, hν, smul_pow, one_pow]

theorem exists_root_of_bar_fixed (hU : UnitaryFieldData p f E) {u v : E} (hu : hU.bar u = u)
    (hv : hU.bar v = v) : ∃ μ : E, μ ^ 2 + u * μ + v = 0 := by
  classical
  have : Fact p.Prime := ⟨hU.prime⟩
  have : CharP E p := hU.charP
  have := hU.finite
  have := Fintype.ofFinite E
  by_contra hno
  push Not at hno
  obtain ⟨P, hP⟩ : ∃ P : Polynomial E, P = .X ^ 2 + .C u * .X + .C v := ⟨_, rfl⟩
  have hPdeg : P.natDegree = 2 := by
    rw [hP]; compute_degree!
  have hPm : P.Monic := by
    rw [hP]; monicity!
  have hirr : Irreducible P := by
    rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hPm (by omega)
      (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun μ hμ => hno μ ?_
    rw [Polynomial.mem_roots hPm.ne_zero, Polynomial.IsRoot, hP] at hμ
    simpa using hμ
  have : Fact (Irreducible P) := ⟨hirr⟩
  have hθ : AdjoinRoot.root P ^ 2 + algebraMap E (AdjoinRoot P) u * AdjoinRoot.root P +
      algebraMap E (AdjoinRoot P) v = 0 := by
    have h : AdjoinRoot.mk P (.X ^ 2 + .C u * .X + .C v) = 0 := by
      rw [← hP]; exact AdjoinRoot.mk_self
    simpa [AdjoinRoot.algebraMap_eq] using h
  have hinj : Function.Injective (algebraMap E (AdjoinRoot P)) := (algebraMap E _).injective
  have : CharP (AdjoinRoot P) p := charP_of_injective_algebraMap hinj p
  obtain ⟨θ, hθdef⟩ : ∃ θ : AdjoinRoot P, θ = AdjoinRoot.root P := ⟨_, rfl⟩
  rw [← hθdef] at hθ
  obtain ⟨φ, hφdef⟩ : ∃ φ : AdjoinRoot P →+* AdjoinRoot P, φ = iterateFrobenius _ p f :=
    ⟨_, rfl⟩
  have hφa : ∀ e : E, φ (algebraMap E _ e) = algebraMap E _ (hU.bar e) := by
    intro e; rw [hφdef, iterateFrobenius_def, ← map_pow, hU.bar_apply]
  have hφθ : φ θ ^ 2 + algebraMap E _ u * φ θ + algebraMap E _ v = 0 := by
    have h := congrArg φ hθ
    rw [map_zero, map_add, map_add, map_mul, map_pow, hφa, hφa, hu, hv] at h
    exact h
  have hcases : φ θ = θ ∨ φ θ = -algebraMap E _ u - θ := by
    have h : (φ θ - θ) * (φ θ + algebraMap E _ u + θ) = 0 := by
      linear_combination hφθ - hθ
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (by linear_combination h)
  have hφφ : φ (φ θ) = θ := by
    rcases hcases with h | h
    · rw [h, h]
    · rw [h, map_sub, map_neg, hφa, hu, h]; ring
  have hpow : θ ^ Nat.card E = θ := by
    conv_rhs => rw [← hφφ]
    rw [hφdef, iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, ← two_mul,
      hU.card]
  have hq1 : 1 < Nat.card E := by
    rw [hU.card]
    exact Nat.one_lt_pow (by have := hU.one_le; omega) hU.prime.one_lt
  have hθmem : θ ∈ Set.range (algebraMap E (AdjoinRoot P)) := by
    by_contra hθn
    obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial (AdjoinRoot P), Q = .X ^ Nat.card E - .X := ⟨_, rfl⟩
    have hQ0 : Q ≠ 0 := by rw [hQ]; exact FiniteField.X_pow_card_sub_X_ne_zero _ hq1
    have hQdeg : Q.natDegree = Nat.card E := by
      rw [hQ]; exact FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1
    obtain ⟨S, hSdef⟩ : ∃ S : Finset (AdjoinRoot P),
        S = insert θ (Finset.univ.image (algebraMap E (AdjoinRoot P))) := ⟨_, rfl⟩
    have hS : S.card = Nat.card E + 1 := by
      rw [hSdef, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hinj,
        Finset.card_univ, Nat.card_eq_fintype_card]
      intro hmem
      apply hθn
      obtain ⟨e, -, he⟩ := Finset.mem_image.1 hmem
      exact ⟨e, he⟩
    have hsub : S.val ⊆ Q.roots := by
      intro z hz
      rw [Polynomial.mem_roots hQ0, Polynomial.IsRoot, hQ]
      have hz' : z ∈ S := hz
      rw [hSdef] at hz'
      rcases Finset.mem_insert.1 hz' with rfl | hz'
      · rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hpow, sub_self]
      · obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hz'
        rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow,
          Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
    have := Polynomial.card_le_degree_of_subset_roots hsub
    omega
  obtain ⟨e, he⟩ := hθmem
  apply hno e
  apply hinj
  rw [map_add, map_add, map_mul, map_pow, he, map_zero]
  exact hθ

theorem exists_eigen_of_nondegenerate (hU : UnitaryFieldData 2 f E)
    {U : Submodule E (Fin 3 → E)} (hU2 : finrank E U = 2)
    (hnd : ∀ y ∈ U, (∀ w ∈ U, hform hU y w = 0) → y = 0) {M : Matrix (Fin 3) (Fin 3) E}
    (hM : ∀ v w, hform hU (M *ᵥ v) (M *ᵥ w) = hform hU v w) (hMU : ∀ u ∈ U, M *ᵥ u ∈ U) :
    ∃ y ∈ U, y ≠ 0 ∧ ∃ μ : E, M *ᵥ y = μ • y := by
  have : CharP E 2 := hU.charP
  have hsep : ((hform hU).domRestrict₁₂ U U).SeparatingLeft := by
    intro x hx
    refine Subtype.ext (hnd x x.2 fun w hw => ?_)
    have := hx ⟨w, hw⟩
    rwa [LinearMap.domRestrict₁₂_apply] at this
  obtain ⟨⟨y, hyU⟩, hy0, hyy⟩ := CFSG.LinearGroups.exists_isotropic_of_finrank_two hU
    ((hform_isSymm hU).domRestrict U) hsep hU2
  rw [LinearMap.domRestrict₁₂_apply] at hyy
  have hy0' : y ≠ 0 := fun h => hy0 (Subtype.ext h)
  by_cases hey : ∃ μ : E, M *ᵥ y = μ • y
  · exact ⟨y, hyU, hy0', hey⟩
  push Not at hey
  have hli := linearIndependent_pair_of_not_smul hy0' hey
  have hspan := exists_eq_add_of_pair hU2 hyU (hMU y hyU) hli
  obtain ⟨d, s, hds⟩ := hspan _ (hMU _ (hMU y hyU))
  obtain ⟨β, hβdef⟩ : ∃ β, β = hform hU y (M *ᵥ y) := ⟨_, rfl⟩
  have hMyMy : hform hU (M *ᵥ y) (M *ᵥ y) = 0 := by rw [hM, hyy]
  have hMyy : hform hU (M *ᵥ y) y = hU.bar β := by rw [hform_symm hU y, hβdef]
  have hβ : β ≠ 0 := by
    intro h0
    apply hy0'
    refine hnd y hyU fun w hw => ?_
    obtain ⟨α, γ, rfl⟩ := hspan w hw
    rw [map_add, map_smul, map_smul, hyy, ← hβdef, h0, smul_zero, smul_zero, add_zero]
  have hβ' : hU.bar β ≠ 0 := (map_ne_zero hU.bar).2 hβ
  have R1 : d * hU.bar β = β := by
    have h := hM y (M *ᵥ y)
    rw [← hds, map_add, map_smul, map_smul, hMyy, hMyMy, ← hβdef, smul_zero, add_zero,
      smul_eq_mul] at h
    exact h
  have R2 : hU.bar d * s * β + hU.bar s * d * hU.bar β = 0 := by
    have h := hM (M *ᵥ y) (M *ᵥ y)
    rw [hMyMy, ← hds] at h
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hyy, hMyMy, hMyy, ← hβdef] at h
    linear_combination h
  have e1 : hU.bar d * β = hU.bar β := by
    have := congrArg hU.bar R1
    rwa [map_mul, hU.bar_bar] at this
  have hsym : hU.bar s * β = s * hU.bar β := by
    have h3 : s * hU.bar β + hU.bar s * β = 0 := by
      linear_combination R2 - s * e1 - hU.bar s * R1
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    linear_combination h3 - s * hU.bar β * h2
  have hu : hU.bar (-s / β) = -s / β := by
    rw [map_div₀, map_neg, div_eq_div_iff hβ' hβ]
    linear_combination -hsym
  have hv : hU.bar (-d / β ^ 2) = -d / β ^ 2 := by
    rw [map_div₀, map_neg, map_pow, div_eq_div_iff (pow_ne_zero 2 hβ') (pow_ne_zero 2 hβ)]
    linear_combination -β * e1 + hU.bar β * R1
  obtain ⟨μ, hμ⟩ := exists_root_of_bar_fixed hU hu hv
  obtain ⟨r, hr⟩ : ∃ r, r = β * μ := ⟨_, rfl⟩
  have hrr : r ^ 2 - s * r - d = 0 := by
    have : r ^ 2 - s * r - d = β ^ 2 * (μ ^ 2 + -s / β * μ + -d / β ^ 2) := by
      rw [hr]; field_simp; ring
    rw [this, hμ, mul_zero]
  refine ⟨M *ᵥ y - (s - r) • y, U.sub_mem (hMU y hyU) (U.smul_mem _ hyU), ?_, r, ?_⟩
  · intro h
    exact hey (s - r) (sub_eq_zero.1 h)
  · rw [mulVec_sub, mulVec_smul, ← hds]
    have hd : d = r ^ 2 - s * r := by linear_combination -hrr
    rw [hd]
    module

theorem exists_eigen_of_plane (hU : UnitaryFieldData 2 f E) {U : Submodule E (Fin 3 → E)}
    (hU2 : finrank E U = 2) {M : Matrix (Fin 3) (Fin 3) E}
    (hM : ∀ v w, hform hU (M *ᵥ v) (M *ᵥ w) = hform hU v w) (hMU : ∀ u ∈ U, M *ᵥ u ∈ U) :
    ∃ y ∈ U, y ≠ 0 ∧ ∃ μ : E, M *ᵥ y = μ • y := by
  by_cases hnd : ∀ y ∈ U, (∀ w ∈ U, hform hU y w = 0) → y = 0
  · exact exists_eigen_of_nondegenerate hU hU2 hnd hM hMU
  push Not at hnd
  obtain ⟨y, hyU, hyrad, hy0⟩ := hnd
  refine ⟨y, hyU, hy0, ?_⟩
  by_contra hey
  push Not at hey
  have hli := linearIndependent_pair_of_not_smul hy0 hey
  have hspan := exists_eq_add_of_pair hU2 hyU (hMU y hyU) hli
  have hyy : hform hU y y = 0 := hyrad y hyU
  have hMy : ∀ w ∈ U, hform hU (M *ᵥ y) w = 0 := by
    intro w hw
    obtain ⟨α, γ, rfl⟩ := hspan w hw
    rw [map_add, map_smul, map_smul, hform_symm hU y, hyrad _ (hMU y hyU), map_zero, hM, hyy,
      smul_zero, smul_zero, add_zero]
  apply not_totallyIsotropic_two hU hU2
  intro v hv w hw
  obtain ⟨α, γ, rfl⟩ := hspan v hv
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hyrad w hw, hMy w hw, mul_zero, add_zero]

theorem exists_second_eigen [CharP E 2] {U : Submodule E (Fin 3 → E)} (hU2 : finrank E U = 2)
    {M : Matrix (Fin 3) (Fin 3) E} {m : ℕ} (hm : Odd m) (hMm : M ^ m = 1)
    (hMU : ∀ u ∈ U, M *ᵥ u ∈ U) {y₀ : Fin 3 → E} (hy₀U : y₀ ∈ U) (hy₀ : y₀ ≠ 0) {μ : E}
    (hMy₀ : M *ᵥ y₀ = μ • y₀) {u₁ : Fin 3 → E} (hu₁U : u₁ ∈ U) (hu₁ : M *ᵥ u₁ ≠ μ • u₁) :
    ∃ z ∈ U, ∃ β : E, β ≠ μ ∧ M *ᵥ z = β • z ∧ LinearIndependent E ![y₀, z] ∧
      ∀ N : Matrix (Fin 3) (Fin 3) E, (∀ u ∈ U, N *ᵥ u ∈ U) →
        (∀ u ∈ U, N *ᵥ (M *ᵥ u) = M *ᵥ (N *ᵥ u)) →
        (∃ κ : E, N *ᵥ y₀ = κ • y₀) ∧ ∃ κ : E, N *ᵥ z = κ • z := by
  have hli1 : LinearIndependent E ![y₀, u₁] := by
    refine linearIndependent_pair_of_not_smul hy₀ fun c hc => hu₁ ?_
    rw [hc, mulVec_smul, hMy₀, smul_comm]
  obtain ⟨α, β, hαβ⟩ := exists_eq_add_of_pair hU2 hy₀U hu₁U hli1 _ (hMU u₁ hu₁U)
  obtain ⟨z, hzdef⟩ : ∃ z, z = α • y₀ + (β - μ) • u₁ := ⟨_, rfl⟩
  have hzU : z ∈ U := by
    rw [hzdef]
    exact U.add_mem (U.smul_mem _ hy₀U) (U.smul_mem _ hu₁U)
  have hz : M *ᵥ z = β • z := by
    rw [hzdef, mulVec_add, mulVec_smul, mulVec_smul, hMy₀, ← hαβ]
    module
  have hu₁z : M *ᵥ u₁ = μ • u₁ + z := by
    rw [hzdef, ← hαβ]
    module
  have hβμ : β ≠ μ := by
    intro hβ
    apply hu₁
    have h0 := eq_zero_of_odd_pow hm hMm (by rw [hz, hβ]) hu₁z
    rw [hu₁z, h0, add_zero]
  have hli2 : LinearIndependent E ![y₀, z] := by
    rw [LinearIndependent.pair_iff]
    intro s r h
    have h' : (s + r * α) • y₀ + (r * (β - μ)) • u₁ = 0 := by
      rw [← h, hzdef]
      module
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hli1 _ _ h'
    have hr : r = 0 := (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hβμ)
    subst hr
    exact ⟨by simpa using h1, rfl⟩
  refine ⟨z, hzU, β, hβμ, hz, hli2, fun N hNU hNM => ⟨?_, ?_⟩⟩
  · obtain ⟨s, r, hsr⟩ := exists_eq_add_of_pair hU2 hy₀U hzU hli2 _ (hNU y₀ hy₀U)
    have h1 : M *ᵥ (N *ᵥ y₀) = μ • (N *ᵥ y₀) := by
      rw [← hNM y₀ hy₀U, hMy₀, mulVec_smul]
    rw [← hsr, mulVec_add, mulVec_smul, mulVec_smul, hMy₀, hz] at h1
    have h2 : (0 : E) • y₀ + (r * (β - μ)) • z = 0 := by
      linear_combination (norm := module) h1
    obtain ⟨-, h3⟩ := LinearIndependent.pair_iff.1 hli2 _ _ h2
    have hr : r = 0 := (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hβμ)
    exact ⟨s, by rw [← hsr, hr, zero_smul, add_zero]⟩
  · obtain ⟨s, r, hsr⟩ := exists_eq_add_of_pair hU2 hy₀U hzU hli2 _ (hNU z hzU)
    have h1 : M *ᵥ (N *ᵥ z) = β • (N *ᵥ z) := by
      rw [← hNM z hzU, hz, mulVec_smul]
    rw [← hsr, mulVec_add, mulVec_smul, mulVec_smul, hMy₀, hz] at h1
    have h2 : (s * (μ - β)) • y₀ + (0 : E) • z = 0 := by
      linear_combination (norm := module) h1
    obtain ⟨h3, -⟩ := LinearIndependent.pair_iff.1 hli2 _ _ h2
    have hs : s = 0 := (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hβμ.symm)
    exact ⟨r, by rw [← hsr, hs, zero_smul, zero_add]⟩

def CommonEigen (B : Subgroup (GL (Fin 3) E)) (v : Fin 3 → E) : Prop :=
  ∀ b ∈ B, ∃ μ : E, (b : Matrix (Fin 3) (Fin 3) E) *ᵥ v = μ • v

def Separates (B : Subgroup (GL (Fin 3) E)) (u v : Fin 3 → E) : Prop :=
  ∃ b ∈ B, ∃ μ ν : E, (b : Matrix (Fin 3) (Fin 3) E) *ᵥ u = μ • u ∧
    (b : Matrix (Fin 3) (Fin 3) E) *ᵥ v = ν • v ∧ μ ≠ ν

theorem Separates.symm {B : Subgroup (GL (Fin 3) E)} {u v : Fin 3 → E} (h : Separates B u v) :
    Separates B v u := by
  obtain ⟨b, hb, μ, ν, h1, h2, h3⟩ := h
  exact ⟨b, hb, ν, μ, h2, h1, h3.symm⟩

theorem separates_of_three {B : Subgroup (GL (Fin 3) E)} {x y z : Fin 3 → E}
    (hxy : Separates B x y) (hxz : Separates B x z) (hyz : Separates B y z) :
    ∀ i j : Fin 3, i ≠ j → Separates B (![x, y, z] i) (![x, y, z] j) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact hxy
    | exact hxz
    | exact hyz
    | exact hxy.symm
    | exact hxz.symm
    | exact hyz.symm

theorem frame_of_triple (hU : UnitaryFieldData 2 f E) {C B : Subgroup (GL (Fin 3) E)}
    {t : GL (Fin 3) E} (hC : C ≤ gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))
    (hodd : Odd (Nat.card C)) (hiso : ¬ FixesIsotropicLine hU C)
    (hB : B ≤ gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))
    (hBC : ∀ c ∈ C, ∀ b ∈ B, c⁻¹ * b * c ∈ B) (hBt : ∀ b ∈ B, t⁻¹ * b * t ∈ B)
    {x : Fin 3 → Fin 3 → E} (hli : LinearIndependent E x) (heig : ∀ i, CommonEigen B (x i))
    (hdist : ∀ i j, i ≠ j → Separates B (x i) (x j)) :
    ∃ v : Fin 3 → (Fin 3 → E), IsOrthonormalFrame hU v ∧ (∀ c ∈ C, PermutesLines v c) ∧
      PermutesLines v t := by
  have hx0 : ∀ i, x i ≠ 0 := fun i => hli.ne_zero i
  have honly : ∀ y : Fin 3 → E, y ≠ 0 → CommonEigen B y → ∃ i, ∃ c : E, y = c • x i := by
    intro y hy0 hy
    obtain ⟨a, ha⟩ := exists_coeffs hli y
    have hcoef : ∀ i j, i ≠ j → a i = 0 ∨ a j = 0 := by
      intro i j hij
      by_contra hcon
      push Not at hcon
      obtain ⟨b, hb, μ, ν, hbi, hbj, hμν⟩ := hdist i j hij
      obtain ⟨κ, hκ⟩ := hy b hb
      choose μs hμs using fun l => heig l b hb
      have h1 : ∑ l, (a l * μs l) • x l = ∑ l, (κ * a l) • x l := by
        have e1 : (b : Matrix (Fin 3) (Fin 3) E) *ᵥ y = ∑ l, (a l * μs l) • x l := by
          rw [← ha, mulVec_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [mulVec_smul, hμs, smul_smul]
        have e2 : κ • y = ∑ l, (κ * a l) • x l := by
          rw [← ha, Finset.smul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [smul_smul]
        rw [← e1, ← e2, hκ]
      have h2 := congrFun (coeffs_eq hli h1)
      have hi : μs i = κ := by
        have := h2 i
        rw [mul_comm κ] at this
        exact mul_left_cancel₀ hcon.1 this
      have hj : μs j = κ := by
        have := h2 j
        rw [mul_comm κ] at this
        exact mul_left_cancel₀ hcon.2 this
      apply hμν
      rw [eigen_unique (hx0 i) hbi (hμs i), eigen_unique (hx0 j) hbj (hμs j), hi, hj]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      apply hy0
      rw [← ha]
      simp [h]
    refine ⟨i, a i, ?_⟩
    rw [← ha, Finset.sum_eq_single i]
    · intro l _ hl
      rw [(hcoef i l (Ne.symm hl)).resolve_left hi, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hperm : ∀ g : GL (Fin 3) E, (∀ b ∈ B, g⁻¹ * b * g ∈ B) →
      ∀ i, ∃ j, ∃ c : E, (g : Matrix (Fin 3) (Fin 3) E) *ᵥ x i = c • x j := by
    intro g hg i
    apply honly _ (mulVec_ne_zero g (hx0 i))
    intro b hb
    obtain ⟨κ, hκ⟩ := heig i _ (hg b hb)
    exact ⟨κ, by rw [mulVec_conj g b, hκ, mulVec_smul]⟩
  have hpair : ∀ b ∈ B, ∀ i j, ∀ μ ν : E, (b : Matrix (Fin 3) (Fin 3) E) *ᵥ x i = μ • x i →
      (b : Matrix (Fin 3) (Fin 3) E) *ᵥ x j = ν • x j → hform hU (x i) (x j) ≠ 0 →
      hU.bar μ * ν = 1 := by
    intro b hb i j μ ν hi hj hne
    have h := hform_mulVec (hB hb) (x i) (x j)
    rw [hi, hj] at h
    simp only [map_smulₛₗ, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul] at h
    have : (hU.bar μ * ν - 1) * hform hU (x i) (x j) = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)
  have hcancel : ∀ α β γ : E, hU.bar α * β = 1 → hU.bar α * γ = 1 → β = γ := by
    intro α β γ h1 h2
    exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h1) (h1.trans h2.symm)
  have hthird : ∀ i j k l : Fin 3, i ≠ j → i ≠ k → j ≠ k → l = i ∨ l = j ∨ l = k := by decide
  have horth3 : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → hform hU (x i) (x j) = 0 := by
    intro i j k hij hik hjk
    by_contra hne
    have hne' : hform hU (x j) (x i) ≠ 0 := by
      rw [hform_symm hU (x i) (x j)]
      exact (map_ne_zero hU.bar).2 hne
    obtain ⟨b, hb, μ, ν, hbi, hbj, hμν⟩ := hdist i j hij
    have hii : hform hU (x i) (x i) = 0 := by
      by_contra h
      exact hμν (hcancel _ _ _ (hpair b hb i i μ μ hbi hbi h) (hpair b hb i j μ ν hbi hbj hne))
    have hjj : hform hU (x j) (x j) = 0 := by
      by_contra h
      exact hμν (hcancel _ _ _ (hpair b hb j i ν μ hbj hbi hne')
        (hpair b hb j j ν ν hbj hbj h))
    have hik0 : hform hU (x i) (x k) = 0 := by
      by_contra h
      obtain ⟨b', hb', μ', ν', hb'j, hb'k, hμν'⟩ := hdist j k hjk
      obtain ⟨κ, hb'i⟩ := heig i b' hb'
      exact hμν' (hcancel _ _ _ (hpair b' hb' i j κ μ' hb'i hb'j hne)
        (hpair b' hb' i k κ ν' hb'i hb'k h))
    have hjk0 : hform hU (x j) (x k) = 0 := by
      by_contra h
      obtain ⟨b', hb', μ', ν', hb'i, hb'k, hμν'⟩ := hdist i k hik
      obtain ⟨κ, hb'j⟩ := heig j b' hb'
      exact hμν' (hcancel _ _ _ (hpair b' hb' j i κ μ' hb'j hb'i hne')
        (hpair b' hb' j k κ ν' hb'j hb'k h))
    have hkk : hform hU (x k) (x k) ≠ 0 := by
      intro hkk
      apply hx0 k
      apply eq_zero_of_hform_basis hU hli
      intro l
      rcases hthird i j k l hij hik hjk with rfl | rfl | rfl
      · rw [hform_symm hU, hik0, map_zero]
      · rw [hform_symm hU, hjk0, map_zero]
      · exact hkk
    apply hiso
    refine ⟨x i, hx0 i, by rw [← hform_apply]; exact hii, fun c hc => ?_⟩
    have hCU := hform_mulVec (hC hc)
    have hne0 : ∀ l, ∀ κ : E, ∀ m, (c : Matrix (Fin 3) (Fin 3) E) *ᵥ x l = κ • x m → κ ≠ 0 := by
      rintro l κ m h rfl
      rw [zero_smul] at h
      exact mulVec_ne_zero c (hx0 l) h
    have himg : ∀ l, hform hU (x l) (x l) = 0 → ∀ κ : E,
        (c : Matrix (Fin 3) (Fin 3) E) *ᵥ x l ≠ κ • x k := by
      intro l hl κ hκ
      have hκ0 := hne0 l κ k hκ
      have h := hCU (x l) (x l)
      rw [hκ, hl] at h
      simp only [map_smulₛₗ, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul] at h
      have h' : (hU.bar κ * κ) * hform hU (x k) (x k) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h' | h'
      · rcases mul_eq_zero.1 h' with h' | h'
        · exact hκ0 ((map_eq_zero hU.bar).1 h')
        · exact hκ0 h'
      · exact hkk h'
    have hpij := pair_of_linearIndependent hli hij
    obtain ⟨m₁, κ₁, h₁⟩ := hperm c (hBC c hc) i
    rcases hthird i j k m₁ hij hik hjk with rfl | rfl | rfl
    · exact ⟨κ₁, h₁⟩
    · exfalso
      have hκ₁0 := hne0 _ _ _ h₁
      obtain ⟨m₂, κ₂, h₂⟩ := hperm c (hBC c hc) m₁
      rcases hthird i m₁ k m₂ hij hik hjk with rfl | rfl | rfl
      · have hc2 : ((c * c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x m₂ =
            (κ₁ * κ₂) • x m₂ := by
          rw [Units.val_mul, ← mulVec_mulVec, h₁, mulVec_smul, h₂, smul_smul]
        obtain ⟨n, hn⟩ := eq_sq_pow_of_odd (odd_orderOf_of_mem hodd hc) (pow_orderOf_eq_one c)
        have hcx : (c : Matrix (Fin 3) (Fin 3) E) *ᵥ x m₂ = (κ₁ * κ₂) ^ (n + 1) • x m₂ := by
          conv_lhs => rw [hn]
          rw [Units.val_pow_eq_pow_val]
          exact pow_mulVec_of_eigen hc2 _
        rw [h₁] at hcx
        have := LinearIndependent.pair_iff.1 hpij (-(κ₁ * κ₂) ^ (n + 1)) κ₁
          (by rw [hcx]; module)
        exact hκ₁0 this.2
      · have h0 : (c : Matrix (Fin 3) (Fin 3) E) *ᵥ (κ₂ • x i - κ₁ • x m₂) = 0 := by
          rw [mulVec_sub, mulVec_smul, mulVec_smul, h₁, h₂, smul_smul, smul_smul, mul_comm,
            sub_self]
        have h0' : κ₂ • x i - κ₁ • x m₂ = 0 := by
          by_contra h
          exact mulVec_ne_zero c h h0
        have := LinearIndependent.pair_iff.1 hpij κ₂ (-κ₁) (by rw [← h0']; module)
        exact hκ₁0 (neg_eq_zero.1 this.2)
      · exact himg _ hjj κ₂ h₂
    · exact absurd h₁ (himg i hii κ₁)
  have horth : ∀ i j, i ≠ j → hform hU (x i) (x j) = 0 := by
    intro i j hij
    obtain ⟨k, hik, hjk⟩ : ∃ k, i ≠ k ∧ j ≠ k := by
      revert i j
      decide
    exact horth3 i j k hij hik hjk
  have hanis : ∀ i, hform hU (x i) (x i) ≠ 0 := by
    intro i hii
    apply hx0 i
    apply eq_zero_of_hform_basis hU hli
    intro l
    by_cases hl : l = i
    · rw [hl]
      exact hii
    · exact horth i l (Ne.symm hl)
  choose c hc using fun i =>
    CFSG.OddSolvableUnitary.exists_apply_smul_smul_eq_one hU (hform_isSymm hU) (hanis i)
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h
    have := hc i
    rw [h, zero_smul] at this
    simp at this
  have hperm' : ∀ g : GL (Fin 3) E, (∀ b ∈ B, g⁻¹ * b * g ∈ B) →
      PermutesLines (fun i => c i • x i) g := by
    intro g hg i
    obtain ⟨j, κ, hκ⟩ := hperm g hg i
    refine ⟨j, c i * κ / c j, ?_⟩
    simp only
    rw [mulVec_smul, hκ, smul_smul, smul_smul, div_mul_cancel₀ _ (hc0 j)]
  refine ⟨fun i => c i • x i, ?_, fun g hg => hperm' g (hBC g hg), hperm' t hBt⟩
  intro i j
  simp only
  rw [← hform_apply]
  split_ifs with hij
  · subst hij
    exact hc i
  · simp only [map_smulₛₗ, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul, horth i j hij,
      mul_zero]

theorem dichotomy (hU : UnitaryFieldData 2 f E) {A : Subgroup (GL (Fin 3) E)}
    (hAU : ∀ a ∈ A, ∀ v w, hform hU ((a : Matrix (Fin 3) (Fin 3) E) *ᵥ v)
      ((a : Matrix (Fin 3) (Fin 3) E) *ᵥ w) = hform hU v w)
    (hAodd : ∀ a ∈ A, ∃ m, Odd m ∧ a ^ m = 1) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {a : GL (Fin 3) E} (haA : a ∈ A) (hans : ¬ IsScalarMat a) {x₀ : Fin 3 → E} (hx₀ : x₀ ≠ 0)
    {c₀ : E} (hax₀ : (a : Matrix (Fin 3) (Fin 3) E) *ᵥ x₀ = c₀ • x₀) :
    (∃ x : Fin 3 → Fin 3 → E, LinearIndependent E x ∧ (∀ i, CommonEigen A (x i)) ∧
      ∀ i j, i ≠ j → Separates A (x i) (x j)) ∨
    ∃ y₁ y₂ w : Fin 3 → E, LinearIndependent E ![y₁, y₂, w] ∧
      (∀ b ∈ A, ∃ μ ν : E, (b : Matrix (Fin 3) (Fin 3) E) *ᵥ y₁ = μ • y₁ ∧
        (b : Matrix (Fin 3) (Fin 3) E) *ᵥ y₂ = μ • y₂ ∧
        (b : Matrix (Fin 3) (Fin 3) E) *ᵥ w = ν • w) ∧ Separates A y₁ w := by
  have : CharP E 2 := hU.charP
  obtain ⟨m, hm, ham⟩ := hAodd a haA
  have ham' := val_pow_eq_one ham
  obtain ⟨T, hTdef⟩ : ∃ T, T = (a : Matrix (Fin 3) (Fin 3) E) - c₀ • 1 := ⟨_, rfl⟩
  have hTv : ∀ v, T *ᵥ v = (a : Matrix (Fin 3) (Fin 3) E) *ᵥ v - c₀ • v := by
    intro v
    rw [hTdef, sub_mulVec, smul_mulVec, one_mulVec]
  obtain ⟨K, hKdef⟩ : ∃ K, K = LinearMap.ker (Matrix.toLin' T) := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R, R = LinearMap.range (Matrix.toLin' T) := ⟨_, rfl⟩
  have hmemK : ∀ v, v ∈ K ↔ (a : Matrix (Fin 3) (Fin 3) E) *ᵥ v = c₀ • v := by
    intro v
    rw [hKdef, LinearMap.mem_ker, Matrix.toLin'_apply, hTv, sub_eq_zero]
  have hmemR : ∀ v, v ∈ R ↔ ∃ w, T *ᵥ w = v := by
    intro v
    rw [hRdef, LinearMap.mem_range]
    simp only [Matrix.toLin'_apply]
  have hKR : ∀ v ∈ K, v ∈ R → v = 0 := by
    intro v hvK hvR
    obtain ⟨w', rfl⟩ := (hmemR _).1 hvR
    exact eq_zero_of_odd_pow (v := w') hm ham' ((hmemK _).1 hvK) (by rw [hTv]; abel)
  have hdim : finrank E K + finrank E R = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' T)
    rw [Module.finrank_fin_fun, ← hKdef, ← hRdef] at this
    omega
  have hx₀K : x₀ ∈ K := (hmemK x₀).2 hax₀
  have hKne : K ≠ ⊥ := fun h => hx₀ (by rw [h] at hx₀K; exact (Submodule.mem_bot E).1 hx₀K)
  have hK1 : 1 ≤ finrank E K := Submodule.one_le_finrank_iff.2 hKne
  have hK2 : finrank E K ≤ 2 := by
    by_contra h
    apply hans
    have hle := Submodule.finrank_le K
    rw [Module.finrank_fin_fun] at hle
    have hKtop : K = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
    exact isScalarMat_of_forall fun v => (hmemK v).1 (by rw [hKtop]; exact Submodule.mem_top)
  have hcomm : ∀ b ∈ A, (b : Matrix (Fin 3) (Fin 3) E) * (a : Matrix (Fin 3) (Fin 3) E) =
      (a : Matrix (Fin 3) (Fin 3) E) * (b : Matrix (Fin 3) (Fin 3) E) := by
    intro b hb
    rw [← Units.val_mul, ← Units.val_mul, hAab b hb a haA]
  have hKinv : ∀ b ∈ A, ∀ v ∈ K, (b : Matrix (Fin 3) (Fin 3) E) *ᵥ v ∈ K := by
    intro b hb v hv
    rw [hmemK] at hv ⊢
    rw [mulVec_mulVec, ← hcomm b hb, ← mulVec_mulVec, hv, mulVec_smul]
  have hRinv : ∀ b ∈ A, ∀ v ∈ R, (b : Matrix (Fin 3) (Fin 3) E) *ᵥ v ∈ R := by
    intro b hb v hv
    obtain ⟨w, rfl⟩ := (hmemR _).1 hv
    refine (hmemR _).2 ⟨(b : Matrix (Fin 3) (Fin 3) E) *ᵥ w, ?_⟩
    rw [hTv, hTv, mulVec_sub, mulVec_smul, mulVec_mulVec, mulVec_mulVec, hcomm b hb]
  have hline : ∀ L : Submodule E (Fin 3 → E), finrank E L = 1 → ∀ x ∈ L, x ≠ 0 →
      ∀ v ∈ L, ∃ c : E, v = c • x := by
    intro L hL x hx hx0 v hv
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hx⟩ : L)
      (fun h => hx0 (congrArg Subtype.val h))).1 hL ⟨v, hv⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  obtain ⟨x₁, U, hx₁0, hU2, hx₁U, hx₁eig, hUinv, hdistU⟩ :
      ∃ (x₁ : Fin 3 → E) (U : Submodule E (Fin 3 → E)), x₁ ≠ 0 ∧ finrank E U = 2 ∧ x₁ ∉ U ∧
        CommonEigen A x₁ ∧ (∀ b ∈ A, ∀ u ∈ U, (b : Matrix (Fin 3) (Fin 3) E) *ᵥ u ∈ U) ∧
        ∀ μ : E, (∀ u ∈ U, (a : Matrix (Fin 3) (Fin 3) E) *ᵥ u = μ • u) →
          (a : Matrix (Fin 3) (Fin 3) E) *ᵥ x₁ ≠ μ • x₁ := by
    rcases (by omega : finrank E K = 1 ∨ finrank E K = 2) with h1 | h2
    · refine ⟨x₀, R, hx₀, by omega, fun h => hx₀ (hKR x₀ hx₀K h), fun b hb => ?_, hRinv,
        fun μ hμ hax => ?_⟩
      · obtain ⟨c, hc⟩ := hline K h1 x₀ hx₀K hx₀ _ (hKinv b hb x₀ hx₀K)
        exact ⟨c, hc⟩
      · have hμ0 : μ = c₀ := eigen_unique hx₀ hax hax₀
        apply hans
        refine isScalarMat_of_forall (μ := c₀) fun v => ?_
        have hTvR : T *ᵥ v ∈ R := (hmemR _).2 ⟨v, rfl⟩
        have hTvK : T *ᵥ v ∈ K := (hmemK _).2 (by rw [hμ _ hTvR, hμ0])
        have h0 := hKR _ hTvK hTvR
        rwa [hTv, sub_eq_zero] at h0
    · have hR1 : finrank E R = 1 := by omega
      have hRne : R ≠ ⊥ := fun h => by
        rw [h, finrank_bot] at hR1
        exact zero_ne_one hR1
      obtain ⟨x₁, hx₁R, hx₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRne
      refine ⟨x₁, K, hx₁0, h2, fun h => hx₁0 (hKR x₁ h hx₁R), fun b hb => ?_, hKinv,
        fun μ hμ hax => ?_⟩
      · obtain ⟨c, hc⟩ := hline R hR1 x₁ hx₁R hx₁0 _ (hRinv b hb x₁ hx₁R)
        exact ⟨c, hc⟩
      · have hμ0 : μ = c₀ := eigen_unique hx₀ (hμ x₀ hx₀K) hax₀
        exact hx₁0 (hKR x₁ ((hmemK x₁).2 (by rw [hax, hμ0])) hx₁R)
  by_cases hsc : ∀ b ∈ A, ∃ μ : E, ∀ u ∈ U, (b : Matrix (Fin 3) (Fin 3) E) *ᵥ u = μ • u
  · right
    let e := Module.finBasisOfFinrankEq E U hU2
    have he : LinearIndependent E ![(e 0 : Fin 3 → E), (e 1 : Fin 3 → E)] := by
      have h := e.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
      convert h using 1
      funext i
      fin_cases i <;> rfl
    have hli : LinearIndependent E ![(e 0 : Fin 3 → E), (e 1 : Fin 3 → E), x₁] := by
      have h := linearIndependent_cons3 hx₁U (e 0).2 (e 1).2 he
      rw [Fintype.linearIndependent_iff] at h ⊢
      intro g hg i
      have := h ![g 2, g 0, g 1] (by
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg ⊢
        rw [← hg]
        abel)
      fin_cases i
      · exact this 1
      · exact this 2
      · exact this 0
    refine ⟨e 0, e 1, x₁, hli, fun b hb => ?_, ?_⟩
    · obtain ⟨μ, hμ⟩ := hsc b hb
      obtain ⟨ν, hν⟩ := hx₁eig b hb
      exact ⟨μ, ν, hμ _ (e 0).2, hμ _ (e 1).2, hν⟩
    · obtain ⟨μ, hμ⟩ := hsc a haA
      obtain ⟨ν, hν⟩ := hx₁eig a haA
      refine ⟨a, haA, μ, ν, hμ _ (e 0).2, hν, fun hμν => hdistU μ hμ ?_⟩
      rw [hν, hμν]
  · push Not at hsc
    obtain ⟨b, hbA, hbns⟩ := hsc
    obtain ⟨y₀, hy₀U, hy₀0, μ₀, hby₀⟩ := exists_eigen_of_plane hU hU2 (hAU b hbA) (hUinv b hbA)
    obtain ⟨u₁, hu₁U, hu₁⟩ := hbns μ₀
    obtain ⟨mb, hmb, hbm⟩ := hAodd b hbA
    obtain ⟨z, hzU, β, hβμ, hbz, hli, hinv⟩ := exists_second_eigen hU2 hmb (val_pow_eq_one hbm)
      (hUinv b hbA) hy₀U hy₀0 hby₀ hu₁U hu₁
    have hcommU : ∀ b' ∈ A, ∀ u ∈ U, (b' : Matrix (Fin 3) (Fin 3) E) *ᵥ
        ((b : Matrix (Fin 3) (Fin 3) E) *ᵥ u) =
        (b : Matrix (Fin 3) (Fin 3) E) *ᵥ ((b' : Matrix (Fin 3) (Fin 3) E) *ᵥ u) := by
      intro b' hb' u _
      rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hAab b' hb' b hbA]
    have hy₀eig : CommonEigen A y₀ := fun b' hb' =>
      (hinv _ (hUinv b' hb') (hcommU b' hb')).1
    have hzeig : CommonEigen A z := fun b' hb' => (hinv _ (hUinv b' hb') (hcommU b' hb')).2
    have hli3 : LinearIndependent E ![x₁, y₀, z] := linearIndependent_cons3 hx₁U hy₀U hzU hli
    by_cases h01 : Separates A x₁ y₀
    · by_cases h02 : Separates A x₁ z
      · left
        refine ⟨![x₁, y₀, z], hli3, fun i => ?_,
          separates_of_three h01 h02 ⟨b, hbA, μ₀, β, hby₀, hbz, hβμ.symm⟩⟩
        fin_cases i
        exacts [hx₁eig, hy₀eig, hzeig]
      · right
        refine ⟨x₁, z, y₀, linearIndependent_cons3 hx₁U hzU hy₀U
          (linearIndependent_pair_symm hli), fun b' hb' => ?_, ⟨b, hbA, β, μ₀, ?_, hby₀, hβμ⟩⟩
        · obtain ⟨μ, hμ⟩ := hx₁eig b' hb'
          obtain ⟨ν, hν⟩ := hzeig b' hb'
          obtain ⟨κ, hκ⟩ := hy₀eig b' hb'
          have : μ = ν := by
            by_contra hne
            exact h02 ⟨b', hb', μ, ν, hμ, hν, hne⟩
          exact ⟨μ, κ, hμ, by rw [hν, ← this], hκ⟩
        · obtain ⟨μ, hμ⟩ := hx₁eig b hbA
          have : μ = β := by
            by_contra hne
            exact h02 ⟨b, hbA, μ, β, hμ, hbz, hne⟩
          rw [hμ, this]
    · right
      refine ⟨x₁, y₀, z, hli3, fun b' hb' => ?_, ⟨b, hbA, μ₀, β, ?_, hbz, hβμ.symm⟩⟩
      · obtain ⟨μ, hμ⟩ := hx₁eig b' hb'
        obtain ⟨ν, hν⟩ := hy₀eig b' hb'
        obtain ⟨κ, hκ⟩ := hzeig b' hb'
        have : μ = ν := by
          by_contra hne
          exact h01 ⟨b', hb', μ, ν, hμ, hν, hne⟩
        exact ⟨μ, κ, hμ, by rw [hν, ← this], hκ⟩
      · obtain ⟨μ, hμ⟩ := hx₁eig b hbA
        have : μ = μ₀ := by
          by_contra hne
          exact h01 ⟨b, hbA, μ, μ₀, hμ, hby₀, hne⟩
        rw [hμ, this]

theorem triple_of_scalar_plane (hU : UnitaryFieldData 2 f E) {C A : Subgroup (GL (Fin 3) E)}
    (hCU : ∀ c ∈ C, ∀ v w, hform hU ((c : Matrix (Fin 3) (Fin 3) E) *ᵥ v)
      ((c : Matrix (Fin 3) (Fin 3) E) *ᵥ w) = hform hU v w)
    (hodd : Odd (Nat.card C)) (hiso : ¬ FixesIsotropicLine hU C) (hAC : A ≤ C)
    (hAC' : ∀ c ∈ C, ∀ a ∈ A, c⁻¹ * a * c ∈ A) {y₁ y₂ w : Fin 3 → E}
    (hli : LinearIndependent E ![y₁, y₂, w])
    (heig : ∀ b ∈ A, ∃ μ ν : E, (b : Matrix (Fin 3) (Fin 3) E) *ᵥ y₁ = μ • y₁ ∧
      (b : Matrix (Fin 3) (Fin 3) E) *ᵥ y₂ = μ • y₂ ∧ (b : Matrix (Fin 3) (Fin 3) E) *ᵥ w = ν • w)
    (hsep : Separates A y₁ w) :
    ∃ x : Fin 3 → Fin 3 → E, LinearIndependent E x ∧ (∀ i, CommonEigen C (x i)) ∧
      ∀ i j, i ≠ j → Separates C (x i) (x j) := by
  have : CharP E 2 := hU.charP
  have : Finite E := hU.finite
  have : Finite C := Nat.finite_of_card_ne_zero hodd.pos.ne'
  obtain ⟨a₀, ha₀, μ₀, ν₀, ha₀y₁, ha₀w, hμν⟩ := hsep
  have hy₁0 : y₁ ≠ 0 := hli.ne_zero 0
  have hy₂0 : y₂ ≠ 0 := hli.ne_zero 1
  have hw0 : w ≠ 0 := hli.ne_zero 2
  have ha₀y₂ : (a₀ : Matrix (Fin 3) (Fin 3) E) *ᵥ y₂ = μ₀ • y₂ := by
    obtain ⟨μ, ν, h1, h2, -⟩ := heig a₀ ha₀
    rw [h2, eigen_unique hy₁0 h1 ha₀y₁]
  have hcoord : ∀ v : Fin 3 → E, ∃ s r c : E, s • y₁ + r • y₂ + c • w = v := by
    intro v
    obtain ⟨g, hg⟩ := exists_coeffs hli v
    refine ⟨g 0, g 1, g 2, ?_⟩
    rw [← hg, Fin.sum_univ_three]
    rfl
  have huniq : ∀ s r c s' r' c' : E, s • y₁ + r • y₂ + c • w = s' • y₁ + r' • y₂ + c' • w →
      s = s' ∧ r = r' ∧ c = c' := by
    intro s r c s' r' c' h
    have h' := congrFun (coeffs_eq hli (a := ![s, r, c]) (a' := ![s', r', c']) (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exact h))
    exact ⟨h' 0, h' 1, h' 2⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Submodule E (Fin 3 → E), P = Submodule.span E {y₁, y₂} := ⟨_, rfl⟩
  have hmemP : ∀ v, v ∈ P ↔ ∃ s r : E, s • y₁ + r • y₂ = v := fun v => by
    rw [hPdef]
    exact Submodule.mem_span_pair
  have hy₁P : y₁ ∈ P := (hmemP _).2 ⟨1, 0, by simp⟩
  have hy₂P : y₂ ∈ P := (hmemP _).2 ⟨0, 1, by simp⟩
  have hwP' : ∀ κ : E, κ • w ∈ P → κ = 0 := by
    intro κ h
    obtain ⟨s, r, hsr⟩ := (hmemP _).1 h
    exact (huniq s r 0 0 0 κ (by rw [hsr]; simp)).2.2.symm
  have hwP : w ∉ P := fun h => one_ne_zero (hwP' 1 (by rw [one_smul]; exact h))
  have hy₁₂ : LinearIndependent E ![y₁, y₂] := by
    rw [LinearIndependent.pair_iff]
    intro s r h
    have := huniq s r 0 0 0 0 (by rw [h]; simp)
    exact ⟨this.1, this.2.1⟩
  have hP2 : finrank E P = 2 := by
    have hrange : Set.range ![y₁, y₂] = {y₁, y₂} := by
      ext x
      simp [eq_comm, or_comm]
    rw [hPdef, ← hrange, finrank_span_eq_card hy₁₂, Fintype.card_fin]
  have ha₀P : ∀ v ∈ P, (a₀ : Matrix (Fin 3) (Fin 3) E) *ᵥ v = μ₀ • v := by
    intro v hv
    obtain ⟨s, r, rfl⟩ := (hmemP v).1 hv
    rw [mulVec_add, mulVec_smul, mulVec_smul, ha₀y₁, ha₀y₂, smul_add, smul_comm s,
      smul_comm r]
  have hloc : ∀ v : Fin 3 → E, CommonEigen A v → v ∈ P ∨ ∃ c : E, v = c • w := by
    intro v hv
    obtain ⟨s, r, c, rfl⟩ := hcoord v
    obtain ⟨κ, hκ⟩ := hv a₀ ha₀
    rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, ha₀y₁, ha₀y₂,
      ha₀w] at hκ
    obtain ⟨hs, hr, hc⟩ := huniq (s * μ₀) (r * μ₀) (c * ν₀) (κ * s) (κ * r) (κ * c) (by
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
        at hκ
      exact hκ)
    by_cases hc0 : c = 0
    · left
      rw [hc0, zero_smul, add_zero]
      exact (hmemP _).2 ⟨s, r, rfl⟩
    · right
      have hκν : κ = ν₀ := by
        rw [mul_comm κ] at hc
        exact (mul_left_cancel₀ hc0 hc).symm
      rw [hκν, mul_comm ν₀] at hs hr
      have hs0 : s = 0 := by
        by_contra h
        exact hμν (mul_left_cancel₀ h hs)
      have hr0 : r = 0 := by
        by_contra h
        exact hμν (mul_left_cancel₀ h hr)
      exact ⟨c, by rw [hs0, hr0, zero_smul, zero_smul, zero_add, zero_add]⟩
  have hCeig : ∀ c ∈ C, ∀ v, CommonEigen A v →
      CommonEigen A ((c : Matrix (Fin 3) (Fin 3) E) *ᵥ v) := by
    intro c hc v hv b hb
    obtain ⟨κ, hκ⟩ := hv _ (hAC' c hc b hb)
    exact ⟨κ, by rw [mulVec_conj c b, hκ, mulVec_smul]⟩
  have hy₁eig : CommonEigen A y₁ := fun b hb => by
    obtain ⟨μ, ν, h1, -, -⟩ := heig b hb
    exact ⟨μ, h1⟩
  have hy₂eig : CommonEigen A y₂ := fun b hb => by
    obtain ⟨μ, ν, -, h2, -⟩ := heig b hb
    exact ⟨μ, h2⟩
  have hy₁₂eig : CommonEigen A (y₁ + y₂) := fun b hb => by
    obtain ⟨μ, ν, h1, h2, -⟩ := heig b hb
    exact ⟨μ, by rw [mulVec_add, h1, h2, smul_add]⟩
  have hweig : CommonEigen A w := fun b hb => by
    obtain ⟨μ, ν, -, -, h3⟩ := heig b hb
    exact ⟨ν, h3⟩
  have hCP : ∀ c ∈ C, ∀ v ∈ P, (c : Matrix (Fin 3) (Fin 3) E) *ᵥ v ∈ P := by
    intro c hc
    have hne : ∀ v, v ≠ 0 → (c : Matrix (Fin 3) (Fin 3) E) *ᵥ v ≠ 0 :=
      fun v hv => mulVec_ne_zero c hv
    have key : (c : Matrix (Fin 3) (Fin 3) E) *ᵥ y₁ ∈ P ∧
        (c : Matrix (Fin 3) (Fin 3) E) *ᵥ y₂ ∈ P := by
      have h12 := hloc _ (hCeig c hc _ hy₁₂eig)
      rw [mulVec_add] at h12
      rcases hloc _ (hCeig c hc _ hy₁eig) with h1 | ⟨κ₁, h1⟩ <;>
        rcases hloc _ (hCeig c hc _ hy₂eig) with h2 | ⟨κ₂, h2⟩
      · exact ⟨h1, h2⟩
      · exfalso
        have hκ₂ : κ₂ ≠ 0 := by
          rintro rfl
          rw [zero_smul] at h2
          exact hne y₂ hy₂0 h2
        rcases h12 with h | ⟨κ, h⟩
        · apply hκ₂
          apply hwP'
          have := P.sub_mem h h1
          rwa [h2, add_sub_cancel_left] at this
        · apply hne y₁ hy₁0
          have h' : (c : Matrix (Fin 3) (Fin 3) E) *ᵥ y₁ = (κ - κ₂) • w := by
            rw [sub_smul, ← h, h2, add_sub_cancel_right]
          have hk := hwP' (κ - κ₂) (by rw [← h']; exact h1)
          rw [h', hk, zero_smul]
      · exfalso
        have hκ₁ : κ₁ ≠ 0 := by
          rintro rfl
          rw [zero_smul] at h1
          exact hne y₁ hy₁0 h1
        rcases h12 with h | ⟨κ, h⟩
        · apply hκ₁
          apply hwP'
          have := P.sub_mem h h2
          rwa [h1, add_sub_cancel_right] at this
        · apply hne y₂ hy₂0
          have h' : (c : Matrix (Fin 3) (Fin 3) E) *ᵥ y₂ = (κ - κ₁) • w := by
            rw [sub_smul, ← h, h1, add_sub_cancel_left]
          have hk := hwP' (κ - κ₁) (by rw [← h']; exact h2)
          rw [h', hk, zero_smul]
      · exfalso
        have h0 : (c : Matrix (Fin 3) (Fin 3) E) *ᵥ (κ₂ • y₁ - κ₁ • y₂) = 0 := by
          rw [mulVec_sub, mulVec_smul, mulVec_smul, h1, h2, smul_smul, smul_smul, mul_comm,
            sub_self]
        have h0' : κ₂ • y₁ - κ₁ • y₂ = 0 := by
          by_contra h
          exact hne _ h h0
        have := huniq κ₂ (-κ₁) 0 0 0 0 (by linear_combination (norm := module) h0')
        have hκ₁ : κ₁ = 0 := neg_eq_zero.1 this.2.1
        apply hne y₁ hy₁0
        rw [h1, hκ₁, zero_smul]
    intro v hv
    obtain ⟨s, r, rfl⟩ := (hmemP v).1 hv
    rw [mulVec_add, mulVec_smul, mulVec_smul]
    exact P.add_mem (P.smul_mem _ key.1) (P.smul_mem _ key.2)
  have hCw : CommonEigen C w := by
    intro c hc
    rcases hloc _ (hCeig c hc _ hweig) with h | h
    · exfalso
      have hker : LinearMap.ker (Matrix.toLin' (c : Matrix (Fin 3) (Fin 3) E)) = ⊥ :=
        LinearMap.ker_eq_bot.2 fun v v' hvv' => mulVec_injective c (by
          simpa only [Matrix.toLin'_apply] using hvv')
      have hli' := hli.map' _ hker
      refine false_of_three_mem_span_pair (y₁ := y₁) (y₂ := y₂) hli' fun i => ?_
      rw [← hPdef]
      fin_cases i
      · exact hCP c hc _ hy₁P
      · exact hCP c hc _ hy₂P
      · exact h
    · exact h
  have hpair : ∀ (u v : Fin 3 → E) (α β : E), (a₀ : Matrix (Fin 3) (Fin 3) E) *ᵥ u = α • u →
      (a₀ : Matrix (Fin 3) (Fin 3) E) *ᵥ v = β • v → hform hU u v ≠ 0 → hU.bar α * β = 1 := by
    intro u v α β hu hv hne
    have h := hCU a₀ (hAC ha₀) u v
    rw [hu, hv] at h
    simp only [map_smulₛₗ, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul] at h
    have : (hU.bar α * β - 1) * hform hU u v = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)
  have hwP0 : ∀ v ∈ P, hform hU w v = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v₀, hv₀P, hv₀⟩ := hcon
    have h1 := hpair w v₀ ν₀ μ₀ ha₀w (ha₀P v₀ hv₀P) hv₀
    apply not_totallyIsotropic_two hU hP2
    intro u hu v hv
    by_contra huv
    have h2 := hpair u v μ₀ μ₀ (ha₀P u hu) (ha₀P v hv) huv
    apply hμν
    have hμ0 : μ₀ ≠ 0 := right_ne_zero_of_mul_eq_one h2
    exact hU.bar.injective (mul_right_cancel₀ hμ0 (h2.trans h1.symm))
  have hPnd : ∀ y ∈ P, (∀ v ∈ P, hform hU y v = 0) → y = 0 := by
    intro y hy hyP
    apply eq_zero_of_hform_basis hU hli
    intro l
    fin_cases l
    · exact hyP y₁ hy₁P
    · exact hyP y₂ hy₂P
    · change hform hU y w = 0
      rw [hform_symm hU w y, hwP0 y hy, map_zero]
  have hsolv : Group.IsSolvable C := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  let ρ : C →* Module.End E P :=
    { toFun := fun c => (Matrix.toLin' ((c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)).restrict
        (fun v hv => by rw [Matrix.toLin'_apply]; exact hCP c c.2 v hv)
      map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
      map_mul' := fun c d => LinearMap.ext fun v => Subtype.ext (by
        simp [Matrix.mulVec_mulVec]) }
  have hcommP : ∀ c ∈ C, ∀ d ∈ C, ∀ v ∈ P,
      (c : Matrix (Fin 3) (Fin 3) E) *ᵥ ((d : Matrix (Fin 3) (Fin 3) E) *ᵥ v) =
        (d : Matrix (Fin 3) (Fin 3) E) *ᵥ ((c : Matrix (Fin 3) (Fin 3) E) *ᵥ v) := by
    intro c hc d hd v hv
    have h := CFSG.OddSolvableUnitary.commute_of_odd_of_finrank_two hodd hsolv hP2 ρ ⟨c, hc⟩
      ⟨d, hd⟩
    have h' := congrArg (fun φ : Module.End E P => ((φ ⟨v, hv⟩ : P) : Fin 3 → E)) h
    simpa [ρ, Matrix.toLin'_apply] using h'
  obtain ⟨c, hcC, hcns⟩ : ∃ c ∈ C, ∀ μ : E, ∃ v ∈ P,
      (c : Matrix (Fin 3) (Fin 3) E) *ᵥ v ≠ μ • v := by
    by_contra hcon
    push Not at hcon
    apply hiso
    have hsepP : ((hform hU).domRestrict₁₂ P P).SeparatingLeft := by
      intro x hx
      refine Subtype.ext (hPnd x x.2 fun v hv => ?_)
      have := hx ⟨v, hv⟩
      rwa [LinearMap.domRestrict₁₂_apply] at this
    obtain ⟨⟨y, hyP⟩, hy0, hyy⟩ := CFSG.LinearGroups.exists_isotropic_of_finrank_two hU
      ((hform_isSymm hU).domRestrict P) hsepP hP2
    rw [LinearMap.domRestrict₁₂_apply] at hyy
    refine ⟨y, fun h => hy0 (Subtype.ext h), by rw [← hform_apply]; exact hyy, fun c hc => ?_⟩
    obtain ⟨μ, hμ⟩ := hcon c hc
    exact ⟨μ, hμ y hyP⟩
  obtain ⟨y₀, hy₀P, hy₀0, μ, hcy₀⟩ := exists_eigen_of_plane hU hP2 (hCU c hcC) (hCP c hcC)
  obtain ⟨u₁, hu₁P, hu₁⟩ := hcns μ
  obtain ⟨z, hzP, β, hβμ, hcz, hli2, hinv⟩ := exists_second_eigen hP2
    (odd_orderOf_of_mem hodd hcC) (val_pow_eq_one (pow_orderOf_eq_one c)) (hCP c hcC) hy₀P hy₀0
    hcy₀ hu₁P hu₁
  have hy₀eig : CommonEigen C y₀ := fun c' hc' =>
    (hinv _ (hCP c' hc') fun u hu => hcommP c' hc' c hcC u hu).1
  have hzeig : CommonEigen C z := fun c' hc' =>
    (hinv _ (hCP c' hc') fun u hu => hcommP c' hc' c hcC u hu).2
  refine ⟨![w, y₀, z], linearIndependent_cons3 hwP hy₀P hzP hli2, fun i => ?_,
    separates_of_three ⟨a₀, hAC ha₀, ν₀, μ₀, ha₀w, ha₀P y₀ hy₀P, hμν.symm⟩
      ⟨a₀, hAC ha₀, ν₀, μ₀, ha₀w, ha₀P z hzP, hμν.symm⟩ ⟨c, hcC, μ, β, hcy₀, hcz, hβμ.symm⟩⟩
  fin_cases i
  exacts [hCw, hy₀eig, hzeig]

end A2

open A2 in
theorem frame_of_abelian_normal (hU : UnitaryFieldData 2 f E) (hf : 2 ≤ f)
    {C A : Subgroup (GL (Fin 3) E)} {t : GL (Fin 3) E}
    (hC : C ≤ gramSU hU 1) (hodd : Odd (Nat.card C)) (ht : t ∈ gramSU hU 1) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hnorm : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (hiso : ¬ FixesIsotropicLine hU C)
    (hAC : A ≤ C) (hAC' : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) (hAt : ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAns : ∃ a ∈ A, ¬ IsScalarMat a) :
    ∃ v : Fin 3 → (Fin 3 → E), IsOrthonormalFrame hU v ∧ (∀ c ∈ C, PermutesLines v c) ∧
      PermutesLines v t := by
  have _ := hf
  have _ := ht
  have : CharP E 2 := hU.charP
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_left ht2).symm
  have hCodd : ∀ c ∈ C, ∃ m, Odd m ∧ c ^ m = 1 := fun c hc =>
    ⟨orderOf c, odd_orderOf_of_mem hodd hc, pow_orderOf_eq_one c⟩
  have hAC'' : ∀ c ∈ C, ∀ a ∈ A, c⁻¹ * a * c ∈ A := fun c hc a ha => by
    simpa using hAC' c⁻¹ (C.inv_mem hc) a ha
  have hAt' : ∀ a ∈ A, t⁻¹ * a * t ∈ A := fun a ha => by
    have := hAt a ha
    rw [htinv] at this ⊢
    exact this
  have hCt' : ∀ c ∈ C, t⁻¹ * c * t ∈ C := fun c hc => by
    have := hnorm c hc
    rw [htinv] at this ⊢
    exact this
  obtain ⟨a, haA, hans, x₀, hx₀, c₀, hax₀⟩ :=
    exists_nonscalar_eigen (fun a ha => hCodd a (hAC ha)) ht2 ht1 hAt hAab hAns
  rcases dichotomy hU (fun a ha => hform_mulVec (hC (hAC ha))) (fun a ha => hCodd a (hAC ha))
      hAab haA hans hx₀ hax₀ with ⟨x, hli, heig, hdist⟩ | ⟨y₁, y₂, w, hli, heig, hsep⟩
  · exact frame_of_triple hU hC hodd hiso (hAC.trans hC) hAC'' hAt' hli heig hdist
  · obtain ⟨x, hli', heig', hdist'⟩ := triple_of_scalar_plane hU
      (fun c hc => hform_mulVec (hC hc)) hodd hiso hAC hAC'' hli heig hsep
    exact frame_of_triple hU hC hodd hiso hC
      (fun c hc b hb => C.mul_mem (C.mul_mem (C.inv_mem hc) hb) hc) hCt' hli' heig' hdist'

end CFSG.GH74.Uniqueness.Bender.Frame
