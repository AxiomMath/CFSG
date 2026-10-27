module

public import CFSG.ClassicalGroups.Orthogonal.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open QuadraticMap Polynomial Module

section Eigen

variable {K M : Type*} [Field K] [Fintype K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

theorem exists_eigen_of_pow_card_eq [Nontrivial M] (T : Module.End K M)
    (hT : T ^ Fintype.card K = T) : ∃ (μ : K) (v : M), v ≠ 0 ∧ T v = μ • v := by
  have h0 : aeval T (X ^ Fintype.card K - X : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, hT, sub_self]
  have hdvd : minpoly K T ∣ (X ^ Fintype.card K - X : K[X]) := minpoly.dvd K T h0
  have hne : (X ^ Fintype.card K - X : K[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have hsplit : Splits (X ^ Fintype.card K - X : K[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]
    rfl
  have hms : Splits (minpoly K T) := hsplit.of_dvd hne hdvd
  have hdeg : (minpoly K T).degree ≠ 0 :=
    (minpoly.degree_pos (Algebra.IsIntegral.isIntegral T)).ne'
  obtain ⟨μ, hμ⟩ := hms.exists_eval_eq_zero hdeg
  have hev : T.HasEigenvalue μ := Module.End.hasEigenvalue_iff_isRoot.mpr hμ
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  exact ⟨μ, v, hv.2, hv.apply_eq_smul⟩

end Eigen

section Average

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def fixSub (g : V ≃ₗ[K] V) : Submodule K V where
  carrier := {v | g v = v}
  add_mem' {a b} ha hb := by
    change g (a + b) = a + b
    rw [map_add, show g a = a from ha, show g b = b from hb]
  zero_mem' := map_zero g
  smul_mem' c v hv := by
    change g (c • v) = c • v
    rw [map_smul, show g v = v from hv]

theorem mem_fixSub {g : V ≃ₗ[K] V} {v : V} : v ∈ fixSub g ↔ g v = v := Iff.rfl

@[expose] noncomputable def avgOp (y : V ≃ₗ[K] V) (m : ℕ) : V →ₗ[K] V :=
  ∑ s ∈ Finset.range m, (y ^ s).toLinearMap

theorem avgOp_apply (y : V ≃ₗ[K] V) (m : ℕ) (x : V) :
    avgOp y m x = ∑ s ∈ Finset.range m, (y ^ s) x := by
  rw [avgOp, LinearMap.sum_apply]
  rfl

theorem pow_apply_of_mem_fixSub {y : V ≃ₗ[K] V} {w : V} (hw : y w = w) (s : ℕ) :
    (y ^ s) w = w := by
  induction s with
  | zero => rfl
  | succ s ih => rw [pow_succ, LinearEquiv.mul_apply, hw, ih]

theorem sum_range_succ_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) {m : ℕ} (hm : f m = f 0) :
    ∑ s ∈ Finset.range m, f (s + 1) = ∑ s ∈ Finset.range m, f s := by
  have h1 := Finset.sum_range_succ' f m
  have h2 := Finset.sum_range_succ f m
  rw [hm] at h2
  exact add_right_cancel (h1.symm.trans h2)

variable {y : V ≃ₗ[K] V} {m : ℕ}

theorem avgOp_apply_apply (hm : y ^ m = 1) (x : V) : avgOp y m (y x) = avgOp y m x := by
  rw [avgOp_apply, avgOp_apply]
  have h := sum_range_succ_shift (fun s => (y ^ s) x) (m := m) (by
    simp only [hm, pow_zero])
  rw [← h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pow_succ, LinearEquiv.mul_apply]

theorem apply_avgOp (hm : y ^ m = 1) (x : V) : y (avgOp y m x) = avgOp y m x := by
  rw [avgOp_apply, map_sum]
  have h := sum_range_succ_shift (fun s => (y ^ s) x) (m := m) (by
    simp only [hm, pow_zero])
  rw [← h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pow_succ', LinearEquiv.mul_apply]

theorem natCast_eq_one_of_odd [CharP K 2] {m : ℕ} (hm : Odd m) : (m : K) = 1 := by
  obtain ⟨k, rfl⟩ := hm
  push_cast
  rw [CharTwo.two_eq_zero, zero_mul, zero_add]

theorem avgOp_apply_of_fix [CharP K 2] (hmo : Odd m) {w : V} (hw : y w = w) :
    avgOp y m w = w := by
  rw [avgOp_apply, Finset.sum_congr rfl fun s _ => pow_apply_of_mem_fixSub hw s,
    Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul K, natCast_eq_one_of_odd hmo,
    one_smul]

theorem polar_avgOp_left [CharP K 2] {Q : QuadraticForm K V}
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hmo : Odd m) (x : V) {w : V}
    (hw : y w = w) : polar Q (avgOp y m x) w = polar Q x w := by
  have hs : ∀ s : ℕ, polar Q ((y ^ s) x) w = polar Q x w := fun s => by
    conv_lhs => rw [← pow_apply_of_mem_fixSub hw s]
    exact CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (pow_mem hyO s) x w
  rw [avgOp_apply]
  have hsum : polar Q (∑ s ∈ Finset.range m, (y ^ s) x) w =
      ∑ s ∈ Finset.range m, polar Q ((y ^ s) x) w := by
    induction (Finset.range m) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, polar_add_left, ih]
  rw [hsum, Finset.sum_congr rfl fun s _ => hs s, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, natCast_eq_one_of_odd hmo, one_mul]

end Average

section Plane

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem zpow_apply_of_apply_eq_smul {y : V ≃ₗ[K] V} {w : V} {a : Kˣ} (h : y w = (a : K) • w) :
    ∀ k : ℤ, (y ^ k) w = ((a ^ k : Kˣ) : K) • w := by
  have hinv : y⁻¹ w = ((a⁻¹ : Kˣ) : K) • w := by
    apply y.injective
    rw [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply', map_smul, h, smul_smul,
      Units.inv_mul, one_smul]
  intro k
  refine Int.induction_on k ?_ ?_ ?_
  · simp
  · intro i ih
    rw [zpow_add_one, LinearEquiv.mul_apply, h, map_smul, ih, smul_smul, zpow_add_one,
      Units.val_mul, mul_comm]
  · intro i ih
    rw [zpow_sub_one, LinearEquiv.mul_apply, hinv, map_smul, ih, smul_smul, zpow_sub_one,
      Units.val_mul, mul_comm]

theorem mul_self_ne_one_of_ne_one [CharP K 2] {μ : K} (hμ : μ ≠ 1) : μ * μ ≠ 1 := by
  intro h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h0 : (μ - 1) * (μ - 1) = 0 := by linear_combination h + (1 - μ) * h2
  exact hμ (sub_eq_zero.mp (mul_self_eq_zero.mp h0))

variable [Finite K] [CharP K 2] [FiniteDimensional K V] {Q : QuadraticForm K V}

open CFSG.ClassicalGroups.Orthogonal in
theorem exists_hypPair_of_codim_fix_le_two (hQ : (polarBilin Q).Nondegenerate)
    {y : V ≃ₗ[K] V} (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hyodd : Odd (orderOf y)) (hyq : y ^ Nat.card K = y) (hy1 : y ≠ 1)
    (hF : finrank K V ≤ finrank K (fixSub y) + 2) :
    ∃ u v : V, Q u = 0 ∧ Q v = 0 ∧ polar Q u v = 1 ∧ ∃ c : Kˣ, ∀ k : ℤ,
      (y ^ k) u = ((c ^ k : Kˣ) : K) • u ∧ (y ^ k) v = (((c ^ k)⁻¹ : Kˣ) : K) • v ∧
        ∀ x, polar Q x u = 0 → polar Q x v = 0 → (y ^ k) x = x := by
  classical
  have := Fintype.ofFinite K
  have hm : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  set π := avgOp y (orderOf y) with hπ
  set E := LinearMap.ker π with hE
  have hπF : ∀ x, y (π x) = π x := fun x => apply_avgOp hm x
  have hπw : ∀ w, y w = w → π w = w := fun w hw => avgOp_apply_of_fix hyodd hw
  have hEF : ∀ x ∈ E, ∀ w, y w = w → polar Q x w = 0 := by
    intro x hx w hw
    rw [← polar_avgOp_left hyO hyodd x hw, LinearMap.mem_ker.mp hx, polar_zero_left]
  have hsubE : ∀ x, x - π x ∈ E := fun x => by
    rw [LinearMap.mem_ker, map_sub, hπw _ (hπF x), sub_self]
  have hEy : ∀ x ∈ E, y x ∈ E := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hπ, avgOp_apply_apply hm, ← hπ, hx]
  have hFE : fixSub y ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwF, hwE⟩ := Submodule.mem_inf.mp hw
    rw [Submodule.mem_bot, ← hπw w hwF]
    exact LinearMap.mem_ker.mp hwE
  have hFE' : fixSub y ⊔ E = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = π x + (x - π x) := by abel
    rw [hx]
    exact Submodule.add_mem_sup (hπF x) (hsubE x)
  have hdim : finrank K (fixSub y) + finrank K E = finrank K V := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSub y) E
    rw [hFE, hFE', finrank_bot, add_zero, finrank_top] at h
    exact h.symm
  have hE2 : finrank K E ≤ 2 := by omega
  have hEnd : ∀ x ∈ E, (∀ x' ∈ E, polar Q x x' = 0) → x = 0 := by
    intro x hxE hx
    apply eq_zero_of_polar_eq_zero hQ
    intro z
    have hz : z = π z + (z - π z) := by abel
    rw [hz, polar_add_right, hx _ (hsubE z), hEF x hxE _ (hπF z), add_zero]
  have hEne : Nontrivial E := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply hy1
    refine LinearEquiv.ext fun x => ?_
    have h0 : (⟨x - π x, hsubE x⟩ : E) = 0 := Subsingleton.elim _ _
    have hx : x = π x := sub_eq_zero.mp (congrArg Subtype.val h0)
    change y x = x
    rw [hx, hπF]
  set T : Module.End K E := LinearMap.restrict y.toLinearMap hEy with hT
  have hTk : ∀ k : ℕ, ∀ x : E, ((T ^ k) x : V) = (y ^ k) (x : V) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', LinearEquiv.mul_apply, ← ih]
      rfl
  have hTq : T ^ Fintype.card K = T := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [hTk, ← Nat.card_eq_fintype_card, hyq]
    rfl
  obtain ⟨μ, u', hu'0, hTu⟩ := exists_eigen_of_pow_card_eq T hTq
  set u : V := (u' : V) with hudef
  have huE : u ∈ E := u'.2
  have hu0 : u ≠ 0 := fun h => hu'0 (Subtype.ext h)
  have hyu : y u = μ • u := congrArg Subtype.val hTu
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    rw [one_smul] at hyu
    have h : u ∈ fixSub y ⊓ E := Submodule.mem_inf.mpr ⟨hyu, huE⟩
    rw [hFE, Submodule.mem_bot] at h
    exact hu0 h
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hyu
    exact hu0 (y.injective (hyu.trans (map_zero y).symm))
  have hQu : Q u = 0 := by
    have h := map_of_mem hyO u
    rw [hyu, map_smul_eq_sq] at h
    have h' : (μ * μ - 1) * Q u = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) (mul_self_ne_one_of_ne_one hμ1)
    · exact h0
  obtain ⟨v', hv'E, hv'⟩ : ∃ v' ∈ E, polar Q u v' ≠ 0 := by
    by_contra! h
    exact hu0 (hEnd u huE h)
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : V, v₁ = (polar Q u v')⁻¹ • v' := ⟨_, rfl⟩
  have hv₁E : v₁ ∈ E := hv₁ ▸ E.smul_mem _ hv'E
  have huv₁ : polar Q u v₁ = 1 := by
    rw [hv₁, polar_smul_right_eq, inv_mul_cancel₀ hv']
  obtain ⟨v, hvdef⟩ : ∃ v : V, v = v₁ + Q v₁ • u := ⟨_, rfl⟩
  have hvE : v ∈ E := hvdef ▸ E.add_mem hv₁E (E.smul_mem _ huE)
  have huv : polar Q u v = 1 := by
    rw [hvdef, polar_add_right, huv₁, polar_smul_right_eq, polar_self_eq_zero hQu, mul_zero,
      add_zero]
  have hvu : polar Q v u = 1 := by rw [polar_comm, huv]
  have hQv : Q v = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [hvdef, QuadraticMap.map_add Q, map_smul_eq_sq, hQu, polar_smul_right_eq,
      polar_comm Q v₁ u, huv₁]
    linear_combination Q v₁ * h2
  have hvv : polar Q v v = 0 := polar_self_eq_zero hQv
  have huu : polar Q u u = 0 := polar_self_eq_zero hQu
  have hdecomp : ∀ w ∈ E, w = polar Q w v • u + polar Q w u • v := by
    intro w hwE
    by_contra hne
    set w' := w - (polar Q w v • u + polar Q w u • v) with hw'
    have hw'0 : w' ≠ 0 := fun h => hne (sub_eq_zero.mp h)
    have hw'E : w' ∈ E := E.sub_mem hwE (E.add_mem (E.smul_mem _ huE) (E.smul_mem _ hvE))
    have hw'u : polar Q w' u = 0 := by
      rw [hw', polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, huu, hvu]
      ring
    have hw'v : polar Q w' v = 0 := by
      rw [hw', polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, huv, hvv]
      ring
    have hli : LinearIndependent K ![u, v, w'] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
      have h1 := congrArg (fun z => polar Q z u) hg
      have h2 := congrArg (fun z => polar Q z v) hg
      simp only [polar_add_left, polar_smul_left_eq, huu, hvu, hw'u, polar_zero_left] at h1
      simp only [polar_add_left, polar_smul_left_eq, huv, hvv, hw'v, polar_zero_left] at h2
      have hg1 : g 1 = 0 := by linear_combination h1
      have hg0 : g 0 = 0 := by linear_combination h2
      rw [hg0, hg1, zero_smul, zero_smul, zero_add, zero_add, smul_eq_zero] at hg
      have hg2 : g 2 = 0 := hg.resolve_right hw'0
      intro i
      fin_cases i
      · exact hg0
      · exact hg1
      · exact hg2
    have h3 := finrank_span_eq_card hli
    have hle : Submodule.span K (Set.range ![u, v, w']) ≤ E := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact huE
      · exact hvE
      · exact hw'E
    have h4 := Submodule.finrank_mono hle
    rw [h3, Fintype.card_fin] at h4
    omega
  have hyv : y v = μ⁻¹ • v := by
    have hyvE := hEy v hvE
    have hd := hdecomp _ hyvE
    have hB : polar Q (y u) (y v) = 1 := by rw [polar_map_of_mem hyO, huv]
    have hQyv : Q (y v) = 0 := by rw [map_of_mem hyO, hQv]
    set α := polar Q (y v) v
    set β := polar Q (y v) u
    rw [hyu, polar_smul_left_eq, hd, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
      huu, huv] at hB
    rw [hd, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQu, hQv,
      polar_smul_left_eq, polar_smul_right_eq, huv] at hQyv
    have hβ : β = μ⁻¹ := by
      have h : μ * β = 1 := by linear_combination hB
      exact eq_inv_of_mul_eq_one_right h
    have hα : α = 0 := by
      have hβ0 : β ≠ 0 := by rw [hβ]; exact inv_ne_zero hμ0
      have h : α * β = 0 := by linear_combination hQyv
      exact (mul_eq_zero.mp h).resolve_right hβ0
    rw [hd, hα, hβ, zero_smul, zero_add]
  set c : Kˣ := Units.mk0 μ hμ0 with hc
  have hyu' : y u = (c : K) • u := by rw [hc, Units.val_mk0, hyu]
  have hyv' : y v = ((c⁻¹ : Kˣ) : K) • v := by rw [hc, Units.val_inv_eq_inv_val, Units.val_mk0, hyv]
  refine ⟨u, v, hQu, hQv, huv, c, fun k => ⟨zpow_apply_of_apply_eq_smul hyu' k, ?_, ?_⟩⟩
  · rw [zpow_apply_of_apply_eq_smul hyv' k, inv_zpow]
  · intro x hxu hxv
    have hxF : y x = x := by
      have hd := hdecomp _ (hsubE x)
      have h1 : polar Q (x - π x) v = 0 := by
        rw [polar_sub_left, hxv, polar_comm Q (π x) v, hEF v hvE _ (hπF x), sub_zero]
      have h2 : polar Q (x - π x) u = 0 := by
        rw [polar_sub_left, hxu, polar_comm Q (π x) u, hEF u huE _ (hπF x), sub_zero]
      rw [h1, h2, zero_smul, zero_smul, add_zero] at hd
      have hx : x = π x := sub_eq_zero.mp hd
      rw [hx]
      exact hπF x
    have hx1 : y x = ((1 : Kˣ) : K) • x := by rw [Units.val_one, one_smul]; exact hxF
    have h := zpow_apply_of_apply_eq_smul hx1 k
    rw [h, one_zpow, Units.val_one, one_smul]

end Plane

end CFSG.SeitzReduction.OmegaPilot
