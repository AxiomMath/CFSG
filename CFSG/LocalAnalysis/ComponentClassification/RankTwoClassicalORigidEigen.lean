module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open QuadraticMap

section Eigen

variable {K : Type} [Field K] [Fintype K] {V : Type*} [AddCommGroup V] [Module K V]
  (f : Module.End K V)

@[expose] noncomputable def eigenSum (a : Kˣ) (v : V) : V :=
  ∑ j ∈ Finset.range (Fintype.card K - 1), ((a : K)⁻¹) ^ j • (f ^ j) v

variable {f}

theorem apply_eigenSum (hf : f ^ (Fintype.card K - 1) = 1) (a : Kˣ) (v : V) :
    f (eigenSum f a v) = (a : K) • eigenSum f a v := by
  set N := Fintype.card K - 1
  set b : K := (a : K)⁻¹
  have hb : b ^ N = 1 := by
    rw [inv_pow, FiniteField.pow_card_sub_one_eq_one (a : K) a.ne_zero, inv_one]
  set g : ℕ → V := fun j => b ^ j • (f ^ j) v
  have hgN : g N = g 0 := by
    simp only [g, hb, hf, pow_zero, one_smul, Module.End.one_apply]
  have hshift : ∑ j ∈ Finset.range N, g (j + 1) = ∑ j ∈ Finset.range N, g j := by
    have h1 := Finset.sum_range_succ' g N
    have h2 := Finset.sum_range_succ g N
    rw [hgN] at h2
    exact add_right_cancel (h1.symm.trans h2)
  have hab : (a : K) * b = 1 := mul_inv_cancel₀ a.ne_zero
  calc f (eigenSum f a v) = ∑ j ∈ Finset.range N, b ^ j • (f ^ (j + 1)) v := by
        simp only [eigenSum, map_sum, map_smul, pow_succ', Module.End.mul_apply]
        rfl
    _ = (a : K) • ∑ j ∈ Finset.range N, g (j + 1) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [g, smul_smul, pow_succ, ← mul_assoc]
        rw [mul_comm (a : K) (b ^ j), mul_assoc, hab, mul_one]
    _ = (a : K) • eigenSum f a v := by rw [hshift]; rfl

theorem sum_eigenSum [DecidableEq K] (v : V) : ∑ a : Kˣ, eigenSum f a v = -v := by
  simp only [eigenSum]
  rw [Finset.sum_comm]
  have hterm : ∀ j ∈ Finset.range (Fintype.card K - 1),
      ∑ a : Kˣ, ((a : K)⁻¹) ^ j • (f ^ j) v = if j = 0 then -v else 0 := by
    intro j hj
    rw [← Finset.sum_smul]
    have hs : ∑ a : Kˣ, ((a : K)⁻¹) ^ j = ∑ a : Kˣ, (a : K) ^ j := by
      refine Fintype.sum_equiv (MulEquiv.inv Kˣ).toEquiv _ _ fun a => ?_
      simp
    rw [hs, FiniteField.sum_pow_units]
    have hlt := Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst hj0
      simp
    · have hnd : ¬ Fintype.card K - 1 ∣ j := fun h =>
        absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) h) (by omega)
      simp [hnd, hj0]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  have hpos : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  simp [Finset.mem_range, hpos]

end Eigen

section Singular

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2] {ι : Type} [Fintype ι]
  [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {f : Module.End K (ι → K)}

omit [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι] in
theorem quad_eq_zero_of_apply_eq_smul (hQf : ∀ v, Q (f v) = Q v) {a : K} (ha : a ≠ 1)
    {v : ι → K} (hv : f v = a • v) : Q v = 0 := by
  have h1 := hQf v
  rw [hv, QuadraticMap.map_smul, smul_eq_mul] at h1
  have h2 : (a * a - 1) * Q v = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  refine (mul_eq_zero.mp h2).resolve_left fun h => ha ?_
  have h3 : (a - 1) * (a - 1) = 0 := by
    linear_combination h - (a - 1) * CharTwo.two_eq_zero (R := K)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)

omit [Fintype K] [DecidableEq K] [CharP K 2] [Fintype ι] [DecidableEq ι] in
theorem polarBilin_apply_of_isometry (hQf : ∀ v, Q (f v) = Q v) (x y : ι → K) :
    Q.polarBilin (f x) (f y) = Q.polarBilin x y := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar, ← map_add, hQf, hQf, hQf]

omit [CharP K 2] [Fintype ι] [DecidableEq ι] in
theorem exists_eigen_not_mem (hf : f ^ (Fintype.card K - 1) = 1) {S T : Submodule K (ι → K)}
    (hfS : ∀ v ∈ S, f v ∈ S) {v : ι → K} (hvS : v ∈ S) (hvT : v ∉ T) :
    ∃ a : Kˣ, eigenSum f a v ∈ S ∧ eigenSum f a v ∉ T ∧
      f (eigenSum f a v) = (a : K) • eigenSum f a v := by
  have hpow : ∀ j : ℕ, (f ^ j) v ∈ S := by
    intro j
    induction j with
    | zero => simpa using hvS
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hfS _ ih
  have hmem : ∀ a : Kˣ, eigenSum f a v ∈ S := fun a =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hpow j)
  by_contra hcon
  have hall : ∀ a : Kˣ, eigenSum f a v ∈ T := fun a => by
    by_contra h
    exact hcon ⟨a, hmem a, h, apply_eigenSum hf a v⟩
  have hsum : ∑ a : Kˣ, eigenSum f a v ∈ T := Submodule.sum_mem _ fun a _ => hall a
  rw [sum_eigenSum] at hsum
  exact hvT (by simpa using T.neg_mem hsum)

omit [DecidableEq ι] in
theorem exists_totallySingular_pair (hf : f ^ (Fintype.card K - 1) = 1)
    (hQf : ∀ v, Q (f v) = Q v) {S : Submodule K (ι → K)} (hfS : ∀ v ∈ S, f v ∈ S)
    (hS : 3 ≤ Module.finrank K S) (hfix : ∀ v ∈ S, f v = v → v = 0) :
    ∃ x₀ ∈ S, ∃ x₁ ∈ S, LinearIndependent K ![x₀, x₁] ∧ Q x₀ = 0 ∧ Q x₁ = 0 ∧
      Q.polarBilin x₀ x₁ = 0 := by
  obtain ⟨v, hvS, hv0⟩ : ∃ v ∈ S, v ≠ 0 := by
    by_contra h
    push Not at h
    have hb : S = ⊥ := (Submodule.eq_bot_iff S).mpr h
    rw [hb, finrank_bot] at hS
    omega
  obtain ⟨a, hwS, hwT, hw⟩ := exists_eigen_not_mem hf hfS hvS (T := ⊥) (by simpa using hv0)
  set w := eigenSum f a v
  have hw0 : w ≠ 0 := by simpa using hwT
  have ha1 : (a : K) ≠ 1 := fun h => hw0 (hfix w hwS (by rw [hw, h, one_smul]))
  have hQw := quad_eq_zero_of_apply_eq_smul hQf ha1 hw
  set S' := S ⊓ LinearMap.ker (Q.polarBilin w)
  have hfS' : ∀ x ∈ S', f x ∈ S' := by
    rintro x ⟨hxS, hxk⟩
    refine ⟨hfS x hxS, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hxk ⊢
    have h1 := polarBilin_apply_of_isometry hQf w x
    rw [hw, map_smul, LinearMap.smul_apply, smul_eq_mul, hxk] at h1
    exact (mul_eq_zero.mp h1).resolve_left a.ne_zero
  have hS' : 2 ≤ Module.finrank K S' := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker (Q.polarBilin w))
    have h2 : Module.finrank K ↥(S ⊔ LinearMap.ker (Q.polarBilin w)) ≤
        Module.finrank K (ι → K) := Submodule.finrank_le _
    have h3 := LinearMap.finrank_range_add_finrank_ker (Q.polarBilin w)
    have h4 : Module.finrank K ↥(LinearMap.range (Q.polarBilin w)) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range (Q.polarBilin w))
      simpa using this
    show 2 ≤ Module.finrank K ↥(S ⊓ LinearMap.ker (Q.polarBilin w))
    omega
  obtain ⟨u₀, hu₀S', hu₀⟩ : ∃ u₀ ∈ S', u₀ ∉ K ∙ w := by
    by_contra h
    push Not at h
    have := Submodule.finrank_mono (show S' ≤ K ∙ w from h)
    rw [finrank_span_singleton hw0] at this
    omega
  obtain ⟨b, huS', huT, hu⟩ := exists_eigen_not_mem hf hfS' hu₀S' hu₀
  set u := eigenSum f b u₀
  have hb1 : (b : K) ≠ 1 := fun h => huT (by
    rw [hfix u huS'.1 (by rw [hu, h, one_smul])]
    exact zero_mem _)
  have hQu := quad_eq_zero_of_apply_eq_smul hQf hb1 hu
  refine ⟨w, hwS, u, huS'.1, ?_, hQw, hQu, huS'.2⟩
  refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hw0, rfl⟩
  · exfalso
    apply huT
    have h1 : t • u = -(s • w) := eq_neg_of_add_eq_zero_right hst
    have h2 : u = t⁻¹ • (t • u) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, h1]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)))

end Singular

end CFSG.ComponentClassification.RankTwoClassical.ORigid
