module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal

section Sign

variable {K : Type} [Field K]

open scoped Classical in
noncomputable def chi (a : K) : ℤ := if a = 0 then 1 else -1

theorem eq_zero_or_eq_one_of_natCard_eq_two [Finite K] (hK : Nat.card K = 2) (a : K) :
    a = 0 ∨ a = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : ({0, 1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK]
  have h := Finset.eq_univ_of_card _ hc
  have ha : a ∈ ({0, 1} : Finset K) := h ▸ Finset.mem_univ a
  simpa using ha

theorem chi_zero : chi (0 : K) = 1 := by simp [chi]

theorem chi_of_ne_zero {a : K} (ha : a ≠ 0) : chi a = -1 := by simp [chi, ha]

theorem chi_add [Finite K] [CharP K 2] (hK : Nat.card K = 2) (a b : K) :
    chi (a + b) = chi a * chi b := by
  rcases eq_zero_or_eq_one_of_natCard_eq_two hK a with rfl | rfl <;>
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK b with rfl | rfl
  · simp [chi_zero]
  · simp [chi_zero]
  · simp [chi_zero]
  · rw [CharTwo.add_self_eq_zero, chi_zero, chi_of_ne_zero one_ne_zero]
    norm_num

theorem sum_chi_of_forall_eq_zero {M : Type*} [Fintype M] (f : M → K) (hf : ∀ u, f u = 0) :
    ∑ u, chi (f u) = (Fintype.card M : ℤ) := by
  simp [hf, chi_zero]

theorem sum_chi_of_ne_zero [Finite K] [CharP K 2] (hK : Nat.card K = 2) {M : Type*}
    [AddCommGroup M] [Fintype M] (f : M →+ K) {u₀ : M} (hu₀ : f u₀ ≠ 0) :
    ∑ u, chi (f u) = 0 := by
  have hs : ∑ u, chi (f (u + u₀)) = ∑ u, chi (f u) :=
    Fintype.sum_equiv (Equiv.addRight u₀) _ _ fun u => rfl
  have hs' : ∑ u, chi (f (u + u₀)) = - ∑ u, chi (f u) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_add, chi_add hK, chi_of_ne_zero hu₀, mul_neg_one]
  omega

end Sign

section Quadratic

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

theorem chi_map_add (hK : Nat.card K = 2) (Q : QuadraticForm K V) (v u : V) :
    chi (Q (v + u)) = chi (Q v) * chi (Q u) * chi (polar Q v u) := by
  rw [QuadraticMap.map_add (⇑Q) v u, chi_add hK, chi_add hK]

theorem charSum_eq_of_totallySingular (hK : Nat.card K = 2) [FiniteDimensional K V] [Fintype V]
    {Q : QuadraticForm K V} (hB : (polarBilin Q).Nondegenerate) {U : Submodule K V}
    (hU : ∀ u ∈ U, Q u = 0) (hdim : finrank K V = 2 * finrank K U) :
    ∑ v, chi (Q v) = (Nat.card U : ℤ) := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hpolU : ∀ v ∈ U, ∀ u ∈ U, polar Q v u = 0 := fun v hv u hu => by
    have := QuadraticMap.map_add (⇑Q) v u
    rw [hU _ (U.add_mem hv hu), hU v hv, hU u hu] at this
    simpa using this.symm
  have hle : U ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U := fun v hv =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => by
      rw [polarBilin_apply_apply]
      exact hpolU u hu v hv
  have heq : U = LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      rw [LinearMap.BilinForm.finrank_orthogonal hB]; omega)
  have hcard : (Nat.card U : ℤ) = (Fintype.card U : ℤ) := by rw [Nat.card_eq_fintype_card]
  have key : ∀ v, ∑ u : U, chi (polar Q v u) = if v ∈ U then (Fintype.card U : ℤ) else 0 := by
    intro v
    by_cases hv : v ∈ U
    · simp only [hv, ↓reduceIte]
      exact sum_chi_of_forall_eq_zero _ fun u => hpolU v hv u u.2
    · simp only [hv, ↓reduceIte]
      rw [heq, LinearMap.BilinForm.mem_orthogonal_iff] at hv
      push Not at hv
      obtain ⟨n, hn, hne⟩ := hv
      rw [polarBilin_apply_apply] at hne
      let f : U →+ K := ((polarBilin Q v).comp U.subtype).toAddMonoidHom
      have := sum_chi_of_ne_zero hK f (u₀ := ⟨n, hn⟩) (by
        simpa [f, polarBilin_apply_apply, QuadraticMap.polar_comm Q v n] using hne)
      simpa [f, polarBilin_apply_apply] using this
  have hmain : (Fintype.card U : ℤ) * ∑ v, chi (Q v) =
      (Fintype.card U : ℤ) * (Fintype.card U : ℤ) := by
    calc (Fintype.card U : ℤ) * ∑ v, chi (Q v) = ∑ _u : U, ∑ v, chi (Q v) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ u : U, ∑ v, chi (Q (v + u)) := Finset.sum_congr rfl fun u _ =>
          (Fintype.sum_equiv (Equiv.addRight (u : V)) _ _ fun v => rfl).symm
      _ = ∑ v, ∑ u : U, chi (Q v) * chi (polar Q v u) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
          rw [chi_map_add hK, hU u u.2, chi_zero, mul_one]
      _ = ∑ v, chi (Q v) * (if v ∈ U then (Fintype.card U : ℤ) else 0) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← key, Finset.mul_sum]
      _ = ∑ v ∈ Finset.univ.filter (· ∈ U), (Fintype.card U : ℤ) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases hv : v ∈ U
          · simp only [hv, ↓reduceIte, hU v hv, chi_zero, one_mul]
          · simp only [hv, ↓reduceIte, mul_zero]
      _ = (Fintype.card U : ℤ) * (Fintype.card U : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype]
  have hpos : (Fintype.card U : ℤ) ≠ 0 := by
    have := Fintype.card_pos (α := U)
    omega
  rw [hcard]
  exact mul_left_cancel₀ hpos hmain

theorem card_filter_modEq_three {α : Type*} [Fintype α] [DecidableEq α] (g : α → α)
    (hg : ∀ a, g (g (g a)) = a) (P : α → Prop) [DecidablePred P] (hP : ∀ a, P (g a) ↔ P a) :
    (Finset.univ.filter P).card ≡ (Finset.univ.filter fun a => P a ∧ g a = a).card [MOD 3] := by
  classical
  let f : Function.End {a // P a} := fun b => ⟨g b, (hP b).2 b.2⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    funext b
    apply Subtype.ext
    show g (g (g b)) = b
    exact hg b
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  have e : f.fixedPoints ≃ {a // P a ∧ g a = a} :=
    { toFun := fun b => ⟨b.1.1, b.1.2, congrArg Subtype.val b.2⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, Subtype.ext a.2.2⟩
      left_inv := fun b => rfl
      right_inv := fun a => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype, Fintype.card_subtype] at h
  exact h

omit [Finite K] [CharP K 2] in
open scoped Classical in
theorem sum_chi_eq_card_sub (Q : QuadraticForm K V) (s : Finset V) :
    ∑ v ∈ s, chi (Q v) = ((s.filter fun v => Q v = 0).card : ℤ) -
      (s.filter fun v => ¬ Q v = 0).card := by
  classical
  simp only [chi]
  rw [Finset.sum_ite]
  simp [sub_eq_add_neg]

omit [Finite K] [CharP K 2] in
open scoped Classical in
theorem charSum_modEq_fixed [Fintype V] (Q : QuadraticForm K V) (x : V ≃ₗ[K] V)
    (hQ : ∀ v, Q (x v) = Q v) (h3 : x ^ 3 = 1) :
    ∑ v, chi (Q v) ≡ ∑ v ∈ Finset.univ.filter (fun v => x v = v), chi (Q v) [ZMOD 3] := by
  classical
  have hg : ∀ v, x (x (x v)) = v := fun v => by
    have := congrArg (fun y : V ≃ₗ[K] V => y v) h3
    simpa [pow_succ] using this
  have h1 := card_filter_modEq_three (fun v => x v) hg (fun v => Q v = 0)
    (fun v => by simp only [hQ])
  have h2 := card_filter_modEq_three (fun v => x v) hg (fun v => ¬ Q v = 0)
    (fun v => by simp only [hQ])
  rw [sum_chi_eq_card_sub, sum_chi_eq_card_sub, Finset.filter_filter, Finset.filter_filter]
  refine Int.ModEq.sub (Int.natCast_modEq_iff.mpr ?_) (Int.natCast_modEq_iff.mpr ?_)
  · convert h1 using 3
    simp [and_comm]
  · convert h2 using 3
    simp [and_comm]

end Quadratic

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem not_exists_totallySingular_fixed_of_odd (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 x) {r m : ℕ} (hdim : finrank K V = 2 * r)
    (hmax : ∃ U : Submodule K V, finrank K U = r ∧ ∀ u ∈ U, Q u = 0)
    (hfix : finrank K (fixedSpace x) + 2 * m = 2 * r) (hm : Odd m) :
    ¬ ∃ W : Submodule K V, W ≤ fixedSpace x ∧ finrank K W = r - m ∧ ∀ w ∈ W, Q w = 0 := by
  classical
  rintro ⟨W, hWle, hWdim, hWQ⟩
  have : Finite V := Module.finite_of_finite K
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨U, hU, hUQ⟩ := hmax
  have hB : (polarBilin Q).Nondegenerate :=
    ⟨fun v hv => hx.regular v fun w => by simpa [polarBilin_apply_apply] using hv w,
     fun v hv => hx.regular v fun w => by
      rw [QuadraticMap.polar_comm]; simpa [polarBilin_apply_apply] using hv w⟩
  have hS : ∑ v, chi (Q v) = 2 ^ r := by
    rw [charSum_eq_of_totallySingular hK hB hUQ (by omega), Module.natCard_eq_pow_finrank (K := K),
      hK, hU]
    norm_cast
  set V₁ := fixedSpace x with hV₁
  let Q₁ : QuadraticForm K V₁ := Q.comp V₁.subtype
  have hB₁ : (polarBilin Q₁).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  have : Finite V₁ := Module.finite_of_finite K
  have : Fintype V₁ := Fintype.ofFinite V₁
  let W' : Submodule K V₁ := W.comap V₁.subtype
  have hW'dim : finrank K W' = r - m := by
    rw [← hWdim]
    exact (Submodule.comapSubtypeEquivOfLe hWle).finrank_eq
  have hS₁ : ∑ v : V₁, chi (Q₁ v) = 2 ^ (r - m) := by
    rw [charSum_eq_of_totallySingular hK hB₁ (U := W') (fun w hw => hWQ w hw) (by omega),
      Module.natCard_eq_pow_finrank (K := K), hK, hW'dim]
    norm_cast
  have hmod := charSum_modEq_fixed Q x (fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    hx.mem v) hx.pow_eq_one
  have hsub : ∑ v ∈ Finset.univ.filter (fun v => x v = v), chi (Q v) = ∑ v : V₁, chi (Q₁ v) :=
    Finset.sum_subtype (p := (· ∈ V₁)) _ (fun v => by simp [hV₁, mem_fixedSpace]) _
  rw [hS, hsub, hS₁] at hmod
  have hz := (ZMod.intCast_eq_intCast_iff _ _ 3).mpr hmod
  obtain ⟨k, rfl⟩ := hm
  have hrm : r = (r - (2 * k + 1)) + (2 * k + 1) := by omega
  generalize r - (2 * k + 1) = a at hrm hz
  subst hrm
  push_cast at hz
  have h4 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have hunit : (2 : ZMod 3) ^ a * (2 ^ (2 * k + 1)) = (2 : ZMod 3) ^ a * 1 := by
    rw [mul_one, ← pow_add]; exact hz
  have h2a : (2 : ZMod 3) ^ a ≠ 0 := pow_ne_zero _ (by decide)
  have := mul_left_cancel₀ h2a hunit
  rw [pow_succ, pow_mul, h4, one_pow, one_mul] at this
  exact absurd this (by decide)

end Main

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
