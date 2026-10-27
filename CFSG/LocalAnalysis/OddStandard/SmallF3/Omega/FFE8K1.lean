module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffE8K1_polar_eq {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (x y : V) :
    QuadraticMap.polar Q x y = ∑ i, 2 * c i * (fr.b.repr x i * fr.b.repr y i) := by
  rw [QuadraticMap.polar, fr.map_eq (x + y), fr.map_eq x, fr.map_eq y, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, Finsupp.add_apply]
  ring

theorem ffE8K1_polar_basis {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (i : ι) (x : V) :
    QuadraticMap.polar Q (fr.b i) x = 2 * c i * fr.b.repr x i := by
  rw [ffE8K1_polar_eq fr, Finset.sum_eq_single i]
  · rw [Module.Basis.repr_self_apply, if_pos rfl]
    ring
  · intro j _ hj
    rw [Module.Basis.repr_self_apply, if_neg (Ne.symm hj)]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ffE8K1_signChange_fix {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    (J : Finset (Fin 4)) {x : V} (hx : ∀ k, fr.b.repr x (Sum.inr k) = 0) :
    ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) x = x := by
  apply fr.b.repr.injective
  ext m
  rw [fr.repr_signChange]
  rcases m with a | k
  · simp [ffE8Hat]
  · simp [ffE8Hat, hx k]

theorem ffE8K1_mem_normalizer_of_monomial {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {g : OGroup Q} (hg : g * g = 1) (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ZMod 3)
    (hab : ∀ (i : Fin 2) (k : Fin 4),
      fr.b.repr ((g : V ≃ₗ[ZMod 3] V) (fr.b (Sum.inl i))) (Sum.inr k) = 0)
    (hmap : ∀ k, (g : V ≃ₗ[ZMod 3] V) (fr.b (Sum.inr k)) = s k • fr.b (Sum.inr (σ k))) :
    g ∈ normalizer (ffE8Group fr : Set (OGroup Q)) := by
  have key : ∀ e ∈ ffE8Group fr, g * e * g⁻¹ ∈ ffE8Group fr := by
    rintro e ⟨J, hJ, rfl⟩
    refine ⟨J.map σ.toEmbedding, ?_, ?_⟩
    · rw [Finset.card_map]
      exact hJ
    · rw [mul_inv_eq_iff_eq_mul]
      apply Subtype.ext
      apply fr.b.ext'
      intro i
      rw [Submonoid.coe_mul, Submonoid.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      rcases i with i | k
      · rw [fr.signChange_basis, if_neg (by simp [ffE8Hat]),
          ffE8K1_signChange_fix fr _ (hab i)]
      · have hiff : Sum.inr (σ k) ∈ ffE8Hat (J.map σ.toEmbedding) ↔
            Sum.inr k ∈ ffE8Hat J := by
          simp [ffE8Hat]
        rw [fr.signChange_basis]
        by_cases hk : Sum.inr k ∈ ffE8Hat J
        · rw [if_pos hk, map_neg, hmap k, map_smul, fr.signChange_basis, if_pos (hiff.mpr hk),
            smul_neg]
        · rw [if_neg hk, hmap k, map_smul, fr.signChange_basis,
            if_neg (fun h => hk (hiff.mp h))]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [mem_normalizer_iff]
  intro e
  refine ⟨key e, fun h => ?_⟩
  have h2 := key _ h
  have h3 : g * (g * e * g⁻¹) * g⁻¹ = e := by
    rw [hginv]
    calc g * (g * e * g) * g = (g * g) * e * (g * g) := by group
      _ = e := by rw [hg]; group
  rwa [h3] at h2

theorem ffE8K1_two_nonzero (c : Fin 4 → ZMod 3) (h : ∑ k, c k ^ 2 = 2) :
    ∃ j k : Fin 4, j ≠ k ∧ c j ≠ 0 ∧ c k ≠ 0 ∧ ∀ l, l ≠ j → l ≠ k → c l = 0 := by
  revert c
  decide +kernel

theorem ffE8K1_sq_one (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  revert x
  decide

theorem ffE8K1_coeff {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) {u : V} [Invertible (Q u)]
    (hu : Q u = -ε) (c : ZMod 3) : ⅟(Q u) * (2 * ε * c) = c := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> decide
  have h1 : (⅟(Q u) : ZMod 3) = -ε := by
    rw [invOf_eq_inv]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [hu, neg_mul_neg, hε2]
  rw [h1]
  have h2 : (-2 : ZMod 3) = 1 := by decide
  calc -ε * (2 * ε * c) = (-2) * (ε * ε) * c := by ring
    _ = c := by rw [hε2, h2]; ring

theorem ffE8K1_coords {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {u : V} (hu : Q u = -ε) (ha : fr.b.repr u (Sum.inl 0) = 0)
    (hb : fr.b.repr u (Sum.inl 1) = 0) :
    ∃ j k : Fin 4, j ≠ k ∧ fr.b.repr u (Sum.inr j) ≠ 0 ∧ fr.b.repr u (Sum.inr k) ≠ 0 ∧
      ∀ l, l ≠ j → l ≠ k → fr.b.repr u (Sum.inr l) = 0 := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> decide
  have hQ := fr.map_eq u
  rw [hu, Fintype.sum_sum_type, Fin.sum_univ_two] at hQ
  simp only [ffE8Norm, Sum.elim_inl, Sum.elim_inr, ha, hb] at hQ
  have hsum : ∑ k, fr.b.repr u (Sum.inr k) ^ 2 = 2 := by
    have h1 : -ε = ε * ∑ k, fr.b.repr u (Sum.inr k) ^ 2 := by
      rw [hQ, Finset.mul_sum]
      simp
    have h2 : ∑ k, fr.b.repr u (Sum.inr k) ^ 2 = -ε * ε := by
      calc ∑ k, fr.b.repr u (Sum.inr k) ^ 2
          = (ε * ε) * ∑ k, fr.b.repr u (Sum.inr k) ^ 2 := by rw [hε2, one_mul]
        _ = ε * (ε * ∑ k, fr.b.repr u (Sum.inr k) ^ 2) := by ring
        _ = -ε * ε := by rw [← h1]; ring
    rw [h2, neg_mul, hε2]
    decide
  exact ffE8K1_two_nonzero (fun k => fr.b.repr u (Sum.inr k)) hsum

theorem ffE8K1_aux {cj ck : ZMod 3} {bj bk w : V} (h : w = cj • bj + ck • bk) :
    bj - cj • w = (1 - cj * cj) • bj + (-(cj * ck)) • bk := by
  rw [h]
  module

theorem ffE8K1_refl_mem_normalizer {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {u : V} [Invertible (Q u)] (hu : Q u = -ε)
    (ha : fr.b.repr u (Sum.inl 0) = 0) (hb : fr.b.repr u (Sum.inl 1) = 0) :
    TauCeti.QuadraticMap.reflectionOrthogonal Q u ∈
      normalizer (ffE8Group fr : Set (OGroup Q)) := by
  obtain ⟨j, k, hjk, hcj, hck, hoth⟩ := ffE8K1_coords hε fr hu ha hb
  have hpol : ∀ p, QuadraticMap.polar Q u (fr.b p) = 2 * ffE8Norm ε p * fr.b.repr u p :=
    fun p => by rw [QuadraticMap.polar_comm Q u (fr.b p), ffE8K1_polar_basis]
  have hr1 : ∀ i : Fin 2, TauCeti.QuadraticMap.reflection Q u (fr.b (Sum.inl i)) =
      fr.b (Sum.inl i) := by
    intro i
    refine TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q u ?_
    rw [hpol]
    fin_cases i <;> simp [ha, hb]
  have hr2 : ∀ l, l ≠ j → l ≠ k → TauCeti.QuadraticMap.reflection Q u (fr.b (Sum.inr l)) =
      fr.b (Sum.inr l) := by
    intro l hlj hlk
    refine TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q u ?_
    rw [hpol]
    simp [ffE8Norm, hoth l hlj hlk]
  have hexp : u = fr.b.repr u (Sum.inr j) • fr.b (Sum.inr j) +
      fr.b.repr u (Sum.inr k) • fr.b (Sum.inr k) := by
    conv_lhs => rw [← fr.b.sum_repr u]
    rw [Fintype.sum_sum_type, Fin.sum_univ_two, ha, hb, zero_smul, zero_smul, zero_add, zero_add]
    rw [Finset.sum_eq_add j k hjk]
    · intro l _ hl
      rw [hoth l hl.1 hl.2, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ j) h
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hrefl : ∀ l, TauCeti.QuadraticMap.reflection Q u (fr.b (Sum.inr l)) =
      fr.b (Sum.inr l) - fr.b.repr u (Sum.inr l) • u := by
    intro l
    rw [TauCeti.QuadraticMap.reflection_apply, hpol]
    simp only [ffE8Norm, Sum.elim_inr]
    rw [ffE8K1_coeff hε hu]
  have hjj := ffE8K1_sq_one _ hcj
  have hkk := ffE8K1_sq_one _ hck
  have hrj : TauCeti.QuadraticMap.reflection Q u (fr.b (Sum.inr j)) =
      (-(fr.b.repr u (Sum.inr j) * fr.b.repr u (Sum.inr k))) • fr.b (Sum.inr k) := by
    rw [hrefl j, ffE8K1_aux hexp, hjj, sub_self, zero_smul, zero_add]
  have hrk : TauCeti.QuadraticMap.reflection Q u (fr.b (Sum.inr k)) =
      (-(fr.b.repr u (Sum.inr j) * fr.b.repr u (Sum.inr k))) • fr.b (Sum.inr j) := by
    rw [hrefl k, ffE8K1_aux (hexp.trans (add_comm _ _)), hkk, sub_self, zero_smul, zero_add,
      mul_comm]
  refine ffE8K1_mem_normalizer_of_monomial fr
    (TauCeti.QuadraticMap.reflectionOrthogonal_mul_self Q u) (Equiv.swap j k)
    (fun l => if l = j ∨ l = k then -(fr.b.repr u (Sum.inr j) * fr.b.repr u (Sum.inr k)) else 1)
    ?_ ?_
  · intro i k'
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal, hr1 i, Module.Basis.repr_self_apply,
      if_neg (by simp)]
  · intro l
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
    by_cases hlj : l = j
    · subst hlj
      simp [hrj]
    · by_cases hlk : l = k
      · subst hlk
        simp [hrk, hjk.symm]
      · simp [hr2 l hlj hlk, hlj, hlk, Equiv.swap_apply_of_ne_of_ne hlj hlk]

theorem ffE8K1_refl_mem_normalizer_perp {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {u : V} [Invertible (Q u)] (hu : ∀ k, fr.b.repr u (Sum.inr k) = 0) :
    TauCeti.QuadraticMap.reflectionOrthogonal Q u ∈
      normalizer (ffE8Group fr : Set (OGroup Q)) := by
  have hpol : ∀ p, QuadraticMap.polar Q u (fr.b p) = 2 * ffE8Norm ε p * fr.b.repr u p :=
    fun p => by rw [QuadraticMap.polar_comm Q u (fr.b p), ffE8K1_polar_basis]
  refine ffE8K1_mem_normalizer_of_monomial fr
    (TauCeti.QuadraticMap.reflectionOrthogonal_mul_self Q u) 1 (fun _ => 1) ?_ ?_
  · intro i k
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal, TauCeti.QuadraticMap.reflection_apply]
    simp [hu k, Module.Basis.repr_self_apply]
  · intro l
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal, one_smul,
      TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q u]
    · rfl
    · rw [hpol]
      simp [hu l]

theorem ffE8K1_signChange_mem {N : Subgroup (OGroup Q)} (frP : PFrame Q (Option (Fin 5)) ffC)
    (hN : ∀ i : Fin 5, frP.signChange {some i} ∈ N) (J : Finset (Option (Fin 5)))
    (hJ : none ∉ J) : frP.signChange J ∈ N := by
  induction J using Finset.induction_on with
  | empty => rw [frP.signChange_empty]; exact N.one_mem
  | insert j J hj ih =>
    have hsym : symmDiff {j} J = insert j J := by
      ext m
      by_cases hmj : m = j
      · subst hmj
        simp [Finset.mem_symmDiff, hj]
      · simp [Finset.mem_symmDiff, hmj]
    have hprod : frP.signChange (insert j J) = frP.signChange {j} * frP.signChange J := by
      rw [← hsym, ← frP.signChange_mul]
    rw [hprod]
    have hjn : j ≠ none := fun h => hJ (h ▸ Finset.mem_insert_self j J)
    have hJn : none ∉ J := fun h => hJ (Finset.mem_insert_of_mem h)
    obtain ⟨i, rfl⟩ := Option.ne_none_iff_exists'.mp hjn
    exact N.mul_mem (hN i) (ih hJn)

end CFSG.OddStandard.SmallF3.Omega
