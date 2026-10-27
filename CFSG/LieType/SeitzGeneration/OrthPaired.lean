module

public import CFSG.LieType.SeitzGeneration.OrthMix
public import CFSG.LieType.SeitzGeneration.OrthTrans

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical2 (orthDerived)

section Vector

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
theorem pow_apply_mem_primaryComponent {h : K[X]} {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap h) (n : ℕ) :
    (x.toLinearMap ^ n) v ∈ primaryComponent x.toLinearMap h := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact apply_mem_primaryComponent (Commute.refl _) ih

theorem q_eq_zero_of_paired (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) {v : V} (hv : v ∈ primaryComponent x.toLinearMap h) :
    Q v = 0 := by
  have hQi : ∀ n : ℕ, Q ((x.toLinearMap ^ n) v) = Q v := fun n => by
    have : (x.toLinearMap ^ n) v = (x ^ n) v := by rw [← toLinearMap_pow]; rfl
    rw [this]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (pow_mem hx.mem n) v
  have hpolar : ∀ (s : Finset ℕ) (n : ℕ),
      polar Q (∑ i ∈ s, (x.toLinearMap ^ i) v) ((x.toLinearMap ^ n) v) = 0 := by
    intro s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, polar_add_left, ih, add_zero]
      exact hx.polar_eq_zero_of_ne hh hne (pow_apply_mem_primaryComponent hv a)
        (pow_apply_mem_primaryComponent hv n)
  have key : ∀ n : ℕ, Q (∑ i ∈ Finset.range n, (x.toLinearMap ^ i) v) = (n : K) * Q v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,
        QuadraticMap.map_add Q (∑ i ∈ Finset.range n, (x.toLinearMap ^ i) v)
          ((x.toLinearMap ^ n) v), ih, hQi n, hpolar]
      push_cast
      ring
  have h0 := key p
  rw [hx.sum_pow_eq_zero hh hne1 hv, QuadraticMap.map_zero] at h0
  exact (mul_eq_zero.mp h0.symm).resolve_left hx.cast_ne_zero

theorem eq_zero_of_fixed_primary {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap h) (hfix : x v = v) : v = 0 := by
  have hcop : IsCoprime h (X - 1 : K[X]) :=
    isCoprime_of_irreducible_monic_ne (irreducible_of_mem_primaryFactors hh)
      irreducible_X_sub_one (monic_of_mem_primaryFactors hh) monic_X_sub_one hne1
  have hdisj := Polynomial.disjoint_ker_aeval_of_isCoprime x.toLinearMap hcop
  refine Submodule.disjoint_def.mp hdisj v hv ?_
  rw [LinearMap.mem_ker]
  simp [hfix]

theorem apply_ne_smul (hx : OddOrderIsometry Q p x)
    (hroot : ∀ ζ : K, ζ ^ p = 1 → ζ = 1) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) {w : V}
    (hw : w ∈ primaryComponent x.toLinearMap h) (hw0 : w ≠ 0) (c : K) : x w ≠ c • w := by
  intro hc
  have hpow : ∀ n : ℕ, (x ^ n) w = c ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hc, smul_smul, pow_succ]
  have h1 : (x ^ p) w = c ^ p • w := hpow p
  rw [hx.pow_eq_one] at h1
  have h2 : (1 - c ^ p) • w = 0 := by
    rw [sub_smul, one_smul, ← h1]
    simp
  have h3 : c ^ p = 1 := by
    have := (smul_eq_zero.mp h2).resolve_right hw0
    exact (sub_eq_zero.mp this).symm
  have hc1 := hroot c h3
  rw [hc1, one_smul] at hc
  exact hw0 (eq_zero_of_fixed_primary hh hne1 hw hc)

theorem exists_polar_ne_zero_of_stable (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {U : Submodule K V} (hU : ∀ u ∈ U, x u ∈ U)
    (hreg : ∀ u ∈ U, (∀ t ∈ U, polar Q u t = 0) → u = 0) {w : V} (hwU : w ∈ U)
    (hwh : w ∈ primaryComponent x.toLinearMap h) (hw0 : w ≠ 0) :
    ∃ s ∈ U, s ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) ∧ polar Q w s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hw0 (hreg w hwU fun t ht => ?_)
  have hsum := congrArg (fun f : Module.End K V => f t)
    (sum_primaryProjection (x := x.toLinearMap) hx.squarefree_minpoly)
  simp only [LinearMap.sum_apply, Module.End.one_apply] at hsum
  have h1 : polar Q w t = ∑ k ∈ primaryFactors x.toLinearMap,
      polar Q w (primaryProjection x.toLinearMap k t) := by
    conv_lhs => rw [← hsum]
    exact map_sum (polarBilin Q w) _ _
  rw [h1]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkmem := primaryProjection_mem hx.squarefree_minpoly hk t
  have hkU : primaryProjection x.toLinearMap k t ∈ U := aeval_mem_of_stable hU _ ht
  by_cases hkh : k = reciprocalPolynomial h
  · subst hkh
    exact hcon _ hkU hkmem
  · exact hx.polar_primaryComponent_eq_zero hh hk hkh hwh hkmem

theorem exists_orth_partner (hx : OddOrderIsometry Q p x) (hroot : ∀ ζ : K, ζ ^ p = 1 → ζ = 1)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    {U : Submodule K V} (hU : ∀ u ∈ U, x u ∈ U)
    (hreg : ∀ u ∈ U, (∀ t ∈ U, polar Q u t = 0) → u = 0) {w : V} (hwU : w ∈ U)
    (hwh : w ∈ primaryComponent x.toLinearMap h) (hw0 : w ≠ 0) :
    ∃ s ∈ U, s ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) ∧ s ≠ 0 ∧
      polar Q s w = 0 := by
  have hh' := hx.reciprocalPolynomial_mem hh
  have hne1' : reciprocalPolynomial h ≠ X - 1 := fun heq => hne1 (by
    rw [← hx.reciprocal_reciprocal_eq hh, heq, reciprocalPolynomial_X_sub_one])
  obtain ⟨s₁, hs₁U, hs₁h, hs₁⟩ := exists_polar_ne_zero_of_stable hx hh hU hreg hwU hwh hw0
  have hs₁0 : s₁ ≠ 0 := fun h0 => hs₁ (by rw [h0, polar_zero_right])
  have hs₂U : x s₁ ∈ U := hU _ hs₁U
  have hs₂h : x s₁ ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
    apply_mem_primaryComponent (Commute.refl _) hs₁h
  by_cases ha : polar Q s₁ w = 0
  · exact ⟨s₁, hs₁U, hs₁h, hs₁0, ha⟩
  · have ha' : polar Q w s₁ ≠ 0 := by rwa [polar_comm]
    refine ⟨polar Q (x s₁) w • s₁ - polar Q s₁ w • x s₁,
      U.sub_mem (U.smul_mem _ hs₁U) (U.smul_mem _ hs₂U),
      Submodule.sub_mem _ (Submodule.smul_mem _ _ hs₁h) (Submodule.smul_mem _ _ hs₂h), ?_, ?_⟩
    · intro h0
      refine apply_ne_smul hx hroot hh' hne1' hs₁h hs₁0 (polar Q (x s₁) w / polar Q s₁ w) ?_
      have h1 : polar Q s₁ w • x s₁ = polar Q (x s₁) w • s₁ := (sub_eq_zero.mp h0).symm
      calc x s₁ = (polar Q s₁ w)⁻¹ • (polar Q s₁ w • x s₁) := by
            rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        _ = _ := by rw [h1, smul_smul, div_eq_inv_mul]
    · rw [polar_sub_left, polar_smul_left_eq, polar_smul_left_eq]
      ring

theorem fixes_dual_of_transvection (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgx : g * x = x * g)
    {S : Submodule K V} (hgS : ∀ u ∈ primaryComponent x.toLinearMap h, g u - u ∈ S) {s : V}
    (hs : s ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h))
    (hperp : ∀ t ∈ S, polar Q t s = 0) : g s = s := by
  have hcomm : ∀ (e : V ≃ₗ[K] V), e * x = x * e → Commute e.toLinearMap x.toLinearMap :=
    fun e he => LinearMap.ext fun v => by
      have := congrArg (fun f : V ≃ₗ[K] V => f v) he
      simpa using this
  have hginv : g⁻¹ * x = x * g⁻¹ := (Commute.inv_left (show Commute g x from hgx)).eq
  have hgs : g s ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
    apply_mem_primaryComponent (hcomm g hgx) hs
  have hd : g s - s ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
    Submodule.sub_mem _ hgs hs
  have hzero : g s - s = 0 := by
    refine hx.eq_zero_of_polar_paired_right hh hd fun u hu => ?_
    have hu' : g⁻¹ u ∈ primaryComponent x.toLinearMap h :=
      apply_mem_primaryComponent (hcomm g⁻¹ hginv) hu
    have h1 : g (g⁻¹ u) - g⁻¹ u ∈ S := hgS _ hu'
    rw [show g (g⁻¹ u) = u from g.apply_symm_apply u] at h1
    have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg (g⁻¹ u) s
    rw [show g (g⁻¹ u) = u from g.apply_symm_apply u] at h2
    rw [polar_sub_right, h2]
    have h3 := hperp _ h1
    rw [polar_sub_left] at h3
    linear_combination -h3
  exact sub_eq_zero.mp hzero

end Vector

section Pivot

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem regular_lineSpace (hK : KernelLineData Q p E) {M : Subgroup E} (hM : Nat.card M = p) :
    ∀ u ∈ lineSpace M, (∀ t ∈ lineSpace M, polar Q u t = 0) → u = 0 := fun u hu hperp =>
  congrArg Subtype.val ((hK.regular (some ⟨M, hM⟩)).1 ⟨u, hu⟩ fun t => by
    simpa [polarBilin_apply_apply] using hperp t t.2)

omit [Finite K] [FiniteDimensional K V] in
theorem mem_orthCentralizerSpan_of_commute {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q)
    {a : orthDerived Q} (ha : a ∈ E) (ha1 : a ≠ 1)
    (hc : g * (a : V ≃ₗ[K] V) = (a : V ≃ₗ[K] V) * g) : g ∈ orthCentralizerSpan Q E :=
  Subgroup.subset_closure ⟨hg, (a : V ≃ₗ[K] V), ⟨a, ha, rfl⟩, fun h => ha1 (Subtype.ext h), hc⟩

omit [Finite K] [FiniteDimensional K V] in
theorem ne_bot_of_card_prime (hp : p.Prime) {N : Subgroup E} (hN : Nat.card N = p) : N ≠ ⊥ := by
  intro h0
  rw [h0, Subgroup.card_bot] at hN
  exact hp.one_lt.ne' hN.symm

theorem paired_pivot (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp3 : 3 < p)
    (hpl : p ≠ ringChar K) (hroot : ∀ ζ : K, ζ ^ p = 1 → ζ = 1) (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {M N : Subgroup E} (hM : Nat.card M = p)
    (hN : Nat.card N = p) (hMN : M ≠ N) {a : E} (ha : a ≠ 1) {h : K[X]}
    (hh : h ∈ primaryFactors (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap)
    (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap h)
    {z w : V} (hzM : z ∈ lineSpace M)
    (hzh : z ∈ primaryComponent (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap h)
    (hwN : w ∈ lineSpace N)
    (hwh : w ∈ primaryComponent (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap h)
    (hw0 : w ≠ 0) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ z ∈ rootSet Q (orthCentralizerSpan Q E) s₀ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hN0 := ne_bot_of_card_prime hp hN
  have hx := oddOrderIsometry_of_mem hQ hp hpl hK ha
  have hh' := hx.reciprocalPolynomial_mem hh
  have hne1' : reciprocalPolynomial h ≠ X - 1 := fun heq => hne1 (by
    rw [← hx.reciprocal_reciprocal_eq hh, heq, reciprocalPolynomial_X_sub_one])
  have hne' : reciprocalPolynomial h ≠ reciprocalPolynomial (reciprocalPolynomial h) := by
    rw [hx.reciprocal_reciprocal_eq hh]
    exact fun e => hne e.symm
  have hSM : ∀ s ∈ lineSpace M, (((a : E) : orthDerived Q) : V ≃ₗ[K] V) s ∈ lineSpace M :=
    fun s hs => lineSpace_stable hK.comm M a hs
  have hSN : ∀ s ∈ lineSpace N, (((a : E) : orthDerived Q) : V ≃ₗ[K] V) s ∈ lineSpace N :=
    fun s hs => lineSpace_stable hK.comm N a hs
  have hwS : w ∉ lineSpace M := fun hwM =>
    hw0 (Submodule.disjoint_def.mp (disjoint_lineSpace_sup hK hM hN hMN) w hwM
      (Submodule.mem_sup_right hwN))
  obtain ⟨g, hgΩ, hgx, hgS, -, hgw⟩ :=
    exists_paired_transvection hx hp hp3 hh hne1 hne hm hSM hzM hzh hwh hwS
  obtain ⟨s₀, hs₀N, hs₀h, hs₀0, hs₀w⟩ :=
    exists_orth_partner hx hroot hh hne1 hSN (regular_lineSpace hK hN) hwN hwh hw0
  have hQs₀ : Q s₀ = 0 := q_eq_zero_of_paired hx hh' hne1' hne' hs₀h
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup Q hgΩ
  have hgs₀ : g s₀ = s₀ := by
    refine fixes_dual_of_transvection hx hh hgO hgx hgS hs₀h fun t ht => ?_
    exact polar_eq_zero_of_mem_sup hK hN hM hMN ht (Submodule.mem_sup_right hs₀N)
  have hgH : g ∈ orthCentralizerSpan Q E :=
    mem_orthCentralizerSpan_of_commute hgΩ (a := ((a : E) : orthDerived Q)) a.2
      (fun h1 => ha (Subtype.ext h1)) hgx
  have hH : orthCentralizerSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthCentralizerSpan_le_orthogonalGroup E
  have hwR : w ∈ rootSet Q (orthCentralizerSpan Q E) s₀ :=
    ⟨hs₀w,
      eichler_mem_span_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hs₀N)
        (Submodule.mem_sup_right hwN)⟩
  have h1 := rootSet_map hH hgH hwR
  rw [hgs₀] at h1
  have h2 := AddSubgroup.sub_mem _ h1 hwR
  rw [hgw, add_sub_cancel_left] at h2
  exact ⟨s₀, hs₀N, hs₀0, hQs₀, h2⟩

theorem hasOrthPairs_of_paired (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hpl : p ≠ ringChar K) (hroot : ∀ ζ : K, ζ ^ p = 1 → ζ = 1) (hK : KernelLineData Q p E)
    {M : Subgroup E} (hM : Nat.card M = p) {a : E} (ha : a ≠ 1) {h : K[X]}
    (hh : h ∈ primaryFactors (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap)
    (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h) {z : V} (hzM : z ∈ lineSpace M)
    (hzh : z ∈ primaryComponent (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap h)
    (hz0 : z ≠ 0) : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace M) := by
  have hx := oddOrderIsometry_of_mem hQ hp hpl hK ha
  have hz2 : (((a : E) : orthDerived Q) : V ≃ₗ[K] V) z ∈ lineSpace M :=
    lineSpace_stable hK.comm M a hzM
  have hz2h : (((a : E) : orthDerived Q) : V ≃ₗ[K] V) z ∈
      primaryComponent (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap h :=
    apply_mem_primaryComponent (Commute.refl _) hzh
  refine exists_orthPairs (regular_sup hK hM) (Submodule.mem_sup_right hzM)
    (Submodule.mem_sup_right hz2) (q_eq_zero_of_paired hx hh hne1 hne hzh)
    (q_eq_zero_of_paired hx hh hne1 hne hz2h) (hx.polar_eq_zero_of_ne hh hne hzh hz2h) hz0 ?_
  intro c hc
  exact apply_ne_smul hx hroot hh hne1 hzh hz0 c hc

end Pivot

section AllPaired

theorem nontrivial_of_three_singular {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) : Nontrivial V := by
  obtain ⟨U, hU3, -⟩ := hT
  exact Module.nontrivial_of_finrank_pos (R := K)
    (lt_of_lt_of_le (by norm_num : 0 < 3) (hU3 ▸ Submodule.finrank_le U))

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

variable (Q) in
@[expose] def HasSelfDualFactor (E : Subgroup (orthDerived Q)) : Prop :=
  ∃ a ∈ E, a ≠ 1 ∧ ∃ h ∈ primaryFactors (((a : orthDerived Q) : V ≃ₗ[K] V)).toLinearMap,
    h ≠ X - 1 ∧ h = reciprocalPolynomial h

theorem closure_eq_top_of_allPaired (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime) (hp3 : 3 < p)
    (hpl : p ≠ ringChar K) (hroot : ∀ ζ : K, ζ ^ p = 1 → ζ = 1)
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) (hnsd : ¬ HasSelfDualFactor Q E) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  classical
  have : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp (by omega) hpl E hcomm hexp hcard
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  obtain ⟨N, M₀, hN, hM₀, hNM, hVN, hVM₀⟩ := hK.two_active
  have hpair : ∀ a : E, a ≠ 1 → ∀ h ∈ primaryFactors
      (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
        h ≠ reciprocalPolynomial h := fun a ha h hh hne1 heq =>
    hnsd ⟨(a : orthDerived Q), a.2, fun e => ha (Subtype.ext e), h, hh, hne1, heq⟩
  obtain ⟨a₀, ha₀, h₀, hh₀, hne₀, -, -, ⟨w₀, hw₀N, hw₀h, hw₀0⟩⟩ :=
    exists_mixing_factor_orth hQ hp hpl hK hM₀ hN hNM.symm hVM₀ hVN
  have hPN := hasOrthPairs_of_paired hQ hp hpl hroot hK hN ha₀ hh₀ hne₀
    (hpair a₀ ha₀ h₀ hh₀ hne₀) hw₀N hw₀h hw₀0
  have hle : elementaryGroup Q ≤ orthCentralizerSpan Q E := by
    refine elementaryGroup_le_span_of_pivots hK hEΩ hp hQ hN hPN fun M hM hMN hVM => ?_
    obtain ⟨a, ha, h, hh, hne1, hm2, ⟨v, hvM, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
      exists_mixing_factor_orth hQ hp hpl hK hM hN hMN hVM hVN
    have hne := hpair a ha h hh hne1
    obtain ⟨s₀, hs₀N, hs₀0, hQs₀, hb⟩ := paired_pivot hQ hp hp3 hpl hroot hK hEΩ hM hN hMN ha hh
      hne1 hne hm2 hvM hvh hwN hwh hw0
    exact ⟨hasOrthPairs_of_paired hQ hp hpl hroot hK hM ha hh hne1 hne hvM hvh hv0, s₀, hs₀N,
      hs₀0, hQs₀, v, hvM, hv0, hb⟩
  exact closure_centralizers_eq_top_of_le E ((orthDerived_eq_and_le_closure hQ hT).1 ▸ hle)

end AllPaired

end CFSG.LieType.SeitzGeneration
