module

public import CFSG.LocalAnalysis.ComponentInitial.LinearOrthogonalBasis
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Module QuadraticMap

section Square

variable {K : Type} [Field K] [Finite K] {E : Type} [Field E] [Finite E] [Algebra K E]

theorem isSquare_algebraMap (hK : ringChar K ≠ 2) (hcard : Nat.card E = Nat.card K ^ 2)
    (a : K) : IsSquare (algebraMap K E a) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype E := Fintype.ofFinite E
  by_cases ha : a = 0
  · rw [ha, map_zero]
    exact ⟨0, by rw [mul_zero]⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hE2 : ringChar E ≠ 2 := by
    intro h
    have h3 : ((2 : ℕ) : E) = 0 := by rw [← h]; exact ringChar.Nat.cast_ringChar
    apply h2
    apply (algebraMap K E).injective
    rw [map_ofNat, map_zero]
    exact_mod_cast h3
  have ha' : algebraMap K E a ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap K E).injective]
    exact ha
  rw [FiniteField.isSquare_iff hE2 ha']
  set q := Fintype.card K with hq
  have hqodd : Odd q := by
    rw [Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hK
  have hcardE : Fintype.card E = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hcard, Nat.card_eq_fintype_card]
  obtain ⟨m, hm⟩ := hqodd
  have hdiv : Fintype.card E / 2 = (q - 1) * (m + 1) := by
    rw [hcardE, hm]
    have h1 : (2 * m + 1) ^ 2 = 2 * ((2 * m + 1 - 1) * (m + 1)) + 1 := by
      have : 2 * m + 1 - 1 = 2 * m := by omega
      rw [this]
      ring
    rw [h1, Nat.mul_add_div (by norm_num : 0 < 2), show (1 : ℕ) / 2 = 0 from rfl, add_zero]
  rw [hdiv, pow_mul, ← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one, one_pow]

end Square

section Split

variable {K : Type} [Field K] [Finite K] {E : Type} [Field E] [Algebra K E]
  {V : Type} [AddCommGroup V] [Module K V] [Module E V] [IsScalarTower K E V]

theorem quad_eq_zero_of_mem_span_pair {BE : LinearMap.BilinForm E V} (hBEs : BE.IsSymm)
    {QE : QuadraticForm E V} (hQE : ∀ x, QE x = BE x x / 2) {v w : V} (hv : BE v v = 0)
    (hw : BE w w = 0) (hvw : BE v w = 0) : ∀ x ∈ Submodule.span E {v, w}, QE x = 0 := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  have hwv : BE w v = 0 := by rw [hBEs.eq]; exact hvw
  rw [hQE]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv, hw,
    hvw, hwv, mul_zero, add_zero, zero_div]

variable [FiniteDimensional K V]

theorem exists_split_of_totallySingular [Finite E] (hK2 : ringChar K ≠ 2)
    (hcard : Nat.card E = Nat.card K ^ 2) {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) (hV8 : finrank K V = 8)
    {A : V →ₗ[K] V} {d : K} (hd : d ≠ 0) (hAA : ∀ x, A (A x) = d • x)
    (hQA : ∀ x, Q (A x) = d * Q x)
    (hadj : ∀ x y, Q.polarBilin (A x) y = Q.polarBilin x (A y))
    (g0 : E) (hg0 : ∀ v : V, g0 • v = A v)
    (hE : ∀ z : E, ∃ a b : K, z = algebraMap K E a + algebraMap K E b * g0)
    {BE : LinearMap.BilinForm E V} (hBEs : BE.IsSymm)
    (hBE : ∀ x y, BE x y = algebraMap K E (Q.polarBilin x y) +
      algebraMap K E (d⁻¹ * Q.polarBilin (A x) y) * g0)
    {QE : QuadraticForm E V} (hQE : ∀ x, QE x = BE x x / 2)
    {U : Submodule K V} (hU4 : finrank K U = 4) (hUQ : ∀ x ∈ U, Q x = 0) :
    ∃ S : Submodule E V, finrank E S = 2 ∧ ∀ x ∈ S, QE x = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hBs : ∀ x y, Q.polarBilin x y = Q.polarBilin y x := fun x y =>
    QuadraticMap.polar_comm Q x y
  have hBU : ∀ x ∈ U, ∀ y ∈ U, Q.polarBilin x y = 0 := by
    intro x hx y hy
    change polar Q x y = 0
    rw [polar, hUQ _ (add_mem hx hy), hUQ x hx, hUQ y hy, sub_zero, sub_zero]
  have hBA : ∀ x y, Q.polarBilin (A x) (A y) = d * Q.polarBilin x y := by
    intro x y
    change polar Q (A x) (A y) = d * polar Q x y
    rw [polar, polar, ← map_add, hQA, hQA, hQA]
    ring
  have hAinj : Function.Injective A := by
    intro x y h
    have h1 := congrArg A h
    rw [hAA, hAA] at h1
    exact smul_right_injective V hd h1
  set AU := U.map A with hAUdef
  have hAU4 : finrank K AU = 4 := by
    rw [← hU4]
    exact (Submodule.equivMapOfInjective A hAinj U).finrank_eq.symm
  have hBAU : ∀ x ∈ AU, ∀ y ∈ AU, Q.polarBilin x y = 0 := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hBA, hBU x hx y hy, mul_zero]
  have hAUperp : LinearMap.BilinForm.orthogonal Q.polarBilin AU = AU := by
    refine (Submodule.eq_of_le_of_finrank_eq (fun x hx =>
      LinearMap.BilinForm.mem_orthogonal_iff.mpr fun y hy => hBAU y hy x hx) ?_).symm
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hV8, hAU4]
  have hsmul : ∀ (z : E) (v : V), ∃ a b : K, z • v = a • v + b • A v := by
    intro z v
    obtain ⟨a, b, rfl⟩ := hE z
    refine ⟨a, b, ?_⟩
    rw [add_smul, mul_smul, hg0, algebraMap_smul, algebraMap_smul]
  set W0 := U ⊓ AU with hW0def
  have hAW0 : ∀ x ∈ W0, A x ∈ W0 := by
    rintro x ⟨hxU, ⟨y, hyU, hyx⟩⟩
    refine ⟨?_, ⟨x, hxU, rfl⟩⟩
    rw [← hyx, hAA]
    exact U.smul_mem d hyU
  have hBEU : ∀ x ∈ U, ∀ y ∈ U,
      BE x y = algebraMap K E (d⁻¹ * Q.polarBilin x (A y)) * g0 := by
    intro x hx y hy
    rw [hBE, hBU x hx y hy, map_zero, zero_add, hadj]
  have hBEW0 : ∀ w ∈ W0, ∀ u ∈ U, BE w u = 0 := by
    intro w hw u hu
    rw [hBEU w hw.1 u hu]
    have : Q.polarBilin w (A u) = 0 := hBAU w hw.2 (A u) ⟨u, hu, rfl⟩
    rw [this, mul_zero, map_zero, zero_mul]
  have hBEU' : ∀ u ∈ U, ∀ w ∈ W0, BE u w = 0 := fun u hu w hw => by
    rw [hBEs.eq]
    exact hBEW0 w hw u hu
  have hEspan : ∀ (v : V) (z : E), z • v ∈ Submodule.span K {v, A v} := by
    intro v z
    obtain ⟨a, b, h⟩ := hsmul z v
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ a (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ b (Submodule.subset_span (by simp)))
  have hfinish : ∀ v w : V, (∀ s t : E, s • v + t • w = 0 → s = 0 ∧ t = 0) →
      BE v v = 0 → BE w w = 0 → BE v w = 0 →
      ∃ S : Submodule E V, finrank E S = 2 ∧ ∀ x ∈ S, QE x = 0 := by
    intro v w hind hv hw hvw
    refine ⟨Submodule.span E {v, w}, ?_, quad_eq_zero_of_mem_span_pair hBEs hQE hv hw hvw⟩
    have hli : LinearIndependent E ![v, w] := LinearIndependent.pair_iff.mpr hind
    rw [show ({v, w} : Set V) = Set.range ![v, w] by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]]
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hiso : ∀ u₁ ∈ U, ∀ u₂ ∈ U, Q.polarBilin u₁ (A u₂) = 0 → ∀ γ₁ γ₂ ι : E,
      γ₁ * γ₁ = algebraMap K E (Q.polarBilin u₁ (A u₁)) →
      γ₂ * γ₂ = algebraMap K E (Q.polarBilin u₂ (A u₂)) → ι * ι = -1 →
      BE (γ₂ • u₁ + (ι * γ₁) • u₂) (γ₂ • u₁ + (ι * γ₁) • u₂) = 0 := by
    intro u₁ hu₁ u₂ hu₂ h12 γ₁ γ₂ ι hγ₁ hγ₂ hι
    have h21 : Q.polarBilin u₂ (A u₁) = 0 := by rw [← hadj, hBs]; exact h12
    have e12 := hBEU u₁ hu₁ u₂ hu₂
    have e21 := hBEU u₂ hu₂ u₁ hu₁
    have e11 := hBEU u₁ hu₁ u₁ hu₁
    have e22 := hBEU u₂ hu₂ u₂ hu₂
    rw [h12, mul_zero, map_zero, zero_mul] at e12
    rw [h21, mul_zero, map_zero, zero_mul] at e21
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e12,
      e21, e11, e22, map_mul, mul_zero, add_zero, zero_add]
    linear_combination (algebraMap K E d⁻¹ * algebraMap K E (Q.polarBilin u₁ (A u₁)) * g0) * hγ₂ +
      (γ₁ * γ₁ * algebraMap K E d⁻¹ * algebraMap K E (Q.polarBilin u₂ (A u₂)) * g0) * hι -
      (algebraMap K E d⁻¹ * algebraMap K E (Q.polarBilin u₂ (A u₂)) * g0) * hγ₁
  have hEW0 : ∀ (z : E) (x : V), x ∈ W0 → z • x ∈ W0 := by
    intro z x hx
    obtain ⟨a, b, h⟩ := hsmul z x
    rw [h]
    exact W0.add_mem (W0.smul_mem a hx) (W0.smul_mem b (hAW0 x hx))
  have hsq : ∀ a : K, ∃ γ : E, γ * γ = algebraMap K E a := fun a => by
    obtain ⟨γ, hγ⟩ := isSquare_algebraMap (E := E) hK2 hcard a
    exact ⟨γ, hγ.symm⟩
  obtain ⟨ι, hι⟩ : ∃ ι : E, ι * ι = -1 := by
    obtain ⟨ι, hι⟩ := hsq (-1)
    exact ⟨ι, by rw [hι, map_neg, map_one]⟩
  by_cases hW3 : 3 ≤ finrank K W0
  ·
    obtain ⟨w, hwW, hw0⟩ : ∃ w ∈ W0, w ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot (by
      intro h
      rw [h, finrank_bot] at hW3
      omega)
    have hspan2 : finrank K (Submodule.span K ({w, A w} : Set V)) ≤ 2 := by
      have h := finrank_span_finset_le_card (R := K) ({w, A w} : Finset V)
      rw [Finset.coe_insert, Finset.coe_singleton] at h
      exact h.trans (Finset.card_le_two)
    obtain ⟨w', hw'W, hw'⟩ : ∃ w' ∈ W0, w' ∉ Submodule.span K ({w, A w} : Set V) := by
      by_contra h
      push Not at h
      have := Submodule.finrank_mono (show W0 ≤ Submodule.span K ({w, A w} : Set V) from h)
      omega
    refine hfinish w w' ?_ (hBEW0 w hwW w hwW.1) (hBEW0 w' hw'W w' hw'W.1)
      (hBEW0 w hwW w' hw'W.1)
    intro s t hst
    by_cases ht : t = 0
    · rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hw0, ht⟩
    · exfalso
      apply hw'
      have h1 : t • w' = -(s • w) := eq_neg_of_add_eq_zero_right hst
      have h2 : w' = (-(t⁻¹ * s)) • w := by
        calc w' = t⁻¹ • (t • w') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(t⁻¹ * s)) • w := by rw [h1, smul_neg, smul_smul, neg_smul]
      rw [h2]
      exact hEspan w _
  push Not at hW3
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (W0.comap U.subtype)
  set U1 := C.map U.subtype with hU1def
  have hU1U : U1 ≤ U := Submodule.map_subtype_le U C
  have hU1W0 : ∀ x ∈ U1, x ∈ W0 → x = 0 := by
    rintro _ ⟨c, hc, rfl⟩ hcW
    have hcc : c ∈ W0.comap U.subtype ⊓ C := ⟨hcW, hc⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hcc
    rw [hcc]
    rfl
  have hU1sum : ∀ u ∈ U, ∃ y ∈ U1, ∃ w ∈ W0, u = y + w := by
    intro u hu
    have hmem : (⟨u, hu⟩ : U) ∈ W0.comap U.subtype ⊔ C := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hmem
    refine ⟨c, ⟨c, hc, rfl⟩, a, ha, ?_⟩
    have h1 := congrArg Subtype.val hac
    rw [Submodule.coe_add] at h1
    change u = (c : V) + (a : V)
    rw [add_comm]
    exact h1.symm
  have hdimU1 : finrank K U1 + finrank K W0 = 4 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 : finrank K U1 = finrank K C :=
      (Submodule.equivMapOfInjective U.subtype U.injective_subtype C).finrank_eq.symm
    have h3 : finrank K (W0.comap U.subtype) = finrank K W0 := by
      have := (Submodule.equivMapOfInjective U.subtype U.injective_subtype
        (W0.comap U.subtype)).finrank_eq
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr (inf_le_left : U ⊓ AU ≤ U)] at this
      exact this
    have h4 : finrank K (⊤ : Submodule K U) = 4 := by rw [finrank_top]; exact hU4
    omega
  set β : LinearMap.BilinForm K U1 := Q.polarBilin.compl₁₂ U1.subtype (A ∘ₗ U1.subtype)
    with hβ
  have hβapp : ∀ x y : U1, β x y = Q.polarBilin x (A y) := fun _ _ => rfl
  have hβs : β.IsSymm := ⟨fun x y => by rw [hβapp, hβapp, ← hadj, hBs]⟩
  have hβnd : β.Nondegenerate := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hβs.isRefl).mpr fun x hx => ?_
    have hxAU : (x : V) ∈ LinearMap.BilinForm.orthogonal Q.polarBilin AU := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨y, hy, w, hw, rfl⟩ := hU1sum u hu
      rw [map_add, map_add, LinearMap.add_apply]
      have h1 : Q.polarBilin (A y) x = 0 := by
        rw [hBs, ← hβapp x ⟨y, hy⟩]
        exact hx ⟨y, hy⟩
      have h2 : Q.polarBilin (A w) x = 0 := hBU _ (hAW0 w hw).1 _ (hU1U x.2)
      rw [h1, h2, add_zero]
    rw [hAUperp] at hxAU
    exact Subtype.ext (hU1W0 x x.2 ⟨hU1U x.2, hxAU⟩)
  have hodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hK2
  obtain ⟨hval, hbas⟩ :=
    LocalAnalysis.ComponentInitial.finite_odd_symmetric_equal_value_orthogonal_basis hodd rfl
      (by omega : 2 ≤ finrank K U1) hβnd hβs
  obtain ⟨v1, hv1⟩ := hval 1 one_ne_zero
  obtain ⟨eb, heo, -, hea, hel⟩ := hbas 1 v1 one_ne_zero hv1
  have hβne : ∀ i, Q.polarBilin (eb i : V) (A (eb i : V)) ≠ 0 := by
    intro i
    rw [← hβapp]
    rcases Nat.lt_or_ge (i : ℕ) (finrank K U1 - 1) with h | h
    · rw [hea i h]
      exact one_ne_zero
    · exact hel i (by have := i.isLt; omega)
  have hβo : ∀ i j, i ≠ j → Q.polarBilin (eb i : V) (A (eb j : V)) = 0 := fun i j hij => by
    rw [← hβapp]
    exact heo hij
  have hebU : ∀ i, (eb i : V) ∈ U := fun i => hU1U (eb i).2
  have hg00 : g0 ≠ 0 := by
    intro h
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    apply hx
    have h1 := hAA x
    rw [← hg0 x, h, zero_smul, map_zero] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left hd
  have hBEe : ∀ i j, BE (eb i : V) (eb j : V) =
      algebraMap K E (d⁻¹ * Q.polarBilin (eb i : V) (A (eb j : V))) * g0 :=
    fun i j => hBEU _ (hebU i) _ (hebU j)
  have hBEo : ∀ i j, i ≠ j → BE (eb i : V) (eb j : V) = 0 := by
    intro i j hij
    rw [hBEe, hβo i j hij, mul_zero, map_zero, zero_mul]
  have hBEne : ∀ i, BE (eb i : V) (eb i : V) ≠ 0 := by
    intro i
    rw [hBEe]
    refine mul_ne_zero ?_ hg00
    rw [ne_eq, map_eq_zero_iff _ (algebraMap K E).injective]
    exact mul_ne_zero (inv_ne_zero hd) (hβne i)
  choose γ hγ using fun i => hsq (Q.polarBilin (eb i : V) (A (eb i : V)))
  have hγne : ∀ i, γ i ≠ 0 := by
    intro i h
    have h1 := hγ i
    rw [h, mul_zero, eq_comm, map_eq_zero_iff _ (algebraMap K E).injective] at h1
    exact hβne i h1
  have hy : ∀ i j, i ≠ j → BE (γ j • (eb i : V) + (ι * γ i) • (eb j : V))
      (γ j • (eb i : V) + (ι * γ i) • (eb j : V)) = 0 := fun i j hij =>
    hiso _ (hebU i) _ (hebU j) (hβo i j hij) (γ i) (γ j) ι (hγ i) (hγ j) hι
  by_cases hW0 : W0 = ⊥
  ·
    have hn : finrank K U1 = 4 := by
      rw [hW0, finrank_bot] at hdimU1
      omega
    obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl⟩ : ∃ i j k l : Fin (finrank K U1),
        i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l :=
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, by simp [Fin.ext_iff]⟩
    refine hfinish (γ j • (eb i : V) + (ι * γ i) • (eb j : V))
      (γ l • (eb k : V) + (ι * γ k) • (eb l : V)) ?_ (hy i j hij) (hy k l hkl) ?_
    · intro s t hst
      have h1 := congrArg (fun v => BE v (eb i : V)) hst
      have h2 := congrArg (fun v => BE v (eb k : V)) hst
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero, LinearMap.zero_apply, hBEo j i hij.symm, hBEo k i hik.symm,
        hBEo l i hil.symm, hBEo i k hik, hBEo j k hjk, hBEo l k hkl.symm, mul_zero, add_zero,
        zero_add] at h1 h2
      exact ⟨(mul_eq_zero.mp h1).resolve_right (mul_ne_zero (hγne j) (hBEne i)),
        (mul_eq_zero.mp h2).resolve_right (mul_ne_zero (hγne l) (hBEne k))⟩
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBEo i k hik, hBEo i l hil, hBEo j k hjk, hBEo j l hjl, mul_zero, add_zero]
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin (finrank K U1), i ≠ j :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  refine hfinish w (γ j • (eb i : V) + (ι * γ i) • (eb j : V)) ?_ (hBEW0 w hwW w hwW.1)
    (hy i j hij) ?_
  · intro s t hst
    by_cases ht : t = 0
    · rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hw0, ht⟩
    · exfalso
      have h1 : t • (γ j • (eb i : V) + (ι * γ i) • (eb j : V)) = -(s • w) :=
        eq_neg_of_add_eq_zero_right hst
      have hyW : γ j • (eb i : V) + (ι * γ i) • (eb j : V) ∈ W0 := by
        have h2 : γ j • (eb i : V) + (ι * γ i) • (eb j : V) = (-(t⁻¹ * s)) • w := by
          calc _ = t⁻¹ • (t • (γ j • (eb i : V) + (ι * γ i) • (eb j : V))) := by
                rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
            _ = (-(t⁻¹ * s)) • w := by rw [h1, smul_neg, smul_smul, neg_smul]
        rw [h2]
        exact hEW0 _ _ hwW
      have h3 := hBEW0 _ hyW (eb i : V) (hebU i)
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBEo j i hij.symm, mul_zero, add_zero] at h3
      exact hγne j ((mul_eq_zero.mp h3).resolve_right (hBEne i))
  · simp only [map_add, map_smul, smul_eq_mul, hBEW0 w hwW _ (hebU i), hBEW0 w hwW _ (hebU j),
      mul_zero, add_zero]

end Split

end CFSG.ComponentClassification.OddClassSelector
