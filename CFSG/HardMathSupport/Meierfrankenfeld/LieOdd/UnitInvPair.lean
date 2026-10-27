module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitSemilinear
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitComplete
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionPaired
public import CFSG.LinearAlgebra.LinearGroups.UnitaryTransitivity
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.QuadIsotropic

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {p f : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  (h : UnitaryFieldData p f K) (G : Matrix ι ι K)

@[expose] def UnitPairData (τ : (ι → K) → (ι → K)) (v u : ι → K) : Prop :=
  v ≠ 0 ∧ hf h G v v = 0 ∧ hf h G v u = 0 ∧ (∀ k : K, u ≠ k • v) ∧
    ∃ lam mu : K, τ v = lam • v ∧ τ u = mu • u ∧ h.bar lam * mu = -1 ∧
      (lam * h.bar lam = 1 ∨ hf h G u u = 0)

open CFSG.LinearGroups in
theorem exists_isotropic_of_two_le' (hG : (G.map h.bar)ᵀ = G) {E : Submodule K (ι → K)}
    (hE : 2 ≤ Module.finrank K E) :
    ∃ w ∈ E, w ≠ 0 ∧ hf h G w w = 0 := by
  have := h.finite
  set b := Module.finBasis K E with hb
  set i0 : Fin (Module.finrank K E) := ⟨0, by omega⟩
  set i1 : Fin (Module.finrank K E) := ⟨1, by omega⟩
  set v : Fin 2 → (ι → K) := ![(b i0 : ι → K), (b i1 : ι → K)] with hv
  have hli : LinearIndependent K v := by
    have hinj : Function.Injective ![i0, i1] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [i0, i1, Fin.ext_iff]
    have h1 := (b.linearIndependent.comp _ hinj).map' E.subtype (Submodule.ker_subtype E)
    convert h1 using 1
    funext j
    fin_cases j <;> rfl
  set S : Submodule K (ι → K) := Submodule.span K (Set.range v) with hS
  have hSE : S ≤ E := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact (b i0).2
    · exact (b i1).2
  have hS2 : Module.finrank K S = 2 := by
    rw [hS, finrank_span_eq_card hli, Fintype.card_fin]
  set B : S →ₛₗ[h.bar] S →ₗ[K] K := ((gramForm h G).comp S.subtype).compl₂ S.subtype
    with hBdef
  have hBsymm : B.IsSymm := ⟨fun x y => (gramForm_isSymm h hG).eq x y⟩
  by_cases hsep : B.SeparatingLeft
  · obtain ⟨a, ha0, ha⟩ := exists_isotropic_of_finrank_two h hBsymm hsep hS2
    exact ⟨a, hSE a.2, fun h0 => ha0 (Subtype.ext h0), ha⟩
  · simp only [LinearMap.SeparatingLeft, not_forall] at hsep
    obtain ⟨x, hx, hx0⟩ := hsep
    exact ⟨x, hSE x.2, fun h0 => hx0 (Subtype.ext h0), hx x⟩

section IdCase

variable (A : Matrix ι ι K) (l : K)

@[expose] def eig (c : K) : Submodule K (ι → K) where
  carrier := {x | A *ᵥ x = c • x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Matrix.mulVec_add, hx, hy, smul_add]
  zero_mem' := by simp
  smul_mem' a x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Matrix.mulVec_smul, hx, smul_comm]

theorem mem_eig {A : Matrix ι ι K} {c : K} {x : ι → K} : x ∈ eig A c ↔ A *ᵥ x = c • x :=
  Iff.rfl

variable (hl0 : l ≠ 0) (hAA : ∀ x, A *ᵥ (A *ᵥ x) = (l ^ 2) • x) (h2 : (2 : K) ≠ 0)

include hl0 hAA h2

theorem eig_isCompl : IsCompl (eig A l) (eig A (-l)) := by
  refine ⟨Submodule.disjoint_def.mpr fun x hx hx' => ?_,
    Submodule.codisjoint_iff_exists_add_eq.mpr fun x => ?_⟩
  · rw [mem_eig] at hx hx'
    have h1 : l • x = (-l) • x := hx.symm.trans hx'
    have h3 : (2 * l) • x = 0 := by
      have : (2 * l) • x = l • x - (-l) • x := by rw [mul_smul, two_smul]; module
      rw [this, h1, sub_self]
    exact (smul_eq_zero.1 h3).resolve_left (mul_ne_zero h2 hl0)
  · refine ⟨(2⁻¹ : K) • (x + l⁻¹ • (A *ᵥ x)), (2⁻¹ : K) • (x - l⁻¹ • (A *ᵥ x)), ?_, ?_, ?_⟩
    · rw [mem_eig]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, hAA]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · rw [mem_eig]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, hAA]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring

theorem eig_finrank (hcard : Fintype.card ι = 4) :
    Module.finrank K (eig A l) + Module.finrank K (eig A (-l)) = 4 := by
  have := Submodule.finrank_add_eq_of_isCompl (eig_isCompl A l hl0 hAA h2)
  rw [Module.finrank_fintype_fun_eq_card, hcard] at this
  exact this

theorem eig_ne_bot (hns : ∀ c : K, ∃ x, A *ᵥ x ≠ c • x) : eig A l ≠ ⊥ ∧ eig A (-l) ≠ ⊥ := by
  have hc := Submodule.codisjoint_iff_exists_add_eq.mp (eig_isCompl A l hl0 hAA h2).codisjoint
  constructor
  · intro hb
    obtain ⟨x, hx⟩ := hns (-l)
    obtain ⟨y₁, y₂, hy₁, hy₂, h12⟩ := hc x
    rw [hb, Submodule.mem_bot] at hy₁
    subst hy₁
    rw [zero_add] at h12
    subst h12
    exact hx hy₂
  · intro hb
    obtain ⟨x, hx⟩ := hns l
    obtain ⟨y₁, y₂, hy₁, hy₂, h12⟩ := hc x
    rw [hb, Submodule.mem_bot] at hy₂
    subst hy₂
    rw [add_zero] at h12
    subst h12
    exact hx hy₁

omit hl0 hAA in
theorem hf_eq_zero_of_eig (hA : ∀ x y, hf h G (A *ᵥ x) (A *ᵥ y) = hf h G x y) {c d : K}
    (hcd : h.bar c * d = -1) {x y : ι → K} (hx : x ∈ eig A c) (hy : y ∈ eig A d) :
    hf h G x y = 0 := by
  have h1 := hA x y
  rw [mem_eig.1 hx, mem_eig.1 hy, hf_smul_left, hf_smul_right] at h1
  have h3 : (2 : K) * hf h G x y = 0 := by
    linear_combination -h1 + hf h G x y * hcd
  exact (mul_eq_zero.1 h3).resolve_left h2

theorem pair_refl_one_of_dim (hG : (G.map h.bar)ᵀ = G)
    (hA : ∀ x y, hf h G (A *ᵥ x) (A *ᵥ y) = hf h G x y) (hN1 : h.bar l * l = 1)
    (hns : ∀ c : K, ∃ x, A *ᵥ x ≠ c • x) (hd : 2 ≤ Module.finrank K (eig A l)) :
    ∃ v u, UnitPairData h G (fun x => A *ᵥ x) v u := by
  obtain ⟨v, hvE, hv0, hvv⟩ := exists_isotropic_of_two_le' h G hG hd
  obtain ⟨u, huE, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (eig_ne_bot A l hl0 hAA h2 hns).2
  have hlk : h.bar l * (-l) = -1 := by linear_combination -hN1
  have hvu : hf h G v u = 0 := hf_eq_zero_of_eig h G A h2 hA hlk hvE huE
  refine ⟨v, u, hv0, hvv, hvu, ?_, l, -l, mem_eig.1 hvE, mem_eig.1 huE, hlk, Or.inl ?_⟩
  · intro k hk
    have e1 : A *ᵥ u = (k * l) • v := by
      rw [hk, Matrix.mulVec_smul, mem_eig.1 hvE, smul_smul]
    have e2 : A *ᵥ u = (-l * k) • v := by
      rw [mem_eig.1 huE, hk, smul_smul]
    have e3 : (2 * l * k) • v = 0 := by
      have e4 := e1.symm.trans e2
      have e5 : (2 * l * k) • v = (k * l) • v - (-l * k) • v := by
        rw [← sub_smul]; congr 1; ring
      rw [e5, e4, sub_self]
    have hk0 : k = 0 := by
      rcases smul_eq_zero.1 e3 with h0 | h0
      · have : 2 * l ≠ 0 := mul_ne_zero h2 hl0
        exact (mul_eq_zero.1 h0).resolve_left this
      · exact absurd h0 hv0
    apply hu0
    rw [hk, hk0, zero_smul]
  · rw [mul_comm]; exact hN1

theorem pair_refl_one (hG : (G.map h.bar)ᵀ = G) (hcard : Fintype.card ι = 4)
    (hA : ∀ x y, hf h G (A *ᵥ x) (A *ᵥ y) = hf h G x y) (hN1 : h.bar l * l = 1)
    (hns : ∀ c : K, ∃ x, A *ᵥ x ≠ c • x) : ∃ v u, UnitPairData h G (fun x => A *ᵥ x) v u := by
  have hsum := eig_finrank A l hl0 hAA h2 hcard
  by_cases hd : 2 ≤ Module.finrank K (eig A l)
  · exact pair_refl_one_of_dim h G A l hl0 hAA h2 hG hA hN1 hns hd
  · have hd' : 2 ≤ Module.finrank K (eig A (-l)) := by omega
    exact pair_refl_one_of_dim h G A (-l) (neg_ne_zero.2 hl0)
      (fun x => by rw [hAA x, neg_sq]) h2 hG hA (by rw [map_neg, neg_mul_neg]; exact hN1) hns hd'

theorem eig_pair_le (hG : (G.map h.bar)ᵀ = G) (hdet : G.det ≠ 0)
    (hA : ∀ x y, hf h G (A *ᵥ x) (A *ᵥ y) = hf h G x y) (hN : h.bar l * l = -1) :
    Module.finrank K (eig A (-l)) ≤ Module.finrank K (eig A l) := by
  have hc := Submodule.codisjoint_iff_exists_add_eq.mp (eig_isCompl A l hl0 hAA h2).codisjoint
  refine finrank_le_of_pairing (h := h) (B := gramForm h G) (W₁ := eig A l) (W₂ := eig A (-l))
    fun w hw h0 => ?_
  refine eq_zero_of_hf_eq_zero h G hdet fun y => ?_
  obtain ⟨y₁, y₂, hy₁, hy₂, h12⟩ := hc y
  have hN' : h.bar (-l) * (-l) = -1 := by rw [map_neg, neg_mul_neg]; exact hN
  rw [← h12, hf_add_right]
  have e1 : hf h G w y₁ = 0 := h0 y₁ hy₁
  have e2 : hf h G w y₂ = 0 := hf_eq_zero_of_eig h G A h2 hA hN' hw hy₂
  rw [e1, e2, add_zero]

theorem pair_refl_neg (hG : (G.map h.bar)ᵀ = G) (hdet : G.det ≠ 0) (hcard : Fintype.card ι = 4)
    (hA : ∀ x y, hf h G (A *ᵥ x) (A *ᵥ y) = hf h G x y) (hN : h.bar l * l = -1)
    (hns : ∀ c : K, ∃ x, A *ᵥ x ≠ c • x) : ∃ v u, UnitPairData h G (fun x => A *ᵥ x) v u := by
  have hsum := eig_finrank A l hl0 hAA h2 hcard
  have hle1 := eig_pair_le h G A l hl0 hAA h2 hG hdet hA hN
  have hle2 := eig_pair_le h G A (-l) (neg_ne_zero.2 hl0) (fun x => by rw [hAA x, neg_sq]) h2 hG
    hdet hA (by rw [map_neg, neg_mul_neg]; exact hN)
  rw [neg_neg] at hle2
  have hd : Module.finrank K (eig A l) = 2 := by omega
  obtain ⟨v, hvE, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (eig_ne_bot A l hl0 hAA h2 hns).1
  have hu : ∃ u ∈ eig A l, u ∉ Submodule.span K {v} := by
    by_contra hcon
    push Not at hcon
    have hle : eig A l ≤ Submodule.span K {v} := fun u hu => hcon u hu
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hv0] at this
    omega
  obtain ⟨u, huE, hu'⟩ := hu
  have hiso : ∀ x ∈ eig A l, ∀ y ∈ eig A l, hf h G x y = 0 := fun x hx y hy =>
    hf_eq_zero_of_eig h G A h2 hA hN hx hy
  refine ⟨v, u, hv0, hiso v hvE v hvE, hiso v hvE u huE, ?_, l, l, mem_eig.1 hvE, mem_eig.1 huE,
    hN, Or.inr (hiso u huE u huE)⟩
  intro k hk
  exact hu' (by rw [hk]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))

end IdCase

section BarCase

variable (σ : K ≃+* K) (hσ : ∀ c, σ c = h.bar c)

@[expose] noncomputable def tauLin (A : Matrix ι ι K) (a : K) : (ι → K) →ₛₗ[h.bar] (ι → K) where
  toFun x := a • tau σ A x
  map_add' x y := by rw [tau_add, smul_add]
  map_smul' c x := by rw [tau_smul, hσ, smul_comm]

theorem tauLin_apply (A : Matrix ι ι K) (a : K) (x : ι → K) :
    tauLin h σ hσ A a x = a • tau σ A x := rfl

theorem exists_perp_of_conjFixed (hdet : G.det ≠ 0) (hcard : Fintype.card ι = 4)
    {τ' : (ι → K) →ₛₗ[h.bar] (ι → K)} (hττ : ∀ v, τ' (τ' v) = v) {t : K} (ht : h.bar t = -t)
    (ht0 : t ≠ 0) (h2 : (2 : K) ≠ 0) {ε : K} (hε0 : ε ≠ 0)
    (hval : ∀ x ∈ conjFixed h τ', ∀ y ∈ conjFixed h τ', h.bar (hf h G x y) = ε * hf h G x y)
    {v : ι → K} (hvW : v ∈ conjFixed h τ') (hv0 : v ≠ 0) :
    ∃ w ∈ conjFixed h τ', hf h G v w = 0 ∧ ∀ κ : K, w ≠ κ • v := by
  have hspan := span_conjFixed hττ ht ht0 h2
  have hfin : Module.finrank K (ι → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  obtain ⟨w₀, hw₀W, hw₀⟩ : ∃ w₀ ∈ conjFixed h τ', hf h G v w₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ z ∈ Submodule.span K (conjFixed h τ' : Set (ι → K)), hf h G v z = 0 := by
      intro z hz
      refine Submodule.span_induction (p := fun z _ => hf h G v z = 0) (fun x hx => hcon x hx)
        (hf_zero_right h G v) (fun x y _ _ hx hy => by rw [hf_add_right, hx, hy, add_zero])
        (fun a x _ hx => by rw [hf_smul_right, hx, mul_zero]) hz
    rw [hspan] at hall
    exact hv0 (eq_zero_of_hf_eq_zero h G hdet fun z => hall z trivial)
  by_contra hcon
  push Not at hcon
  have hsub : Submodule.span K (conjFixed h τ' : Set (ι → K)) ≤ Submodule.span K {w₀, v} := by
    rw [Submodule.span_le]
    intro w hw
    have hbw := hval v hvW w hw
    have hbw₀ := hval v hvW w₀ hw₀W
    obtain ⟨r, hr⟩ : ∃ r : K, r = hf h G v w / hf h G v w₀ := ⟨_, rfl⟩
    have hbr : h.bar r = r := by
      rw [hr, map_div₀, hbw, hbw₀]
      field_simp
    have hrk : r ∈ h.fixedField := h.mem_fixedField.2 hbr
    have hw' : w - r • w₀ ∈ conjFixed h τ' := by
      have : r • w₀ = (⟨r, hrk⟩ : h.fixedField) • w₀ := rfl
      rw [this]
      exact sub_mem hw (Submodule.smul_mem _ _ hw₀W)
    have hperp : hf h G v (w - r • w₀) = 0 := by
      rw [hf_sub_right, hf_smul_right, hr]
      field_simp
      ring
    obtain ⟨κ, hκ⟩ := hcon _ hw' hperp
    have : w = r • w₀ + κ • v := by rw [← hκ]; abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  rw [hspan] at hsub
  have h4 := Submodule.finrank_mono hsub
  rw [finrank_top, hfin] at h4
  classical
  have h5 := finrank_span_finset_le_card (R := K) ({w₀, v} : Finset (ι → K))
  have e : (({w₀, v} : Finset (ι → K)) : Set (ι → K)) = {w₀, v} := by ext x; simp
  rw [e] at h5
  have h6 : Module.finrank K (Submodule.span K ({w₀, v} : Set (ι → K))) ≤ 2 :=
    h5.trans (Finset.card_le_two (a := w₀) (b := v))
  omega

theorem exists_isotropic_conjFixed (hcard : Fintype.card ι = 4)
    {τ' : (ι → K) →ₛₗ[h.bar] (ι → K)} (hττ : ∀ v, τ' (τ' v) = v) {t : K} (ht : h.bar t = -t)
    (ht0 : t ≠ 0) (h2 : (2 : K) ≠ 0)
    (hval : ∀ x ∈ conjFixed h τ', ∀ y ∈ conjFixed h τ', h.bar (hf h G x y) = hf h G x y) :
    ∃ v ∈ conjFixed h τ', v ≠ 0 ∧ hf h G v v = 0 := by
  classical
  have := h.finite
  haveI : Fintype h.fixedField := Fintype.ofFinite _
  have hfin : Module.finrank K (ι → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  have hW4 : Module.finrank h.fixedField (conjFixed h τ') = 4 := by
    rw [finrank_conjFixed hττ ht ht0 h2, hfin]
  set b := Module.finBasis h.fixedField (conjFixed h τ') with hb
  set n := Module.finrank h.fixedField (conjFixed h τ') with hn
  have hmem : ∀ i j : Fin n, h.bar (hf h G (b i : ι → K) (b j : ι → K)) =
      hf h G (b i : ι → K) (b j : ι → K) := fun i j => hval _ (b i).2 _ (b j).2
  let M : Matrix (Fin n) (Fin n) h.fixedField := fun i j =>
    ⟨hf h G (b i : ι → K) (b j : ι → K), h.mem_fixedField.2 (hmem i j)⟩
  obtain ⟨v, hv0, hv⟩ := exists_isotropic_of_three_le (K := h.fixedField)
    (by rw [Fintype.card_fin]; omega) M
  have hbarv : ∀ i, h.bar ((v i : h.fixedField) : K) = (v i : K) := fun i =>
    h.mem_fixedField.1 (v i).2
  obtain ⟨wW, hwW⟩ : ∃ wW : conjFixed h τ', wW = ∑ i, v i • b i := ⟨_, rfl⟩
  have hwcoe : (wW : ι → K) = ∑ i, ((v i : h.fixedField) : K) • (b i : ι → K) := by
    rw [hwW]
    simp [Submodule.coe_sum, Submodule.coe_smul, Subfield.smul_def]
  refine ⟨wW, wW.2, ?_, ?_⟩
  · intro h0
    have h1 : wW = 0 := Subtype.ext h0
    rw [hwW] at h1
    have h3 := Fintype.linearIndependent_iff.1 b.linearIndependent v h1
    exact hv0 (funext h3)
  · have e : hf h G (wW : ι → K) (wW : ι → K) = ((v ⬝ᵥ (M *ᵥ v) : h.fixedField) : K) := by
      rw [hwcoe]
      simp only [hf, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, hbarv, dotProduct, Matrix.mulVec, M]
      push_cast
      simp only [id, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e, hv]
    rfl

include hσ in
theorem pair_bar (h2 : (2 : K) ≠ 0) (hG : (G.map h.bar)ᵀ = G) (hGb : G.map h.bar = G)
    (hdet : G.det ≠ 0) (hcard : Fintype.card ι = 4) (A : Matrix ι ι K)
    (hA : (A.map h.bar)ᵀ * G * A = G)
    (c : K) (hc : A * A.map h.bar = c • 1) (hc1 : c = 1 ∨ c = -1) :
    ∃ v u, UnitPairData h G (tau σ A) v u := by
  have hσb : ∀ c, σ (h.bar c) = h.bar (σ c) := fun c => by rw [hσ, hσ]
  have hσ2 : ∀ c, σ (σ c) = c := fun c => by rw [hσ, hσ, h.bar_bar]
  have hGσ : G.map σ = G := by
    have : G.map σ = G.map h.bar := by ext i j; simp [hσ]
    rw [this, hGb]
  have hAσ : A.map σ = A.map h.bar := by ext i j; simp [hσ]
  have hττ_c : ∀ x, tau σ A (tau σ A x) = c • x := by
    intro x
    rw [tau_tau σ A hσ2 A x, hAσ, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hiso : ∀ x y, hf h G (tau σ A x) (tau σ A y) = h.bar (hf h G x y) := by
    intro x y
    rw [tau_hf h G σ A hσb hGσ hA x y, hσ]
  obtain ⟨t, ht, ht0⟩ := h.exists_mem_traceZero_ne_zero
  rw [UnitaryFieldData.mem_traceZero] at ht
  have ht' : h.bar t = -t := by
    have : t + h.bar t = 0 := ht
    linear_combination this
  have hfin : Module.finrank K (ι → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  rcases hc1 with rfl | rfl
  ·
    obtain ⟨τ', hτ'⟩ : ∃ τ' : (ι → K) →ₛₗ[h.bar] (ι → K), τ' = tauLin h σ hσ A 1 := ⟨_, rfl⟩
    have hτ'app : ∀ x, τ' x = tau σ A x := fun x => by rw [hτ', tauLin_apply, one_smul]
    have hττ : ∀ v, τ' (τ' v) = v := fun v => by
      rw [hτ'app, hτ'app, hττ_c, one_smul]
    have memW : ∀ x, x ∈ conjFixed h τ' ↔ tau σ A x = x := fun x => by
      rw [mem_conjFixed, hτ'app]
    have hval : ∀ x ∈ conjFixed h τ', ∀ y ∈ conjFixed h τ',
        h.bar (hf h G x y) = 1 * hf h G x y := by
      intro x hx y hy
      have := hiso x y
      rw [(memW x).1 hx, (memW y).1 hy] at this
      rw [one_mul]; exact this.symm
    obtain ⟨v, hvW, hv0, hvv⟩ := exists_isotropic_conjFixed h G hcard hττ ht' ht0 h2
      (fun x hx y hy => by simpa using hval x hx y hy)
    obtain ⟨w, hwW, hvw, hwκ⟩ := exists_perp_of_conjFixed h G hdet hcard hττ ht' ht0 h2
      (ε := 1) one_ne_zero hval hvW hv0
    refine ⟨v, t • w, hv0, hvv, ?_, ?_, 1, -1, ?_, ?_, ?_, Or.inl ?_⟩
    · rw [hf_smul_right, hvw, mul_zero]
    · intro k hk
      apply hwκ (t⁻¹ * k)
      rw [← smul_smul, ← hk, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    · rw [(memW v).1 hvW, one_smul]
    · rw [tau_smul, hσ, (memW w).1 hwW, ht']
      module
    · simp
    · simp
  · obtain ⟨γ, hγ⟩ := h.normHom_surjective ⟨-1, h.mem_fixedField.2 (by rw [map_neg, map_one])⟩
    have hγn : γ * h.bar γ = -1 := by
      have := congrArg Subtype.val hγ
      simpa [UnitaryFieldData.norm] using this
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      simp at hγn
    have hbγ : h.bar γ * γ = -1 := by rw [mul_comm]; exact hγn
    have hinv : γ⁻¹ * h.bar γ⁻¹ = -1 := by
      rw [map_inv₀, ← mul_inv, hγn, inv_neg, inv_one]
    obtain ⟨τ', hτ'⟩ : ∃ τ' : (ι → K) →ₛₗ[h.bar] (ι → K), τ' = tauLin h σ hσ A γ⁻¹ := ⟨_, rfl⟩
    have hτ'app : ∀ x, τ' x = γ⁻¹ • tau σ A x := fun x => by rw [hτ', tauLin_apply]
    have hττ : ∀ v, τ' (τ' v) = v := fun v => by
      rw [hτ'app, hτ'app, tau_smul, hσ, hττ_c, smul_smul, smul_smul]
      have e : γ⁻¹ * h.bar γ⁻¹ * -1 = 1 := by
        rw [hinv]; norm_num
      rw [e, one_smul]
    have memW : ∀ x, x ∈ conjFixed h τ' ↔ tau σ A x = γ • x := fun x => by
      rw [mem_conjFixed, hτ'app]
      constructor
      · intro hx
        calc tau σ A x = γ • γ⁻¹ • tau σ A x := (smul_inv_smul₀ hγ0 _).symm
          _ = γ • x := by rw [hx]
      · intro hx
        rw [hx, inv_smul_smul₀ hγ0]
    have hval : ∀ x ∈ conjFixed h τ', ∀ y ∈ conjFixed h τ',
        h.bar (hf h G x y) = -1 * hf h G x y := by
      intro x hx y hy
      have := hiso x y
      rw [(memW x).1 hx, (memW y).1 hy, hf_smul_left, hf_smul_right] at this
      rw [← this]
      linear_combination (hf h G x y) * hbγ
    have hisoW : ∀ x ∈ conjFixed h τ', hf h G x x = 0 := by
      intro x hx
      have h1 := hval x hx x hx
      rw [hf_self_bar h G hG x] at h1
      have h3 : (2 : K) * hf h G x x = 0 := by linear_combination h1
      exact (mul_eq_zero.1 h3).resolve_left h2
    have hW4 : Module.finrank h.fixedField (conjFixed h τ') = 4 := by
      rw [finrank_conjFixed hττ ht' ht0 h2, hfin]
    have hne : conjFixed h τ' ≠ ⊥ := by
      intro hb
      rw [hb] at hW4
      simp at hW4
    obtain ⟨x₀, hx₀W, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨w, hwW, hvw, hwκ⟩ := exists_perp_of_conjFixed h G hdet hcard hττ ht' ht0 h2
      (ε := -1) (neg_ne_zero.2 one_ne_zero) hval hx₀W hv0
    refine ⟨x₀, w, hv0, hisoW _ hx₀W, hvw, hwκ, γ, γ, (memW _).1 hx₀W, (memW w).1 hwW,
      hbγ, Or.inr (hisoW w hwW)⟩

include hσ in
theorem bar_scalar_pm_one (hG : (G.map h.bar)ᵀ = G) (hGb : G.map h.bar = G) (hdet : G.det ≠ 0)
    (hcard : Fintype.card ι = 4) (A B : Matrix ι ι K) (hAB : A * B = 1)
    (hA : (A.map h.bar)ᵀ * G * A = G) (c : K) (hc : A * A.map h.bar = c • 1) :
    c = 1 ∨ c = -1 := by
  have hσb : ∀ c, σ (h.bar c) = h.bar (σ c) := fun c => by rw [hσ, hσ]
  have hσ2 : ∀ c, σ (σ c) = c := fun c => by rw [hσ, hσ, h.bar_bar]
  have hGσ : G.map σ = G := by
    have : G.map σ = G.map h.bar := by ext i j; simp [hσ]
    rw [this, hGb]
  have hAσ : A.map σ = A.map h.bar := by ext i j; simp [hσ]
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hbc : h.bar c = c := by
    have h1 := congrArg (fun M : Matrix ι ι K => M.map h.bar) hc
    simp only [Matrix.map_mul, Matrix.map_map] at h1
    have e : (h.bar ∘ h.bar : K → K) = id := funext h.bar_bar
    rw [e, Matrix.map_id] at h1
    have h2' : (h.bar c) • (1 : Matrix ι ι K) = A.map h.bar * A := by
      rw [h1]; ext i j; simp [Matrix.smul_apply, Matrix.one_apply]; split_ifs <;> simp
    have h3 : (h.bar c) • A = c • A := by
      calc (h.bar c) • A = A * ((h.bar c) • (1 : Matrix ι ι K)) := by simp
        _ = A * (A.map h.bar * A) := by rw [h2']
        _ = (A * A.map h.bar) * A := by rw [Matrix.mul_assoc]
        _ = c • A := by rw [hc]; simp
    have h4 : (h.bar c) • (1 : Matrix ι ι K) = c • 1 := by
      calc (h.bar c) • (1 : Matrix ι ι K) = ((h.bar c) • A) * B := by
            rw [Matrix.smul_mul, hAB]
        _ = (c • A) * B := by rw [h3]
        _ = c • 1 := by rw [Matrix.smul_mul, hAB]
    obtain ⟨i⟩ := hne
    have := congrFun (congrFun h4 i) i
    simpa using this
  obtain ⟨x, hx⟩ : ∃ x : ι → K, x ≠ 0 := by
    obtain ⟨i⟩ := hne
    exact ⟨Pi.single i 1, fun h0 => by simpa using congrFun h0 i⟩
  obtain ⟨y, hy⟩ := exists_hf_ne_zero h G hdet hx
  have hττ_c : ∀ x, tau σ A (tau σ A x) = c • x := by
    intro x
    rw [tau_tau σ A hσ2 A x, hAσ, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hiso : ∀ x y, hf h G (tau σ A x) (tau σ A y) = h.bar (hf h G x y) := by
    intro x y
    rw [tau_hf h G σ A hσb hGσ hA x y, hσ]
  have h5 := hiso (tau σ A x) (tau σ A y)
  rw [hiso x y, h.bar_bar, hττ_c, hττ_c, hf_smul_left, hf_smul_right, hbc] at h5
  have h6 : (c * c - 1) * hf h G x y = 0 := by linear_combination h5
  have h7 : c * c = 1 := by
    have := (mul_eq_zero.1 h6).resolve_right hy
    linear_combination this
  have h8 : (c - 1) * (c + 1) = 0 := by linear_combination h7
  rcases mul_eq_zero.1 h8 with h9 | h9
  · left; linear_combination h9
  · right; linear_combination h9

end BarCase

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
