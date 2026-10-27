module

public import CFSG.LieType.Universal.Spin.Twisted.Unipotent

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem

section

variable (n : ℕ) {K : Type} [Field K] (b c : K)

@[expose] noncomputable def eSpan : Submodule K (Vm n K) :=
  Submodule.span K (Set.range (eVec n (K := K)))

theorem mem_eSpan_iff (v : Vm n K) :
    v ∈ eSpan n (K := K) ↔ ∀ a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2,
      (∀ k : Fin (n - 1), a ≠ .inl k) → v a = 0 := by
  constructor
  · intro hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨j, rfl⟩ a ha
      simp only [eVec, Pi.single_apply]
      exact ite_eq_right_iff.mpr (fun h => absurd h (ha j))
    · intro a _; rfl
    · intro x y _ _ hx hy a ha
      simp [hx a ha, hy a ha]
    · intro r x _ hx a ha
      simp [hx a ha]
  · intro h
    have hv : v = ∑ j : Fin (n - 1), v (.inl j) • eVec n (K := K) j := by
      funext a
      rcases a with k | k | t
      · simp [eVec, Pi.single_apply]
      · simp [eVec, h (.inr (.inl k)) (fun j => by simp)]
      · simp [eVec, h (.inr (.inr t)) (fun j => by simp)]
    rw [hv]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

variable {n b c}

@[expose] noncomputable def stabE : Subgroup (spinGroup (quadMinus n K b c)) where
  carrier := {g | ∀ v ∈ eSpan n (K := K), spinAction (quadMinus n K b c) g v ∈ eSpan n (K := K)}
  mul_mem' := by
    intro g h hg hh v hv
    rw [map_mul, LinearEquiv.mul_apply]
    exact hg _ (hh v hv)
  one_mem' := by
    intro v hv
    rw [map_one]
    exact hv
  inv_mem' := by
    intro g hg v hv
    let f : eSpan n (K := K) →ₗ[K] eSpan n (K := K) :=
      ((spinAction (quadMinus n K b c) g).toLinearMap).restrict (fun w hw => hg w hw)
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have := congrArg Subtype.val hxy
      exact (spinAction (quadMinus n K b c) g).injective this
    obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨v, hv⟩
    have hw' : spinAction (quadMinus n K b c) g (w : Vm n K) = v := congrArg Subtype.val hw
    have : spinAction (quadMinus n K b c) g⁻¹ v = w := by
      calc spinAction (quadMinus n K b c) g⁻¹ v
          = spinAction (quadMinus n K b c) g⁻¹ (spinAction (quadMinus n K b c) g (w : Vm n K)) := by
            rw [hw']
        _ = (spinAction (quadMinus n K b c) g⁻¹ * spinAction (quadMinus n K b c) g) (w : Vm n K) :=
            (LinearEquiv.mul_apply _ _ _).symm
        _ = w := by rw [← map_mul, inv_mul_cancel, map_one]; rfl
    rw [this]
    exact w.2

theorem mem_stabE_of_mat {g : spinGroup (quadMinus n K b c)}
    (h : ∀ (j : Fin (n - 1)) (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2),
      (∀ k : Fin (n - 1), a ≠ .inl k) → mat n g a (.inl j) = 0) : g ∈ stabE (n := n) (b := b) (c := c) := by
  intro v hv
  rw [mem_eSpan_iff] at hv ⊢
  intro a ha
  rw [← spinMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun e _ => ?_
  rcases e with j | j | t
  · have := h j a ha
    rw [mat] at this
    rw [this, zero_mul]
  · rw [hv (.inr (.inl j)) (fun k => by simp), mul_zero]
  · rw [hv (.inr (.inr t)) (fun k => by simp), mul_zero]

theorem longRoot_mem_stabE {i j : Fin (n - 1)} (hij : i ≠ j) {s t : Bool}
    (hst : ¬(s = false ∧ t = false)) (y : K) :
    (minusFrame n b c).longRoot hij s t (.ofAdd y) ∈ stabE (n := n) (b := b) (c := c) := by
  refine mem_stabE_of_mat fun l a ha => ?_
  rw [mat_longRoot_apply]
  have hae : a ≠ .inl l := ha l
  cases s <;> cases t
  · exact absurd ⟨rfl, rfl⟩ hst
  · simp [minusPos, hae, ha j, eq_comm (a := a)]
  · simp [minusPos, hae, ha i, eq_comm (a := a)]
  · simp [minusPos, hae, ha i, ha j]

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem twShortRoot_true_mem_stabE (i : Fin (n - 1)) (p : Fin 2 → K) :
    twShortRoot n hirr i true (.ofAdd p) ∈ stabE (n := n) (b := b) (c := c) := by
  refine mem_stabE_of_mat fun l a ha => ?_
  rw [mat_twShortRoot_apply]
  have hae : a ≠ .inl l := ha l
  simp [minusPos, hae, ha i]

theorem epsHt_single (i : Fin (n - 1)) (z : ℤ) :
    epsHt n (Pi.single i z) = (((n - 1 : ℕ) : ℤ) - i) * z := by
  simp [epsHt, Pi.single_apply]

theorem epsHt_pos (i : Fin (n - 1)) : 0 < (((n - 1 : ℕ) : ℤ) - i) := by
  have := i.2
  omega

theorem minusRootGroup_le_stabE {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (hpos : 0 < ht γ) :
    minusRootGroup n hirr γ ≤ stabE (n := n) (b := b) (c := c) := by
  intro x hx
  have hh := epsHt_toStdB n γ
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · obtain ⟨y, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
    refine longRoot_mem_stabE hij ?_ y
    rintro ⟨rfl, rfl⟩
    rw [hγ', map_add, epsHt_single, epsHt_single] at hh
    have := epsHt_pos (n := n) i
    have := epsHt_pos (n := n) j
    simp only [boolSign_false] at hh
    omega
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
    cases s
    · rw [hγ', epsHt_single] at hh
      have := epsHt_pos (n := n) i
      simp only [boolSign_false] at hh
      omega
    · exact twShortRoot_true_mem_stabE hirr i p

theorem rankOne_le_stabE_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    CFSG.LieType.CurtisTits.rankOne (minusRootGroup n hirr) k ≤
      stabE (n := n) (b := b) (c := c) := by
  rw [CFSG.LieType.CurtisTits.rankOne, minusRootGroup_single_of_lt n hirr hk,
    minusRootGroup_neg_single_of_lt n hirr hk]
  refine sup_le ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact longRoot_mem_stabE (succ_ne_of_lt n hk) (s := true) (t := false) (by simp) _
  · rintro _ ⟨a, rfl⟩
    exact longRoot_mem_stabE (succ_ne_of_lt n hk).symm (s := true) (t := false) (by simp) _

theorem mem_stabE_of_eVec {g : spinGroup (quadMinus n K b c)}
    (h : ∀ j : Fin (n - 1), spinAction (quadMinus n K b c) g (eVec n j) ∈ eSpan n (K := K)) :
    g ∈ stabE (n := n) (b := b) (c := c) := by
  have : eSpan n (K := K) ≤ (eSpan n (K := K)).comap
      (spinAction (quadMinus n K b c) g).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact h j
  exact fun v hv => this hv

theorem shortTorus_le_stabE (i : Fin (n - 1)) :
    shortTorus n hirr i ≤ stabE (n := n) (b := b) (c := c) := by
  rw [shortTorus, Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  refine mem_stabE_of_eVec fun j => ?_
  by_cases hji : j = i
  · subst hji
    rw [spinAction_shortTorusElt_eVec n hirr j ha]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [spinAction_shortTorusElt_eVec_of_ne n hirr hji]
    exact Submodule.subset_span ⟨j, rfl⟩

end

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
