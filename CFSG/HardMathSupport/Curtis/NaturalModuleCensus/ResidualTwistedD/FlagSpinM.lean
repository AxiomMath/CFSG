module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.FlagSpin
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega.Range
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

section

variable (n : ℕ) {K : Type} [Field K] (b c : K) (m : ℕ)

@[expose] noncomputable def eSpanM : Submodule K (Vm n K) :=
  Submodule.span K {v | ∃ j : Fin (n - 1), j.val < m ∧ v = eVec n j}

variable {n b c m}

theorem mem_eSpanM_iff (v : Vm n K) :
    v ∈ eSpanM n (K := K) m ↔ ∀ a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2,
      (∀ k : Fin (n - 1), k.val < m → a ≠ .inl k) → v a = 0 := by
  constructor
  · intro hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨j, hj, rfl⟩ a ha
      simp only [eVec, Pi.single_apply]
      exact ite_eq_right_iff.mpr (fun h => absurd h (ha j hj))
    · intro a _; rfl
    · intro x y _ _ hx hy a ha
      simp [hx a ha, hy a ha]
    · intro r x _ hx a ha
      simp [hx a ha]
  · intro h
    have hv : v = ∑ j : Fin (n - 1), (if j.val < m then v (.inl j) else 0) • eVec n (K := K) j := by
      funext a
      rw [Finset.sum_apply]
      rcases a with k | k | t
      · by_cases hk : k.val < m
        · simp [eVec, Pi.single_apply, hk]
        · have h0 := h (.inl k) (fun j hj hjk => hk (by cases hjk; exact hj))
          simp [eVec, Pi.single_apply, hk, h0]
      · simp [eVec, h (.inr (.inl k)) (fun j _ => by simp)]
      · simp [eVec, h (.inr (.inr t)) (fun j _ => by simp)]
    rw [hv]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j.val < m
    · simp only [hj, ↓reduceIte]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · simp only [hj, ↓reduceIte, zero_smul]
      exact Submodule.zero_mem _

theorem finrank_eSpanM {n m : ℕ} (hm : m ≤ n - 1) :
    Module.finrank K (eSpanM n (K := K) m) = m := by
  have hb := (Pi.basisFun K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).linearIndependent
  have hli : LinearIndependent K (fun j : Fin (n - 1) =>
      (Pi.basisFun K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) (Sum.inl j)) :=
    hb.comp _ Sum.inl_injective
  have hli' : LinearIndependent K (eVec n (K := K)) := by
    convert hli using 2
    simp [eVec, Pi.basisFun_apply]
  have hli'' : LinearIndependent K (fun j : {j : Fin (n - 1) // j.val < m} => eVec n (K := K) j.1) :=
    hli'.comp Subtype.val Subtype.val_injective
  have hset : {v | ∃ j : Fin (n - 1), j.val < m ∧ v = eVec n (K := K) j} =
      Set.range (fun j : {j : Fin (n - 1) // j.val < m} => eVec n (K := K) j.1) := by
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨j, hj, rfl⟩
  rw [eSpanM, hset, finrank_span_eq_card hli'', Fintype.card_subtype]
  have : (Finset.univ.filter fun j : Fin (n - 1) => j.val < m) =
      (Finset.range m).attachFin (fun a ha => lt_of_lt_of_le (Finset.mem_range.1 ha) hm) := by
    ext j
    simp
  rw [this, Finset.card_attachFin, Finset.card_range]

@[expose] noncomputable def stabEM (m : ℕ) : Subgroup (spinGroup (quadMinus n K b c)) where
  carrier := {g | ∀ v ∈ eSpanM n (K := K) m,
    spinAction (quadMinus n K b c) g v ∈ eSpanM n (K := K) m}
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
    let f : eSpanM n (K := K) m →ₗ[K] eSpanM n (K := K) m :=
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

theorem mem_stabEM_of_mat {g : spinGroup (quadMinus n K b c)}
    (h : ∀ (j : Fin (n - 1)) (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2), j.val < m →
      (∀ k : Fin (n - 1), k.val < m → a ≠ .inl k) → mat n g a (.inl j) = 0) :
    g ∈ stabEM (n := n) (b := b) (c := c) m := by
  intro v hv
  rw [mem_eSpanM_iff] at hv ⊢
  intro a ha
  rw [← spinMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun e _ => ?_
  rcases e with j | j | t
  · by_cases hj : j.val < m
    · have := h j a hj ha
      rw [mat] at this
      rw [this, zero_mul]
    · rw [hv (.inl j) (fun k hk hjk => hj (by cases hjk; exact hk)), mul_zero]
  · rw [hv (.inr (.inl j)) (fun k _ => by simp), mul_zero]
  · rw [hv (.inr (.inr t)) (fun k _ => by simp), mul_zero]

theorem mem_stabEM_of_eVec {g : spinGroup (quadMinus n K b c)}
    (h : ∀ j : Fin (n - 1), j.val < m →
      spinAction (quadMinus n K b c) g (eVec n j) ∈ eSpanM n (K := K) m) :
    g ∈ stabEM (n := n) (b := b) (c := c) m := by
  have : eSpanM n (K := K) m ≤ (eSpanM n (K := K) m).comap
      (spinAction (quadMinus n K b c) g).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, hj, rfl⟩
    exact h j hj
  exact fun v hv => this hv

theorem longRoot_mem_stabEM {i j : Fin (n - 1)} (hij : i ≠ j) {s t : Bool}
    (h1 : t = false → j.val < m → (s = true ∧ i.val < m))
    (h2 : s = false → i.val < m → (t = true ∧ j.val < m)) (y : K) :
    (minusFrame n b c).longRoot hij s t (.ofAdd y) ∈ stabEM (n := n) (b := b) (c := c) m := by
  refine mem_stabEM_of_mat fun l a hl ha => ?_
  rw [mat_longRoot_apply]
  have hae : a ≠ .inl l := ha l hl
  have k2 : ¬ (minusPos n j (!t) = .inl l ∧ a = minusPos n i s) := by
    rintro ⟨e1, e2⟩
    cases t
    · have hjl : j = l := by
        simpa [minusPos] using e1
      subst hjl
      obtain ⟨hs, hi⟩ := h1 rfl hl
      subst hs
      exact ha i hi (by simpa [minusPos] using e2)
    · simp [minusPos] at e1
  have k3 : ¬ (minusPos n i (!s) = .inl l ∧ a = minusPos n j t) := by
    rintro ⟨e1, e2⟩
    cases s
    · have hil : i = l := by
        simpa [minusPos] using e1
      subst hil
      obtain ⟨ht, hj⟩ := h2 rfl hl
      subst ht
      exact ha j hj (by simpa [minusPos] using e2)
    · simp [minusPos] at e1
  have hae' : (if a = Sum.inl l then (1 : K) else 0) = 0 := ite_eq_right_iff.mpr (fun h => absurd h hae)
  have e2' : (if minusPos n j (!t) = .inl l then (1 : K) else 0) *
      (if a = minusPos n i s then 1 else 0) = 0 := by
    by_cases p : minusPos n j (!t) = .inl l
    · have : ¬ a = minusPos n i s := fun q => k2 ⟨p, q⟩
      simp [this]
    · simp [p]
  have e3' : (if minusPos n i (!s) = .inl l then (1 : K) else 0) *
      (if a = minusPos n j t then 1 else 0) = 0 := by
    by_cases p : minusPos n i (!s) = .inl l
    · have : ¬ a = minusPos n j t := fun q => k3 ⟨p, q⟩
      simp [this]
    · simp [p]
  rw [e2', e3', hae']
  simp

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem twShortRoot_mem_stabEM (i : Fin (n - 1)) (s : Bool) (hs : s = true ∨ m ≤ i.val)
    (p : Fin 2 → K) :
    twShortRoot n hirr i s (.ofAdd p) ∈ stabEM (n := n) (b := b) (c := c) m := by
  refine mem_stabEM_of_mat fun l a hl ha => ?_
  rw [mat_twShortRoot_apply]
  have hae : a ≠ .inl l := ha l hl
  have hne : ¬ minusPos n i (!s) = .inl l := by
    intro e1
    cases s
    · have hil : i = l := by simpa [minusPos] using e1
      subst hil
      rcases hs with hs | hs
      · exact absurd hs (by simp)
      · omega
    · simp [minusPos] at e1
  have hpol : polar (quadMinus n K b c) (Pi.single (.inl l) 1) (planeVec n p) = 0 :=
    polar_single_planeVec_of_ne n (fun t => by simp) p
  simp [hne, hae, hpol]

theorem minusRootGroup_le_stabEM {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (hpos : 0 < ht γ) :
    minusRootGroup n hirr γ ≤ stabEM (n := n) (b := b) (c := c) m := by
  intro x hx
  have hh := epsHt_toStdB n γ
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · obtain ⟨y, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
    rw [hγ', map_add, epsHt_single, epsHt_single] at hh
    have hi := epsHt_pos (n := n) i
    have hj := epsHt_pos (n := n) j
    refine longRoot_mem_stabEM hij ?_ ?_ y
    · intro ht' hjm
      subst ht'
      cases s
      · simp only [boolSign_false] at hh
        omega
      · simp only [boolSign_true, boolSign_false] at hh
        exact ⟨rfl, by omega⟩
    · intro hs' him
      subst hs'
      cases t
      · simp only [boolSign_false] at hh
        omega
      · simp only [boolSign_true, boolSign_false] at hh
        exact ⟨rfl, by omega⟩
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
    cases s
    · rw [hγ', epsHt_single] at hh
      have := epsHt_pos (n := n) i
      simp only [boolSign_false] at hh
      omega
    · exact twShortRoot_mem_stabEM hirr i true (Or.inl rfl) p

theorem rankOne_le_stabEM_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) (hkm : k.val + 1 ≠ m) :
    CFSG.LieType.CurtisTits.rankOne (minusRootGroup n hirr) k ≤
      stabEM (n := n) (b := b) (c := c) m := by
  rw [CFSG.LieType.CurtisTits.rankOne, minusRootGroup_single_of_lt n hirr hk,
    minusRootGroup_neg_single_of_lt n hirr hk]
  refine sup_le ?_ ?_
  · rintro _ ⟨a, rfl⟩
    refine longRoot_mem_stabEM (succ_ne_of_lt n hk) (s := true) (t := false) ?_ (by simp) _
    intro _ hj
    exact ⟨rfl, by simp at hj ⊢; omega⟩
  · rintro _ ⟨a, rfl⟩
    refine longRoot_mem_stabEM (succ_ne_of_lt n hk).symm (s := true) (t := false) ?_ (by simp) _
    intro _ hj
    exact ⟨rfl, by simp at hj ⊢; omega⟩

theorem rankOne_le_stabEM_short {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) (hm : m ≤ k.val) :
    CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup k ≤
      stabEM (n := n) (b := b) (c := c) m := by
  refine sup_le ?_ ?_
  · intro x hx
    obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr k true
      (toStdB_single_of_not_lt' n hk)).mp hx
    exact twShortRoot_mem_stabEM hirr k true (Or.inl rfl) p
  · intro x hx
    obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr k false
      (toStdB_neg_single_of_not_lt' n hk)).mp hx
    exact twShortRoot_mem_stabEM hirr k false (Or.inr hm) p

theorem shortTorus_le_stabEM (i : Fin (n - 1)) :
    shortTorus n hirr i ≤ stabEM (n := n) (b := b) (c := c) m := by
  rw [shortTorus, Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  refine mem_stabEM_of_eVec fun j hj => ?_
  by_cases hji : j = i
  · subst hji
    rw [spinAction_shortTorusElt_eVec n hirr j ha]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [spinAction_shortTorusElt_eVec_of_ne n hirr hji]
    exact Submodule.subset_span ⟨j, hj, rfl⟩

theorem longTorus_le_stabEM {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    ((minusFrame n b c).longTorus hij s t).range ≤ stabEM (n := n) (b := b) (c := c) m := by
  rintro _ ⟨τ, rfl⟩
  refine mem_stabEM_of_eVec fun l hl => ?_
  have := (minusFrame n b c).spinAction_longTorus_vec hij s t τ l true
  simp only [minusFrame_vec, minusVec_true] at this
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hl, rfl⟩)

theorem minusTorus_le_stabEM (i : Fin (n - 1)) :
    minusTorus n hirr i ≤ stabEM (n := n) (b := b) (c := c) m := by
  by_cases hk : i.val + 1 < n - 1
  · rw [minusTorus_of_lt n hirr hk]
    exact longTorus_le_stabEM _ _ _
  · rw [minusTorus_of_not_lt n hirr hk]
    exact shortTorus_le_stabEM hirr i

theorem borel_le_stabEM :
    borel (minusDatum n hirr) (minusTorus n hirr) ≤ stabEM (n := n) (b := b) (c := c) m := by
  refine sup_le (iSup_le fun i => minusTorus_le_stabEM hirr i) ?_
  exact iSup₂_le fun γ hγ => minusRootGroup_le_stabEM hirr hγ.1 hγ.2

end

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
