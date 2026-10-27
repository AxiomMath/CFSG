module

public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.Spin.Twisted.Graded
public import CFSG.LieType.Universal.SpinOmega.Kernel

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Graded

variable (n : ℕ) {K : Type*} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] def minusPos (i : Fin (n - 1)) : Bool → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2
  | true => .inl i
  | false => .inr (.inl i)

@[expose] def minusWt : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → Fin (n - 1) → ℤ
  | .inl i => Pi.single i 1
  | .inr (.inl i) => Pi.single i (-1)
  | .inr (.inr _) => 0

theorem minusWt_minusPos (i : Fin (n - 1)) (s : Bool) :
    minusWt n (minusPos n i s) = Pi.single i (boolSign s) := by
  cases s <;> rfl

theorem minusVec_eq_single (i : Fin (n - 1)) (s : Bool) :
    minusVec n (K := K) i s = Pi.single (minusPos n i s) 1 := by
  cases s <;> rfl

theorem minusPos_inj {i j : Fin (n - 1)} {s t : Bool} :
    minusPos n i s = minusPos n j t ↔ i = j ∧ s = t := by
  cases s <;> cases t <;> simp [minusPos]

theorem minusPos_ne_inr_inr (i : Fin (n - 1)) (s : Bool) (t : Fin 2) :
    minusPos n i s ≠ .inr (.inr t) := by
  cases s <;> simp [minusPos]

theorem polar_minusVec_eq_apply (v : Vm n K) (j : Fin (n - 1)) (t : Bool) :
    polar (quadMinus n K b c) v (minusVec n j t) = v (minusPos n j (!t)) := by
  cases t
  · exact polar_quadMinus_single_inr_inl n K b c v j
  · exact polar_quadMinus_single_inl n K b c v j

theorem polar_single_planeVec_of_ne {a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2}
    (ha : ∀ t, a ≠ .inr (.inr t)) (p : Fin 2 → K) :
    polar (quadMinus n K b c) (Pi.single a 1) (planeVec n p) = 0 := by
  rw [polar_quadMinus]
  rcases a with k | k | t
  · simp [planeVec, Pi.single_apply]
  · simp [planeVec, Pi.single_apply]
  · exact absurd rfl (ha t)

@[expose] noncomputable def mat (g : spinGroup (quadMinus n K b c)) :
    Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K :=
  (spinMatrix (quadMinus n K b c) g : Matrix _ _ K)

theorem mat_apply (g : spinGroup (quadMinus n K b c)) (a e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    mat n g a e = spinAction (quadMinus n K b c) g (Pi.single e 1) a := by
  rw [mat, coe_spinMatrix, LinearMap.toMatrix'_apply]
  rfl

theorem mat_mul (g h : spinGroup (quadMinus n K b c)) : mat n (g * h) = mat n g * mat n h := by
  rw [mat, mat, mat, map_mul, Units.val_mul]

theorem mat_one : mat n (1 : spinGroup (quadMinus n K b c)) = 1 := by
  rw [mat, map_one, Units.val_one]

@[expose] noncomputable def matHom :
    spinGroup (quadMinus n K b c) →* Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K where
  toFun := mat n
  map_one' := mat_one n
  map_mul' := mat_mul n

theorem isUnit_mat (g : spinGroup (quadMinus n K b c)) : IsUnit (mat n g) :=
  (spinMatrix (quadMinus n K b c) g).isUnit

theorem mat_longRoot_apply {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (x : K)
    (a e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    mat n ((minusFrame n b c).longRoot hij s t (.ofAdd x)) a e =
      (if a = e then 1 else 0) +
        x * ((if minusPos n j (!t) = e then 1 else 0) * (if a = minusPos n i s then 1 else 0)) -
        x * ((if minusPos n i (!s) = e then 1 else 0) * (if a = minusPos n j t then 1 else 0)) := by
  rw [mat_apply, HypFrame.spinAction_longRoot]
  simp only [minusFrame_vec]
  rw [polar_minusVec_eq_apply, polar_minusVec_eq_apply]
  simp only [minusVec_eq_single, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  ring

theorem mat_twShortRoot_apply (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K)
    (a e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    mat n (twShortRoot n hirr i s (.ofAdd p)) a e =
      (if a = e then 1 else 0) + (if minusPos n i (!s) = e then 1 else 0) * planeVec n p a -
        (polar (quadMinus n K b c) (Pi.single e 1) (planeVec n p) +
          planeNorm b c p * (if minusPos n i (!s) = e then 1 else 0)) *
          (if a = minusPos n i s then 1 else 0) := by
  rw [mat_apply, spinAction_twShortRoot, polar_minusVec_eq_apply]
  simp only [minusVec_eq_single, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  ring

theorem minusWt_inr_inr (t : Fin 2) : minusWt n (.inr (.inr t)) = 0 := rfl

theorem planeVec_apply_minusPos (p : Fin 2 → K) (i : Fin (n - 1)) (s : Bool) :
    planeVec n p (minusPos n i s) = 0 := by
  cases s <;> rfl

theorem minusPos_ne_not (i : Fin (n - 1)) (s : Bool) : minusPos n i s ≠ minusPos n i (!s) := by
  rw [ne_eq, minusPos_inj]
  cases s <;> simp

theorem eq_inr_inr_of_ne {e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2} {p : Fin 2 → K}
    (h : polar (quadMinus n K b c) (Pi.single e 1) (planeVec n p) ≠ 0) :
    ∃ t, e = .inr (.inr t) := by
  by_contra h'
  push Not at h'
  exact h (polar_single_planeVec_of_ne n (fun t he => h' t he) p)

section Long

variable {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)

theorem mat_longRoot_diag (x : K) (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    mat n ((minusFrame n b c).longRoot hij s t (.ofAdd x)) a a = 1 := by
  rw [mat_longRoot_apply]
  have e1 : (if minusPos n j (!t) = a then (1 : K) else 0) * (if a = minusPos n i s then 1 else 0)
      = 0 := by
    by_cases h : a = minusPos n i s
    · subst h
      rw [ite_eq_right_iff.mpr (fun h' => absurd ((minusPos_inj n).mp h').1 (Ne.symm hij)),
        zero_mul]
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), mul_zero]
  have e2 : (if minusPos n i (!s) = a then (1 : K) else 0) * (if a = minusPos n j t then 1 else 0)
      = 0 := by
    by_cases h : a = minusPos n j t
    · subst h
      rw [ite_eq_right_iff.mpr (fun h' => absurd ((minusPos_inj n).mp h').1 hij), zero_mul]
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), mul_zero]
  rw [e1, e2]
  simp

theorem mat_longRoot_shift (x : K) (a e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (hae : a ≠ e)
    (hne : mat n ((minusFrame n b c).longRoot hij s t (.ofAdd x)) a e ≠ 0) :
    minusWt n a - minusWt n e = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
  rw [mat_longRoot_apply, ite_eq_right_iff.mpr (fun h => absurd h hae), zero_add] at hne
  by_cases h1 : minusPos n j (!t) = e ∧ a = minusPos n i s
  · obtain ⟨rfl, rfl⟩ := h1
    rw [minusWt_minusPos, minusWt_minusPos, boolSign_not, Pi.single_neg, sub_neg_eq_add]
  · by_cases h2 : minusPos n i (!s) = e ∧ a = minusPos n j t
    · obtain ⟨rfl, rfl⟩ := h2
      rw [minusWt_minusPos, minusWt_minusPos, boolSign_not, Pi.single_neg, sub_neg_eq_add,
        add_comm]
    · exfalso
      apply hne
      have e1 : (if minusPos n j (!t) = e then (1 : K) else 0) *
          (if a = minusPos n i s then 1 else 0) = 0 := by
        by_cases h : a = minusPos n i s
        · rw [ite_eq_right_iff.mpr (fun h' => absurd ⟨h', h⟩ h1), zero_mul]
        · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), mul_zero]
      have e2 : (if minusPos n i (!s) = e then (1 : K) else 0) *
          (if a = minusPos n j t then 1 else 0) = 0 := by
        by_cases h : a = minusPos n j t
        · rw [ite_eq_right_iff.mpr (fun h' => absurd ⟨h', h⟩ h2), zero_mul]
        · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), mul_zero]
      rw [e1, e2]
      ring

theorem mat_longRoot_first (x : K) :
    mat n ((minusFrame n b c).longRoot hij s t (.ofAdd x)) (minusPos n i s) (minusPos n j (!t)) =
      x := by
  rw [mat_longRoot_apply, ite_eq_right_iff.mpr (fun h => absurd ((minusPos_inj n).mp h).1 hij),
    ite_eq_left rfl, ite_eq_left rfl,
    ite_eq_right_iff.mpr (fun h => absurd ((minusPos_inj n).mp h).1 hij), zero_mul]
  ring

end Long

section Short

variable (i : Fin (n - 1)) (s : Bool)

theorem mat_twShortRoot_diag (p : Fin 2 → K) (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    mat n (twShortRoot n hirr i s (.ofAdd p)) a a = 1 := by
  rw [mat_twShortRoot_apply, ite_eq_left rfl]
  by_cases h1 : a = minusPos n i (!s)
  · subst h1
    rw [planeVec_apply_minusPos, ite_eq_right_iff.mpr
      (fun h => absurd h (minusPos_ne_not n i s).symm)]
    ring
  · by_cases h2 : a = minusPos n i s
    · subst h2
      rw [ite_eq_right_iff.mpr (fun h => absurd h.symm h1),
        polar_single_planeVec_of_ne n (fun t => minusPos_ne_inr_inr n i s t)]
      ring
    · rw [ite_eq_right_iff.mpr (fun h => absurd h.symm h1), ite_eq_right_iff.mpr
        (fun h => absurd h h2)]
      ring

theorem mat_twShortRoot_shift (p : Fin 2 → K) (a e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (hae : a ≠ e) (hne : mat n (twShortRoot n hirr i s (.ofAdd p)) a e ≠ 0) :
    minusWt n a - minusWt n e = Pi.single i (boolSign s) ∨
      minusWt n a - minusWt n e = 2 • Pi.single i (boolSign s) := by
  rw [mat_twShortRoot_apply, ite_eq_right_iff.mpr (fun h => absurd h hae), zero_add] at hne
  by_cases he : minusPos n i (!s) = e
  · subst he
    by_cases ha : a = minusPos n i s
    · subst ha
      right
      rw [minusWt_minusPos, minusWt_minusPos, boolSign_not, Pi.single_neg, sub_neg_eq_add,
        two_nsmul]
    · left
      rw [ite_eq_right_iff.mpr (fun h => absurd h ha), mul_zero, sub_zero, ite_eq_left rfl,
        one_mul] at hne
      rcases a with k | k | t
      · exact absurd rfl hne
      · exact absurd rfl hne
      · rw [minusWt_inr_inr, minusWt_minusPos, boolSign_not, Pi.single_neg, zero_sub, neg_neg]
  · left
    rw [ite_eq_right_iff.mpr (fun h => absurd h he), zero_mul, zero_sub, mul_zero,
      add_zero] at hne
    have ha : a = minusPos n i s := by
      by_contra ha
      rw [ite_eq_right_iff.mpr (fun h => absurd h ha), mul_zero, neg_zero] at hne
      exact hne rfl
    subst ha
    have hp : polar (quadMinus n K b c) (Pi.single e 1) (planeVec n p) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, neg_zero] at hne
      exact hne rfl
    obtain ⟨t, rfl⟩ := eq_inr_inr_of_ne n hp
    rw [minusWt_minusPos, minusWt_inr_inr, sub_zero]

theorem mat_twShortRoot_first (p : Fin 2 → K) (t : Fin 2) :
    mat n (twShortRoot n hirr i s (.ofAdd p)) (.inr (.inr t)) (minusPos n i (!s)) = p t := by
  rw [mat_twShortRoot_apply, ite_eq_right_iff.mpr
      (fun h => absurd h.symm (minusPos_ne_inr_inr n i (!s) t)), ite_eq_left rfl,
    ite_eq_right_iff.mpr (fun h => absurd h.symm (minusPos_ne_inr_inr n i s t))]
  simp [planeVec]

end Short

theorem mat_diag_of_mem_minusRootGroup {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) {x : spinGroup (quadMinus n K b c)}
    (hx : x ∈ minusRootGroup n hirr γ) (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    mat n x a a = 1 := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · obtain ⟨y, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
    exact mat_longRoot_diag n hij s t y a
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
    exact mat_twShortRoot_diag n hirr i s p a

theorem mat_shift_of_mem_minusRootGroup {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) {x : spinGroup (quadMinus n K b c)}
    (hx : x ∈ minusRootGroup n hirr γ) (a e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (hae : a ≠ e)
    (hne : mat n x a e ≠ 0) :
    minusWt n a - minusWt n e = toStdB (n - 1) γ ∨
      minusWt n a - minusWt n e = 2 • toStdB (n - 1) γ := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · obtain ⟨y, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
    rw [hγ']
    exact Or.inl (mat_longRoot_shift n hij s t y a e hae hne)
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
    rw [hγ']
    exact mat_twShortRoot_shift n hirr i s p a e hae hne

theorem eq_of_mat_shift_eq {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) {x x' : spinGroup (quadMinus n K b c)}
    (hx : x ∈ minusRootGroup n hirr γ) (hx' : x' ∈ minusRootGroup n hirr γ)
    (h : ∀ a e, minusWt n a - minusWt n e = toStdB (n - 1) γ → mat n x a e = mat n x' a e) :
    x = x' := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · obtain ⟨y, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
    obtain ⟨y', rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx'
    have := h (minusPos n i s) (minusPos n j (!t)) (by
      rw [minusWt_minusPos, minusWt_minusPos, hγ', boolSign_not, Pi.single_neg, sub_neg_eq_add])
    rw [mat_longRoot_first, mat_longRoot_first] at this
    rw [this]
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
    obtain ⟨p', rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx'
    have hp : p = p' := funext fun t => by
      have := h (.inr (.inr t)) (minusPos n i (!s)) (by
        rw [minusWt_inr_inr, minusWt_minusPos, hγ', boolSign_not, Pi.single_neg, zero_sub,
          neg_neg])
      rwa [mat_twShortRoot_first, mat_twShortRoot_first] at this
    rw [hp]

@[expose] def epsHt : (Fin (n - 1) → ℤ) →+ ℤ where
  toFun e := ∑ a : Fin (n - 1), (((n - 1 : ℕ) : ℤ) - a) * e a
  map_zero' := by simp
  map_add' e e' := by simp [mul_add, Finset.sum_add_distrib]

theorem epsHt_toStdB (γ : Fin (n - 1) → ℤ) : epsHt n (toStdB (n - 1) γ) = ht γ :=
  (ht_eq_sum_toStdB (n - 1) γ).symm

theorem minusDatum_prodInjective (σ : ℤ) (L : List (Fin (n - 1) → ℤ)) (hL : L.Nodup)
    (hroots : ∀ γ ∈ L, γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅)
    (hlev : ∀ γ ∈ L, 0 < σ * ht γ) (hsort : L.Pairwise fun γ δ => σ * ht γ ≤ σ * ht δ) :
    ProdInjectiveFor (minusRootGroup n hirr) L := by
  intro F G hF hG hFG
  have h := congrArg (matHom n) hFG
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map] at h
  have hf : ∀ γ, (σ • epsHt n) (toStdB (n - 1) γ) = σ * ht γ := fun γ => by
    rw [AddMonoidHom.smul_apply, epsHt_toStdB, smul_eq_mul]
  have key := eq_of_list_prod_eq_of_shift (minusWt n) (σ • epsHt n) (toStdB (n - 1))
    (fun γ M => ∃ x ∈ minusRootGroup n hirr γ, γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧
      M = mat n x)
    (fun γ M ⟨x, hx, hγ, hM⟩ a e hae hne => by
      rw [hM] at hne
      exact mat_shift_of_mem_minusRootGroup n hirr hγ hx a e hae hne)
    (fun γ M ⟨x, hx, hγ, hM⟩ a => by rw [hM]; exact mat_diag_of_mem_minusRootGroup n hirr hγ hx a)
    (fun γ M M' ⟨x, hx, hγ, hM⟩ ⟨x', hx', _, hM'⟩ hMM => by
      rw [hM, hM', eq_of_mat_shift_eq n hirr hγ hx hx' (fun a e hae => by
        rw [← hM, ← hM']; exact hMM a e hae)])
    (fun γ M ⟨x, _, _, hM⟩ => by rw [hM]; exact isUnit_mat n x)
    L hL (fun γ _ δ _ h => toStdB_injective (n - 1) h) (fun γ hγ => by rw [hf]; exact hlev γ hγ)
    (hsort.imp fun {γ δ} h => by rw [hf, hf]; exact h)
    (matHom n ∘ F) (matHom n ∘ G) (fun γ hγ => ⟨F γ, hF γ hγ, hroots γ hγ, rfl⟩)
    (fun γ hγ => ⟨G γ, hG γ hγ, hroots γ hγ, rfl⟩) h
  intro γ hγ
  exact eq_of_mat_shift_eq n hirr (hroots γ hγ) (hF γ hγ) (hG γ hγ)
    (fun a e _ => congrFun (congrFun (key γ hγ) a) e)

theorem idBelow_of_mem_iSup (σ : ℤ) (P : Set (Fin (n - 1) → ℤ))
    (hP : ∀ γ ∈ P, γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧ 0 < σ * ht γ)
    {x : spinGroup (quadMinus n K b c)} (hx : x ∈ ⨆ γ ∈ P, minusRootGroup n hirr γ) :
    IdBelow (fun a => (σ • epsHt n) (minusWt n a)) 1 (mat n x) := by
  rw [iSup_subtype'] at hx
  refine Subgroup.iSup_induction _ hx (C := fun x : spinGroup (quadMinus n K b c) =>
    IdBelow (fun a => (σ • epsHt n) (minusWt n a)) 1 (mat n x)) (fun γ y hy => ?_) ?_
    fun y z hy hz => ?_
  · obtain ⟨hroot, hlev⟩ := hP γ.1 γ.2
    have hf : (σ • epsHt n) (toStdB (n - 1) γ.1) = σ * ht γ.1 := by
      rw [AddMonoidHom.smul_apply, epsHt_toStdB, smul_eq_mul]
    refine (idBelow_of_shift (minusWt n) (σ • epsHt n) (toStdB (n - 1))
      (fun γ M => ∃ x ∈ minusRootGroup n hirr γ, γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧
        M = mat n x)
      (fun γ M ⟨x, hx, hγ, hM⟩ a e hae hne => by
        rw [hM] at hne
        exact mat_shift_of_mem_minusRootGroup n hirr hγ hx a e hae hne)
      (fun γ M ⟨x, hx, hγ, hM⟩ a => by
        rw [hM]
        exact mat_diag_of_mem_minusRootGroup n hirr hγ hx a)
      (by rw [hf]; exact hlev) ⟨y, hy, hroot, rfl⟩).mono ?_
    rw [hf]
    omega
  · rw [mat_one]
    exact idBelow_one 1
  · rw [mat_mul]
    exact idBelow_mul one_pos hy hz

theorem eq_one_of_idBelow_of_idBelow (lev : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℤ)
    {M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K}
    (h1 : IdBelow lev 1 M) (h2 : IdBelow (fun a => -lev a) 1 M) : M = 1 := by
  ext a e
  rcases lt_or_ge (lev a - lev e) 1 with h | h
  · exact h1 a e h
  · exact h2 a e (by simp only; omega)

@[expose] noncomputable def posTestElt : CliffordAlgebra (quadMinus n K b c) :=
  (minusFrame n b c).toHypFrame.testElt fun _ => true

theorem posTestElt_ne_zero : posTestElt (K := K) (b := b) (c := c) n ≠ 0 :=
  (minusFrame n b c).toHypFrame.testElt_ne_zero _

@[expose] noncomputable def fixPosTestElt : Subgroup (spinGroup (quadMinus n K b c)) where
  carrier := {g | (g : CliffordAlgebra (quadMinus n K b c)) * posTestElt n = posTestElt n}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [Submonoid.coe_mul, mul_assoc, hh, hg]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, OneMemClass.coe_one, one_mul]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    conv_lhs => rw [← hg]
    rw [← mul_assoc, coe_inv_mul_coe, one_mul]

theorem minusRootGroup_le_fixPosTestElt {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (hpos : 0 < ht γ) :
    minusRootGroup n hirr γ ≤ fixPosTestElt n := by
  intro x hx
  change (x : CliffordAlgebra (quadMinus n K b c)) * posTestElt n = posTestElt n
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · obtain ⟨y, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
    have hst : s = true ∨ t = true := by
      by_contra h
      push Not at h
      have hs : s = false := by simpa using h.1
      have ht : t = false := by simpa using h.2
      rw [ht_of_toStdB_eq_add (n - 1) hγ', hs, ht, boolSign_false] at hpos
      have := i.isLt
      have := j.isLt
      omega
    rcases hst with rfl | rfl
    · rw [(minusFrame n b c).longRoot_swap hij]
      exact (minusFrame n b c).toHypFrame.longRoot_mul_testElt hij.symm _ true _ rfl
    · exact (minusFrame n b c).toHypFrame.longRoot_mul_testElt hij _ true _ rfl
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
    have hs : s = true := by
      by_contra h
      have hs : s = false := by simpa using h
      rw [ht_of_toStdB_eq_single (n - 1) hγ', hs, boolSign_false] at hpos
      have := i.isLt
      omega
    subst hs
    rw [coe_twShortRoot, posTestElt, add_mul, one_mul, mul_assoc]
    have h0 := (minusFrame n b c).toHypFrame.ι_vec_mul_testElt (fun _ => true) i
    simp only [minusFrame_vec] at h0
    rw [h0, mul_zero, add_zero]

theorem posPart_le_fixPosTestElt :
    ⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧ 0 < ht γ}, minusRootGroup n hirr γ ≤
      fixPosTestElt n :=
  iSup₂_le fun _ hγ => minusRootGroup_le_fixPosTestElt n hirr hγ.1 hγ.2

theorem eq_one_of_mat_eq_one {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {x : spinGroup (quadMinus n K b c)}
    (hmat : mat n x = 1) (hT : x ∈ fixPosTestElt n) : x = 1 := by
  have hker : x ∈ (spinMatrix (quadMinus n K b c)).ker := by
    rw [MonoidHom.mem_ker]
    exact Units.ext hmat
  rcases (mem_ker_spinMatrix_quadMinus_iff hirr x).mp hker with h | h
  · exact h
  · change (x : CliffordAlgebra (quadMinus n K b c)) * posTestElt n = posTestElt n at hT
    rw [h, neg_one_mul] at hT
    have h2 : (2 : K) • posTestElt (K := K) (b := b) (c := c) n = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hT]
      exact neg_add_cancel _
    have h20 : (2 : K) = 0 := by
      by_contra h20
      exact posTestElt_ne_zero n ((smul_eq_zero.mp h2).resolve_left h20)
    apply Subtype.ext
    rw [h, Submonoid.coe_one, neg_one_eq_one_of_two_eq_zero _ h20]

theorem minusDatum_posPart_inf_negPart {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧ 0 < ht γ},
        minusRootGroup n hirr γ) ⊓
      (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧ ht γ < 0},
        minusRootGroup n hirr γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxp, hxn⟩
  rw [Subgroup.mem_bot]
  have h1 := idBelow_of_mem_iSup n hirr 1 _ (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hxp
  have h2 := idBelow_of_mem_iSup n hirr (-1) _ (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hxn
  refine eq_one_of_mat_eq_one n hirr (eq_one_of_idBelow_of_idBelow n _ h1 ?_)
    (posPart_le_fixPosTestElt n hirr hxp)
  intro a e hae
  have hneg : ∀ v, ((-1 : ℤ) • epsHt n) v = -((1 : ℤ) • epsHt n) v := fun v => by
    simp only [AddMonoidHom.smul_apply, smul_eq_mul]
    ring
  refine h2 a e ?_
  simp only [hneg] at hae ⊢
  omega

end CFSG.LieType.Universal.Spin.Twisted
