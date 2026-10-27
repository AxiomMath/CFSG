module

public import CFSG.LieType.Chevalley.E6PinnedAdjoint

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6PinnedAdjoint

set_option linter.unusedSectionVars false

section Pair

variable {τ : Tag}

@[expose] def cartanPair (τ : Tag) (δ : Fin τ.rank → ℤ) (k : Fin τ.rank) : ℤ :=
  ∑ l, τ.cartan k l * δ l

theorem cartanPair_single (j k : Fin τ.rank) :
    cartanPair τ (Pi.single j 1) k = τ.cartan k j := by
  simp [cartanPair, Pi.single_apply]

theorem cartanPair_reflect (a : Fin τ.rank) (δ : Fin τ.rank → ℤ) (k : Fin τ.rank) :
    cartanPair τ (reflect τ a δ) k =
      cartanPair τ δ k - cartanPair τ δ a * τ.cartan k a := by
  have h : ∑ l, τ.cartan k l * ((∑ j, τ.cartan a j * δ j) *
      (Pi.single a (1 : ℤ) : Fin τ.rank → ℤ) l) = (∑ j, τ.cartan a j * δ j) * τ.cartan k a := by
    simp [Pi.single_apply, mul_comm]
  simp only [cartanPair, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, h]

theorem wordReflect_concat (w : List ℕ) (a : ℕ) (v : Fin τ.rank → ℤ) :
    wordReflect τ (w ++ [a]) v = reflect τ (τ.idx a) (wordReflect τ w v) := by
  simp [wordReflect, List.foldl_append]

end Pair

section Word

variable {τ : Tag} {K : Type*} [Field K]

theorem weylElt_apply_hVec_sub (a k : Fin τ.rank) :
    (weylElt τ K a 1 : Module.End K (RootModule τ K))
      (hVec τ K k - ((τ.cartan k a).natAbs : K) • hVec τ K a) = hVec τ K k := by
  rw [map_sub, map_smul, weylElt_hVec, weylElt_hVec_self]
  module

theorem weylElt_inv_hVec (a k : Fin τ.rank) :
    (((weylElt τ K a 1)⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
        (hVec τ K k) = hVec τ K k - ((τ.cartan k a).natAbs : K) • hVec τ K a := by
  have := units_inv_apply_of_apply_eq (weylElt τ K a 1) (1 : K) (Or.inl rfl)
    (x := hVec τ K k - ((τ.cartan k a).natAbs : K) • hVec τ K a) (y := hVec τ K k)
    (by rw [one_smul]; exact weylElt_apply_hVec_sub a k)
  rw [this, one_smul]

theorem weylElt_conj_step (s : Fin τ.rank → ℤ) (hs : ∀ m, s m = 1 ∨ s m = -1)
    (habs : ∀ m j, ((τ.cartan m j).natAbs : ℤ) = s m * s j * τ.cartan m j)
    (b : Fin τ.rank) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (S : K)
    (U : K → (Module.End K (RootModule τ K))ˣ)
    (hU : ∀ (c : K) (k : Fin τ.rank), (U c : Module.End K (RootModule τ K)) (hVec τ K k) =
      hVec τ K k + (S * c * ((s k * cartanPair τ δ k : ℤ) : K)) • rootVec τ K δ) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ (c : K) (k : Fin τ.rank),
      ((weylElt τ K b 1 * U c * (weylElt τ K b 1)⁻¹ : (Module.End K (RootModule τ K))ˣ) :
        Module.End K (RootModule τ K)) (hVec τ K k) =
        hVec τ K k + (ε * S * c * ((s k * cartanPair τ (reflect τ b δ) k : ℤ) : K)) •
          rootVec τ K (reflect τ b δ) := by
  obtain ⟨ε, hε, hn⟩ := weylElt_one_rootVec_sgn (K := K) b hδ
  refine ⟨ε, hε, fun c k => ?_⟩
  have hint : ((τ.cartan k b).natAbs : ℤ) * s b = s k * τ.cartan k b := by
    have h := habs k b
    rcases hs b with hb | hb <;> rw [hb] at h ⊢ <;> linarith
  have hK : ((τ.cartan k b).natAbs : K) * ((s b : ℤ) : K) =
      ((s k : ℤ) : K) * ((τ.cartan k b : ℤ) : K) := by
    have h := congrArg (Int.cast : ℤ → K) hint
    rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast] at h
    exact h
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    weylElt_inv_hVec, map_sub, map_smul, hU c k, hU c b]
  have hsplit : hVec τ K k + (S * c * ((s k * cartanPair τ δ k : ℤ) : K)) • rootVec τ K δ -
      ((τ.cartan k b).natAbs : K) • (hVec τ K b +
        (S * c * ((s b * cartanPair τ δ b : ℤ) : K)) • rootVec τ K δ) =
      (hVec τ K k - ((τ.cartan k b).natAbs : K) • hVec τ K b) +
        ((S * c * ((s k * cartanPair τ δ k : ℤ) : K)) - ((τ.cartan k b).natAbs : K) *
          (S * c * ((s b * cartanPair τ δ b : ℤ) : K))) • rootVec τ K δ := by
    module
  rw [hsplit, map_add, map_smul, hn, weylElt_apply_hVec_sub, smul_smul, cartanPair_reflect]
  congr 2
  push_cast
  linear_combination (-(ε * S * c * ((cartanPair τ δ b : ℤ) : K))) * hK

theorem word_conj_hVec (s : Fin τ.rank → ℤ) (hs : ∀ m, s m = 1 ∨ s m = -1)
    (habs : ∀ m j, ((τ.cartan m j).natAbs : ℤ) = s m * s j * τ.cartan m j)
    (j : Fin τ.rank) (w : List ℕ) :
    ∃ S : K, (S = 1 ∨ S = -1) ∧ ∀ (c : K) (k : Fin τ.rank),
      ((((w.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod * xUnit τ K j c *
          (((w.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod)⁻¹ :
            (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) (hVec τ K k) =
        hVec τ K k + (S * c * ((s k * cartanPair τ (wordReflect τ w (Pi.single j 1)) k : ℤ) : K))
          • rootVec τ K (wordReflect τ w (Pi.single j 1)) := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨(s j : K), ?_, fun c k => ?_⟩
    · rcases hs j with h | h <;> rw [h] <;> simp
    · have e : ((s j : ℤ) : K) * c * ((s k * cartanPair τ (Pi.single j 1) k : ℤ) : K) =
          ((τ.cartan k j).natAbs : K) * c := by
        rw [cartanPair_single]
        have h := congrArg (Int.cast : ℤ → K) (habs k j)
        rw [Int.cast_natCast, Int.cast_mul, Int.cast_mul] at h
        push_cast
        rw [h]
        ring
      simp only [List.map_nil, List.reverse_nil, List.prod_nil, one_mul, inv_one, mul_one]
      change (xOp τ K j c : Module.End K (RootModule τ K)) (hVec τ K k) = _
      rw [xOp_apply_hVec]
      simp only [wordReflect, List.foldl_nil, e]
  | append_singleton w' a ih =>
    obtain ⟨S, hS, hIH⟩ := ih
    have hroot : IsRoot τ (wordReflect τ w' (Pi.single j 1)) :=
      wordReflect_isRoot w' (IsRoot.basis j)
    obtain ⟨ε, hε, hstep⟩ := weylElt_conj_step s hs habs (τ.idx a) hroot S
      (fun c => ((w'.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod * xUnit τ K j c *
        (((w'.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod)⁻¹) hIH
    refine ⟨ε * S, ?_, fun c k => ?_⟩
    · rcases hε with rfl | rfl <;> rcases hS with rfl | rfl <;> simp
    · have hW : (((w' ++ [a]).map fun i => weylElt τ K (τ.idx i) 1).reverse).prod =
          weylElt τ K (τ.idx a) 1 *
            ((w'.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod := by
        simp [List.map_append, List.reverse_append, List.prod_append]
      have e1 : weylElt τ K (τ.idx a) 1 *
          ((w'.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod * xUnit τ K j c *
          (weylElt τ K (τ.idx a) 1 *
            ((w'.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod)⁻¹ =
          weylElt τ K (τ.idx a) 1 * (((w'.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod *
            xUnit τ K j c * (((w'.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod)⁻¹) *
          (weylElt τ K (τ.idx a) 1)⁻¹ := by group
      rw [hW, e1, hstep c k, wordReflect_concat]

theorem pinnedX_hVec (s : Fin τ.rank → ℤ) (hs : ∀ m, s m = 1 ∨ s m = -1)
    (habs : ∀ m j, ((τ.cartan m j).natAbs : ℤ) = s m * s j * τ.cartan m j)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    ∃ S : K, (S = 1 ∨ S = -1) ∧ ∀ (c : K) (k : Fin τ.rank),
      (pinnedX τ K δ c : Module.End K (RootModule τ K)) (hVec τ K k) =
        hVec τ K k + (S * c * ((s k * cartanPair τ δ k : ℤ) : K)) • rootVec τ K δ := by
  obtain ⟨S, hS, h⟩ := word_conj_hVec (K := K) s hs habs (pinnedData τ δ).1 (pinnedData τ δ).2.1
  have hfold : wordReflect τ (pinnedData τ δ).2.1 (Pi.single (pinnedData τ δ).1 1) = δ :=
    foldl_reflect_pinnedData hδ
  rw [hfold] at h
  have hε : (((pinnedData τ δ).2.2 : ℤ) : K) = 1 ∨ (((pinnedData τ δ).2.2 : ℤ) : K) = -1 := by
    rcases pinnedSign_eq τ δ with h | h <;> rw [h] <;> simp
  refine ⟨S * (((pinnedData τ δ).2.2 : ℤ) : K), ?_, fun c k => ?_⟩
  · rcases hS with rfl | rfl <;> rcases hε with h | h <;> rw [h] <;> simp
  · have h' := h (((pinnedData τ δ).2.2 : ℤ) • c) k
    rw [zsmul_eq_mul] at h'
    change (((((pinnedData τ δ).2.1.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod *
        xUnit τ K (pinnedData τ δ).1 ((pinnedData τ δ).2.2 • c) *
        ((((pinnedData τ δ).2.1.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod)⁻¹ :
          (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
            (hVec τ K k) = _
    rw [zsmul_eq_mul, h']
    congr 2
    ring

end Word

section E6

variable {K : Type*} [Field K]

@[expose] def e6Sgn : Fin Tag.E6.rank → ℤ := ![1, -1, -1, 1, -1, 1]

theorem e6Sgn_sign : ∀ m, e6Sgn m = 1 ∨ e6Sgn m = -1 := by decide +kernel

theorem e6Sgn_abs : ∀ m j : Fin Tag.E6.rank,
    ((Tag.E6.cartan m j).natAbs : ℤ) = e6Sgn m * e6Sgn j * Tag.E6.cartan m j := by decide +kernel

theorem pinnedX_hVec_e6 {δ : Fin Tag.E6.rank → ℤ} (hδ : IsRoot Tag.E6 δ) :
    ∃ S : K, (S = 1 ∨ S = -1) ∧ ∀ (c : K) (k : Fin Tag.E6.rank),
      (pinnedX Tag.E6 K δ c : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K k) =
        hVec Tag.E6 K k + (S * c * ((e6Sgn k * cartanPair Tag.E6 δ k : ℤ) : K)) •
          rootVec Tag.E6 K δ :=
  pinnedX_hVec e6Sgn e6Sgn_sign e6Sgn_abs hδ

theorem not_fix_hVec_of_conj {g : (Module.End K (RootModule Tag.E6 K))ˣ}
    (hfix : ∀ k, (g : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K k) = hVec Tag.E6 K k)
    {δ δ' : Fin Tag.E6.rank → ℤ} (hδ : IsRoot Tag.E6 δ) (hδ' : IsRoot Tag.E6 δ') (u : K)
    (hconj : g * pinnedX Tag.E6 K δ 1 * g⁻¹ = pinnedX Tag.E6 K δ' u)
    (k₁ k₂ : Fin Tag.E6.rank)
    (hD : ((cartanPair Tag.E6 δ k₁ * cartanPair Tag.E6 δ' k₂ -
      cartanPair Tag.E6 δ k₂ * cartanPair Tag.E6 δ' k₁ : ℤ) : K) ≠ 0) : False := by
  obtain ⟨S, hS, hX⟩ := pinnedX_hVec_e6 (K := K) hδ
  obtain ⟨S', hS', hX'⟩ := pinnedX_hVec_e6 (K := K) hδ'
  have hfix' : ∀ k, ((g⁻¹ : (Module.End K (RootModule Tag.E6 K))ˣ) :
      Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K k) = hVec Tag.E6 K k := fun k => by
    have := units_inv_apply_of_apply_eq g (1 : K) (Or.inl rfl) (x := hVec Tag.E6 K k)
      (y := hVec Tag.E6 K k) (by rw [one_smul]; exact hfix k)
    rw [this, one_smul]
  have key : ∀ k, (S * 1 * ((e6Sgn k * cartanPair Tag.E6 δ k : ℤ) : K)) •
      (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K δ) =
      (S' * u * ((e6Sgn k * cartanPair Tag.E6 δ' k : ℤ) : K)) • rootVec Tag.E6 K δ' := by
    intro k
    have h := congrArg (fun f : (Module.End K (RootModule Tag.E6 K))ˣ =>
      (f : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K k)) hconj
    simp only [Units.val_mul, Module.End.mul_apply, hfix', hX 1 k, hX' u k, map_add, map_smul,
      hfix] at h
    exact add_left_cancel h
  have h1 := key k₁
  have h2 := key k₂
  have hmin : ((S' * ((e6Sgn k₂ * cartanPair Tag.E6 δ' k₂ : ℤ) : K)) *
      (S * 1 * ((e6Sgn k₁ * cartanPair Tag.E6 δ k₁ : ℤ) : K)) -
      (S' * ((e6Sgn k₁ * cartanPair Tag.E6 δ' k₁ : ℤ) : K)) *
      (S * 1 * ((e6Sgn k₂ * cartanPair Tag.E6 δ k₂ : ℤ) : K))) •
      (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K δ) = 0 := by
    linear_combination (norm := module)
      (S' * ((e6Sgn k₂ * cartanPair Tag.E6 δ' k₂ : ℤ) : K)) • h1 -
      (S' * ((e6Sgn k₁ * cartanPair Tag.E6 δ' k₁ : ℤ) : K)) • h2
  have hS0 : S ≠ 0 := by rcases hS with rfl | rfl <;> simp
  have hS0' : S' ≠ 0 := by rcases hS' with rfl | rfl <;> simp
  have hsg : ∀ k, ((e6Sgn k : ℤ) : K) ≠ 0 := fun k => by
    rcases e6Sgn_sign k with h | h <;> rw [h] <;> simp
  have hμ : ((S' * ((e6Sgn k₂ * cartanPair Tag.E6 δ' k₂ : ℤ) : K)) *
      (S * 1 * ((e6Sgn k₁ * cartanPair Tag.E6 δ k₁ : ℤ) : K)) -
      (S' * ((e6Sgn k₁ * cartanPair Tag.E6 δ' k₁ : ℤ) : K)) *
      (S * 1 * ((e6Sgn k₂ * cartanPair Tag.E6 δ k₂ : ℤ) : K))) =
      (S * S' * ((e6Sgn k₁ : ℤ) : K) * ((e6Sgn k₂ : ℤ) : K)) *
        ((cartanPair Tag.E6 δ k₁ * cartanPair Tag.E6 δ' k₂ -
          cartanPair Tag.E6 δ k₂ * cartanPair Tag.E6 δ' k₁ : ℤ) : K) := by
    push_cast
    ring
  rw [hμ] at hmin
  have hcoef : (S * S' * ((e6Sgn k₁ : ℤ) : K) * ((e6Sgn k₂ : ℤ) : K)) *
      ((cartanPair Tag.E6 δ k₁ * cartanPair Tag.E6 δ' k₂ -
        cartanPair Tag.E6 δ k₂ * cartanPair Tag.E6 δ' k₁ : ℤ) : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hS0 hS0') (hsg k₁)) (hsg k₂)) hD
  have hV0 : (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K δ) = 0 :=
    (smul_eq_zero.1 hmin).resolve_left hcoef
  have hne : rootVec Tag.E6 K δ ≠ 0 := by
    rw [rootVec_eq_basisVec_of_isRoot hδ]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  apply hne
  have h1 := congrArg (fun f : Module.End K (RootModule Tag.E6 K) => f (rootVec Tag.E6 K δ))
    (Units.inv_mul g)
  simp only [Module.End.mul_apply, hV0, map_zero, Module.End.one_apply] at h1
  exact h1.symm

end E6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
