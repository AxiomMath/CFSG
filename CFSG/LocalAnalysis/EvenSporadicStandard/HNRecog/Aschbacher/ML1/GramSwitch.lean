module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GramBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GramSwitchData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private lemma list_map_congr {α β : Type*} (l : List α) (f g : α → β)
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, h a (by simp)]
      exact congrArg (List.cons (g a)) (ih fun b hb => h b (by simp [hb]))

private lemma list_map_map_apply {α β γ : Type*} (l : List α) (f : β → γ) (g : α → β) :
    (l.map g).map f = l.map fun a => f (g a) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, ih]

private lemma bilin_sum_left (B : LinearMap.BilinForm (ZMod 2) V) (l : List V) (w : V) :
    B l.sum w = (l.map fun u => B u w).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.sum_cons, List.map_cons, LinearMap.BilinForm.add_left, ih]

private lemma bilin_sum_right (B : LinearMap.BilinForm (ZMod 2) V) (w : V) (l : List V) :
    B w l.sum = (l.map fun u => B w u).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.sum_cons, List.map_cons, LinearMap.BilinForm.add_right, ih]

private lemma le_list_sum (e : V ≃ₗ[ZMod 2] V) (l : List V) : e l.sum = (l.map e).sum :=
  map_list_sum e.toAddEquiv l

private theorem gram_switch_aux
    (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (B : LinearMap.BilinForm (ZMod 2) V)
    (hS : Swap.StdHyp σ) (hF : FormHyp σ B) (v : V) (hv : ∀ x : A5, σ (x, x) v = v)
    (hv0 : v ≠ 0) (n : List A5)
    (hF_n : ∀ y : A5, (y = a₀ ∨ y = c₃) → ∀ h : A5,
      (n.map fun g => gramF σ B v (g⁻¹ * (y⁻¹ * h * y))).sum
        = (n.map fun g => gramF σ B v (g⁻¹ * h)).sum)
    (hG_n : ∀ x : A5,
      (n.map fun g => (n.map fun g' => gramF σ B v (g⁻¹ * x * g')).sum).sum = gramFn b₁ x) :
    ∃ v' : V, v' ≠ 0 ∧ (∀ x : A5, σ (x, x) v' = v') ∧ gramF σ B v' = gramFn b₁ := by
  set v' : V := (n.map fun g => σ (g, 1) v).sum with hv'_def
  have hB : ∀ h : A5, B v' (σ (h, 1) v) = (n.map fun g => gramF σ B v (g⁻¹ * h)).sum := by
    intro h
    have h1 : B v' (σ (h, 1) v) = (n.map fun g => B (σ (g, 1) v) (σ (h, 1) v)).sum := by
      rw [hv'_def, bilin_sum_left, list_map_map_apply]
    rw [h1]
    exact congrArg List.sum (list_map_congr n _ _ fun g _ => B_w σ B v hF g h)
  have hF_inv : ∀ y : A5, ∀ h : A5,
      (n.map fun g => gramF σ B v (g⁻¹ * (y⁻¹ * h * y))).sum
        = (n.map fun g => gramF σ B v (g⁻¹ * h)).sum := by
    let T : Subgroup A5 :=
      { carrier := {y | ∀ h : A5,
            (n.map fun g => gramF σ B v (g⁻¹ * (y⁻¹ * h * y))).sum
              = (n.map fun g => gramF σ B v (g⁻¹ * h)).sum}
        mul_mem' := by
          intro y y' hy hy' h
          have h1 : (y * y')⁻¹ * h * (y * y') = y'⁻¹ * (y⁻¹ * h * y) * y' := by group
          rw [h1, hy' (y⁻¹ * h * y), hy h]
        one_mem' := by intro h; simp
        inv_mem' := by
          intro y hy h
          have h2 := hy (y * h * y⁻¹)
          have h3 : y⁻¹ * (y * h * y⁻¹) * y = h := by group
          rw [h3] at h2
          simpa using h2.symm }
    have hgen : ({a₀, c₃} : Set A5) ⊆ (T : Set A5) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hF_n a₀ (Or.inl rfl)
      · exact hF_n c₃ (Or.inr rfl)
    have hclosure : Subgroup.closure ({a₀, c₃} : Set A5) ≤ T :=
      (Subgroup.closure_le T).mpr hgen
    have htop : T = ⊤ := by
      rw [closure_a₀_c₃] at hclosure
      exact top_le_iff.mp hclosure
    intro y h
    have hyT : y ∈ T := by rw [htop]; trivial
    exact hyT h
  have hfix : ∀ x : A5, σ (x, x) v' = v' := by
    intro x
    have hdiag : σ (x, x) v' = (n.map fun g => σ (x * g * x⁻¹, 1) v).sum := by
      rw [hv'_def]
      rw [le_list_sum (σ (x, x)) (n.map fun g => σ (g, 1) v)]
      rw [list_map_map_apply]
      exact congrArg List.sum (list_map_congr n _ _ fun g _ => σ_diag_w σ v hv x g)
    have hB_diag : ∀ h : A5, B (σ (x, x) v') (σ (h, 1) v)
        = (n.map fun g => gramF σ B v (g⁻¹ * (x⁻¹ * h * x))).sum := by
      intro h
      have h1 : B (σ (x, x) v') (σ (h, 1) v)
          = (n.map fun g => B (σ (x * g * x⁻¹, 1) v) (σ (h, 1) v)).sum := by
        rw [hdiag, bilin_sum_left, list_map_map_apply]
      rw [h1]
      apply congrArg List.sum
      apply list_map_congr
      intro g _
      rw [B_w σ B v hF (x * g * x⁻¹) h]
      rw [show (x * g * x⁻¹)⁻¹ * h = x * (g⁻¹ * (x⁻¹ * h * x)) * x⁻¹ by group]
      exact gramF_conj σ B v hF hv (g⁻¹ * (x⁻¹ * h * x)) x
    have hzero : ∀ h : A5, B (σ (x, x) v' - v') (σ (h, 1) v) = 0 := by
      intro h
      rw [LinearMap.BilinForm.sub_left, hB_diag h, hB h]
      exact sub_eq_zero.mpr (hF_inv x h)
    have hspan := span_w σ v hS hv hv0
    have hle : Submodule.span (ZMod 2) (Set.range fun g : A5 => σ (g, 1) v)
        ≤ LinearMap.ker (B (σ (x, x) v' - v')) := by
      rw [Submodule.span_le]
      rintro z ⟨h, rfl⟩
      exact LinearMap.mem_ker.mpr (hzero h)
    have hall : ∀ z : V, B (σ (x, x) v' - v') z = 0 := by
      intro z
      exact LinearMap.mem_ker.mp (hle (by rw [hspan]; trivial))
    exact sub_eq_zero.mp (hF.nondeg.1 _ hall)
  have hgram : gramF σ B v' = gramFn b₁ := by
    funext x
    have hx1 : σ (x, 1) v' = (n.map fun g' => σ (x * g', 1) v).sum := by
      rw [hv'_def]
      rw [le_list_sum (σ (x, 1)) (n.map fun g => σ (g, 1) v)]
      rw [list_map_map_apply]
      exact congrArg List.sum (list_map_congr n _ _ fun g _ => σ_inl_w σ v x g)
    have hA : B v' (σ (x, 1) v') = (n.map fun g => B (σ (g, 1) v) (σ (x, 1) v')).sum := by
      rw [hv'_def, bilin_sum_left, list_map_map_apply]
    have h1 : B v' (σ (x, 1) v')
        = (n.map fun g => (n.map fun g' => gramF σ B v (g⁻¹ * x * g')).sum).sum := by
      calc B v' (σ (x, 1) v')
          = (n.map fun g => B (σ (g, 1) v) (σ (x, 1) v')).sum := hA
        _ = (n.map fun g => B (σ (g, 1) v) ((n.map fun g' => σ (x * g', 1) v).sum)).sum := by
              rw [hx1]
        _ = (n.map fun g => (n.map fun g' => B (σ (g, 1) v) (σ (x * g', 1) v)).sum).sum := by
              apply congrArg List.sum
              apply list_map_congr
              intro g _
              rw [bilin_sum_right, list_map_map_apply]
        _ = (n.map fun g => (n.map fun g' => gramF σ B v (g⁻¹ * x * g')).sum).sum := by
              apply congrArg List.sum
              apply list_map_congr
              intro g _
              apply congrArg List.sum
              apply list_map_congr
              intro g' _
              rw [B_w σ B v hF g (x * g')]
              exact congrArg (gramF σ B v) (mul_assoc g⁻¹ x g').symm
    change B v' (σ (x, 1) v') = gramFn b₁ x
    exact h1.trans (hG_n x)
  have hv'0 : v' ≠ 0 := by
    intro h0
    have hzero : gramF σ B v' a₀ = 0 := by
      rw [h0]
      simp [gramF]
    have : gramFn b₁ a₀ = 0 := by
      rw [← hgram]
      exact hzero
    exact (by decide +kernel : gramFn b₁ a₀ ≠ 0) this
  exact ⟨v', hv'0, hfix, hgram⟩

theorem gram_switch (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (B : LinearMap.BilinForm (ZMod 2) V)
    (hS : Swap.StdHyp σ) (hF : FormHyp σ B) (v : V) (hv : ∀ x : A5, σ (x, x) v = v) (hv0 : v ≠ 0)
    (b : Fin 5 → ZMod 2) (hb : b = b₂ ∨ b = b₃) (hf : gramF σ B v = gramFn b) :
    ∃ v' : V, v' ≠ 0 ∧ (∀ x : A5, σ (x, x) v' = v') ∧ gramF σ B v' = gramFn b₁ := by
  rcases hb with rfl | rfl
  · refine gram_switch_aux σ B hS hF v hv hv0 sw₂ ?_ ?_
    · intro y hy h
      simp only [hf]
      exact sw₂_F y hy h
    · intro x
      simp only [hf]
      exact sw₂_G x
  · refine gram_switch_aux σ B hS hF v hv hv0 sw₃ ?_ ?_
    · intro y hy h
      simp only [hf]
      exact sw₃_F y hy h
    · intro x
      simp only [hf]
      exact sw₃_G x

end CFSG.EvenSporadicStandard.HNRecog.ML1
