module

public import CFSG.LieType.CurtisTits.RootData
public import CFSG.LieType.RootSystem.Parabolic

public section

namespace CFSG.LieType.RootSystem

open CFSG.LieType.CurtisTits

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem isCTRootSystem (D : Set I) :
    IsCTRootSystem (coxeterMatrix hA).toCoxeterSystem (weylAction hA) (roots hA D) where
  single_mem i := Or.inl ⟨1, i, by simp⟩
  smul_mem w _ hγ := weylAction_mem_roots hA w hγ
  exists_eq γ hγ := by
    rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, -, rfl⟩
    · exact ⟨w, i, 1, one_ne_zero, (one_smul ℤ _).symm⟩
    · exact ⟨w, i, 2, two_ne_zero, by rw [two_nsmul, two_zsmul]⟩
  simple_single i := weylAction_simple_single hA i
  simple_apply_of_ne i v _ hj := weylAction_simple_apply_of_ne hA i v hj
  not_isLeftDescent v k hk hdesc := weylAction_single_ne_zero hA v⁻¹ k <|
    le_antisymm ((isRightDescent_iff hA v⁻¹ k).mp
      ((coxeterMatrix hA).toCoxeterSystem.isRightDescent_inv_iff.mpr hdesc)) hk
  eq_single J u i hJ hsupp := eq_single_of_forall_not_isLeftDescent hA J u i hJ hsupp
  exists_parabolic J w i hsupp := exists_parabolic_of_support hA J w i hsupp

omit [DecidableEq I] in
private theorem exists_toRat_eq_smul (x : I → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : I → ℤ, toRat z = (N : ℚ) • x := by
  classical
  refine ⟨∏ k, (x k).den, Finset.prod_pos fun k _ => (x k).pos,
    fun k => (x k).num * ∏ l ∈ Finset.univ.erase k, ((x l).den : ℤ), funext fun k => ?_⟩
  simp only [toRat_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← Finset.mul_prod_erase Finset.univ (fun l => ((x l).den : ℚ)) (Finset.mem_univ k),
    ← Rat.mul_den_eq_num]
  ring

private theorem exists_forall_ne_zero {V ι : Type*} [AddCommGroup V] [Module ℚ V] (P : V → Prop)
    (h0 : P 0) (hP : ∀ x y (c : ℚ), P x → P y → P (x + c • y)) (f : ι → V → ℚ)
    (hf : ∀ t x y (c : ℚ), f t (x + c • y) = f t x + c * f t y) (F : Finset ι)
    (hF : ∀ t ∈ F, ∃ y, P y ∧ f t y ≠ 0) : ∃ x, P x ∧ ∀ t ∈ F, f t x ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, h0, by simp⟩
  | insert t F ht ih =>
    obtain ⟨x, hx, hxF⟩ := ih fun s hs => hF s (Finset.mem_insert_of_mem hs)
    obtain ⟨y, hy, hty⟩ := hF t (Finset.mem_insert_self t F)
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
      (insert (-(f t x) / f t y) (F.image fun s => -(f s x) / f s y))
    refine ⟨x + c • y, hP x y c hx hy, fun s hs => ?_⟩
    rw [hf]
    have key : ∀ s, c ≠ -(f s x) / f s y → f s x ≠ 0 → f s x + c * f s y ≠ 0 := by
      intro s hcs hsx h
      by_cases hsy : f s y = 0
      · rw [hsy, mul_zero, add_zero] at h
        exact hsx h
      · exact hcs (by field_simp; linarith)
    rcases Finset.mem_insert.mp hs with rfl | hs
    · intro h
      apply hc
      refine Finset.mem_insert.mpr (Or.inl ?_)
      field_simp
      linarith
    · exact key s (fun h => hc (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, hs, h.symm⟩)))
        (hxF s hs)

private theorem exists_orthogonal {a b g : I → ℚ} (ha : a ≠ 0)
    (hg : ∀ p q : ℚ, g ≠ p • a + q • b) :
    ∃ y, form hA y a = 0 ∧ form hA y b = 0 ∧ form hA y g ≠ 0 := by
  have haa := form_pos hA ha
  set b' := b - (form hA b a / form hA a a) • a with hb'
  have hb'a : form hA b' a = 0 := by
    simp only [hb', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hab' : form hA a b' = 0 := by rw [form_comm]; exact hb'a
  set y := g - (form hA g a / form hA a a) • a - (form hA g b' / form hA b' b') • b' with hy
  have hya : form hA y a = 0 := by
    simp only [hy, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hb'a]
    field_simp
    ring
  have hyb' : form hA y b' = 0 := by
    simp only [hy, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hab']
    by_cases hbb : form hA b' b' = 0
    · have hb0 : b' = 0 := by
        by_contra h
        exact (form_pos hA h).ne' hbb
      simp [hb0]
    · field_simp
      ring
  have hyb : form hA y b = 0 := by
    have hb : b = b' + (form hA b a / form hA a a) • a := by rw [hb']; abel
    rw [hb, map_add, map_smul, hyb', hya, smul_zero, add_zero]
  have hgy : g = y + (form hA g a / form hA a a) • a + (form hA g b' / form hA b' b') • b' := by
    rw [hy]; abel
  have hyne : y ≠ 0 := by
    intro h0
    apply hg (form hA g a / form hA a a - form hA g b' / form hA b' b' *
      (form hA b a / form hA a a)) (form hA g b' / form hA b' b')
    linear_combination (norm := module) hgy + h0 + (form hA g b' / form hA b' b') • hb'
  refine ⟨y, hya, hyb, ?_⟩
  have hyg : form hA y g = form hA y y := by
    conv_lhs => rw [hgy]
    rw [map_add, map_add, map_smul, map_smul, hya, hyb', smul_zero, smul_zero, add_zero, add_zero]
  rw [hyg]
  exact (form_pos hA hyne).ne'

private theorem exists_generic (D : Set I) {α β : I → ℤ} (hα : α ∈ roots hA D) :
    ∃ x : I → ℤ, form hA (toRat x) (toRat α) = 0 ∧ form hA (toRat x) (toRat β) = 0 ∧
      ∀ δ ∈ roots hA D, (¬ ∃ a b : ℚ, ∀ k, (δ k : ℚ) = a * α k + b * β k) →
        form hA (toRat x) (toRat δ) ≠ 0 := by
  classical
  have hα0 : toRat α ≠ 0 := fun h =>
    ne_zero_of_mem_roots hA D hα (toRat_injective (by rw [h, map_zero]))
  obtain ⟨y, ⟨hya, hyb⟩, hyF⟩ := exists_forall_ne_zero
    (fun y => form hA y (toRat α) = 0 ∧ form hA y (toRat β) = 0) ⟨by simp, by simp⟩
    (fun x y c hx hy => ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩)
    (fun δ y => form hA y (toRat δ)) (fun t x y c => by simp)
    ((finite_roots hA D).toFinset.filter
      fun δ => ¬ ∃ a b : ℚ, ∀ k, (δ k : ℚ) = a * α k + b * β k) fun δ hδ => by
    obtain ⟨-, hδU⟩ := Finset.mem_filter.mp hδ
    obtain ⟨y, h1, h2, h3⟩ := exists_orthogonal hA hα0 (g := toRat δ) (b := toRat β)
      fun p q h => hδU ⟨p, q, fun k => by simpa using congrFun h k⟩
    exact ⟨y, ⟨h1, h2⟩, h3⟩
  obtain ⟨N, hN, z, hz⟩ := exists_toRat_eq_smul y
  refine ⟨z, ?_, ?_, fun δ hδ hδU => ?_⟩
  · rw [hz, map_smul, LinearMap.smul_apply, hya, smul_zero]
  · rw [hz, map_smul, LinearMap.smul_apply, hyb, smul_zero]
  · rw [hz, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero (by positivity)
      (hyF δ (Finset.mem_filter.mpr ⟨(finite_roots hA D).mem_toFinset.mpr hδ, hδU⟩))

private theorem exists_dominant (x : I → ℤ) :
    ∃ u : (coxeterMatrix hA).Group, ∀ k, 0 ≤ coroot A k (weylAction hA u x) := by
  have := finite_group hA
  obtain ⟨u, hu⟩ := Finite.exists_max fun u : (coxeterMatrix hA).Group =>
    ∑ l, weylAction hA u x l
  refine ⟨u, fun k => by_contra fun hk => ?_⟩
  push Not at hk
  have h := hu ((coxeterMatrix hA).toCoxeterSystem.simple k * u)
  rw [weylAction_mul_apply, weylAction_simple, reflection_apply_coroot] at h
  simp [Finset.sum_sub_distrib, Pi.single_apply] at h
  linarith

private noncomputable def ratExt (f : Module.End ℤ (I → ℤ)) : Module.End ℚ (I → ℚ) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (Int.cast : ℤ → ℚ))

private theorem ratExt_toRat (f : Module.End ℤ (I → ℤ)) (v : I → ℤ) :
    ratExt f (toRat v) = toRat (f v) := by
  funext k
  rw [ratExt, Matrix.toLin'_apply, toRat_apply, ← LinearMap.toMatrix'_mulVec f v]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, toRat_apply]
  push_cast
  rfl

omit [DecidableEq I] in
private theorem card_le_two_of_linearIndependent {ι : Type*} [Fintype ι] {f : ι → I → ℚ}
    (hf : LinearIndependent ℚ f) {a b : I → ℚ} (hab : ∀ l, ∃ p q : ℚ, f l = p • a + q • b) :
    Fintype.card ι ≤ 2 := by
  classical
  have hmem : ∀ l, f l ∈ Submodule.span ℚ ({a, b} : Set (I → ℚ)) := fun l => by
    obtain ⟨p, q, h⟩ := hab l
    exact Submodule.mem_span_pair.mpr ⟨p, q, h.symm⟩
  have hf' : LinearIndependent ℚ fun l => (⟨f l, hmem l⟩ : Submodule.span ℚ ({a, b} : Set _)) :=
    LinearIndependent.of_comp (Submodule.subtype _) hf
  have h1 := hf'.fintype_card_le_finrank
  have h2 := finrank_span_finset_le_card (R := ℚ) ({a, b} : Finset (I → ℚ))
  simp only [Finset.coe_insert, Finset.coe_singleton] at h2
  have h3 : ({a, b} : Finset (I → ℚ)).card ≤ 2 := Finset.card_le_two
  exact h1.trans (h2.trans h3)

theorem exists_weylAction_support_subset (D : Set I) {α β : I → ℤ} (hα : α ∈ roots hA D)
    (hβ : β ∈ roots hA D) :
    ∃ (u : (coxeterMatrix hA).Group) (J : Finset I), J.card ≤ 2 ∧
      ∀ γ ∈ roots hA D, (∃ a b : ℚ, ∀ k, (γ k : ℚ) = a * α k + b * β k) →
        ∀ k ∉ J, weylAction hA u γ k = 0 := by
  classical
  have _ := hβ
  obtain ⟨x, hxα, hxβ, hxgen⟩ := exists_generic hA D hα (β := β)
  obtain ⟨u, hu⟩ := exists_dominant hA x
  refine ⟨u, Finset.univ.filter fun l => ∃ a b : ℚ, ∀ k,
    (weylAction hA u⁻¹ (Pi.single l 1) k : ℚ) = a * α k + b * β k, ?_, ?_⟩
  · set J := Finset.univ.filter fun l => ∃ a b : ℚ, ∀ k,
      (weylAction hA u⁻¹ (Pi.single l 1) k : ℚ) = a * α k + b * β k
    have hli : LinearIndependent ℚ fun l : J =>
        toRat (weylAction hA u⁻¹ (Pi.single (l : I) 1)) := by
      apply LinearIndependent.of_comp (ratExt (weylAction hA u))
      have h : (ratExt (weylAction hA u)) ∘ (fun l : J => toRat (weylAction hA u⁻¹
          (Pi.single (l : I) 1))) = fun l : J => Pi.basisFun ℚ I l := by
        funext l
        simp [ratExt_toRat, toRat_single]
      rw [h]
      exact (Pi.basisFun ℚ I).linearIndependent.comp _ Subtype.val_injective
    have := card_le_two_of_linearIndependent hli (a := toRat α) (b := toRat β) fun l => by
      obtain ⟨a, b, hab⟩ := (Finset.mem_filter.mp l.2).2
      exact ⟨a, b, funext fun k => by simp [hab k]⟩
    simpa using this
  · intro γ hγ hγU k hk
    have h0 : form hA (toRat (weylAction hA u x)) (toRat (weylAction hA u γ)) = 0 := by
      rw [form_weylAction]
      obtain ⟨a, b, hab⟩ := hγU
      have : toRat γ = a • toRat α + b • toRat β := funext fun k => by simp [hab k]
      rw [this, map_add, map_smul, map_smul, hxα, hxβ, smul_zero, smul_zero, add_zero]
    have hterm : ∀ l, 0 ≤ form hA (toRat (weylAction hA u x)) (Pi.single l 1) := fun l => by
      rw [form_single_right]
      have h := hu l
      rw [coroot_apply] at h
      refine mul_nonneg (symmetrizer_pos hA l).le ?_
      simp only [toRat_apply]
      exact_mod_cast h
    rw [form_eq_sum] at h0
    by_contra hne
    have hl : form hA (toRat (weylAction hA u x)) (Pi.single k 1) = 0 := by
      rcases nonneg_or_nonpos hA D (weylAction_mem_roots hA u hγ) with hs | hs
      · have h := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => mul_nonneg
          (by simpa using hs l) (hterm l)).mp h0 k (Finset.mem_univ k)
        exact (mul_eq_zero.mp h).resolve_left (by simpa using hne)
      · have h := (Finset.sum_eq_zero_iff_of_nonpos fun l _ => mul_nonpos_of_nonpos_of_nonneg
          (by simpa using hs l) (hterm l)).mp h0 k (Finset.mem_univ k)
        exact (mul_eq_zero.mp h).resolve_left (by simpa using hne)
    apply hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hkU
    apply hxgen _ (Or.inl ⟨u⁻¹, k, rfl⟩) hkU
    rw [← form_weylAction hA u, weylAction_apply_inv_apply, toRat_single]
    exact hl

end CFSG.LieType.RootSystem
