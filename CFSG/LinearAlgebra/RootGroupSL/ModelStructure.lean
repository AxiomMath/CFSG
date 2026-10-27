module

public import CFSG.LinearAlgebra.RootGroupSL.ModelBasic
import CFSG.LinearAlgebra.RootGroupSL.SLTransitive

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

private lemma sl_mul_apply (g₁ g₂ : SpecialLinearGroup k (VJ × V₀)) (p : VJ × V₀) :
    (g₁ * g₂) p = g₁ (g₂ p) := rfl

private lemma sl_map_add (g : SpecialLinearGroup k (VJ × V₀)) (p q : VJ × V₀) :
    g (p + q) = g p + g q := by
  simpa only [SpecialLinearGroup.toLinearEquiv_apply] using
    map_add (SpecialLinearGroup.toLinearEquiv g) p q

private lemma restrictSL_apply (B : SpecialLinearGroup E VJ) (v : VJ) :
    restrictSL (E := E) (VJ := VJ) k B v = B v := rfl

private lemma blockSLE_apply (B : SpecialLinearGroup E VJ) (v : VJ) (w : V₀) :
    blockSLE k V₀ B (v, w) = (B v, w) := by
  change blockSLk k V₀ (restrictSL (E := E) (VJ := VJ) k B) (v, w) = (B v, w)
  rw [blockSLk_apply, restrictSL_apply]

private lemma blockSLE_mem_modelJ (B : SpecialLinearGroup E VJ) :
    blockSLE k V₀ B ∈ modelJ k E VJ V₀ :=
  MonoidHom.mem_range.mpr ⟨B, rfl⟩

theorem modelA1_inf_modelK1 : modelA1 k VJ V₀ ⊓ modelK1 k VJ V₀ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgA, hgK⟩ := hg
  have hfix : ∀ p : VJ × V₀, g p = p := by
    rintro ⟨v, w⟩
    have hp : (v, 0) + (0, w) = (v, w) := by simp
    calc g (v, w) = g ((v, 0) + (0, w)) := by simp [hp]
      _ = g (v, 0) + g (0, w) := sl_map_add g (v, 0) (0, w)
      _ = (v, 0) + (0, w) := by rw [hgA.1 v, hgK.2 w]
      _ = (v, w) := hp
  exact SpecialLinearGroup.ext _ 1 fun p => by simpa using hfix p

theorem modelA2_inf_modelK1 : modelA2 k VJ V₀ ⊓ modelK1 k VJ V₀ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgA, hgK⟩ := hg
  have hfix : ∀ p : VJ × V₀, g p = p := by
    rintro ⟨v, w⟩
    have hv : g (v, 0) = (v, 0) := Prod.ext (hgA.2 v) (hgK.1 v)
    have hw : g (0, w) = (0, w) := hgA.1 w
    have hp : (v, 0) + (0, w) = (v, w) := by simp
    calc g (v, w) = g ((v, 0) + (0, w)) := by simp [hp]
      _ = g (v, 0) + g (0, w) := sl_map_add g (v, 0) (0, w)
      _ = (v, 0) + (0, w) := by rw [hv, hw]
      _ = (v, w) := hp
  exact SpecialLinearGroup.ext _ 1 fun p => by simpa using hfix p

theorem modelA1_mul_comm {a b : SpecialLinearGroup k (VJ × V₀)} (ha : a ∈ modelA1 k VJ V₀)
    (hb : b ∈ modelA1 k VJ V₀) : a * b = b * a := by
  obtain ⟨φ, rfl⟩ := (mem_modelA1_iff a).mp ha
  obtain ⟨φ', rfl⟩ := (mem_modelA1_iff b).mp hb
  calc modelA1Elt φ * modelA1Elt φ' = modelA1Elt (φ + φ') := (modelA1Elt_add φ φ').symm
    _ = modelA1Elt (φ' + φ) := by rw [add_comm]
    _ = modelA1Elt φ' * modelA1Elt φ := modelA1Elt_add φ' φ

theorem modelA2_mul_comm {a b : SpecialLinearGroup k (VJ × V₀)} (ha : a ∈ modelA2 k VJ V₀)
    (hb : b ∈ modelA2 k VJ V₀) : a * b = b * a := by
  obtain ⟨ψ, rfl⟩ := (mem_modelA2_iff a).mp ha
  obtain ⟨ψ', rfl⟩ := (mem_modelA2_iff b).mp hb
  calc modelA2Elt ψ * modelA2Elt ψ' = modelA2Elt (ψ + ψ') := (modelA2Elt_add ψ ψ').symm
    _ = modelA2Elt (ψ' + ψ) := by rw [add_comm]
    _ = modelA2Elt ψ' * modelA2Elt ψ := modelA2Elt_add ψ' ψ

theorem modelK1_conj_mem_modelA1 {g a : SpecialLinearGroup k (VJ × V₀)}
    (hg : g ∈ modelK1 k VJ V₀) (ha : a ∈ modelA1 k VJ V₀) : g * a * g⁻¹ ∈ modelA1 k VJ V₀ := by
  obtain ⟨hg'1, hg'2⟩ := (modelK1 k VJ V₀).inv_mem hg
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨?_, ?_⟩
  · intro v
    let v' : VJ := (g⁻¹ (v, 0)).1
    have hg'v : g⁻¹ (v, 0) = (v', 0) := Prod.ext rfl (hg'1 v)
    have hgg' : g (v', 0) = (v, 0) := by
      have h := LinearEquiv.apply_symm_apply (SpecialLinearGroup.toLinearEquiv g) (v, 0)
      rw [SpecialLinearGroup.toLinearEquiv_symm_apply, hg'v] at h
      simpa only [SpecialLinearGroup.toLinearEquiv_apply] using h
    rw [sl_mul_apply, sl_mul_apply, hg'v, ha1 v', hgg']
  · intro w
    let x : VJ := (a (0, w)).1
    have haw : a (0, w) = (x, w) := Prod.ext rfl (ha2 w)
    have hgw : g (x, w) = g (x, 0) + (0, w) := by
      have hsplit : (x, w) = (x, 0) + (0, w) := by simp
      rw [hsplit, sl_map_add, hg2 w]
    rw [sl_mul_apply, sl_mul_apply, hg'2 w, haw, hgw]
    simp [hg1 x]

theorem modelK1_conj_mem_modelA2 {g a : SpecialLinearGroup k (VJ × V₀)}
    (hg : g ∈ modelK1 k VJ V₀) (ha : a ∈ modelA2 k VJ V₀) : g * a * g⁻¹ ∈ modelA2 k VJ V₀ := by
  obtain ⟨hg'1, hg'2⟩ := (modelK1 k VJ V₀).inv_mem hg
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨?_, ?_⟩
  · intro w
    rw [sl_mul_apply, sl_mul_apply, hg'2 w, ha1 w, hg2 w]
  · intro v
    let v' : VJ := (g⁻¹ (v, 0)).1
    have hg'v : g⁻¹ (v, 0) = (v', 0) := Prod.ext rfl (hg'1 v)
    have hgg' : g (v', 0) = (v, 0) := by
      have h := LinearEquiv.apply_symm_apply (SpecialLinearGroup.toLinearEquiv g) (v, 0)
      rw [SpecialLinearGroup.toLinearEquiv_symm_apply, hg'v] at h
      simpa only [SpecialLinearGroup.toLinearEquiv_apply] using h
    let w' : V₀ := (a (v', 0)).2
    have hav' : a (v', 0) = (v', w') := Prod.ext (ha2 v') rfl
    rw [sl_mul_apply, sl_mul_apply, hg'v, hav']
    have hsplit : (v', w') = (v', 0) + (0, w') := by simp
    rw [hsplit, sl_map_add, Prod.fst_add, hgg', hg2 w']
    simp

theorem modelA1_eq_one_of_commute_modelJ (hm : 2 ≤ Module.finrank E VJ)
    {a : SpecialLinearGroup k (VJ × V₀)} (ha : a ∈ modelA1 k VJ V₀)
    (h : ∀ j ∈ modelJ k E VJ V₀, j * a = a * j) : a = 1 := by
  obtain ⟨φ, rfl⟩ := (mem_modelA1_iff a).mp ha
  have key : ∀ (B : SpecialLinearGroup E VJ) (w : V₀), B (φ w) = φ w := by
    intro B w
    have hcomm : blockSLE k V₀ B * modelA1Elt φ = modelA1Elt φ * blockSLE k V₀ B :=
      h (blockSLE k V₀ B) (blockSLE_mem_modelJ B)
    have h1 : modelA1Elt φ (0, w) = (φ w, w) := by rw [modelA1Elt_apply]; simp
    have h2 : blockSLE k V₀ B (0, w) = (0, w) := by rw [blockSLE_apply]; simp
    have h3 : modelA1Elt φ (blockSLE k V₀ B (0, w)) = (φ w, w) := by rw [h2, h1]
    have h4 : blockSLE k V₀ B (modelA1Elt φ (0, w)) = blockSLE k V₀ B (φ w, w) := by
      rw [h1]
    have happ : blockSLE k V₀ B (modelA1Elt φ (0, w)) =
        modelA1Elt φ (blockSLE k V₀ B (0, w)) := by
      have := congrArg (fun g : SpecialLinearGroup k (VJ × V₀) => g (0, w)) hcomm
      rwa [sl_mul_apply, sl_mul_apply] at this
    rw [h4, h3, blockSLE_apply] at happ
    exact congrArg Prod.fst happ
  have hφw : ∀ w : V₀, φ w = 0 := by
    intro w
    by_contra hu
    have hne : (E ∙ φ w) ≠ ⊤ := by
      intro htop
      have h1 : Module.finrank E (E ∙ φ w) = 1 := finrank_span_singleton hu
      rw [htop, finrank_top] at h1
      omega
    obtain ⟨u', hu'⟩ := SetLike.exists_not_mem_of_ne_top (E ∙ φ w) hne
    have hu'0 : u' ≠ 0 := by
      intro h0
      exact hu' (by simpa [h0] using Submodule.zero_mem (E ∙ φ w))
    obtain ⟨B, hB⟩ := exists_specialLinear_apply_eq hm hu hu'0
    have huu : u' = φ w := by rw [← hB, key B w]
    exact hu' (huu.symm ▸ Submodule.mem_span_singleton_self (φ w))
  have hφ : φ = 0 := by
    ext w
    exact hφw w
  rw [hφ]
  exact SpecialLinearGroup.ext _ 1 fun p => by
    obtain ⟨v, w⟩ := p
    simp [modelA1Elt_apply]

theorem modelA2_eq_one_of_commute_modelJ (hm : 2 ≤ Module.finrank E VJ)
    {a : SpecialLinearGroup k (VJ × V₀)} (ha : a ∈ modelA2 k VJ V₀)
    (h : ∀ j ∈ modelJ k E VJ V₀, j * a = a * j) : a = 1 := by
  obtain ⟨ψ, rfl⟩ := (mem_modelA2_iff a).mp ha
  have key : ∀ (B : SpecialLinearGroup E VJ) (v : VJ), ψ (B v) = ψ v := by
    intro B v
    have hcomm : blockSLE k V₀ B * modelA2Elt ψ = modelA2Elt ψ * blockSLE k V₀ B :=
      h (blockSLE k V₀ B) (blockSLE_mem_modelJ B)
    have h1 : modelA2Elt ψ (v, 0) = (v, ψ v) := by rw [modelA2Elt_apply]; simp
    have h2 : blockSLE k V₀ B (v, 0) = (B v, 0) := by rw [blockSLE_apply]
    have h3 : modelA2Elt ψ (blockSLE k V₀ B (v, 0)) = (B v, ψ (B v)) := by
      rw [h2, modelA2Elt_apply]; simp
    have h4 : blockSLE k V₀ B (modelA2Elt ψ (v, 0)) = blockSLE k V₀ B (v, ψ v) := by
      rw [h1]
    have happ : blockSLE k V₀ B (modelA2Elt ψ (v, 0)) =
        modelA2Elt ψ (blockSLE k V₀ B (v, 0)) := by
      have := congrArg (fun g : SpecialLinearGroup k (VJ × V₀) => g (v, 0)) hcomm
      rwa [sl_mul_apply, sl_mul_apply] at this
    rw [h4, h3, blockSLE_apply] at happ
    exact (congrArg Prod.snd happ).symm
  have hψx : ∀ x : VJ, ψ x = 0 := by
    intro x
    by_cases hx : x = 0
    · rw [hx]
      exact map_zero ψ
    · have hne : (E ∙ x) ≠ ⊤ := by
        intro htop
        have h1 : Module.finrank E (E ∙ x) = 1 := finrank_span_singleton hx
        rw [htop, finrank_top] at h1
        omega
      obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top (E ∙ x) hne
      have hv0 : v ≠ 0 := by
        intro h0
        exact hv (by simpa [h0] using Submodule.zero_mem (E ∙ x))
      have hvx : v + x ≠ 0 := by
        intro h0
        apply hv
        have hv' : v = -x := add_eq_zero_iff_eq_neg.mp h0
        rw [hv']
        exact Submodule.neg_mem (E ∙ x) (Submodule.mem_span_singleton_self x)
      obtain ⟨B, hB⟩ := exists_specialLinear_apply_eq hm hv0 hvx
      have h1 : ψ (v + x) = ψ v := by rw [← hB, key B v]
      have h2 : ψ v + ψ x = ψ v + 0 := by
        rw [add_zero, ← map_add ψ v x]
        exact h1
      exact add_left_cancel h2
  have hψ : ψ = 0 := by
    ext x
    exact hψx x
  rw [hψ]
  exact SpecialLinearGroup.ext _ 1 fun p => by
    obtain ⟨v, w⟩ := p
    simp [modelA2Elt_apply]

end CFSG.LinearAlgebra.RootGroupSL
