module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofBasic
public import CFSG.ClassicalInvolution.RouteD.TypeCRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Generic Module
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Symplectic

variable {F : Type} [Field F] {n : ℕ}

@[expose] def symplFormLeft (u : Fin n ⊕ Fin n → F) : (Fin n ⊕ Fin n → F) →ₗ[F] F where
  toFun v := form v u
  map_add' a b := form_add_left a b u
  map_smul' c a := by simp [form_smul_left]

theorem exists_inv_planeGroup (h2 : (2 : F) ≠ 0) {P : Submodule F (Fin n ⊕ Fin n → F)}
    (hP : IsHyperbolicPlane P) :
    ∃ i, IsLongRootSp2 (planeGroup P) i ∧ minusSpace i = P :=
  exists_isLongRootSp2_of_isHyperbolicPlane h2 hP

theorem planeGroup_injective (h2 : (2 : F) ≠ 0) {P₁ P₂ : Submodule F (Fin n ⊕ Fin n → F)}
    (h₁ : IsHyperbolicPlane P₁) (h₂ : IsHyperbolicPlane P₂)
    (h : planeGroup P₁ = planeGroup P₂) : P₁ = P₂ := by
  obtain ⟨i₁, hi₁, hm₁⟩ := exists_inv_planeGroup h2 h₁
  obtain ⟨i₂, hi₂, hm₂⟩ := exists_inv_planeGroup h2 h₂
  rw [h] at hi₁
  rw [← hm₁, ← hm₂, hi₁.involution_unique h2 hi₂]

theorem commutes_planeGroup_iff (h2 : (2 : F) ≠ 0) {P₁ P₂ : Submodule F (Fin n ⊕ Fin n → F)}
    (h₁ : IsHyperbolicPlane P₁) (h₂ : IsHyperbolicPlane P₂) (hne : P₁ ≠ P₂) :
    Commutes (planeGroup P₁) (planeGroup P₂) ↔ ∀ u ∈ P₁, ∀ v ∈ P₂, form u v = 0 := by
  obtain ⟨i₁, hi₁, hm₁⟩ := exists_inv_planeGroup h2 h₁
  obtain ⟨i₂, hi₂, hm₂⟩ := exists_inv_planeGroup h2 h₂
  have hne' : i₁ ≠ i₂ := by
    rintro rfl
    exact hne (hm₁.symm.trans hm₂)
  constructor
  · intro hc u hu v hv
    have hcomm : Commute i₁ i₂ := hc _ (hi₁.isClassicalSL2 h2).mem _ (hi₂.isClassicalSL2 h2).mem
    exact hi₁.form_eq_zero_of_commute h2 hi₂ hcomm hne' (hm₁ ▸ hu) (hm₂ ▸ hv)
  · intro horth
    have hcomm : Commute i₁ i₂ :=
      (hi₁.commute_iff h2 hi₂).mpr (Or.inr fun u hu v hv => horth u (hm₁ ▸ hu) v (hm₂ ▸ hv))
    exact hi₁.commute_of_commute h2 hi₂ hcomm hne'

theorem exists_form_ne_zero_self {P : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P) :
    ∃ u ∈ P, ∃ v ∈ P, form u v ≠ 0 := by
  obtain ⟨u, w, huw, rfl⟩ := hP
  exact ⟨u, Submodule.subset_span (by simp), w, Submodule.subset_span (by simp), by
    rw [huw]; exact one_ne_zero⟩

theorem form_eq_zero_of_span_pair {u w x y : Fin n ⊕ Fin n → F} (h₁ : form x u = 0)
    (h₂ : form x w = 0) (h₃ : form y u = 0) (h₄ : form y w = 0) :
    ∀ a ∈ Submodule.span F {x, y}, ∀ b ∈ Submodule.span F {u, w}, form a b = 0 := by
  intro a ha b hb
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp ha
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hb
  simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, h₁, h₂, h₃, h₄]
  ring

theorem exists_separating_psp (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n)
    {P₀ P₁ : Submodule F (Fin n ⊕ Fin n → F)} (h₀ : IsHyperbolicPlane P₀)
    (h₁ : IsHyperbolicPlane P₁)
    (horth : ∀ u ∈ P₀, ∀ v ∈ P₁, form u v = 0) :
    ∃ S ∈ planeGroupSet F n, S ≠ planeGroup P₀ ∧ S ≠ planeGroup P₁ ∧
      Commutes S (planeGroup P₀) ∧ ¬ Commutes S (planeGroup P₁) := by
  obtain ⟨u₀, w₀, h₀₁, rfl⟩ := h₀
  obtain ⟨u₁, w₁, h₁₁, rfl⟩ := h₁
  have hdim : Module.finrank F (Fin n ⊕ Fin n → F) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; ring
  let ℓ : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin 4 → F) :=
    LinearMap.pi ![symplFormLeft u₀, symplFormLeft w₀, symplFormLeft u₁, symplFormLeft w₁]
  have hker : LinearMap.ker ℓ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [Module.finrank_fin_fun, hdim]; omega)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hr' : ∀ j, ℓ r j = 0 := fun j => by rw [LinearMap.mem_ker.mp hr]; rfl
  have r₁ : form r u₀ = 0 := hr' 0
  have r₂ : form r w₀ = 0 := hr' 1
  have r₃ : form r u₁ = 0 := hr' 2
  have r₄ : form r w₁ = 0 := hr' 3
  have o₁ : form u₁ u₀ = 0 := by
    rw [form_antisymm]; simpa using horth u₀ (Submodule.subset_span (by simp)) u₁
      (Submodule.subset_span (by simp))
  have o₂ : form u₁ w₀ = 0 := by
    rw [form_antisymm]; simpa using horth w₀ (Submodule.subset_span (by simp)) u₁
      (Submodule.subset_span (by simp))
  have o₃ : form w₁ u₀ = 0 := by
    rw [form_antisymm]; simpa using horth u₀ (Submodule.subset_span (by simp)) w₁
      (Submodule.subset_span (by simp))
  have o₄ : form w₁ w₀ = 0 := by
    rw [form_antisymm]; simpa using horth w₀ (Submodule.subset_span (by simp)) w₁
      (Submodule.subset_span (by simp))
  have hP : IsHyperbolicPlane (Submodule.span F {u₁ + r, w₁}) :=
    ⟨u₁ + r, w₁, by rw [form_add_left, h₁₁, r₄, add_zero], rfl⟩
  have hPorth : ∀ a ∈ Submodule.span F {u₁ + r, w₁}, ∀ b ∈ Submodule.span F {u₀, w₀},
      form a b = 0 :=
    form_eq_zero_of_span_pair (by rw [form_add_left, o₁, r₁, add_zero]) (by
      rw [form_add_left, o₂, r₂, add_zero]) o₃ o₄
  have hP₀ : IsHyperbolicPlane (Submodule.span F {u₀, w₀}) := ⟨u₀, w₀, h₀₁, rfl⟩
  have hP₁ : IsHyperbolicPlane (Submodule.span F {u₁, w₁}) := ⟨u₁, w₁, h₁₁, rfl⟩
  have hne₀ : Submodule.span F {u₁ + r, w₁} ≠ Submodule.span F {u₀, w₀} := by
    intro heq
    obtain ⟨a, ha, b, hb, hab⟩ := exists_form_ne_zero_self hP₀
    exact hab (hPorth a (heq ▸ ha) b hb)
  have hne₁ : Submodule.span F {u₁ + r, w₁} ≠ Submodule.span F {u₁, w₁} := by
    intro heq
    have hmem : u₁ + r ∈ Submodule.span F {u₁, w₁} :=
      heq ▸ Submodule.subset_span (by simp)
    have hrm : r ∈ Submodule.span F {u₁, w₁} := by
      have := Submodule.sub_mem _ hmem (Submodule.subset_span (by simp : u₁ ∈ ({u₁, w₁} : Set _)))
      simpa using this
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hrm
    have e1 : form r w₁ = s := by
      rw [← hst]; simp [form_add_left, form_smul_left, h₁₁, form_self]
    have e2 : form r u₁ = -t := by
      rw [← hst]
      have : form w₁ u₁ = -1 := by rw [form_antisymm, h₁₁]
      simp [form_add_left, form_smul_left, this, form_self]
    have hs : s = 0 := by rw [← e1, r₄]
    have ht : t = 0 := by
      have : -t = 0 := by rw [← e2, r₃]
      exact neg_eq_zero.mp this
    apply hr0
    rw [← hst, hs, ht]
    simp
  refine ⟨planeGroup (Submodule.span F {u₁ + r, w₁}), ⟨_, hP, rfl⟩,
    fun h => hne₀ (planeGroup_injective h2 hP hP₀ h),
    fun h => hne₁ (planeGroup_injective h2 hP hP₁ h), ?_, fun hc => ?_⟩
  · exact (commutes_planeGroup_iff h2 hP hP₀ hne₀).mpr hPorth
  · have := (commutes_planeGroup_iff h2 hP hP₁ hne₁).mp hc (u₁ + r)
      (Submodule.subset_span (by simp)) w₁ (Submodule.subset_span (by simp))
    rw [form_add_left, h₁₁, r₄, add_zero] at this
    exact one_ne_zero this

theorem false_of_orth_three_two {P₀ P₁ P₂ : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (h₀ : IsHyperbolicPlane P₀) (h₁ : IsHyperbolicPlane P₁) (h₂ : IsHyperbolicPlane P₂)
    (o01 : ∀ u ∈ P₀, ∀ v ∈ P₁, form u v = 0) (o02 : ∀ u ∈ P₀, ∀ v ∈ P₂, form u v = 0)
    (o12 : ∀ u ∈ P₁, ∀ v ∈ P₂, form u v = 0) : False := by
  have hd₀ := isHyperbolicPlane_iff.mp h₀
  have hd₁ := isHyperbolicPlane_iff.mp h₁
  have hinf : P₀ ⊓ P₁ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact hd₁.2 v hv.2 fun u hu => o01 v hv.1 u hu
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P₀ P₁
  rw [hinf, finrank_bot, hd₀.1, hd₁.1] at hsum
  have hV : Module.finrank F (Fin 2 ⊕ Fin 2 → F) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have htop : P₀ ⊔ P₁ = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hV]; omega)
  obtain ⟨u₂, w₂, h₂₁, rfl⟩ := h₂
  have hu₂ : u₂ ∈ P₀ ⊔ P₁ := htop ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hu₂
  have hw₂ : w₂ ∈ Submodule.span F {u₂, w₂} := Submodule.subset_span (by simp)
  have := o02 x hx w₂ hw₂
  have := o12 y hy w₂ hw₂
  rw [← hxy, form_add_left] at h₂₁
  simp_all

theorem psp_twinFamily (h2 : (2 : F) ≠ 0) (hn : 2 ≤ n) {a : ℕ} (ha : 2 ≤ a)
    (h : TwinFamily (planeGroupSet F n) a) : n = 2 ∧ a = 2 := by
  obtain ⟨R₀, R₁, hP⟩ := h.exists_two ha
  obtain ⟨⟨P₀, hP₀, rfl⟩, ⟨P₁, hP₁, rfl⟩, hne, hc, htw⟩ := hP
  have hne' : P₀ ≠ P₁ := fun e => hne (by rw [e])
  have horth := (commutes_planeGroup_iff h2 hP₀ hP₁ hne').mp hc
  have hn2 : n = 2 := by
    by_contra hn2
    obtain ⟨S, hS, hS0, hS1, hcS, hncS⟩ := exists_separating_psp h2 (by omega) hP₀ hP₁ horth
    exact hncS ((htw S hS hS0 hS1).mp hcS)
  refine ⟨hn2, ?_⟩
  by_contra ha2
  obtain ⟨R₀', R₁', R₂', ⟨⟨P₀, hP₀, rfl⟩, ⟨P₁, hP₁, rfl⟩, h01, c01, -⟩,
    ⟨-, ⟨P₂, hP₂, rfl⟩, h02, c02, -⟩, ⟨-, -, h12, c12, -⟩, -, -, -⟩ :=
    h.exists_three (by omega)
  subst hn2
  exact false_of_orth_three_two hP₀ hP₁ hP₂
    ((commutes_planeGroup_iff h2 hP₀ hP₁ (fun e => h01 (by rw [e]))).mp c01)
    ((commutes_planeGroup_iff h2 hP₀ hP₂ (fun e => h02 (by rw [e]))).mp c02)
    ((commutes_planeGroup_iff h2 hP₁ hP₂ (fun e => h12 (by rw [e]))).mp c12)

end Symplectic

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem modelTwinClass_psp (hp2 : p ≠ 2) {n a : ℕ} (hadm : StatedLieAdmissible .PSp n p f)
    (ha : 2 ≤ a) (h : ModelTwinClass p .PSp n f a) : n = 2 ∧ a = 2 := by
  have hF : TwinFamily (planeGroupSet (GaloisField p f) n) a := by
    rw [← fundamentalSubgroups_psp_eq hadm]
    exact h
  exact psp_twinFamily (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2)
    hadm.2.2.1 ha hF

end Model

end CFSG.ClassicalInvolution.RouteD.Exotic
