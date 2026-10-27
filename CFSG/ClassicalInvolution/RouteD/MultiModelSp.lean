module

public import CFSG.ClassicalInvolution.RouteD.MultiModelLayer

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic

section Geometry

variable {F : Type} [Field F] {n : ℕ}

theorem form_zero_of_orth {P Q : Submodule F (Fin n ⊕ Fin n → F)}
    (h : ∀ u ∈ P, ∀ v ∈ Q, form u v = 0) {x y : Fin n ⊕ Fin n → F} (hx : x ∈ P) (hy : y ∈ Q) :
    form x y = 0 ∧ form y x = 0 :=
  ⟨h x hx y hy, by rw [form_antisymm, h x hx y hy, neg_zero]⟩

theorem exists_link_psp (h2 : (2 : F) ≠ 0) {P₀ P₁ P₂ : Submodule F (Fin n ⊕ Fin n → F)}
    (h₀ : IsHyperbolicPlane P₀) (h₁ : IsHyperbolicPlane P₁) (h₃ : IsHyperbolicPlane P₂)
    (o01 : ∀ u ∈ P₀, ∀ v ∈ P₁, form u v = 0) (o02 : ∀ u ∈ P₀, ∀ v ∈ P₂, form u v = 0)
    (o12 : ∀ u ∈ P₁, ∀ v ∈ P₂, form u v = 0) :
    ∃ S ∈ planeGroupSet F n, Commutes S (planeGroup P₀) ∧ ¬ Commutes S (planeGroup P₁) ∧
      ¬ Commutes S (planeGroup P₂) := by
  have hP₀ := h₀
  have hP₁ := h₁
  have hP₂ := h₃
  obtain ⟨u₀, w₀, h₀₁, rfl⟩ := h₀
  obtain ⟨u₁, w₁, h₁₁, rfl⟩ := h₁
  obtain ⟨u₂, w₂, h₂₁, rfl⟩ := h₃
  have mu₀ : u₀ ∈ Submodule.span F {u₀, w₀} := Submodule.subset_span (by simp)
  have mw₀ : w₀ ∈ Submodule.span F {u₀, w₀} := Submodule.subset_span (by simp)
  have mu₁ : u₁ ∈ Submodule.span F {u₁, w₁} := Submodule.subset_span (by simp)
  have mw₁ : w₁ ∈ Submodule.span F {u₁, w₁} := Submodule.subset_span (by simp)
  have mu₂ : u₂ ∈ Submodule.span F {u₂, w₂} := Submodule.subset_span (by simp)
  have mw₂ : w₂ ∈ Submodule.span F {u₂, w₂} := Submodule.subset_span (by simp)
  obtain ⟨a₁, a₁'⟩ := form_zero_of_orth o01 mu₀ mu₁
  obtain ⟨a₂, a₂'⟩ := form_zero_of_orth o01 mu₀ mw₁
  obtain ⟨a₃, a₃'⟩ := form_zero_of_orth o01 mw₀ mu₁
  obtain ⟨a₄, a₄'⟩ := form_zero_of_orth o01 mw₀ mw₁
  obtain ⟨b₁, b₁'⟩ := form_zero_of_orth o02 mu₀ mu₂
  obtain ⟨b₂, b₂'⟩ := form_zero_of_orth o02 mu₀ mw₂
  obtain ⟨b₃, b₃'⟩ := form_zero_of_orth o02 mw₀ mu₂
  obtain ⟨b₄, b₄'⟩ := form_zero_of_orth o02 mw₀ mw₂
  obtain ⟨c₁, c₁'⟩ := form_zero_of_orth o12 mu₁ mu₂
  obtain ⟨c₂, c₂'⟩ := form_zero_of_orth o12 mu₁ mw₂
  obtain ⟨c₃, c₃'⟩ := form_zero_of_orth o12 mw₁ mu₂
  obtain ⟨c₄, c₄'⟩ := form_zero_of_orth o12 mw₁ mw₂
  have hPh : IsHyperbolicPlane (Submodule.span F {u₁ + u₂, w₁}) :=
    ⟨u₁ + u₂, w₁, by rw [form_add_left, h₁₁, c₃', add_zero], rfl⟩
  have hPorth : ∀ a ∈ Submodule.span F {u₁ + u₂, w₁}, ∀ b ∈ Submodule.span F {u₀, w₀},
      form a b = 0 :=
    form_eq_zero_of_span_pair (by rw [form_add_left, a₁', b₁']; simp)
      (by rw [form_add_left, a₃', b₃']; simp) a₂' a₄'
  have hne₀ : Submodule.span F {u₁ + u₂, w₁} ≠ Submodule.span F {u₀, w₀} := by
    intro heq
    obtain ⟨a, ha, b, hb, hab⟩ := exists_form_ne_zero_self hP₀
    exact hab (hPorth a (heq ▸ ha) b hb)
  have key₁ : form (u₁ + u₂) w₁ = 1 := by rw [form_add_left, h₁₁, c₃', add_zero]
  have key₂ : form (u₁ + u₂) w₂ = 1 := by rw [form_add_left, c₂, h₂₁, zero_add]
  have mS₁ : u₁ + u₂ ∈ Submodule.span F {u₁ + u₂, w₁} := Submodule.subset_span (by simp)
  have mS₂ : w₁ ∈ Submodule.span F {u₁ + u₂, w₁} := Submodule.subset_span (by simp)
  have hne₁ : Submodule.span F {u₁ + u₂, w₁} ≠ Submodule.span F {u₁, w₁} := by
    intro heq
    have h1 : u₁ + u₂ ∈ Submodule.span F {u₁, w₁} := heq ▸ mS₁
    have h2' : u₂ ∈ Submodule.span F {u₁, w₁} := by
      have := Submodule.sub_mem _ h1 mu₁
      simpa using this
    have := (form_zero_of_orth o12 h2' mw₂).1
    rw [h₂₁] at this
    exact one_ne_zero this
  have hne₂ : Submodule.span F {u₁ + u₂, w₁} ≠ Submodule.span F {u₂, w₂} := by
    intro heq
    have h1 : u₁ + u₂ ∈ Submodule.span F {u₂, w₂} := heq ▸ mS₁
    have h3 : w₁ ∈ Submodule.span F {u₂, w₂} := heq ▸ mS₂
    have h4 : u₁ ∈ Submodule.span F {u₂, w₂} := by
      have := Submodule.sub_mem _ h1 mu₂
      simpa using this
    have := (form_zero_of_orth o12 mu₁ h3).1
    rw [h₁₁] at this
    exact one_ne_zero this
  refine ⟨planeGroup (Submodule.span F {u₁ + u₂, w₁}), ⟨_, hPh, rfl⟩,
    (commutes_planeGroup_iff h2 hPh hP₀ hne₀).mpr hPorth, fun hc => ?_, fun hc => ?_⟩
  · have := (commutes_planeGroup_iff h2 hPh hP₁ hne₁).mp hc (u₁ + u₂) mS₁ w₁ mw₁
    rw [key₁] at this
    exact one_ne_zero this
  · have := (commutes_planeGroup_iff h2 hPh hP₂ hne₂).mp hc (u₁ + u₂) mS₁ w₂ mw₂
    rw [key₂] at this
    exact one_ne_zero this

theorem eq_of_orth_orth_two {P₀ P₁ P₂ : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (h₀ : IsHyperbolicPlane P₀) (h₁ : IsHyperbolicPlane P₁) (h₃ : IsHyperbolicPlane P₂)
    (o01 : ∀ u ∈ P₀, ∀ v ∈ P₁, form u v = 0) (o02 : ∀ u ∈ P₀, ∀ v ∈ P₂, form u v = 0) :
    P₁ = P₂ := by
  have hd₀ := isHyperbolicPlane_iff.mp h₀
  have hd₁ := isHyperbolicPlane_iff.mp h₁
  have hd₂ := isHyperbolicPlane_iff.mp h₃
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
  have hle : P₂ ≤ P₁ := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : v ∈ P₀ ⊔ P₁)
    have ha0 : a = 0 := by
      refine hd₀.2 a ha fun c hc => ?_
      have h1 := (form_zero_of_orth o02 hc hv).1
      rw [form_add_right] at h1
      have h2 := (form_zero_of_orth o01 hc hb).1
      rw [h2, add_zero] at h1
      rw [form_antisymm, h1, neg_zero]
    rw [ha0, zero_add]
    exact hb
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hd₁.1, hd₂.1])).symm

end Geometry

section Model

variable {p : ℕ} [Fact p.Prime]

theorem mem_modelFund_psp_iff {n e : ℕ} (hadm : StatedLieAdmissible .PSp n p e)
    (R : Subgroup (modelUniv .PSp n p e Fact.out).K) :
    R ∈ ModelFund p .PSp n e ↔ R ∈ planeGroupSet (GaloisField p e) n := by
  show R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D ↔ _
  rw [fundamentalSubgroups_psp_eq hadm]
  exact Iff.rfl

theorem linkedIn_modelFund_psp {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSp n p e) {R R₁ R₂ : Subgroup (modelUniv .PSp n p e Fact.out).K}
    (hR : R ∈ ModelFund p .PSp n e) (hR₁ : R₁ ∈ ModelFund p .PSp n e)
    (hR₂ : R₂ ∈ ModelFund p .PSp n e) (c₁ : Commutes R R₁) (c₂ : Commutes R R₂)
    (c₃ : Commutes R₁ R₂) : LinkedIn (ModelFund p .PSp n e) R R₁ R₂ := by
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hnab := fun {S} (hS : S ∈ ModelFund p .PSp n e) =>
    not_commutes_self_modelFund hp2 (show IsFundTag .PSp from trivial) hq hadm hS
  have hR' := (mem_modelFund_psp_iff hadm R).mp hR
  have hR₁' := (mem_modelFund_psp_iff hadm R₁).mp hR₁
  have hR₂' := (mem_modelFund_psp_iff hadm R₂).mp hR₂
  obtain ⟨P₀, hP₀, rfl⟩ := hR'
  obtain ⟨P₁, hP₁, rfl⟩ := hR₁'
  obtain ⟨P₂, hP₂, rfl⟩ := hR₂'
  have n01 : P₀ ≠ P₁ := fun e' => hnab hR (e' ▸ c₁)
  have n02 : P₀ ≠ P₂ := fun e' => hnab hR (e' ▸ c₂)
  have n12 : P₁ ≠ P₂ := fun e' => hnab hR₁ (e' ▸ c₃)
  obtain ⟨S, hS, sc, sn₁, sn₂⟩ := exists_link_psp h2 hP₀ hP₁ hP₂
    ((commutes_planeGroup_iff h2 hP₀ hP₁ n01).mp c₁) ((commutes_planeGroup_iff h2 hP₀ hP₂ n02).mp c₂)
    ((commutes_planeGroup_iff h2 hP₁ hP₂ n12).mp c₃)
  have hSF : S ∈ ModelFund p .PSp n e := (mem_modelFund_psp_iff hadm S).mpr hS
  exact (Relation.ReflTransGen.single ⟨hR₁, hSF, c₁.symm, sc, fun h => sn₁ h.symm⟩).tail
    ⟨hSF, hR₂, sc, c₂.symm, sn₂⟩

theorem eq_of_commutes_commutes_psp_two {e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSp 2 p e) {R R₁ R₂ : Subgroup (modelUniv .PSp 2 p e Fact.out).K}
    (hR : R ∈ ModelFund p .PSp 2 e) (hR₁ : R₁ ∈ ModelFund p .PSp 2 e)
    (hR₂ : R₂ ∈ ModelFund p .PSp 2 e) (c₁ : Commutes R R₁) (c₂ : Commutes R R₂) : R₁ = R₂ := by
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hnab := fun {S} (hS : S ∈ ModelFund p .PSp 2 e) =>
    not_commutes_self_modelFund hp2 (show IsFundTag .PSp from trivial) hq hadm hS
  obtain ⟨P₀, hP₀, rfl⟩ := (mem_modelFund_psp_iff hadm R).mp hR
  obtain ⟨P₁, hP₁, rfl⟩ := (mem_modelFund_psp_iff hadm R₁).mp hR₁
  obtain ⟨P₂, hP₂, rfl⟩ := (mem_modelFund_psp_iff hadm R₂).mp hR₂
  have n01 : P₀ ≠ P₁ := fun e' => hnab hR (e' ▸ c₁)
  have n02 : P₀ ≠ P₂ := fun e' => hnab hR (e' ▸ c₂)
  rw [eq_of_orth_orth_two hP₀ hP₁ hP₂ ((commutes_planeGroup_iff h2 hP₀ hP₁ n01).mp c₁)
    ((commutes_planeGroup_iff h2 hP₀ hP₂ n02).mp c₂)]

end Model

end CFSG.ClassicalInvolution.RouteD
