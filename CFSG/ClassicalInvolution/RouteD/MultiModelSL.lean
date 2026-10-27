module

public import CFSG.ClassicalInvolution.RouteD.MultiModelLayer

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic Module
open scoped MatrixGroups

section Geometry

variable {F : Type} [Field F] {n : ℕ}

theorem isLongRootSL2_eq_of_involution_eq (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n}
    {L₁ L₂ : Subgroup SL(n, F)} {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (h : i₁ = i₂) : L₁ = L₂ := by
  subst h
  rw [h₁.eq_longRootGroup h2, h₂.eq_longRootGroup h2]

theorem involution_eq_of_eigenspaces (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} {L₁ : Subgroup SL(n, F)}
    {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁) (hm : minusSpace i₁ = minusSpace i₂)
    (hf : fixSpace i₁ = fixSpace i₂) : i₁ = i₂ := by
  have c₁ := h₁.isCompl h2
  apply Subtype.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    (c₁.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule F (Fin n → F))))
  have e1a := mem_minusSpace.mp ha
  have e1b := mem_fixSpace.mp hb
  have e2a := mem_minusSpace.mp (hm ▸ ha)
  have e2b := mem_fixSpace.mp (hf ▸ hb)
  simp only [Matrix.mulVec_add, e1a, e1b, e2a, e2b]

theorem isLongRootSL2_eq_of_two (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn2 : n = 2)
    {L₁ L₂ : Subgroup SL(n, F)} {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) : L₁ = L₂ := by
  have key : ∀ {L : Subgroup SL(n, F)} {i : SL(n, F)}, IsLongRootSL2 hn L i →
      minusSpace i = ⊤ ∧ fixSpace i = ⊥ := by
    intro L i h
    have hf := finrank_fixSpace_of_isLongRootSL2 h2 h
    have hv := h.finrank_minusSpace h2
    refine ⟨Submodule.eq_top_of_finrank_eq (by rw [hv, Module.finrank_fin_fun]; omega), ?_⟩
    exact Submodule.finrank_eq_zero.mp (by omega)
  obtain ⟨a₁, b₁⟩ := key h₁
  obtain ⟨a₂, b₂⟩ := key h₂
  exact isLongRootSL2_eq_of_involution_eq h2 h₁ h₂ (involution_eq_of_eigenspaces h2 h₁ (a₁.trans a₂.symm)
    (b₁.trans b₂.symm))

theorem exists_link_sl (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₀ L₁ L₂ : Subgroup SL(n, F)} {i₀ i₁ i₂ : SL(n, F)} (h₀ : IsLongRootSL2 hn L₀ i₀)
    (h₁ : IsLongRootSL2 hn L₁ i₁) (h₃ : IsLongRootSL2 hn L₂ i₂) (n01 : L₀ ≠ L₁) (n02 : L₀ ≠ L₂)
    (n12 : L₁ ≠ L₂) (c01 : Commutes L₀ L₁) (c02 : Commutes L₀ L₂) (c12 : Commutes L₁ L₂) :
    ∃ S ∈ longRootSet (K := F) hn, Commutes S L₀ ∧ ¬ Commutes S L₁ ∧ ¬ Commutes S L₂ := by
  obtain ⟨le01, le10, hb01⟩ := le_of_commutes h2 hn3 h₀ h₁ n01 c01
  obtain ⟨le02, le20, hb02⟩ := le_of_commutes h2 hn3 h₀ h₃ n02 c02
  obtain ⟨le12, le21, hb12⟩ := le_of_commutes h2 hn3 h₁ h₃ n12 c12
  have c₁ := h₁.isCompl h2
  have c₂ := h₃.isCompl h2
  have hV₁W₁ : ∀ v, v ∈ minusSpace i₁ → v ∈ fixSpace i₁ → v = 0 := fun v h h' => by
    have : v ∈ minusSpace i₁ ⊓ fixSpace i₁ := ⟨h, h'⟩
    rwa [c₁.inf_eq_bot, Submodule.mem_bot] at this
  have hV₂W₂ : ∀ v, v ∈ minusSpace i₂ → v ∈ fixSpace i₂ → v = 0 := fun v h h' => by
    have : v ∈ minusSpace i₂ ⊓ fixSpace i₂ := ⟨h, h'⟩
    rwa [c₂.inf_eq_bot, Submodule.mem_bot] at this
  have hV₁V₂ : ∀ v, v ∈ minusSpace i₁ → v ∈ minusSpace i₂ → v = 0 := fun v h h' => by
    have : v ∈ minusSpace i₁ ⊓ minusSpace i₂ := ⟨h, h'⟩
    rwa [hb12, Submodule.mem_bot] at this
  obtain ⟨v₁, hv₁, hv₁0⟩ : ∃ v ∈ minusSpace i₁, v ≠ 0 := by
    have hpos : 0 < finrank F ↥(minusSpace i₁) := by rw [h₁.finrank_minusSpace h2]; norm_num
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨v, hv, fun e => hv0 (Subtype.ext e)⟩
  obtain ⟨r, hr, hr0⟩ : ∃ v ∈ minusSpace i₂, v ≠ 0 := by
    have hpos : 0 < finrank F ↥(minusSpace i₂) := by rw [h₃.finrank_minusSpace h2]; norm_num
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨v, hv, fun e => hv0 (Subtype.ext e)⟩
  have hnot : v₁ ∉ fixSpace i₁ := fun h => hv₁0 (hV₁W₁ v₁ hv₁ h)
  obtain ⟨φ₀, hφ₀, hφ₀'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  set φ : Module.Dual F (Fin n → F) := (φ₀ v₁)⁻¹ • φ₀ with hφdef
  have hφ1 : φ v₁ = 1 := by
    rw [hφdef, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀]
  have hφ0 : ∀ u ∈ fixSpace i₁, φ u = 0 := by
    intro u hu
    have : φ₀ u ∈ (fixSpace i₁).map φ₀ := ⟨u, hu, rfl⟩
    rw [hφ₀', Submodule.mem_bot] at this
    rw [hφdef, LinearMap.smul_apply, smul_eq_mul, this, mul_zero]
  have hφr : φ r = 0 := hφ0 r (le21 hr)
  obtain ⟨t, ht⟩ := exists_sl_transvection φ r hφr
  have hS : IsLongRootSL2 hn (L₁.map (MulAut.conj t).toMonoidHom) (t * i₁ * t⁻¹) := h₁.conj t
  have hVS : minusSpace (t * i₁ * t⁻¹) =
      (minusSpace i₁).map (Matrix.toLin' (t : Matrix (Fin n) (Fin n) F)) := minusSpace_conj t i₁
  have hWS : fixSpace (t * i₁ * t⁻¹) =
      (fixSpace i₁).map (Matrix.toLin' (t : Matrix (Fin n) (Fin n) F)) := fixSpace_conj t i₁
  have htv : ∀ x, Matrix.toLin' (t : Matrix (Fin n) (Fin n) F) x = x + φ x • r := fun x => by
    rw [Matrix.toLin'_apply]; exact ht x
  have hSle₀ : minusSpace (t * i₁ * t⁻¹) ≤ fixSpace i₀ := by
    rw [hVS]
    rintro _ ⟨v, hv, rfl⟩
    rw [htv]
    exact Submodule.add_mem _ (le10 hv) (Submodule.smul_mem _ _ (le20 hr))
  have h₀le : minusSpace i₀ ≤ fixSpace (t * i₁ * t⁻¹) := by
    rw [hWS]
    intro x hx
    refine ⟨x, le01 hx, ?_⟩
    rw [htv, hφ0 x (le01 hx), zero_smul, add_zero]
  have hv₁S : v₁ + r ∈ minusSpace (t * i₁ * t⁻¹) := by
    rw [hVS]
    refine ⟨v₁, hv₁, ?_⟩
    rw [htv, hφ1, one_smul]
  have hne₁ : L₁.map (MulAut.conj t).toMonoidHom ≠ L₁ := by
    intro heq
    have hS' : IsLongRootSL2 hn L₁ (t * i₁ * t⁻¹) := heq ▸ hS
    have hi := hS'.involution_unique h2 h₁
    rw [hi] at hv₁S
    have : r ∈ minusSpace i₁ := by
      have := Submodule.sub_mem _ hv₁S hv₁
      simpa using this
    exact hr0 (hV₁W₁ r this (le21 hr))
  have hne₂ : L₁.map (MulAut.conj t).toMonoidHom ≠ L₂ := by
    intro heq
    have hS' : IsLongRootSL2 hn L₂ (t * i₁ * t⁻¹) := heq ▸ hS
    have hi := hS'.involution_unique h2 h₃
    rw [hi] at hv₁S
    have : v₁ ∈ minusSpace i₂ := by
      have := Submodule.sub_mem _ hv₁S hr
      simpa using this
    exact hv₁0 (hV₁V₂ v₁ hv₁ this)
  refine ⟨_, ⟨_, hS⟩, commutes_of_le h2 hS h₀ hSle₀ h₀le, fun hcomm => ?_, fun hcomm => ?_⟩
  · have := ((commutes_iff_le h2 hn3 hS h₁ hne₁).mp hcomm).1 hv₁S
    have hr' : v₁ ∈ fixSpace i₁ := by
      have := Submodule.sub_mem _ this (le21 hr)
      simpa using this
    exact hv₁0 (hV₁W₁ v₁ hv₁ hr')
  · have := ((commutes_iff_le h2 hn3 hS h₃ hne₂).mp hcomm).1 hv₁S
    have hr' : r ∈ fixSpace i₂ := by
      have := Submodule.sub_mem _ this (le12 hv₁)
      simpa using this
    exact hr0 (hV₂W₂ r hr hr')

theorem eq_of_commutes_commutes_four (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn4 : n = 4)
    {L₀ L₁ L₂ : Subgroup SL(n, F)} {i₀ i₁ i₂ : SL(n, F)} (h₀ : IsLongRootSL2 hn L₀ i₀)
    (h₁ : IsLongRootSL2 hn L₁ i₁) (h₃ : IsLongRootSL2 hn L₂ i₂) (n01 : L₀ ≠ L₁) (n02 : L₀ ≠ L₂)
    (c01 : Commutes L₀ L₁) (c02 : Commutes L₀ L₂) : L₁ = L₂ := by
  obtain ⟨le01, le10, -⟩ := le_of_commutes h2 (by omega) h₀ h₁ n01 c01
  obtain ⟨le02, le20, -⟩ := le_of_commutes h2 (by omega) h₀ h₃ n02 c02
  have hW0 := finrank_fixSpace_of_isLongRootSL2 h2 h₀
  have hW1 := finrank_fixSpace_of_isLongRootSL2 h2 h₁
  have hW2 := finrank_fixSpace_of_isLongRootSL2 h2 h₃
  have hV0 := h₀.finrank_minusSpace h2
  have hV1 := h₁.finrank_minusSpace h2
  have hV2 := h₃.finrank_minusSpace h2
  have e1 : minusSpace i₁ = fixSpace i₀ := Submodule.eq_of_le_of_finrank_eq le10 (by omega)
  have e2 : minusSpace i₂ = fixSpace i₀ := Submodule.eq_of_le_of_finrank_eq le20 (by omega)
  have f1 : fixSpace i₁ = minusSpace i₀ := (Submodule.eq_of_le_of_finrank_eq le01 (by omega)).symm
  have f2 : fixSpace i₂ = minusSpace i₀ := (Submodule.eq_of_le_of_finrank_eq le02 (by omega)).symm
  exact isLongRootSL2_eq_of_involution_eq h2 h₁ h₃ (involution_eq_of_eigenspaces h2 h₁ (e1.trans e2.symm)
    (f1.trans f2.symm))

end Geometry

section Model

variable {p : ℕ} [Fact p.Prime]

theorem mem_modelFund_psl_iff {m e : ℕ} (hm : 1 ≤ m)
    (R : Subgroup (modelUniv .PSL (m + 1) p e Fact.out).K) :
    R ∈ ModelFund p .PSL (m + 1) e ↔
      R ∈ longRootSet (K := GaloisField p e) (by omega : 2 ≤ m + 1) := by
  show R ∈ fundamentalSubgroups .PSL (modelUniv .PSL (m + 1) p e Fact.out).D ↔ _
  rw [fundamentalSubgroups_psl_eq hm]
  exact Iff.rfl

theorem linkedIn_modelFund_psl {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSL n p e) {R R₁ R₂ : Subgroup (modelUniv .PSL n p e Fact.out).K}
    (hR : R ∈ ModelFund p .PSL n e) (hR₁ : R₁ ∈ ModelFund p .PSL n e)
    (hR₂ : R₂ ∈ ModelFund p .PSL n e) (c₁ : Commutes R R₁) (c₂ : Commutes R R₂)
    (c₃ : Commutes R₁ R₂) : LinkedIn (ModelFund p .PSL n e) R R₁ R₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm : 1 ≤ m := by have := hadm.2.2.1; omega
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hnab := fun {S} (hS : S ∈ ModelFund p .PSL (m + 1) e) =>
    not_commutes_self_modelFund hp2 (show IsFundTag .PSL from trivial) hq hadm hS
  obtain ⟨i₀, h₀⟩ := (mem_modelFund_psl_iff hm R).mp hR
  obtain ⟨i₁, h₁⟩ := (mem_modelFund_psl_iff hm R₁).mp hR₁
  obtain ⟨i₂, h₂'⟩ := (mem_modelFund_psl_iff hm R₂).mp hR₂
  have n01 : R ≠ R₁ := fun e' => hnab hR (e' ▸ c₁)
  have n02 : R ≠ R₂ := fun e' => hnab hR (e' ▸ c₂)
  have n12 : R₁ ≠ R₂ := fun e' => hnab hR₁ (e' ▸ c₃)
  have hn3 : 3 ≤ m + 1 := by
    by_contra hlt
    exact n01 (isLongRootSL2_eq_of_two h2 (by have := hadm.2.2.1; omega) h₀ h₁)
  obtain ⟨S, hS, sc, sn₁, sn₂⟩ := exists_link_sl h2 hn3 h₀ h₁ h₂' n01 n02 n12 c₁ c₂ c₃
  have hSF : S ∈ ModelFund p .PSL (m + 1) e := (mem_modelFund_psl_iff hm S).mpr hS
  exact (Relation.ReflTransGen.single ⟨hR₁, hSF, c₁.symm, sc, fun h => sn₁ h.symm⟩).tail
    ⟨hSF, hR₂, sc, c₂.symm, sn₂⟩

theorem eq_of_commutes_commutes_psl_small {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSL n p e) (hn4 : n ≤ 4)
    {R R₁ R₂ : Subgroup (modelUniv .PSL n p e Fact.out).K} (hR : R ∈ ModelFund p .PSL n e)
    (hR₁ : R₁ ∈ ModelFund p .PSL n e) (hR₂ : R₂ ∈ ModelFund p .PSL n e) (c₁ : Commutes R R₁)
    (c₂ : Commutes R R₂) : R₁ = R₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm : 1 ≤ m := by have := hadm.2.2.1; omega
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hnab := fun {S} (hS : S ∈ ModelFund p .PSL (m + 1) e) =>
    not_commutes_self_modelFund hp2 (show IsFundTag .PSL from trivial) hq hadm hS
  obtain ⟨i₀, h₀⟩ := (mem_modelFund_psl_iff hm R).mp hR
  obtain ⟨i₁, h₁⟩ := (mem_modelFund_psl_iff hm R₁).mp hR₁
  obtain ⟨i₂, h₂'⟩ := (mem_modelFund_psl_iff hm R₂).mp hR₂
  have n01 : R ≠ R₁ := fun e' => hnab hR (e' ▸ c₁)
  have n02 : R ≠ R₂ := fun e' => hnab hR (e' ▸ c₂)
  by_cases hn2 : m + 1 = 2
  · exact isLongRootSL2_eq_of_two h2 hn2 h₁ h₂'
  have hn3 : 3 ≤ m + 1 := by have := hadm.2.2.1; omega
  have h4 := four_le_of_commutes h2 hn3 h₀ h₁ n01 c₁
  exact eq_of_commutes_commutes_four h2 (by omega) h₀ h₁ h₂' n01 n02 c₁ c₂

end Model

end CFSG.ClassicalInvolution.RouteD
