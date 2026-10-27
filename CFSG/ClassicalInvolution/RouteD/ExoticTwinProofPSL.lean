module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofBasic

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic Matrix Module
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Linear

variable {F : Type} [Field F] {n : ℕ}

theorem le_of_commutes (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup SL(n, F)}
    {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂ : IsLongRootSL2 hn L₂ i₂) (hne : L₁ ≠ L₂)
    (hc : Commutes L₁ L₂) :
    minusSpace i₁ ≤ fixSpace i₂ ∧ minusSpace i₂ ≤ fixSpace i₁ ∧
      minusSpace i₁ ⊓ minusSpace i₂ = ⊥ := by
  have hi : i₁ ≠ i₂ := by
    rintro rfl
    exact hne ((h₁.eq_longRootGroup h2).trans (h₂.eq_longRootGroup h2).symm)
  rcases lemma_6_5 h2 hn3 h₁ h₂ (hc _ h₁.mem _ h₂.mem) hi with ⟨-, h⟩ | ⟨hnot, -⟩
  · exact h
  · exact absurd (Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx i₂ h₂.mem) hnot

theorem commute_of_le (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} {L₁ L₂ : Subgroup SL(n, F)}
    {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂ : IsLongRootSL2 hn L₂ i₂)
    (h12 : minusSpace i₁ ≤ fixSpace i₂) (h21 : minusSpace i₂ ≤ fixSpace i₁) : Commute i₁ i₂ := by
  have c₁ := h₁.isCompl h2
  have c₂ := h₂.isCompl h2
  have hmul : ∀ v : Fin n → F, ((i₁ * i₂ : SL(n, F)) : Matrix (Fin n) (Fin n) F) *ᵥ v =
      ((i₂ * i₁ : SL(n, F)) : Matrix (Fin n) (Fin n) F) *ᵥ v := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
      (c₁.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule F (Fin n → F))))
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp
      (c₂.sup_eq_top ▸ (Submodule.mem_top : b ∈ (⊤ : Submodule F (Fin n → F))))
    have hd1 : d ∈ fixSpace i₁ := by
      have := Submodule.sub_mem _ hb (h21 hc)
      simpa using this
    have e1a := mem_minusSpace.mp ha
    have e2a := mem_fixSpace.mp (h12 ha)
    have e2c := mem_minusSpace.mp hc
    have e1c := mem_fixSpace.mp (h21 hc)
    have e1d := mem_fixSpace.mp hd1
    have e2d := mem_fixSpace.mp hd
    simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
      e1a, e2a, e2c, e1c, e1d, e2d, Matrix.mulVec_neg]
  apply Subtype.ext
  rw [Matrix.ext_iff_mulVec]
  exact hmul

theorem commutes_of_le (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} {L₁ L₂ : Subgroup SL(n, F)}
    {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂ : IsLongRootSL2 hn L₂ i₂)
    (h12 : minusSpace i₁ ≤ fixSpace i₂) (h21 : minusSpace i₂ ≤ fixSpace i₁) : Commutes L₁ L₂ := by
  have hcc : (i₁ : Matrix (Fin n) (Fin n) F) * i₂ = i₂ * i₁ := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      (commute_of_le h2 h₁ h₂ h12 h21).eq]
  have hV : minusSpace i₁ ⊓ minusSpace i₂ = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rintro v ⟨hv1, hv2⟩
    have : v ∈ minusSpace i₁ ⊓ fixSpace i₁ := ⟨hv1, h21 hv2⟩
    rwa [(h₁.isCompl h2).inf_eq_bot] at this
  intro x hx y hy
  rw [h₁.eq_longRootGroup h2] at hx
  rw [h₂.eq_longRootGroup h2] at hy
  exact mul_comm_of_inf_eq_bot h2 h₁.coe_mul_self h₂.coe_mul_self hcc hV hx hy

theorem commutes_iff_le (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup SL(n, F)}
    {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂ : IsLongRootSL2 hn L₂ i₂)
    (hne : L₁ ≠ L₂) :
    Commutes L₁ L₂ ↔ minusSpace i₁ ≤ fixSpace i₂ ∧ minusSpace i₂ ≤ fixSpace i₁ :=
  ⟨fun hc => ⟨(le_of_commutes h2 hn3 h₁ h₂ hne hc).1, (le_of_commutes h2 hn3 h₁ h₂ hne hc).2.1⟩,
    fun h => commutes_of_le h2 h₁ h₂ h.1 h.2⟩

theorem finrank_fixSpace_of_isLongRootSL2 (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup SL(n, F)} {i : SL(n, F)} (h : IsLongRootSL2 hn L i) :
    finrank F (fixSpace i) + 2 = n := by
  have := Submodule.finrank_add_eq_of_isCompl (h.isCompl h2)
  rw [Module.finrank_fin_fun, h.finrank_minusSpace h2] at this
  omega

theorem minusSpace_conj (t i : SL(n, F)) :
    minusSpace (t * i * t⁻¹) =
      (minusSpace i).map (Matrix.toLin' (t : Matrix (Fin n) (Fin n) F)) := by
  have e : ((t * i * t⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      (t : Matrix (Fin n) (Fin n) F) * (i : Matrix (Fin n) (Fin n) F) *
        ((t⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
  unfold minusSpace
  rw [e]
  exact eigSpace_conj t _ _

theorem fixSpace_conj (t i : SL(n, F)) :
    fixSpace (t * i * t⁻¹) = (fixSpace i).map (Matrix.toLin' (t : Matrix (Fin n) (Fin n) F)) := by
  have e : ((t * i * t⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      (t : Matrix (Fin n) (Fin n) F) * (i : Matrix (Fin n) (Fin n) F) *
        ((t⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
  unfold fixSpace
  rw [e]
  exact eigSpace_conj t _ _

theorem exists_sl_transvection (φ : Module.Dual F (Fin n → F)) (r : Fin n → F) (h : φ r = 0) :
    ∃ t : SL(n, F), ∀ x : Fin n → F, (t : Matrix (Fin n) (Fin n) F) *ᵥ x = x + φ x • r := by
  classical
  refine ⟨⟨LinearMap.toMatrix' (LinearMap.transvection φ r), ?_⟩, fun x => ?_⟩
  · rw [LinearMap.det_toMatrix', LinearMap.transvection.det, h, add_zero]
  · show LinearMap.toMatrix' (LinearMap.transvection φ r) *ᵥ x = _
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    exact LinearMap.transvection.apply φ r x

theorem four_le_of_commutes (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup SL(n, F)} {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hne : L₁ ≠ L₂) (hc : Commutes L₁ L₂) : 4 ≤ n := by
  obtain ⟨-, -, hbot⟩ := le_of_commutes h2 hn3 h₁ h₂ hne hc
  have h := Submodule.finrank_sup_add_finrank_inf_eq (minusSpace i₁) (minusSpace i₂)
  rw [hbot, finrank_bot, h₁.finrank_minusSpace h2, h₂.finrank_minusSpace h2] at h
  have hle := Submodule.finrank_le (minusSpace i₁ ⊔ minusSpace i₂)
  rw [Module.finrank_fin_fun] at hle
  omega

theorem false_of_commutes_three_four (h2 : (2 : F) ≠ 0) {hn : 2 ≤ 4} {L₀ L₁ L₂ : Subgroup SL(4, F)}
    {i₀ i₁ i₂ : SL(4, F)} (h₀ : IsLongRootSL2 hn L₀ i₀) (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂' : IsLongRootSL2 hn L₂ i₂) (h01 : L₀ ≠ L₁) (h02 : L₀ ≠ L₂) (h12 : L₁ ≠ L₂)
    (c01 : Commutes L₀ L₁) (c02 : Commutes L₀ L₂) (c12 : Commutes L₁ L₂) : False := by
  obtain ⟨le01, le10, hb01⟩ := le_of_commutes h2 (by omega) h₀ h₁ h01 c01
  obtain ⟨le02, le20, hb02⟩ := le_of_commutes h2 (by omega) h₀ h₂' h02 c02
  obtain ⟨le12, le21, hb12⟩ := le_of_commutes h2 (by omega) h₁ h₂' h12 c12
  have hW0 := finrank_fixSpace_of_isLongRootSL2 h2 h₀
  have hW1 := finrank_fixSpace_of_isLongRootSL2 h2 h₁
  have hV0 := h₀.finrank_minusSpace h2
  have hV1 := h₁.finrank_minusSpace h2
  have hV2 := h₂'.finrank_minusSpace h2
  have e0 : minusSpace i₁ = fixSpace i₀ :=
    Submodule.eq_of_le_of_finrank_eq le10 (by omega)
  have e1 : minusSpace i₀ = fixSpace i₁ :=
    Submodule.eq_of_le_of_finrank_eq le01 (by omega)
  have hle : minusSpace i₂ ≤ minusSpace i₀ ⊓ minusSpace i₁ :=
    le_inf (by rw [e1]; exact le21) (by rw [e0]; exact le20)
  rw [hb01, le_bot_iff] at hle
  rw [hle, finrank_bot] at hV2
  omega

theorem exists_separating (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn5 : 5 ≤ n) {L₀ L₁ : Subgroup SL(n, F)}
    {i₀ i₁ : SL(n, F)} (h₀ : IsLongRootSL2 hn L₀ i₀) (h₁ : IsLongRootSL2 hn L₁ i₁)
    (hne : L₀ ≠ L₁) (hc : Commutes L₀ L₁) :
    ∃ S ∈ longRootSet (K := F) hn, S ≠ L₀ ∧ S ≠ L₁ ∧ Commutes S L₀ ∧ ¬ Commutes S L₁ := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨le01, le10, hbot⟩ := le_of_commutes h2 hn3 h₀ h₁ hne hc
  have c₀ := h₀.isCompl h2
  have c₁ := h₁.isCompl h2
  obtain ⟨r, hr, hr0⟩ : ∃ r ∈ fixSpace i₀ ⊓ fixSpace i₁, r ≠ 0 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace i₀) (fixSpace i₁)
    have hle := Submodule.finrank_le (fixSpace i₀ ⊔ fixSpace i₁)
    rw [Module.finrank_fin_fun] at hle
    have hW0 := finrank_fixSpace_of_isLongRootSL2 h2 h₀
    have hW1 := finrank_fixSpace_of_isLongRootSL2 h2 h₁
    have hpos : 0 < finrank F ↥(fixSpace i₀ ⊓ fixSpace i₁) := by omega
    obtain ⟨⟨r, hr⟩, hr0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨r, hr, fun e => hr0 (Subtype.ext e)⟩
  obtain ⟨v₁, hv₁, hv₁0⟩ : ∃ v ∈ minusSpace i₁, v ≠ 0 := by
    have hpos : 0 < finrank F ↥(minusSpace i₁) := by rw [h₁.finrank_minusSpace h2]; norm_num
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨v, hv, fun e => hv0 (Subtype.ext e)⟩
  have hV₁W₁ : ∀ v, v ∈ minusSpace i₁ → v ∈ fixSpace i₁ → v = 0 := fun v h h' => by
    have : v ∈ minusSpace i₁ ⊓ fixSpace i₁ := ⟨h, h'⟩
    rwa [c₁.inf_eq_bot, Submodule.mem_bot] at this
  have hV₀W₀ : ∀ v, v ∈ minusSpace i₀ → v ∈ fixSpace i₀ → v = 0 := fun v h h' => by
    have : v ∈ minusSpace i₀ ⊓ fixSpace i₀ := ⟨h, h'⟩
    rwa [c₀.inf_eq_bot, Submodule.mem_bot] at this
  have hnot : v₁ ∉ minusSpace i₀ ⊔ Submodule.span F {r} := by
    intro hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have haW : a ∈ fixSpace i₀ := by
      have h1 : a = v₁ - c • r := by rw [← hab]; abel
      rw [h1]
      exact Submodule.sub_mem _ (le10 hv₁) (Submodule.smul_mem _ _ hr.1)
    have ha0 := hV₀W₀ a ha haW
    rw [ha0, zero_add] at hab
    have : v₁ ∈ fixSpace i₁ := by rw [← hab]; exact Submodule.smul_mem _ _ hr.2
    exact hv₁0 (hV₁W₁ v₁ hv₁ this)
  obtain ⟨φ₀, hφ₀, hφ₀'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  set φ : Module.Dual F (Fin n → F) := (φ₀ v₁)⁻¹ • φ₀ with hφdef
  have hφ1 : φ v₁ = 1 := by
    rw [hφdef, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀]
  have hφ0 : ∀ u ∈ minusSpace i₀ ⊔ Submodule.span F {r}, φ u = 0 := by
    intro u hu
    have : φ₀ u ∈ (minusSpace i₀ ⊔ Submodule.span F {r}).map φ₀ := ⟨u, hu, rfl⟩
    rw [hφ₀', Submodule.mem_bot] at this
    rw [hφdef, LinearMap.smul_apply, smul_eq_mul, this, mul_zero]
  have hφr : φ r = 0 := hφ0 r (Submodule.mem_sup_right (Submodule.mem_span_singleton_self r))
  have hφV₀ : ∀ u ∈ minusSpace i₀, φ u = 0 := fun u hu => hφ0 u (Submodule.mem_sup_left hu)
  obtain ⟨t, ht⟩ := exists_sl_transvection φ r hφr
  have hS : IsLongRootSL2 hn (L₁.map (MulAut.conj t).toMonoidHom) (t * i₁ * t⁻¹) := h₁.conj t
  have hVS : minusSpace (t * i₁ * t⁻¹) =
      (minusSpace i₁).map (Matrix.toLin' (t : Matrix (Fin n) (Fin n) F)) :=
    minusSpace_conj t i₁
  have hWS : fixSpace (t * i₁ * t⁻¹) =
      (fixSpace i₁).map (Matrix.toLin' (t : Matrix (Fin n) (Fin n) F)) :=
    fixSpace_conj t i₁
  have htv : ∀ x, Matrix.toLin' (t : Matrix (Fin n) (Fin n) F) x = x + φ x • r := fun x => by
    rw [Matrix.toLin'_apply]; exact ht x
  have hSle₀ : minusSpace (t * i₁ * t⁻¹) ≤ fixSpace i₀ := by
    rw [hVS]
    rintro _ ⟨v, hv, rfl⟩
    rw [htv]
    exact Submodule.add_mem _ (le10 hv) (Submodule.smul_mem _ _ hr.1)
  have h₀le : minusSpace i₀ ≤ fixSpace (t * i₁ * t⁻¹) := by
    rw [hWS]
    intro x hx
    refine ⟨x, le01 hx, ?_⟩
    rw [htv, hφV₀ x hx, zero_smul, add_zero]
  have htv₁ : Matrix.toLin' (t : Matrix (Fin n) (Fin n) F) v₁ = v₁ + r := by
    rw [htv, hφ1, one_smul]
  have hv₁S : v₁ + r ∈ minusSpace (t * i₁ * t⁻¹) := by
    rw [hVS]
    exact ⟨v₁, hv₁, htv₁⟩
  have hne₁ : L₁.map (MulAut.conj t).toMonoidHom ≠ L₁ := by
    intro heq
    have hS' : IsLongRootSL2 hn L₁ (t * i₁ * t⁻¹) := heq ▸ hS
    have hi := hS'.involution_unique h2 h₁
    rw [hi] at hv₁S
    have : r ∈ minusSpace i₁ := by
      have := Submodule.sub_mem _ hv₁S hv₁
      simpa using this
    exact hr0 (hV₁W₁ r this hr.2)
  have hne₀ : L₁.map (MulAut.conj t).toMonoidHom ≠ L₀ := by
    intro heq
    have hS' : IsLongRootSL2 hn L₀ (t * i₁ * t⁻¹) := heq ▸ hS
    have hi := hS'.involution_unique h2 h₀
    rw [hi] at hSle₀
    have hV := h₀.finrank_minusSpace h2
    have : minusSpace i₀ = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_bot]
      exact hV₀W₀ v hv (hSle₀ hv)
    rw [this, finrank_bot] at hV
    omega
  refine ⟨_, ⟨_, hS⟩, hne₀, hne₁, commutes_of_le h2 hS h₀ hSle₀ h₀le, fun hcomm => ?_⟩
  have := ((commutes_iff_le h2 hn3 hS h₁ hne₁).mp hcomm).1 hv₁S
  have hr' : v₁ ∈ fixSpace i₁ := by
    have := Submodule.sub_mem _ this hr.2
    simpa using this
  exact hv₁0 (hV₁W₁ v₁ hv₁ hr')

theorem psl_twinFamily (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n) {a : ℕ} (ha : 2 ≤ a)
    (h : TwinFamily (longRootSet (K := F) hn) a) : n = 4 ∧ a = 2 := by
  obtain ⟨R₀, R₁, hP⟩ := h.exists_two ha
  obtain ⟨⟨i₀, h₀⟩, ⟨i₁, h₁⟩, hne, hc, htw⟩ := hP
  have h4 := four_le_of_commutes h2 hn3 h₀ h₁ hne hc
  have hn4 : n = 4 := by
    by_contra hn4
    obtain ⟨S, hS, hS0, hS1, hcS, hncS⟩ := exists_separating h2 (by omega) h₀ h₁ hne hc
    exact hncS ((htw S hS hS0 hS1).mp hcS)
  refine ⟨hn4, ?_⟩
  by_contra ha2
  obtain ⟨R₀', R₁', R₂', ⟨⟨i₀, h₀⟩, ⟨i₁, h₁⟩, h01, c01, -⟩, ⟨-, ⟨i₂, h₂'⟩, h02, c02, -⟩,
    ⟨-, -, h12, c12, -⟩, -, -, -⟩ := h.exists_three (by omega)
  subst hn4
  exact false_of_commutes_three_four h2 h₀ h₁ h₂' h01 h02 h12 c01 c02 c12

end Linear

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem fundamentalSubgroups_psl_eq {m : ℕ} (hm : 1 ≤ m) :
    fundamentalSubgroups .PSL (modelUniv .PSL (m + 1) p f Fact.out).D =
      longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1) :=
  Set.Subset.antisymm (fundamentalSubgroups_psl_subset _)
    (longRootSet_subset_fundamentalSubgroups_psl _)

theorem modelTwinClass_psl (hp2 : p ≠ 2) {n a : ℕ} (hn3 : 3 ≤ n) (ha : 2 ≤ a)
    (h : ModelTwinClass p .PSL n f a) : n = 4 ∧ a = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hF : TwinFamily (longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1)) a := by
    rw [← fundamentalSubgroups_psl_eq (p := p) (f := f) (by omega : 1 ≤ m)]
    exact h
  exact psl_twinFamily (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2) hn3 ha hF

end Model

end CFSG.ClassicalInvolution.RouteD.Exotic
