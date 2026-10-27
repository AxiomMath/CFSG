module

public import CFSG.LargeExtraspecial.OrthoF2Timmesfeld12
public import CFSG.LargeExtraspecial.S2OrthB1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
private theorem mem_perp_bot (v : V) : v ∈ S2.perp q (⊥ : Submodule (ZMod 2) V) := by
  rw [S2.perp_bot]
  exact Submodule.mem_top

theorem exists_omega_apply_eq (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    {x y : V} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxq : q x = 0) (hyq : q y = 0) :
    ∃ γ ∈ omegaGroup q hq, γ x = y := by
  obtain ⟨g, hg, hgx⟩ := S2.exists_mem_radGen_apply_eq hq (bot_inf_eq _)
    (by rw [S2.perp_bot, finrank_top, hV]; norm_num) (mem_perp_bot x) (mem_perp_bot y) hx0 hy0
    hxq hyq
  refine ⟨g, ?_, hgx⟩
  have h := S2.radGen_le_omegaFix hq ⊥ hg
  rwa [S2.omegaFix_bot] at h

theorem exists_omega_fix_apply_eq (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) {x y₁ y₂ : V} (hx0 : x ≠ 0) (hxq : q x = 0) (hy₁0 : y₁ ≠ 0)
    (hy₂0 : y₂ ≠ 0) (hy₁q : q y₁ = 0) (hy₂q : q y₂ = 0) (hy₁x : y₁ ≠ x) (hy₂x : y₂ ≠ x)
    (h₁ : polar q x y₁ = 0) (h₂ : polar q x y₂ = 0) :
    ∃ k ∈ omegaGroup q hq, k x = x ∧ k y₁ = y₂ := by
  obtain ⟨g, hg, hgx, hgy⟩ := S2.exists_mem_radGen_apply_eq_orth hq (bot_inf_eq _) (m := 4)
    (by norm_num) (by rw [S2.perp_bot, finrank_top, hV]) (mem_perp_bot x) (mem_perp_bot y₁)
    (mem_perp_bot x) (mem_perp_bot y₂) hx0 hy₁0 hx0 hy₂0 hxq hy₁q hxq hy₂q h₁ hy₁x h₂ hy₂x
  refine ⟨g, ?_, hgx, hgy⟩
  have h := S2.radGen_le_omegaFix hq ⊥ hg
  rwa [S2.omegaFix_bot] at h

theorem exists_conj_mem_pointRadical (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) {x : V} (hx0 : x ≠ 0) (hxq : q x = 0)
    {τ : V ≃ₗ[ZMod 2] V} (hτ : τ ∈ omegaGroup q hq) (hA : IsTypeA q τ 2) :
    ∃ m ∈ omegaGroup q hq, m * τ * m⁻¹ ∈ pointRadical q x := by
  have _ := hτ
  obtain ⟨a, u, hli, hspan⟩ := OrthoF2.exists_pair_of_finrank_eq_two hA.2.2.2.1
  obtain ⟨ha, -, hau, hτE⟩ := OrthoF2.eq_eichler_of_isTypeA hq hA hli hspan.symm
  obtain ⟨ha0, -, -⟩ := OrthoF2.linearIndependent_pair_iff.mp hli
  obtain ⟨m, hm, hma⟩ := exists_omega_apply_eq hq hV ha0 hx0 ha hxq
  refine ⟨m, hm, ?_⟩
  have hmO : m ∈ TauCeti.QuadraticMap.orthogonalGroup q := omegaGroup_le q hq hm
  rw [hτE, CFSG.ClassicalGroups.Orthogonal.eichler_conj hmO, hma]
  refine eichler_mem_pointRadical hxq ?_
  rw [← hma, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hmO, hau]

theorem eq_span_of_invariant (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    {x : V} (hx0 : x ≠ 0) (hxq : q x = 0) {D : Submodule (ZMod 2) V} (hxD : x ∈ D)
    (hD : ∀ v ∈ D, q v = 0)
    (hinv : ∀ k ∈ omegaGroup q hq, k x = x → ∀ v ∈ D, k v ∈ D) : D = (ZMod 2) ∙ x := by
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem x D).mpr hxD)
  intro d hd
  by_contra hdx
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ S2.perp q ⊥ = ⊥ := bot_inf_eq _
  obtain ⟨x₁, -, hx₁, hxx₁⟩ := S2.exists_hyperbolic_partner hq hF (mem_perp_bot x) hx0 hxq
  set F₁ : Submodule (ZMod 2) V :=
    (⊥ : Submodule (ZMod 2) V) ⊔ Submodule.span (ZMod 2) {x, x₁} with hF₁
  have hF₁0 : F₁ ⊓ S2.perp q F₁ = ⊥ :=
    S2.sup_span_pair_inf_perp_eq_bot hF (mem_perp_bot x) (mem_perp_bot x₁) hxx₁
  have hdim₁ : finrank (ZMod 2) (S2.perp q F₁) + 2 =
      finrank (ZMod 2) (S2.perp q (⊥ : Submodule (ZMod 2) V)) :=
    S2.finrank_perp_sup_span_pair hq hF (mem_perp_bot x) (mem_perp_bot x₁) hxx₁
  have hxF₁ : x ∈ F₁ := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hxd : polar q x d = 0 := by
    have h := hD (x + d) (D.add_mem hxD hd)
    rwa [map_add_eq, hD x hxD, hD d hd, zero_add, zero_add] at h
  have hd₀F₁ : d - polar q d x₁ • x ∈ S2.perp q F₁ := by
    have h := S2.sub_mem_perp_sup_span_pair (F := ⊥) (mem_perp_bot x) (mem_perp_bot x₁) hxx₁
      (mem_perp_bot d)
    rwa [polar_comm q d x, hxd, zero_smul, sub_zero] at h
  set d₀ : V := d - polar q d x₁ • x with hd₀
  have hd₀D : d₀ ∈ D := D.sub_mem hd (D.smul_mem _ hxD)
  have hd₀0 : d₀ ≠ 0 := by
    intro h
    rw [hd₀, sub_eq_zero] at h
    exact hdx (h ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
  have hd₀q : q d₀ = 0 := hD d₀ hd₀D
  obtain ⟨a, haF₁, haq, hd₀a⟩ := S2.exists_hyperbolic_partner hq hF₁0 hd₀F₁ hd₀0 hd₀q
  set F₂ : Submodule (ZMod 2) V := F₁ ⊔ Submodule.span (ZMod 2) {d₀, a} with hF₂
  have hF₂0 : F₂ ⊓ S2.perp q F₂ = ⊥ := S2.sup_span_pair_inf_perp_eq_bot hF₁0 hd₀F₁ haF₁ hd₀a
  have hdim₂ : finrank (ZMod 2) (S2.perp q F₂) + 2 = finrank (ZMod 2) (S2.perp q F₁) :=
    S2.finrank_perp_sup_span_pair hq hF₁0 hd₀F₁ haF₁ hd₀a
  have hdimV : finrank (ZMod 2) (S2.perp q (⊥ : Submodule (ZMod 2) V)) = 8 := by
    rw [S2.perp_bot, finrank_top, hV]
  obtain ⟨u₁, hu₁F, hu₁0, hu₁q⟩ := S2.exists_singular_mem_perp (q := q) (F := F₂) (by omega)
  obtain ⟨u₂, hu₂F, hu₂q, hu₁u₂⟩ := S2.exists_hyperbolic_partner hq hF₂0 hu₁F hu₁0 hu₁q
  have key : ∀ u ∈ S2.perp q F₂, q u = 0 → u ∈ D := by
    intro u huF hu
    obtain ⟨huF₁, hd₀u, hau⟩ := S2.mem_perp_sup_span_pair.mp huF
    have hxu : polar q x u = 0 := (S2.mem_perp.mp huF₁) x hxF₁
    have hxa : polar q x a = 0 := (S2.mem_perp.mp haF₁) x hxF₁
    have hkx : CFSG.ClassicalGroups.Orthogonal.eichler q a u x = x :=
      CFSG.ClassicalGroups.Orthogonal.eichler_apply_of_polar_eq_zero hxa hxu
    have hkd₀ : CFSG.ClassicalGroups.Orthogonal.eichler q a u d₀ = d₀ + u := by
      rw [eichler_apply_zmod2 haq hau, hd₀a, hd₀u, hu]
      simp
    have h := hinv _ (S2.eichler_mem_omegaGroup hq a u) hkx d₀ hd₀D
    rw [hkd₀] at h
    simpa using D.sub_mem h hd₀D
  have h := hD _ (D.add_mem (key u₁ hu₁F hu₁q) (key u₂ hu₂F hu₂q))
  rw [map_add_eq, hu₁q, hu₂q, hu₁u₂] at h
  simp at h

end CFSG.GF2Type.Smith1979.W4Insp
