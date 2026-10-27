module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModA
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LE25Shape

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Mod

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y]
  {ρ : Y →* (V ≃ₗ[ZMod 2] V)} {t u x h : Y}

theorem caseA_hA6 (H : HypYW ρ t u x h)
    (e : normalClosure ({x} : Set Y) ≃* alternatingGroup (Fin 6)) :
    Nonempty (Jbar ρ x ≃* alternatingGroup (Fin 6)) :=
  ⟨(Subgroup.equivMapOfInjective _ ρ H.inj).symm.trans e⟩

theorem caseA_centralizer (H : HypYW ρ t u x h)
    (hcen : centralizer ((Jbar ρ x : Subgroup (V ≃ₗ[ZMod 2] V)) : Set (V ≃ₗ[ZMod 2] V)) = ⊥)
    {c : Y} (hc : ∀ j ∈ normalClosure ({x} : Set Y), c * j = j * c) : c = 1 := by
  have h1 : ρ c ∈ centralizer ((Jbar ρ x : Subgroup (V ≃ₗ[ZMod 2] V)) :
      Set (V ≃ₗ[ZMod 2] V)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, hc j hj]
  rw [hcen, Subgroup.mem_bot] at h1
  exact H.inj (h1.trans (map_one ρ).symm)

theorem caseA_eq_one_of_fix (H : HypYW ρ t u x h)
    (hcen : ∀ c : Y, (∀ j ∈ normalClosure ({x} : Set Y), c * j = j * c) → c = 1)
    {M : Submodule (ZMod 2) V} (hst : ∀ g ∈ Jbar ρ x, Stable g M)
    (hfa : ∀ g ∈ Jbar ρ x, (∀ v ∈ M, g v = v) → g = 1) {n : Y} (hn : ∀ v ∈ M, ρ n v = v) :
    n = 1 := by
  apply hcen
  intro j hj
  have hc : n * j * n⁻¹ * j⁻¹ ∈ normalClosure ({x} : Set Y) :=
    (normalClosure ({x} : Set Y)).mul_mem
      ((normalClosure_normal (s := ({x} : Set Y))).conj_mem j hj n) ((normalClosure ({x} :
        Set Y)).inv_mem hj)
  have hρc : ρ (n * j * n⁻¹ * j⁻¹) ∈ Jbar ρ x := Subgroup.mem_map_of_mem ρ hc
  have hρj : ρ j⁻¹ ∈ Jbar ρ x := Subgroup.mem_map_of_mem ρ ((normalClosure ({x} :
    Set Y)).inv_mem hj)
  have hn' : ∀ w ∈ M, (ρ n)⁻¹ w = w := fun w hw => by
    have := hn w hw
    calc (ρ n)⁻¹ w = (ρ n)⁻¹ (ρ n w) := by rw [this]
      _ = w := by simp
  have h1 : ρ (n * j * n⁻¹ * j⁻¹) = 1 := by
    refine hfa _ hρc fun v hv => ?_
    have hw : ρ j⁻¹ v ∈ M := hst _ hρj v hv
    have e1 : ρ (n * j * n⁻¹ * j⁻¹) v = ρ n (ρ j ((ρ n)⁻¹ (ρ j⁻¹ v))) := by
      simp only [map_mul, map_inv]
      rfl
    rw [e1, hn' _ hw]
    have e2 : ρ j (ρ j⁻¹ v) = v := by
      rw [map_inv]
      exact (ρ j).apply_symm_apply v
    rw [show ρ j (ρ j⁻¹ v) = v from e2]
    exact hn v hv
  have h2 : n * j * n⁻¹ * j⁻¹ = 1 := H.inj (h1.trans (map_one ρ).symm)
  calc n * j = (n * j * n⁻¹ * j⁻¹) * (j * n) := by group
    _ = j * n := by rw [h2, one_mul]

theorem caseA_map_not_stab {V₁ V₂ : Submodule (ZMod 2) V} (hc : IsCompl V₁ V₂)
    (hd₂ : finrank (ZMod 2) V₂ = 4) {g : V ≃ₗ[ZMod 2] V}
    (hg : V₁.map (g : V →ₗ[ZMod 2] V) = V₂) : g ∉ modA_stab V₁ := by
  intro hs
  have hle : V₂ ≤ V₁ := by
    rw [← hg]
    rintro _ ⟨v, hv, rfl⟩
    exact hs.1 v hv
  have hbot : V₂ = ⊥ := hc.disjoint.eq_bot_of_ge hle
  rw [hbot, finrank_bot] at hd₂
  exact absurd hd₂ (by norm_num)

end Mod

section Rank

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y]
  {ρ : Y →* (V ≃ₗ[ZMod 2] V)} {t u x h : Y}

theorem caseA_rk_restr_pos [Module.Finite (ZMod 2) V] (H : HypYW ρ t u x h)
    (hcen : ∀ c : Y, (∀ j ∈ normalClosure ({x} : Set Y), c * j = j * c) → c = 1)
    {M : Submodule (ZMod 2) V} (hst : ∀ g ∈ Jbar ρ x, Stable g M)
    (hfa : ∀ g ∈ Jbar ρ x, (∀ v ∈ M, g v = v) → g = 1) {g : Y} (hM : ρ g ∈ modA_stab M)
    (hg1 : g ≠ 1) : 1 ≤ rk (modA_restr M ⟨ρ g, hM⟩) := by
  by_contra hlt
  have h0 : rk (modA_restr M ⟨ρ g, hM⟩) = 0 := by omega
  have h1 := modA_eq_one_of_rk_zero h0
  apply hg1
  refine caseA_eq_one_of_fix H hcen hst hfa fun v hv => ?_
  have := congrArg (fun f : M ≃ₗ[ZMod 2] M => (f ⟨v, hv⟩ : V)) h1
  simpa [modA_restr_apply] using this

theorem caseA_module [Finite Y] (H : HypYW ρ t u x h)
    (e : normalClosure ({x} : Set Y) ≃* alternatingGroup (Fin 6)) :
    (∀ c : Y, (∀ j ∈ normalClosure ({x} : Set Y), c * j = j * c) → c = 1) ∧
    ∃ Y₀ : Subgroup Y, normalClosure ({x} : Set Y) ≤ Y₀ ∧ t ∉ Y₀ ∧
      (∀ g : Y, g * g = 1 → g ∉ Y₀ → rk (ρ g) = 4) ∧
      (∀ g ∈ Y₀, g ≠ 1 → 2 ≤ rk (ρ g)) ∧
      (∀ j ∈ normalClosure ({x} : Set Y), j * j = 1 → j ≠ 1 → rk (ρ j) = 4) := by
  have hA6 := caseA_hA6 H e
  have HM := H.toHypM
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  obtain ⟨V₁, V₂, hd₁, hc, hV₂, hst, -, -, hfa₁, hfa₂, -, hcen, hperm⟩ := module_A6_abs HM hA6
  have hd₂ : finrank (ZMod 2) V₂ = 4 := by
    rw [hV₂]
    exact (LinearEquiv.finrank_map_eq (ρ t) V₁).trans hd₁
  have hC : ∀ c : Y, (∀ j ∈ normalClosure ({x} : Set Y), c * j = j * c) → c = 1 := fun c hc =>
    caseA_centralizer H hcen hc
  have sV₁ : ∀ g ∈ Jbar ρ x, Stable g V₁ := fun g hg => (hst g hg).1
  have sV₂ : ∀ g ∈ Jbar ρ x, Stable g V₂ := fun g hg => (hst g hg).2
  refine ⟨hC, (modA_stab V₁).comap ρ, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · exact modA_le_stab sV₁ (Subgroup.mem_map_of_mem ρ hj)
  · intro htY
    exact caseA_map_not_stab hc hd₂ hV₂.symm htY
  · intro g hg2 hgY
    have hg2' : ρ g * ρ g = 1 := by rw [← map_mul, hg2, map_one]
    rcases hperm g with ⟨e1, -⟩ | ⟨e1, -⟩
    · exact absurd (modA_mem_stab_of_map_eq e1) hgY
    · exact modA_rk_swap hc hd₁ H.dim hg2' fun v hv => e1 ▸ ⟨v, hv, rfl⟩
  · intro g hgY hg1
    have hM₁ : ρ g ∈ modA_stab V₁ := hgY
    have hM₂ : ρ g ∈ modA_stab V₂ := by
      rcases hperm g with ⟨-, e2⟩ | ⟨e1, -⟩
      · exact modA_mem_stab_of_map_eq e2
      · exact absurd hM₁ (caseA_map_not_stab hc hd₂ e1)
    rw [modA_rk_add hc hM₁ hM₂]
    have r1 := caseA_rk_restr_pos H hC sV₁ hfa₁ hM₁ hg1
    have r2 := caseA_rk_restr_pos H hC sV₂ hfa₂ hM₂ hg1
    omega
  · intro j hj hj2 hj1
    exact modA_A6_rk_four HM hA6 (Subgroup.mem_map_of_mem ρ hj)
      (by rw [← map_mul, hj2, map_one]) fun h1 => hj1 (H.inj (h1.trans (map_one ρ).symm))

end Rank

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
