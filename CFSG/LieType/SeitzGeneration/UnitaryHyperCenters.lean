module

public import CFSG.LieType.SeitzGeneration.UnitaryHyperRad
public import CFSG.LieType.SeitzGeneration.UnitaryCenters

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem hermOrth_hermOrth (hσ : ∀ c, σ (σ c) = c) (W : Submodule K (Fin n → K)) :
    hermOrth σ (hermOrth σ W) = W := by
  have hle : W ≤ hermOrth σ (hermOrth σ W) := fun w hw y hy =>
    herm_eq_zero_comm σ hσ (hy w hw)
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have h1 := finrank_hermOrth_add σ hσ W
  have h2 := finrank_hermOrth_add σ hσ (hermOrth σ W)
  omega

theorem isCenter_of_uRad_le {W : Submodule K (Fin n → K)}
    {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0} (hσ : ∀ c, σ (σ c) = c) {H : Subgroup (SUid σ n)}
    (hQ : uRad σ W hW ≤ H) {w : Fin n → K} (hw : w ∈ W) : IsCenter H w :=
  ⟨hW w hw w hw, fun _ hc => ⟨tv hσ (hW w hw w hw) hc, hQ (tv_mem_uRad hσ hw hc),
    tv_smul hσ (hW w hw w hw) hc⟩⟩

theorem eq_top_of_uRad_of_opposite (hσ : IsUnitaryInvolution σ) (hn : 2 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) {W W' : Submodule K (Fin n → K)}
    (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0)
    (hW' : ∀ x ∈ W', ∀ y ∈ W', herm σ x y = 0) (hcompl : IsCompl (hermOrth σ W) W')
    {H : Subgroup (SUid σ n)} (hQ : uRad σ W hW ≤ H) (hQ' : uRad σ W' hW' ≤ H) : H = ⊤ := by
  classical
  have hinv := hσ.invol
  have hWc : ∀ w ∈ W, IsCenter H w := fun w hw => isCenter_of_uRad_le hinv hQ hw
  have hW'c : ∀ w ∈ W', IsCenter H w := fun w hw => isCenter_of_uRad_le hinv hQ' hw
  have hWP : ∀ w ∈ W, w ∈ hermOrth σ W := fun w hw x hx => hW x hx w hw
  have hback : ∀ {g : SUid σ n} {v : Fin n → K}, g ∈ H → IsCenter H (g • v) → IsCenter H v := by
    intro g v hg hc
    have := hc.map (H.inv_mem hg)
    rwa [inv_smul_smul] at this
  have hdec : ∀ v : Fin n → K, ∃ u ∈ hermOrth σ W, ∃ w' ∈ W', v = u + w' := by
    intro v
    have hv : v ∈ hermOrth σ W ⊔ W' := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, w', hw', h⟩ := Submodule.mem_sup.1 hv
    exact ⟨u, hu, w', hw', h.symm⟩
  have hE1 : ∀ w' ∈ W', w' ≠ 0 → ∃ e ∈ W, herm σ e w' ≠ 0 := by
    intro w' hw' hw'0
    by_contra hcon
    push Not at hcon
    exact hw'0 (Submodule.disjoint_def.1 hcompl.disjoint w' (fun e he => hcon e he) hw')
  have hE2 : ∀ e ∈ W, e ≠ 0 → ∃ w' ∈ W', herm σ e w' ≠ 0 := by
    intro e he he0
    by_contra hcon
    push Not at hcon
    refine he0 (eq_zero_of_herm σ fun v => ?_)
    obtain ⟨u, hu, w', hw', rfl⟩ := hdec v
    rw [herm_add_right, hu e he, hcon w' hw', add_zero]
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hA : ∀ w ∈ W, ∀ w' ∈ W', herm σ (w + w') (w + w') = 0 → herm σ w w' ≠ 0 →
      IsCenter H (w + w') := by
    intro w hw w' hw' hiso hne
    refine IsCenter.add hinv (hWc w hw) (hW'c w' hw') hiso ?_
    rw [herm_conj σ hinv w w']
    exact (map_ne_zero σ).mpr hne
  have hB : ∀ w ∈ W, ∀ w' ∈ W', herm σ (w + w') (w + w') = 0 → IsCenter H (w + w') := by
    intro w hw w' hw' hiso
    by_cases hδ : herm σ w w' = 0
    · by_cases hw'0 : w' = 0
      · rw [hw'0, add_zero]
        exact hWc w hw
      · obtain ⟨e, he, hγ⟩ := hE1 w' hw' hw'0
        have htH : tv hinv (hW e he e he) hτ ∈ H := hQ (tv_mem_uRad hinv he hτ)
        have hte := tv_smul hinv (hW e he e he) hτ
        have hx : herm σ e (w + w') = herm σ e w' := by
          rw [herm_add_right, hW e he w hw, zero_add]
        have htx : tv hinv (hW e he e he) hτ • (w + w') =
            (w + (τ * herm σ e w') • e) + w' := by
          rw [hte, hx]
          abel
        have hmem : w + (τ * herm σ e w') • e ∈ W := W.add_mem hw (W.smul_mem _ he)
        have hiso' : herm σ ((w + (τ * herm σ e w') • e) + w')
            ((w + (τ * herm σ e w') • e) + w') = 0 := by
          rw [← htx, herm_smul_smul]
          exact hiso
        have hne : herm σ (w + (τ * herm σ e w') • e) w' ≠ 0 := by
          have hστ : σ τ = -τ := by linear_combination hτ
          rw [herm_add_left, herm_smul_left, hδ, zero_add, map_mul, hστ]
          exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 hτ0) ((map_ne_zero σ).2 hγ)) hγ
        have := hA _ hmem w' hw' hiso' hne
        rw [← htx] at this
        exact hback htH this
    · exact hA w hw w' hw' hiso hδ
  have hC : ∀ u ∈ hermOrth σ W, ∀ w' ∈ W', w' ≠ 0 → herm σ (u + w') (u + w') = 0 →
      IsCenter H (u + w') := by
    intro u hu w' hw' hw'0 hiso
    obtain ⟨e, he, hβ⟩ := hE1 w' hw' hw'0
    set y : Fin n → K := -((herm σ e w')⁻¹ • u) with hydef
    have hy : y ∈ hermOrth σ W := (hermOrth σ W).neg_mem ((hermOrth σ W).smul_mem _ hu)
    obtain ⟨c, hc⟩ := hσ.trace_surj (-herm σ y y) (by rw [map_neg, herm_self_fixed σ hinv])
    have hgH := hQ (eichler_mem_uRad hinv he hy hc)
    have hev : herm σ e (u + w') = herm σ e w' := by rw [herm_add_right, hu e he, zero_add]
    have hβy : herm σ e w' • y = -u := by
      rw [hydef, smul_neg, smul_smul, mul_inv_cancel₀ hβ, one_smul]
    have hgv : eichler hinv (hW e he e he) (hy e he) hc • (u + w') =
        ((herm σ e w' * c - herm σ y (u + w')) • e) + w' := by
      rw [eichler_smul, hev, smul_add (herm σ e w') y (c • e), hβy]
      module
    have hsmem : (herm σ e w' * c - herm σ y (u + w')) • e ∈ W := W.smul_mem _ he
    have hiso' : herm σ (((herm σ e w' * c - herm σ y (u + w')) • e) + w')
        (((herm σ e w' * c - herm σ y (u + w')) • e) + w') = 0 := by
      rw [← hgv, herm_smul_smul]
      exact hiso
    have := hB _ hsmem w' hw' hiso'
    rw [← hgv] at this
    exact hback hgH this
  have hD : ∀ v ∈ hermOrth σ W, herm σ v v = 0 → (∃ w' ∈ W', herm σ w' v ≠ 0) →
      IsCenter H v := by
    rintro v hv hvv ⟨w', hw', hne⟩
    obtain ⟨g, hgH, hg⟩ := (hW'c w' hw').2 τ hτ
    have hw'0 : w' ≠ 0 := fun h => hne (by rw [h, herm_zero_left])
    have hmem : (τ * herm σ w' v) • w' ∈ W' := W'.smul_mem _ hw'
    have hne' : (τ * herm σ w' v) • w' ≠ 0 := smul_ne_zero (mul_ne_zero hτ0 hne) hw'0
    have hiso : herm σ (v + (τ * herm σ w' v) • w') (v + (τ * herm σ w' v) • w') = 0 := by
      rw [← hg v, herm_smul_smul]
      exact hvv
    have := hC v hv _ hmem hne' hiso
    rw [← hg v] at this
    exact hback hgH this
  have hE : ∀ v ∈ hermOrth σ W, herm σ v v = 0 → v ∉ W → IsCenter H v := by
    intro v hv hvv hvW
    have hex : ∃ y ∈ hermOrth σ W, herm σ y v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hvW
      rw [← hermOrth_hermOrth hinv W]
      exact fun y hy => hcon y hy
    obtain ⟨y, hy, hyv⟩ := hex
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨c, hc⟩ := hσ.trace_surj (-herm σ y y) (by rw [map_neg, herm_self_fixed σ hinv])
    have hgH := hQ (eichler_mem_uRad hinv he hy hc)
    have hgv : eichler hinv (hW e he e he) (hy e he) hc • v = v + (-herm σ y v) • e := by
      rw [eichler_smul, hv e he, zero_smul, add_zero, neg_smul, sub_eq_add_neg]
    by_cases hA1 : ∃ w' ∈ W', herm σ w' v ≠ 0
    · exact hD v hv hvv hA1
    · push Not at hA1
      obtain ⟨w', hw', hew'⟩ := hE2 e he he0
      have hv'P : v + (-herm σ y v) • e ∈ hermOrth σ W :=
        (hermOrth σ W).add_mem hv ((hermOrth σ W).smul_mem _ (hWP e he))
      have hv'iso : herm σ (v + (-herm σ y v) • e) (v + (-herm σ y v) • e) = 0 := by
        rw [← hgv, herm_smul_smul]
        exact hvv
      have hne : herm σ w' (v + (-herm σ y v) • e) ≠ 0 := by
        rw [herm_add_right, hA1 w' hw', herm_smul_right, zero_add, herm_conj σ hinv e w']
        exact mul_ne_zero (neg_ne_zero.2 hyv) ((map_ne_zero σ).2 hew')
      have := hD _ hv'P hv'iso ⟨w', hw', hne⟩
      rw [← hgv] at this
      exact hback hgH this
  refine eq_top_of_forall_isCenter hσ hn h3 (fun a ha => ?_)
  obtain ⟨u, hu, w', hw', rfl⟩ := hdec a
  by_cases hw'0 : w' = 0
  · rw [hw'0, add_zero] at ha ⊢
    by_cases huW : u ∈ W
    · exact hWc u huW
    · exact hE u hu ha huW
  · exact hC u hu w' hw' hw'0 ha

end CFSG.LieType.SeitzGeneration
