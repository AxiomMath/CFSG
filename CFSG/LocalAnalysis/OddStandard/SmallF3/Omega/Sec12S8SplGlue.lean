module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplFin

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma s8_glue_decomp_unique {Γ : Type} [Group Γ] {H1 H2 : Subgroup Γ}
    (hdisj : H1 ⊓ H2 = ⊥) {a a' b b' : Γ} (ha : a ∈ H1) (ha' : a' ∈ H1) (hb : b ∈ H2)
    (hb' : b' ∈ H2) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have heq : a'⁻¹ * a = b' * b⁻¹ := by
    have h' : a'⁻¹ * a * b = b' := by
      calc a'⁻¹ * a * b = a'⁻¹ * (a * b) := by group
        _ = a'⁻¹ * (a' * b') := by rw [h]
        _ = b' := by group
    calc a'⁻¹ * a = a'⁻¹ * a * b * b⁻¹ := by group
      _ = b' * b⁻¹ := by rw [h']
  have hmem : a'⁻¹ * a ∈ H1 ⊓ H2 := by
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · exact H1.mul_mem (H1.inv_mem ha') ha
    · rw [heq]
      exact H2.mul_mem hb' (H2.inv_mem hb)
  have hone : a'⁻¹ * a = 1 := by
    rw [hdisj] at hmem
    simpa using hmem
  have haa : a = a' := (inv_mul_eq_one.mp hone).symm
  refine ⟨haa, ?_⟩
  have hb_eq : a * b = a * b' := by simpa [haa] using h
  exact mul_left_cancel hb_eq

theorem s8_glue {Γ : Type} [Group Γ] {G0 H1 H2 V1 V2 C1 : Subgroup Γ} {t : Γ}
    (hG0 : G0.index = 2) (ht : t ∉ G0) (hsup : H1 ⊔ H2 = G0) (hdisj : H1 ⊓ H2 = ⊥)
    (hcomm : ∀ x ∈ H1, ∀ y ∈ H2, x * y = y * x)
    (h12 : H1.map (MulAut.conj t).toMonoidHom ≤ H2)
    (h21 : H2.map (MulAut.conj t).toMonoidHom ≤ H1)
    (hV1 : V1 ≤ H1) (hV2 : V2 ≤ H2) (hVc : ∀ x ∈ V1, ∀ y ∈ V2, x * y = y * x)
    (hv : V1.map (MulAut.conj t).toMonoidHom = V2)
    (hC : C1 ⊓ V1 = ⊥) (hCs : C1 ⊔ V1 = H1) :
    ∃ K : Subgroup Γ, K ⊓ (V1 ⊔ V2) = ⊥ ∧ K ⊔ (V1 ⊔ V2) = ⊤ := by
  have hH1le : H1 ≤ G0 := hsup ▸ le_sup_left
  have hC1le : C1 ≤ H1 := hCs ▸ le_sup_left
  have htH1 : ∀ u ∈ H1, t * u * t⁻¹ ∈ H2 := fun u hu => h12 ⟨u, hu, rfl⟩
  have htH2 : ∀ u ∈ H2, t * u * t⁻¹ ∈ H1 := fun u hu => h21 ⟨u, hu, rfl⟩
  have htt_mem : t * t ∈ G0 := mul_self_mem_of_index_two hG0 t
  obtain ⟨h1, hh1, h2, hh2, hhtt⟩ :=
    s8_mem_sup_of_commute hcomm (by rw [hsup]; exact htt_mem)
  have hxy : (t * h2 * t⁻¹) * (t * h1 * t⁻¹) = h1 * h2 := by
    calc (t * h2 * t⁻¹) * (t * h1 * t⁻¹) = t * (h2 * h1) * t⁻¹ := by group
      _ = t * (h1 * h2) * t⁻¹ := by rw [(hcomm h1 hh1 h2 hh2).symm]
      _ = t * (t * t) * t⁻¹ := by rw [hhtt.symm]
      _ = t * t := by group
      _ = h1 * h2 := hhtt
  have hyx : (t * h1 * t⁻¹) * (t * h2 * t⁻¹) = h1 * h2 := by
    calc (t * h1 * t⁻¹) * (t * h2 * t⁻¹) = t * (h1 * h2) * t⁻¹ := by group
      _ = t * (t * t) * t⁻¹ := by rw [hhtt.symm]
      _ = t * t := by group
      _ = h1 * h2 := hhtt
  obtain ⟨hxh, hyh⟩ := s8_glue_decomp_unique hdisj (htH2 h2 hh2) hh1 (htH1 h1 hh1) hh2 hxy
  set τ : Γ := h1⁻¹ * t with hτdef
  have hc12 : h1 * h2 = h2 * h1 := hcomm h1 hh1 h2 hh2
  have hc2 : h2⁻¹ * h1 = h1 * h2⁻¹ := by
    have h' : h2⁻¹ * h1 * h2 = h1 := by
      calc h2⁻¹ * h1 * h2 = h2⁻¹ * (h1 * h2) := by group
        _ = h2⁻¹ * (h2 * h1) := by rw [hc12]
        _ = h1 := by group
    calc h2⁻¹ * h1 = h2⁻¹ * h1 * h2 * h2⁻¹ := by group
      _ = h1 * h2⁻¹ := by rw [h']
  have hconj_inv : t * h1⁻¹ * t⁻¹ = h2⁻¹ := by
    have := congrArg Inv.inv hyh
    simpa [mul_inv_rev, inv_inv, mul_assoc] using this
  have hτ2 : τ * τ = 1 := by
    rw [hτdef]
    calc (h1⁻¹ * t) * (h1⁻¹ * t) = h1⁻¹ * (t * h1⁻¹ * t⁻¹) * (t * t) := by group
      _ = h1⁻¹ * h2⁻¹ * (t * t) := by rw [hconj_inv]
      _ = h1⁻¹ * h2⁻¹ * (h1 * h2) := by rw [hhtt]
      _ = 1 := by
            calc h1⁻¹ * h2⁻¹ * (h1 * h2) = (h1⁻¹ * (h2⁻¹ * h1)) * h2 := by group
              _ = (h1⁻¹ * (h1 * h2⁻¹)) * h2 := by rw [hc2]
              _ = 1 := by group
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hτ_not : τ ∉ G0 := by
    intro hτG0
    have ht_eq : t = h1 * τ := by rw [hτdef]; group
    rw [ht_eq] at ht
    exact ht (mul_mem (hH1le hh1) hτG0)
  have hσ_eq_t : ∀ x ∈ H1, τ * x * τ⁻¹ = t * x * t⁻¹ := by
    intro x hx
    rw [hτdef]
    have hxH2 : t * x * t⁻¹ ∈ H2 := htH1 x hx
    have hc1 : h1 * (t * x * t⁻¹) = (t * x * t⁻¹) * h1 := hcomm h1 hh1 _ hxH2
    calc (h1⁻¹ * t) * x * (h1⁻¹ * t)⁻¹ = h1⁻¹ * (t * x * t⁻¹) * h1 := by group
      _ = h1⁻¹ * ((t * x * t⁻¹) * h1) := by group
      _ = h1⁻¹ * (h1 * (t * x * t⁻¹)) := by rw [← hc1]
      _ = t * x * t⁻¹ := by group
  let σ : Γ →* Γ := (MulAut.conj τ).toMonoidHom
  have hσ_apply : ∀ g : Γ, σ g = τ * g * τ⁻¹ := fun g => rfl
  have hσ_invol : ∀ g : Γ, σ (σ g) = g := by
    intro g
    show τ * (τ * g * τ⁻¹) * τ⁻¹ = g
    calc τ * (τ * g * τ⁻¹) * τ⁻¹ = (τ * τ) * g * (τ * τ)⁻¹ := by group
      _ = g := by rw [hτ2]; group
  have hσ_inj : Function.Injective σ := fun _ _ h => (MulAut.conj τ).injective h
  have hσH1 : ∀ x ∈ H1, σ x ∈ H2 := by
    intro x hx
    rw [hσ_apply x, hσ_eq_t x hx]
    exact htH1 x hx
  have hσH2 : ∀ y ∈ H2, σ y ∈ H1 := by
    intro y hy
    have hσy : σ y = h1⁻¹ * (t * y * t⁻¹) * h1 := by
      show τ * y * τ⁻¹ = h1⁻¹ * (t * y * t⁻¹) * h1
      rw [hτdef]
      group
    rw [hσy]
    exact mul_mem (mul_mem (inv_mem hh1) (htH2 y hy)) hh1
  have hH1σ : H1.map σ = H2 := by
    apply le_antisymm
    · rintro y hy
      rcases mem_map.mp hy with ⟨x, hx, rfl⟩
      exact hσH1 x hx
    · intro y hy
      exact mem_map.mpr ⟨σ y, hσH2 y hy, hσ_invol y⟩
  have hV1σ : V1.map σ = V2 := by
    rw [← hv]
    apply le_antisymm
    · rintro y hy
      rcases mem_map.mp hy with ⟨x, hx, hxy⟩
      exact mem_map.mpr ⟨x, hx, (hσ_eq_t x (hV1 hx)).symm.trans hxy⟩
    · rintro y hy
      rcases mem_map.mp hy with ⟨x, hx, hxy⟩
      exact mem_map.mpr ⟨x, hx, (hσ_eq_t x (hV1 hx)).trans hxy⟩
  have hC2H2le : C1.map σ ≤ H2 := by
    rintro y hy
    rcases mem_map.mp hy with ⟨x, hx, rfl⟩
    exact hσH1 x (hC1le hx)
  have hC2infV2 : C1.map σ ⊓ V2 = ⊥ := by
    rw [← hV1σ, ← map_inf C1 V1 σ hσ_inj, hC, map_bot σ]
  have hC2supV2 : C1.map σ ⊔ V2 = H2 := by
    rw [← hV1σ, ← map_sup C1 V1 σ, hCs, hH1σ]
  have hDσmem : ∀ d ∈ C1 ⊔ C1.map σ, σ d ∈ C1 ⊔ C1.map σ := by
    intro d hd
    obtain ⟨c1, hc1, c2, hc2, rfl⟩ := s8_mem_sup_of_commute
      (fun a ha b hb => hcomm a (hC1le ha) b (hC2H2le hb)) hd
    rcases mem_map.mp hc2 with ⟨c2', hc2', rfl⟩
    rw [map_mul, hσ_invol c2']
    exact mul_mem (mem_sup_right (mem_map.mpr ⟨c1, hc1, rfl⟩)) (mem_sup_left hc2')
  have hDG0 : C1 ⊔ C1.map σ ≤ H1 ⊔ H2 :=
    sup_le (hC1le.trans le_sup_left) (hC2H2le.trans le_sup_right)
  let K : Subgroup Γ :=
    { carrier := {g | g ∈ C1 ⊔ C1.map σ ∨ ∃ d ∈ C1 ⊔ C1.map σ, g = d * τ}
      mul_mem' := by
        intro g h hg hh
        rcases hg with hg | ⟨d1, hd1, rfl⟩
        · rcases hh with hh | ⟨d2, hd2, rfl⟩
          · exact Or.inl (mul_mem hg hh)
          · exact Or.inr ⟨g * d2, mul_mem hg hd2, by group⟩
        · rcases hh with hh | ⟨d2, hd2, rfl⟩
          · refine Or.inr ⟨d1 * σ h, mul_mem hd1 (hDσmem h hh), ?_⟩
            have htau : τ * h = σ h * τ := by
              show τ * h = τ * h * τ⁻¹ * τ
              group
            calc (d1 * τ) * h = d1 * (τ * h) := by group
              _ = d1 * (σ h * τ) := by rw [htau]
              _ = (d1 * σ h) * τ := by group
          · refine Or.inl ?_
            have htau : τ * d2 = σ d2 * τ := by
              show τ * d2 = τ * d2 * τ⁻¹ * τ
              group
            have heq : (d1 * τ) * (d2 * τ) = d1 * σ d2 := by
              calc (d1 * τ) * (d2 * τ) = d1 * (τ * d2) * τ := by group
                _ = d1 * (σ d2 * τ) * τ := by rw [htau]
                _ = d1 * σ d2 := by
                      calc d1 * (σ d2 * τ) * τ = d1 * (σ d2 * (τ * τ)) := by group
                        _ = d1 * (σ d2 * 1) := by rw [hτ2]
                        _ = d1 * σ d2 := by group
            rw [heq]
            exact mul_mem hd1 (hDσmem d2 hd2)
      one_mem' := Or.inl (one_mem _)
      inv_mem' := by
        intro g hg
        rcases hg with hg | ⟨d, hd, rfl⟩
        · exact Or.inl (inv_mem hg)
        · refine Or.inr ⟨σ d⁻¹, hDσmem d⁻¹ (inv_mem hd), ?_⟩
          have htau : τ * d⁻¹ = σ d⁻¹ * τ := by
            show τ * d⁻¹ = τ * d⁻¹ * τ⁻¹ * τ
            group
          calc (d * τ)⁻¹ = τ⁻¹ * d⁻¹ := by rw [mul_inv_rev]
            _ = τ * d⁻¹ := by rw [hτinv]
            _ = σ d⁻¹ * τ := htau }
  have hKτ : τ ∈ K := by
    change τ ∈ C1 ⊔ C1.map σ ∨ ∃ d ∈ C1 ⊔ C1.map σ, τ = d * τ
    exact Or.inr ⟨1, one_mem _, by rw [one_mul]⟩
  have hKinfV : K ⊓ (V1 ⊔ V2) = ⊥ := by
    apply le_antisymm
    · intro g hg
      rw [mem_bot]
      obtain ⟨hgK, hgV⟩ := hg
      change g ∈ C1 ⊔ C1.map σ ∨ ∃ d ∈ C1 ⊔ C1.map σ, g = d * τ at hgK
      rcases hgK with hgD | ⟨d, hd, rfl⟩
      · obtain ⟨c1, hc1, c2, hc2, hgc⟩ := s8_mem_sup_of_commute
          (fun a ha b hb => hcomm a (hC1le ha) b (hC2H2le hb)) hgD
        obtain ⟨v1, hv1, v2, hv2, hgv⟩ := s8_mem_sup_of_commute hVc hgV
        obtain ⟨hc1v1, hc2v2⟩ := s8_glue_decomp_unique hdisj (hC1le hc1) (hV1 hv1)
          (hC2H2le hc2) (hV2 hv2) (hgc.symm.trans hgv)
        rw [hgc]
        have hc1V1 : c1 ∈ V1 := by rw [hc1v1]; exact hv1
        have hc2V2 : c2 ∈ V2 := by rw [hc2v2]; exact hv2
        have hc1one : c1 = 1 := by
          have hmem : c1 ∈ C1 ⊓ V1 := ⟨hc1, hc1V1⟩
          rw [hC] at hmem
          simpa using hmem
        have hc2one : c2 = 1 := by
          have hmem : c2 ∈ C1.map σ ⊓ V2 := ⟨hc2, hc2V2⟩
          rw [hC2infV2] at hmem
          simpa using hmem
        rw [hc1one, hc2one, mul_one]
      · exfalso
        have hVG0 : V1 ⊔ V2 ≤ H1 ⊔ H2 :=
          sup_le (hV1.trans le_sup_left) (hV2.trans le_sup_right)
        have hgG0 : d * τ ∈ H1 ⊔ H2 := hVG0 hgV
        have hτG0 : τ ∈ H1 ⊔ H2 := by
          have h' := (H1 ⊔ H2).mul_mem ((H1 ⊔ H2).inv_mem (hDG0 hd)) hgG0
          simpa using h'
        exact hτ_not (hsup ▸ hτG0)
    · exact bot_le
  have hH1KV : H1 ≤ K ⊔ (V1 ⊔ V2) := by
    rw [← hCs]
    refine sup_le (fun c hc => ?_) (fun v hv => ?_)
    · exact mem_sup_left (Or.inl (mem_sup_left hc))
    · exact mem_sup_right (mem_sup_left hv)
  have hH2KV : H2 ≤ K ⊔ (V1 ⊔ V2) := by
    rw [← hC2supV2]
    refine sup_le (fun c hc => ?_) (fun v hv => ?_)
    · exact mem_sup_left (Or.inl (mem_sup_right hc))
    · exact mem_sup_right (mem_sup_right hv)
  have hG0KV : H1 ⊔ H2 ≤ K ⊔ (V1 ⊔ V2) := sup_le hH1KV hH2KV
  have hKsupV : K ⊔ (V1 ⊔ V2) = ⊤ := by
    rw [eq_top_iff']
    intro g
    by_cases hgG0 : g ∈ H1 ⊔ H2
    · exact hG0KV hgG0
    · have hgτ_mem : g * τ⁻¹ ∈ H1 ⊔ H2 := by
        have hmem : g * τ⁻¹ ∈ G0 :=
          (mul_mem_iff_of_index_two hG0).mpr
            ⟨fun h => (hgG0 (by rwa [← hsup] at h)).elim,
              fun h => (hτ_not (by simpa [hτinv] using h)).elim⟩
        rwa [← hsup] at hmem
      have hg_eq : g = (g * τ⁻¹) * τ := by group
      rw [hg_eq]
      exact mul_mem (hG0KV hgτ_mem) (mem_sup_left hKτ)
  exact ⟨K, hKinfV, hKsupV⟩

end CFSG.OddStandard.SmallF3.Omega
