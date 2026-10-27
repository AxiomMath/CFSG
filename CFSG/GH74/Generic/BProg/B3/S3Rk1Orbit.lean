module

public import CFSG.GH74.Generic.BProg.B3.S3Rk1Basic

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

namespace S3Rk1Orbit

variable {G : Type} [Group G]

theorem mem_normalizer_A {x : G} {E A : Subgroup G} (hAE : A = E ⊔ zpowers x) {c : G}
    (hcE : c ∈ normalizer (E : Set G)) (hcx : c * x = x * c) : c ∈ normalizer (A : Set G) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
  rw [hAE, Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.1 hcE, MonoidHom.map_zpowers]
  show E ⊔ zpowers (c * x * c⁻¹) = E ⊔ zpowers x
  rw [hcx]
  group

theorem exists_w {x y : G} {E A : Subgroup G} (hx : orderOf x = 2) (hAE : A = E ⊔ zpowers x)
    (hEx : ∀ e ∈ E, e * x = x * e)
    (htr : ∀ a₀ ∈ E, a₀ ≠ 1 → ∀ y' ∈ E, y' ≠ 1 → ∃ σ ∈ normalizer (E : Set G),
      σ * x = x * σ ∧ σ * a₀ * σ⁻¹ = y')
    (hyE : y ∈ E) (hy1 : y ≠ 1) (hxy : ∀ g : G, g * x * g⁻¹ ≠ y)
    (hmove : ∃ g₁ ∈ normalizer (A : Set G), g₁ * x ≠ x * g₁) :
    (∀ g ∈ normalizer (A : Set G), g ∈ normalizer (E : Set G)) ∧
    (∀ z ∈ E, z ≠ 1 → ∃ g ∈ normalizer (A : Set G), g * x * g⁻¹ = z * x) ∧
    (∀ z ∈ E, z ≠ 1 → ∃ w ∈ normalizer (A : Set G), w * y * w⁻¹ = y ∧ w * x * w⁻¹ = z * x) := by
  classical
  have hx1 : x ≠ 1 := fun h => by simp [h] at hx
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hF1 : ∀ g ∈ normalizer (A : Set G), ∃ e ∈ E, g * x * g⁻¹ = e * x := by
    intro g hg
    have hgx : g * x * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hg x).1 hxA
    have hcomm : ∀ e ∈ E, ∀ k ∈ zpowers x, e * k = k * e := by
      intro e he k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact (Commute.zpow_right (show Commute e x from hEx e he) n).eq
    obtain ⟨e, he, k, hk, hek⟩ := S3Rk1Basic.exists_mul_of_mem_sup hcomm (hAE ▸ hgx)
    rcases B1.PilotS5.mem_zpowers_of_two hx hk with hk1 | hk1
    ·
      exfalso
      rw [hk1, mul_one] at hek
      have he1 : e ≠ 1 := by
        intro h
        rw [h] at hek
        apply hx1
        have : g * x * g⁻¹ = 1 := hek
        simpa using this
      obtain ⟨σ, hσE, -, hσ⟩ := htr y hyE hy1 e he he1
      apply hxy (σ⁻¹ * g)
      have : σ⁻¹ * (g * x * g⁻¹) * σ = y := by
        rw [hek, ← hσ]; group
      rw [← this]
      group
    · exact ⟨e, he, by rw [hek, hk1]⟩
  obtain ⟨g₁, hg₁, hg₁x⟩ := hmove
  obtain ⟨e₁, he₁, hge₁⟩ := hF1 g₁ hg₁
  have he₁1 : e₁ ≠ 1 := by
    intro h
    apply hg₁x
    rw [h, one_mul] at hge₁
    have : g₁ * x = x * g₁ := by
      calc g₁ * x = (g₁ * x * g₁⁻¹) * g₁ := by group
        _ = x * g₁ := by rw [hge₁]
    exact this
  have hF2 : ∀ z ∈ E, z ≠ 1 → ∃ g ∈ normalizer (A : Set G), g * x * g⁻¹ = z * x := by
    intro z hz hz1
    obtain ⟨σ, hσE, hσx, hσ⟩ := htr e₁ he₁ he₁1 z hz hz1
    refine ⟨σ * g₁, (normalizer (A : Set G)).mul_mem (mem_normalizer_A hAE hσE hσx) hg₁, ?_⟩
    have hσx' : σ * x * σ⁻¹ = x := by rw [hσx]; group
    calc σ * g₁ * x * (σ * g₁)⁻¹ = σ * (g₁ * x * g₁⁻¹) * σ⁻¹ := by group
      _ = σ * (e₁ * x) * σ⁻¹ := by rw [hge₁]
      _ = (σ * e₁ * σ⁻¹) * (σ * x * σ⁻¹) := by group
      _ = z * x := by rw [hσ, hσx']
  have hF3 : ∀ g ∈ normalizer (A : Set G), ∀ h ∈ E, g * h * g⁻¹ ∈ E := by
    intro g hg h hh
    by_cases hh1 : h = 1
    · rw [hh1]; simp
    obtain ⟨k, hk, hkx⟩ := hF2 h hh hh1
    obtain ⟨e', he', hge'⟩ := hF1 g hg
    obtain ⟨e'', he'', hge''⟩ := hF1 (g * k) ((normalizer (A : Set G)).mul_mem hg hk)
    have h1 : g * h * g⁻¹ = e'' * e'⁻¹ := by
      have e1 : g * (h * x) * g⁻¹ = e'' * x := by
        have : g * k * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
        rw [hge'', hkx] at this
        exact this.symm
      have e2 : g * (h * x) * g⁻¹ = (g * h * g⁻¹) * (e' * x) := by
        calc g * (h * x) * g⁻¹ = (g * h * g⁻¹) * (g * x * g⁻¹) := by group
          _ = (g * h * g⁻¹) * (e' * x) := by rw [hge']
      have e3 : (g * h * g⁻¹) * (e' * x) = e'' * x := e2.symm.trans e1
      calc g * h * g⁻¹ = ((g * h * g⁻¹) * (e' * x)) * (e' * x)⁻¹ := by group
        _ = (e'' * x) * (e' * x)⁻¹ := by rw [e3]
        _ = e'' * (x * x⁻¹) * e'⁻¹ := by
          have hc' : x * e'⁻¹ = e'⁻¹ * x := by
            have := hEx e'⁻¹ (E.inv_mem he')
            exact this.symm
          calc (e'' * x) * (e' * x)⁻¹ = e'' * (x * (x⁻¹ * e'⁻¹)) := by group
            _ = e'' * (x * x⁻¹) * e'⁻¹ := by group
        _ = e'' * e'⁻¹ := by group
    rw [h1]
    exact E.mul_mem he'' (E.inv_mem he')
  have hF3' : ∀ g ∈ normalizer (A : Set G), g ∈ normalizer (E : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hF3 g hg h hh, fun hh => ?_⟩
    have := hF3 g⁻¹ ((normalizer (A : Set G)).inv_mem hg) _ hh
    simpa [mul_assoc] using this
  refine ⟨hF3', hF2, ?_⟩
  intro z hz hz1
  obtain ⟨gz, hgz, hgzx⟩ := hF2 z hz hz1
  have hy' : gz⁻¹ * y * gz ∈ E := by
    have := hF3 gz⁻¹ ((normalizer (A : Set G)).inv_mem hgz) y hyE
    simpa using this
  have hy'1 : gz⁻¹ * y * gz ≠ 1 := by
    intro h
    apply hy1
    have : y = gz * (gz⁻¹ * y * gz) * gz⁻¹ := by group
    rw [this, h]; group
  obtain ⟨c, hcE, hcx, hc⟩ := htr y hyE hy1 _ hy' hy'1
  refine ⟨gz * c, (normalizer (A : Set G)).mul_mem hgz (mem_normalizer_A hAE hcE hcx), ?_, ?_⟩
  · calc gz * c * y * (gz * c)⁻¹ = gz * (c * y * c⁻¹) * gz⁻¹ := by group
      _ = gz * (gz⁻¹ * y * gz) * gz⁻¹ := by rw [hc]
      _ = y := by group
  · have hcx' : c * x * c⁻¹ = x := by rw [hcx]; group
    calc gz * c * x * (gz * c)⁻¹ = gz * (c * x * c⁻¹) * gz⁻¹ := by group
      _ = gz * x * gz⁻¹ := by rw [hcx']
      _ = z * x := hgzx

end S3Rk1Orbit

end CFSG.GH74.Generic.BProg.B3
