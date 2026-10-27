module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma sec11_hcl_conj_apply (a θ : G) :
    (MulAut.conj a⁻¹).toMonoidHom θ = a⁻¹ * θ * a := by
  show (MulAut.conj a⁻¹) θ = a⁻¹ * θ * a
  rw [MulAut.conj_apply, inv_inv]

theorem sec11_hcl_core [Finite G] {H R : Subgroup G} {t z : G} {Θ : Set G}
    (hR : IsSylow2Of R H) (hΘ : ∀ s, s ∈ Θ ↔ s ∈ R ∧ ∃ h ∈ H, s = h⁻¹ * t * h)
    (hzH : ∀ h ∈ H, h * z = z * h) (hzD : z ∈ Subgroup.closure Θ)
    (hDI : ∀ d ∈ Subgroup.closure Θ, orderOf d = 2 → d ≠ z → d ∈ Θ) :
    ∀ x ∈ H, x ∈ normalizer ((Subgroup.closure Θ : Subgroup G) : Set G) →
      x ∉ Subgroup.closure Θ → orderOf x = 2 → ∀ d ∈ Subgroup.closure Θ, orderOf d = 2 →
        ∀ g ∈ H, g⁻¹ * x * g ≠ d := by
  intro x hxH hxN hxD hxord d hdD hdord g hgH hgxd
  set D : Subgroup G := Subgroup.closure Θ with hDdef
  have hΘD : Θ ⊆ (D : Set G) := by
    intro s hs
    rw [hDdef]
    exact Subgroup.subset_closure hs
  have hΘR : Θ ⊆ (R : Set G) := fun s hs => ((hΘ s).mp hs).1
  have hDR : D ≤ R := by
    rw [hDdef]
    exact (Subgroup.closure_le R).mpr hΘR
  have hDH : D ≤ H := hDR.trans hR.1
  have hD2 : IsPGroup 2 D := hR.2.1.to_le hDR
  by_cases hdz : d = z
  ·
    have hxz : x = z := by
      have hgx : g⁻¹ * x * g = z := by rw [hgxd, hdz]
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * z * g⁻¹ := by rw [hgx]
        _ = z := by
              rw [hzH g hgH]
              group
    exact hxD (by simpa [hxz] using hzD)
  ·
    have hdΘ : d ∈ Θ := hDI d hdD hdord hdz
    obtain ⟨hdR, hd0, hhd0H, hdeq⟩ := (hΘ d).mp hdΘ
    have hx_tH : x = (hd0 * g⁻¹)⁻¹ * t * (hd0 * g⁻¹) := by
      have hxd_eq : x = g * d * g⁻¹ := by
        calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = g * d * g⁻¹ := by rw [hgxd]
      rw [hxd_eq, hdeq]
      group
    have hhxH : hd0 * g⁻¹ ∈ H := H.mul_mem hhd0H (H.inv_mem hgH)
    have hzp : IsPGroup 2 (Subgroup.zpowers x) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hxord]
      simp
    have hxNzp : Subgroup.zpowers x ≤ normalizer (D : Set G) :=
      Subgroup.zpowers_le.mpr hxN
    have hnorm : ∀ b ∈ Subgroup.zpowers x, ∀ a' ∈ D, b * a' * b⁻¹ ∈ D := by
      intro b hb a' ha'
      exact (Subgroup.mem_normalizer_iff.mp (hxNzp hb) a').mp ha'
    have hsup2 : IsPGroup 2 ↥(D ⊔ Subgroup.zpowers x) :=
      sec11_isPGroup_sup hD2 hzp hnorm
    have hsup_le_H : D ⊔ Subgroup.zpowers x ≤ H :=
      sup_le hDH (Subgroup.zpowers_le.mpr hxH)
    obtain ⟨R', hR', hleR'⟩ := exists_isSylow2Of_ge hsup2 hsup_le_H
    obtain ⟨a, haH, hconjmem⟩ := hR.exists_conj_mem hR'
    have hconjΘ : ∀ θ ∈ Θ, (MulAut.conj a⁻¹).toMonoidHom θ ∈ Θ := by
      intro θ hθ
      rw [sec11_hcl_conj_apply]
      obtain ⟨hθR, hθ0, hhθ0H, hθeq⟩ := (hΘ θ).mp hθ
      have hθR' : θ ∈ R' := hleR' (Subgroup.mem_sup_left (hΘD hθ))
      have hcθR : a⁻¹ * θ * a ∈ R := by
        simpa [sec11_hcl_conj_apply] using (hconjmem θ).mp hθR'
      refine (hΘ (a⁻¹ * θ * a)).mpr ⟨hcθR, hθ0 * a, H.mul_mem hhθ0H haH, ?_⟩
      rw [hθeq]
      group
    have hDcomap : D ≤ D.comap (MulAut.conj a⁻¹).toMonoidHom := by
      rw [hDdef]
      refine (Subgroup.closure_le _).mpr ?_
      intro θ hθ
      exact Subgroup.mem_comap.mpr (hΘD (hconjΘ θ hθ))
    have hDmap_le : D.map (MulAut.conj a⁻¹).toMonoidHom ≤ D :=
      Subgroup.map_le_iff_le_comap.mpr hDcomap
    have hcard : Nat.card (D.map (MulAut.conj a⁻¹).toMonoidHom) = Nat.card D :=
      Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective
    have hDmap_eq : D.map (MulAut.conj a⁻¹).toMonoidHom = D :=
      Subgroup.eq_of_le_of_card_ge hDmap_le (le_of_eq hcard.symm)
    have hxsup : x ∈ D ⊔ Subgroup.zpowers x :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hxR' : x ∈ R' := hleR' hxsup
    have haxaR : a⁻¹ * x * a ∈ R := by
      simpa [sec11_hcl_conj_apply] using (hconjmem x).mp hxR'
    have haxaΘ : a⁻¹ * x * a ∈ Θ := by
      refine (hΘ (a⁻¹ * x * a)).mpr
        ⟨haxaR, (hd0 * g⁻¹) * a, H.mul_mem hhxH haH, ?_⟩
      rw [hx_tH]
      group
    have haxaD : a⁻¹ * x * a ∈ D := hΘD haxaΘ
    have haxaDmap : a⁻¹ * x * a ∈ D.map (MulAut.conj a⁻¹).toMonoidHom := by
      rw [hDmap_eq]
      exact haxaD
    rw [Subgroup.mem_map] at haxaDmap
    obtain ⟨u, huD, hueq⟩ := haxaDmap
    have hu_eq : u = x := by
      rw [sec11_hcl_conj_apply] at hueq
      calc u = a * (a⁻¹ * u * a) * a⁻¹ := by group
        _ = a * (a⁻¹ * x * a) * a⁻¹ := by rw [hueq]
        _ = x := by group
    exact hxD (hu_eq ▸ huD)

end CFSG.OddStandard.SmallF3.Omega
