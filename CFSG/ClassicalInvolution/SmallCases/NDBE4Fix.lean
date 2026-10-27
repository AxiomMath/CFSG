module

public import CFSG.ClassicalInvolution.AschTight.S19GCore
public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51

public section

namespace CFSG.ClassicalInvolution.NDB.ExoticModel

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19G (FG0Model)

variable {p : ℕ} [Fact p.Prime]

theorem fg0 (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ} (ht : t = .G2 ∨ t = .trialityD4)
    (hadm : StatedLieAdmissible t n p e) {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) : FG0Model R := by
  rcases ht with rfl | rfl
  · exact Disconnected.AschTight.S19G.fg0Model_g2 hp2 hadm.2.1 hR
  · exact Disconnected.AschTight.S19G.fg0Model_d4 hp2 hadm.2.1 hR

theorem involution_fund (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .G2 ∨ t = .trialityD4) (hadm : StatedLieAdmissible t n p e) {H : Type} [Group H]
    (ψ : (modelUniv t n p e Fact.out).K →* H) (hinj : Function.Injective ψ)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {x : (modelUniv t n p e Fact.out).K} (hx : IsUniqueInvolution R x) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * ψ r = ψ r * v) :
    (∀ y ∈ ψ.range, v * y = y * v) ∨ (∀ y ∈ ψ.range, (v * ψ x) * y = y * (v * ψ x)) := by
  obtain ⟨ha1, -, hb⟩ := fg0 hp2 ht hadm hR
  set eψ := MonoidHom.ofInjective hinj with heψ
  set φ : MulAut ψ.range := Asc77.conjOnNormalizer ψ.range ⟨v, hv⟩ with hφ
  set α : MulAut (modelUniv t n p e Fact.out).K := MulAut.congr eψ.symm φ with hα
  have hαk : ∀ k, (eψ (α k) : H) = v * ψ k * v⁻¹ := by
    intro k
    have h1 : α k = eψ.symm (φ (eψ k)) := rfl
    rw [h1, MulEquiv.apply_symm_apply]
    rfl
  have hψα : ∀ k, ψ (α k) = v * ψ k * v⁻¹ := fun k => by
    rw [← hαk]
    rfl
  have hφ2 : φ ^ 2 = 1 := by
    rw [hφ, ← map_pow, pow_two]
    have : (⟨v, hv⟩ : ↥(Subgroup.normalizer (ψ.range : Set H))) * ⟨v, hv⟩ = 1 :=
      Subtype.ext hv2
    rw [this, map_one]
  have hα2 : α ^ (2 ^ 1) = 1 := by
    rw [pow_one, hα, ← map_pow, hφ2, map_one]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hfix : ∀ r ∈ R, α r = r := by
    intro r hr
    apply hinj
    rw [hψα, hvR r hr, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨g, hg⟩ := hb α ⟨1, hα2⟩ hfix
  have hαg : ∀ k, α k = g * k * g⁻¹ := fun k => by rw [hg, MulAut.conj_apply]
  have hgR : g ∈ Subgroup.centralizer (R : Set (modelUniv t n p e Fact.out).K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := hfix r hr
    rw [hαg] at h1
    calc r * g = g * r * g⁻¹ * g := by rw [h1]
      _ = g * r := by group
  have hg2 : g * g = 1 := by
    have hc : g * g ∈ Subgroup.center (modelUniv t n p e Fact.out).K := by
      rw [Subgroup.mem_center_iff]
      intro k
      have h1 : α (α k) = k := by
        have h2 := congrArg (fun β : MulAut (modelUniv t n p e Fact.out).K => β k) hα2
        simpa [pow_two, MulAut.mul_apply] using h2
      rw [hαg, hαg] at h1
      calc k * (g * g) = g * (g * k * g⁻¹) * g⁻¹ * (g * g) := by rw [h1]
        _ = g * g * k := by group
    rw [RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 ht n hadm.2.1] at hc
    exact Subgroup.mem_bot.mp hc
  have hvψ : ∀ k, v * ψ k = ψ (g * k * g⁻¹) * v := fun k => by
    rw [← hαg, hψα, hvinv, mul_assoc (v * ψ k) v v, hv2, mul_one]
  rcases ha1 g hgR hg2 with h1 | hgRm
  · left
    rintro _ ⟨k, rfl⟩
    rw [hvψ, h1]
    simp
  · rcases hx.unique g hgRm hg2 with h1 | h1
    · left
      rintro _ ⟨k, rfl⟩
      rw [hvψ, h1]
      simp
    · right
      have hxv : v * ψ x = ψ x * v := hvR x hx.mem
      have hx2 : ψ x * ψ x = 1 := by rw [← map_mul, hx.sq, map_one]
      rintro _ ⟨k, rfl⟩
      calc v * ψ x * ψ k = ψ x * (v * ψ k) := by rw [hxv, mul_assoc]
        _ = ψ x * (ψ (x * k * x⁻¹) * v) := by rw [hvψ, h1]
        _ = (ψ x * ψ x) * ψ k * (ψ x)⁻¹ * v := by rw [map_mul, map_mul, map_inv]; group
        _ = ψ k * ψ x * v := by
          rw [hx2, one_mul, inv_eq_of_mul_eq_one_right hx2]
        _ = ψ k * (v * ψ x) := by rw [mul_assoc, ← hxv]

end CFSG.ClassicalInvolution.NDB.ExoticModel
