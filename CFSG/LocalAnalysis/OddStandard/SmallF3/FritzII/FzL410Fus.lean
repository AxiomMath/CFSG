module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410FusK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410FusB

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem fusion {e g : G} (he : e ∈ E) (hg : g * t * g⁻¹ = e * (t * s)) :
    ∃ n ∈ normalizer (R : Set G), ∃ z ∈ Z, n * t * n⁻¹ = (e * (t * s)) * z := by
  obtain ⟨k, hk, hkZ⟩ := D.exists_k he hg
  have hRt : R ≤ fz410B Z t := D.R_le_B D.facts.fus_t
  have hRi : R ≤ fz410B Z (e * (t * s)) := D.R_le_B (D.facts.fus_ets e he)
  have hcard : Nat.card R = 2 ^ 8 := by rw [D.str.card_R]; norm_num
  let R' : Subgroup G := R.map (MulAut.conj k).toMonoidHom
  have hmemR' : ∀ x : G, x ∈ R' ↔ k⁻¹ * x * k ∈ R := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      show k⁻¹ * (k * y * k⁻¹) * k ∈ R
      rw [h]
      exact hy
    · intro hx
      refine ⟨k⁻¹ * x * k, hx, ?_⟩
      show k * (k⁻¹ * x * k) * k⁻¹ = x
      group
  have hR'B : R' ≤ fz410B Z (e * (t * s)) := by
    rintro x ⟨y, hy, rfl⟩
    exact (D.conj_B hk hkZ y).mp (hRt hy)
  have hR'card : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hRp : IsPGroup 2 R := IsPGroup.of_card hcard
  have hR'p : IsPGroup 2 R' := IsPGroup.of_card (hR'card.trans hcard)
  have hmax : ∀ Y : Subgroup G, Y ≤ fz410B Z (e * (t * s)) → IsPGroup 2 Y →
      Nat.card Y ≤ Nat.card R := by
    intro Y hY hYp
    let Y' : Subgroup G := Y.map (MulAut.conj k⁻¹).toMonoidHom
    have hY'B : Y' ≤ fz410B Z t := by
      rintro x ⟨y, hy, rfl⟩
      have h : k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ = y := by group
      refine (D.conj_B hk hkZ _).mpr ?_
      show k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ ∈ fz410B Z (e * (t * s))
      rw [h]
      exact hY hy
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hYp
    have hY'card : Nat.card Y' = Nat.card Y :=
      Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
    have hY'p : IsPGroup 2 Y' := IsPGroup.of_card (hY'card.trans hm)
    have hle := D.B_bound Y' hY'B hY'p
    rw [hY'card] at hle
    rw [hcard]
    exact hle
  obtain ⟨b, hbB, hb⟩ := fz410_sylow_conj hRi hR'B hRp hR'p hmax hR'card
  have hbB' : (∀ z ∈ Z, b * z = z * b) ∧ ∃ z ∈ Z, b * (e * (t * s)) * b⁻¹ = (e * (t * s)) * z :=
    hbB
  refine ⟨b * k, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro r
    have h1 : (b * k) * r * (b * k)⁻¹ = b * (k * r * k⁻¹) * b⁻¹ := by group
    have h2 : k⁻¹ * (k * r * k⁻¹) * k = r := by group
    have h3 := hb (k * r * k⁻¹)
    rw [hmemR', h2] at h3
    rw [h1]
    exact h3
  · obtain ⟨z, hz, hbz⟩ := hbB'.2
    refine ⟨z, hz, ?_⟩
    calc b * k * t * (b * k)⁻¹ = b * (k * t * k⁻¹) * b⁻¹ := by group
      _ = b * (e * (t * s)) * b⁻¹ := by rw [hk]
      _ = (e * (t * s)) * z := hbz

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
