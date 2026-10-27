module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdBalJ

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

@[expose] def FusionSet (L : Subgroup G) (z : G) : Set G :=
  {y | y ∈ L ∧ orderOf y = 2 ∧ ∃ g : G, g * z * g⁻¹ = z * y}

omit [Finite G] in
theorem fusionAll_iff {L : Subgroup G} {z : G} :
    FusionAll L z ↔ ∀ y ∈ L, orderOf y = 2 → y ∈ FusionSet L z :=
  ⟨fun hF y hy hy2 => ⟨hy, hy2, hF y hy hy2⟩, fun hF y hy hy2 => (hF y hy hy2).2.2⟩

@[expose] def conjSub (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem mem_conjSub_iff {g x : G} {H : Subgroup G} : x ∈ conjSub g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem FusionSet.conj (h : Setting G L n) (d : Cyc L Q z) {y l : G} (hy : y ∈ FusionSet L z)
    (hl : l ∈ L) : l * y * l⁻¹ ∈ FusionSet L z := by
  obtain ⟨hyL, hy2, g, hg⟩ := hy
  have hlz : l * z = z * l := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hl)
  refine ⟨mul_mem (mul_mem hl hyL) (inv_mem hl), ?_, l * g, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy2
  · calc l * g * z * (l * g)⁻¹ = l * (g * z * g⁻¹) * l⁻¹ := by group
      _ = l * (z * y) * l⁻¹ := by rw [hg]
      _ = (l * z * l⁻¹) * (l * y * l⁻¹) := by group
      _ = z * (l * y * l⁻¹) := by
          have : l * z * l⁻¹ = z := by rw [hlz]; group
          rw [this]

theorem mem_conjSub_of_partner (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {y g : G} (hy : y ∈ L)
    (hg : g * z * g⁻¹ = z * y) : y ∈ conjSub g L := by
  have hyz : y * z = z * y := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hy)
  have hzz := d.mul_self
  have hg' : z = g⁻¹ * (z * y) * g := by rw [← hg]; group
  have hwc : (g⁻¹ * z * g) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * z * g * z = g⁻¹ * z * g * (g⁻¹ * (z * y) * g) := by rw [← hg']
      _ = g⁻¹ * (z * z * y) * g := by group
      _ = g⁻¹ * y * g := by rw [hzz]; group
      _ = g⁻¹ * (z * y * z) * g := by
          have : z * y * z = y := by
            calc z * y * z = z * (y * z) := mul_assoc _ _ _
              _ = z * (z * y) := by rw [hyz]
              _ = (z * z) * y := (mul_assoc _ _ _).symm
              _ = y := by rw [hzz, one_mul]
          rw [this]
      _ = z * (g⁻¹ * z * g) := by
          calc g⁻¹ * (z * y * z) * g = (g⁻¹ * (z * y) * g) * (g⁻¹ * z * g) := by group
            _ = z * (g⁻¹ * z * g) := by rw [← hg']
  obtain ⟨l, hl, q, hq, hlq⟩ := (mem_sup_iff_mul d).1 (hE hwc)
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with hq1 | hq1
  · exfalso
    have := not_conj_mem_L h d hQ2 g⁻¹
    rw [inv_inv] at this
    apply this
    rw [← hlq, hq1, mul_one]
    exact hl
  ·
    rw [hq1] at hlq
    rw [mem_conjSub_iff]
    have hl' : l = g⁻¹ * z * g * z := by
      calc l = l * z * z := by rw [mul_assoc, hzz, mul_one]
        _ = g⁻¹ * z * g * z := by rw [hlq]
    have : g⁻¹ * y * g = l := by
      calc g⁻¹ * y * g = g⁻¹ * (z * (z * y)) * g := by
            rw [← mul_assoc z z y, hzz, one_mul]
        _ = (g⁻¹ * z * g) * (g⁻¹ * (z * y) * g) := by group
        _ = (g⁻¹ * z * g) * z := by rw [← hg']
        _ = l := hl'.symm
    rw [this]
    exact hl

end CFSG.OddStandard.AltStdSec
