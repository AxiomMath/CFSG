module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Frat

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B K : Subgroup G}

theorem sec8t84a2_inv (h8A : Asc82Lemma8A) (h8B : Asc82Lemma8B) (h6 : Asc82Tab6M)
    (hK : Sec8T84K G t L S z g B K) {L1 : Subgroup G} (hle : L1 ≤ K) (hB : B ≤ L1)
    (hinv : ∀ h ∈ Hsub8 t B K, ∀ x ∈ L1, h * x * h⁻¹ ∈ L1) :
    ∀ n ∈ Nsub8 t B, ∀ x ∈ L1, n * x * n⁻¹ ∈ L1 ⊔ oddCoreIn (Nsub8 t B) := by
  intro n hn x hx
  have hpre : Sec8T84A1Pre G t L S z g B K :=
    ⟨hK.ctx, hK.le_C, hK.syl, hK.A_le, hK.card, hK.cent_t, hK.tau⟩
  obtain ⟨k, hk, h, hh, o, ho, rfl⟩ := sec8t84a1_dec h8A h8B h6 hpre n hn
  have hkN : k ∈ Nsub8 t B := (hK.le_C hk).1
  have hhN : h ∈ Nsub8 t B := (sec8t84a1_mem_H.1 hh).1
  have hxN : x ∈ Nsub8 t B := (hK.le_C (hle hx)).1
  have ho₁ : (x⁻¹ * o * x) * o⁻¹ ∈ oddCoreIn (Nsub8 t B) := by
    have h1 : x⁻¹ * o * x ∈ oddCoreIn (Nsub8 t B) := by
      simpa only [inv_inv] using
        sec8t84a1_O_norm x⁻¹ ((Nsub8 t B).inv_mem hxN) o ho
    exact (oddCoreIn (Nsub8 t B)).mul_mem h1 ((oddCoreIn (Nsub8 t B)).inv_mem ho)
  have hx2 : h * x * h⁻¹ ∈ L1 := hinv h hh x hx
  have ho₂ : h * ((x⁻¹ * o * x) * o⁻¹) * h⁻¹ ∈ oddCoreIn (Nsub8 t B) :=
    sec8t84a1_O_norm h hhN _ ho₁
  have hx3 : k * (h * x * h⁻¹) * k⁻¹ ∈ L1 := by
    have hB' : k * (h * x * h⁻¹) * k⁻¹ * (h * x * h⁻¹)⁻¹ ∈ L1 :=
      hB (hK.comm_le k hk _ (hle hx2))
    have heq : k * (h * x * h⁻¹) * k⁻¹ =
        (k * (h * x * h⁻¹) * k⁻¹ * (h * x * h⁻¹)⁻¹) * (h * x * h⁻¹) := by group
    rw [heq]
    exact L1.mul_mem hB' hx2
  have ho₃ : k * (h * ((x⁻¹ * o * x) * o⁻¹) * h⁻¹) * k⁻¹ ∈ oddCoreIn (Nsub8 t B) :=
    sec8t84a1_O_norm k hkN _ ho₂
  have key : (k * h * o) * x * (k * h * o)⁻¹ =
      (k * (h * x * h⁻¹) * k⁻¹) * (k * (h * ((x⁻¹ * o * x) * o⁻¹) * h⁻¹) * k⁻¹) := by
    group
  rw [key]
  exact Subgroup.mul_mem_sup hx3 ho₃

end CFSG.OddStandard.SmallF3.Omega
