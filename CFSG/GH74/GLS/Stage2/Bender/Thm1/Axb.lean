module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed
public import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup
open scoped commutatorElement

theorem ig_11_7_thm : IG_11_7 := by
  intro G _ _ p hp A B P hP hB hA hAP hBP hAB hfix
  have : Fact p.Prime := ⟨hp⟩
  have hA' : ¬ p ∣ Nat.card ↥A := (Nat.Prime.coprime_iff_not_dvd hp).mp hA
  let α : ↥A →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hAP)
  let β : ↥B →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  have hα : ∀ (a : ↥A) (q : ↥P), ((α a q : ↥P) : G) = (a : G) * q * (a : G)⁻¹ := fun _ _ => rfl
  have hβ : ∀ (b : ↥B) (q : ↥P), ((β b q : ↥P) : G) = (b : G) * q * (b : G)⁻¹ := fun _ _ => rfl
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    ext q
    simp only [MulAut.mul_apply]
    rw [hα, hβ, hβ, hα]
    have hab : (a : G) * b = b * a := hAB a a.2 b b.2
    calc (a : G) * ((b : G) * q * (b : G)⁻¹) * (a : G)⁻¹
        = ((a : G) * b) * q * ((a : G) * b)⁻¹ := by group
      _ = ((b : G) * a) * q * ((b : G) * a)⁻¹ := by rw [hab]
      _ = (b : G) * ((a : G) * q * (a : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    intro a r hr
    have hrB : ∀ b ∈ B, (r : G) * b = b * r := by
      intro b hb
      have h := congrArg Subtype.val (hr ⟨b, hb⟩)
      rw [hβ] at h
      calc (r : G) * b = b * r * b⁻¹ * b := by rw [h]
        _ = b * r := by group
    have hrmem : (r : G) ∈ P ⊓ centralizer (B : Set G) :=
      ⟨r.2, Subgroup.mem_centralizer_iff.mpr fun b hb => (hrB b hb).symm⟩
    have hcr : (a : G) * r = r * a :=
      (Subgroup.mem_centralizer_iff.mp (hfix a.2) (r : G) hrmem).symm
    apply Subtype.ext
    rw [hα]
    calc (a : G) * r * (a : G)⁻¹ = r * a * (a : G)⁻¹ := by rw [hcr]
      _ = r := by group
  have h := CFSG.GroupTheory.thompson_A_times_B hP hA' hB α β hcomm hfix'
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h1 := congrArg (fun φ : MulAut ↥P => ((φ ⟨q, hq⟩ : ↥P) : G)) (h ⟨a, ha⟩)
  rw [hα] at h1
  change a * q * a⁻¹ = ((1 : MulAut ↥P) ⟨q, hq⟩ : G) at h1
  rw [MulAut.one_apply] at h1
  calc q * a = a * q * a⁻¹ * a := by rw [h1]
    _ = a * q := by group

theorem ig_11_8_thm : IG_11_8 := ig_11_8_of ig_11_7_thm

end CFSG.GH74.GLS.Stage2.Bender.Thm1
