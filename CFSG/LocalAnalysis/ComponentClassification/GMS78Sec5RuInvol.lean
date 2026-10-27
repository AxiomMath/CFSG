module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAct

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

theorem lin8_ext {r r' : Lin8} (h : ∀ t, linApply r t = linApply r' t) : r = r' := by
  obtain ⟨a₁, a₂, a₃⟩ := r
  obtain ⟨a₁', a₂', a₃'⟩ := r'
  have h1 := h 1
  have h2 := h 2
  have h4 := h 4
  rw [RuSimCode.linApply_one, RuSimCode.linApply_one] at h1
  rw [RuSimCode.linApply_two, RuSimCode.linApply_two] at h2
  rw [RuSimCode.linApply_four, RuSimCode.linApply_four] at h4
  simp only at h1 h2 h4
  rw [h1, h2, h4]

theorem bC_comm (m n : Nat) : bC m n = bC n m := by
  simp only [bC, Nat.xor_comm m n]
  generalize qC (n ^^^ m) = a
  generalize qC m = b
  generalize qC n = c
  revert a b c
  decide

theorem fin8_xor_solve : ∀ a b c d : Fin 8, a = b ^^^ c ^^^ d → d ^^^ a = b ^^^ c := by
  decide

end RuQCode

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

theorem ν_inv {a : G} (ha : a ∈ gmsA L T) : ν a⁻¹ = ν a := by
  have h := hM.ν_mul _ ha _ (inv_mem ha)
  rw [mul_inv_cancel, hM.ν_one] at h
  exact (RuQCode.fin8_eq_of_xor_eq_zero _ _ h.symm).symm

theorem comm_xor_sq_mem_image {y : G} (hyN : y ∈ normalizer (R : Set G)) (hy2 : y ^ 2 = 1)
    {r : Lin8} (hr : r ∈ invList) (hrA : ∀ b ∈ gmsA L T, ν (y * b * y⁻¹) = linApply r (ν b))
    (hrR : ∀ x ∈ R, μ (y * x * y⁻¹) = maskApply (adMat r) (μ x)) {w : G} (hw : w ∈ R)
    (hwf : maskApply (adMat r) (μ w) = μ w) :
    y * w * y⁻¹ * w⁻¹ ∈ gmsA L T ∧
      ∃ s : Fin 8, ν (y * w * y⁻¹ * w⁻¹) ^^^ qC (μ w) = linApply r s ^^^ s := by
  have hyR : ∀ x ∈ R, y * x * y⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hyN x).mp hx
  have hyinv : y⁻¹ = y := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hy2]
  have hcw : y * w * y⁻¹ * w⁻¹ ∈ gmsA L T :=
    hM.mul_inv_mem_of_μ_eq (hyR w hw) hw (by rw [hrR w hw, hwf])
  refine ⟨hcw, ?_⟩
  obtain ⟨n, hn, hnm⟩ := RuQCode.exists_image_eq hr (hM.lt w hw) hwf
  obtain ⟨u, hu, hun⟩ := hM.surj n hn
  set w' := y * u⁻¹ * y⁻¹ * u with hw'
  have hw'R : w' ∈ R := mul_mem (hyR _ (inv_mem hu)) hu
  have hμw' : μ w' = μ w := by
    rw [hw', hM.mul _ (hyR _ (inv_mem hu)) _ hu, hrR _ (inv_mem hu), hM.μ_inv hu, hun, hnm]
  set a := w' * w⁻¹ with ha
  have haA : a ∈ gmsA L T := hM.mul_inv_mem_of_μ_eq hw'R hw hμw'
  have hz : (y * w') ^ 2 = 1 := by
    have e : y * w' = u⁻¹ * y * u := by
      rw [hw']
      calc y * (y * u⁻¹ * y⁻¹ * u) = y * y * u⁻¹ * y⁻¹ * u := by group
        _ = u⁻¹ * y⁻¹ * u := by rw [← pow_two, hy2, one_mul]
        _ = u⁻¹ * y * u := by rw [hyinv]
    rw [e, pow_two, show u⁻¹ * y * u * (u⁻¹ * y * u) = u⁻¹ * (y * y) * u by group, ← pow_two,
      hy2]
    group
  have hcw' : y * w' * y⁻¹ * w'⁻¹ = w'⁻¹ * w'⁻¹ := by
    have h1 : y * w' * y * w' = 1 := by rw [← hz, pow_two]; group
    calc y * w' * y⁻¹ * w'⁻¹ = (y * w' * y * w') * w'⁻¹ * w'⁻¹ := by rw [hyinv]; group
      _ = w'⁻¹ * w'⁻¹ := by rw [h1, one_mul]
  have hν1 : ν (y * w' * y⁻¹ * w'⁻¹) = qC (μ w) := by
    rw [hcw', ← pow_two, hM.sq _ (inv_mem hw'R), hM.μ_inv hw'R, hμw']
  have hyaA : y * a * y⁻¹ ∈ gmsA L T := hM.normA y hyN a haA
  have hdec : y * w' * y⁻¹ * w'⁻¹ = (y * a * y⁻¹ * a⁻¹) * (y * w * y⁻¹ * w⁻¹) := by
    have hw'eq : w' = a * w := by rw [ha]; group
    have hcomm := hM.central _ (hM.le (inv_mem haA)) _ hcw
    calc y * w' * y⁻¹ * w'⁻¹ = (y * a * y⁻¹) * (y * w * y⁻¹ * w⁻¹) * a⁻¹ := by
          rw [hw'eq]; group
      _ = (y * a * y⁻¹) * (a⁻¹ * (y * w * y⁻¹ * w⁻¹)) := by
          rw [mul_assoc, ← hcomm]
      _ = (y * a * y⁻¹ * a⁻¹) * (y * w * y⁻¹ * w⁻¹) := by group
  rw [hdec, hM.ν_mul _ (mul_mem hyaA (inv_mem haA)) _ hcw,
    hM.ν_mul _ hyaA _ (inv_mem haA), hrA a haA, hM.ν_inv haA] at hν1
  exact ⟨ν a, RuQCode.fin8_xor_solve _ _ _ _ hν1.symm⟩

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
