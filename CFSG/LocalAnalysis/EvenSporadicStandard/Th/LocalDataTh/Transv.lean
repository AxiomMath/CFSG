module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvAa2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.ZCenter

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier
open scoped Matrix

section Certified


theorem transv_J : ∀ g : J, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g ∉ B →
    (∃ H : Subgroup J, H ≤ A ∧ Nat.card H = 8 ∧ ∀ a ∈ H, g * a = a * g) →
    ∀ K : Subgroup J, K ≤ AaJ → (∀ x ∈ K, g * x = x * g) → Nat.card K ≤ 16 := by
  intro g hgA hgB hH K hK hKg
  obtain ⟨h, w, hhA, hw, hg⟩ := exists_conj_q1 hgA hgB hH
  have R : AaRel := aaRel
  have W := thLocalWitness_J.toLocalIn_top
  have W2 := thLocalWitness2_J.toIn2
  have hAa : ∀ x ∈ AaJ, h⁻¹ * x * h ∈ AaJ := fun x hx => by
    have := ThLocalIn2.conj_mem_of_mem_L W W2 (n := h⁻¹) (Subgroup.mem_top _)
      (fun a ha => by simpa using conj_inv_mem_of_conj_mem hhA ha) x hx
    simpa using this
  set K' : Subgroup J := K.map (MulAut.conj h⁻¹).toMonoidHom with hK'
  have hK'mem : ∀ y ∈ K', ∃ x ∈ K, y = h⁻¹ * x * h := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  have hK'le : K' ≤ AaJ := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hK'mem y hy
    exact hAa x (hK hx)
  have hcard : Nat.card K' = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective
  have key : ∀ y ∈ K', q 1 * w * y = y * (q 1 * w) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hK'mem y hy
    have hgx := hKg x hx
    rw [hg] at hgx
    calc q 1 * w * (h⁻¹ * x * h) = h⁻¹ * ((h * q 1 * w * h⁻¹) * x) * h := by group
      _ = h⁻¹ * (x * (h * q 1 * w * h⁻¹)) * h := by rw [hgx]
      _ = (h⁻¹ * x * h) * (q 1 * w) := by group
  rw [← hcard]
  rcases W2.mem_Aa_or_mul_b W hw with hwA | hwb
  · apply card_le_16_of_centralizes_q1 R hK'le
    intro y hy
    have hyA := hK'le hy
    have h1 := key y hy
    have h2 : w * y = y * w := AaJ_comm R w hwA y hyA
    have h3 : (q 1 * y) * w = (y * q 1) * w := by
      calc (q 1 * y) * w = q 1 * (y * w) := by rw [mul_assoc]
        _ = q 1 * (w * y) := by rw [h2]
        _ = q 1 * w * y := by rw [mul_assoc]
        _ = y * (q 1 * w) := h1
        _ = (y * q 1) * w := by rw [mul_assoc]
    exact mul_right_cancel h3
  · obtain ⟨c, hcA, rfl⟩ : ∃ c ∈ AaJ, w = c * bAa :=
      ⟨w * bAa, hwb, by rw [mul_assoc, R.bsq, mul_one]⟩
    apply card_le_16_of_centralizes_q1b R hK'le
    intro y hy
    have hyA := hK'le hy
    have h1 := key y hy
    have hbinv : bAa⁻¹ = bAa := inv_eq_of_mul_eq_one_right R.bsq
    have hinv := bAa_inv R y hyA
    have hwy : c * bAa * y * (c * bAa)⁻¹ = y⁻¹ := by
      calc c * bAa * y * (c * bAa)⁻¹ = c * (bAa * y * bAa⁻¹) * c⁻¹ := by group
        _ = c * y⁻¹ * c⁻¹ := by rw [hinv]
        _ = y⁻¹ := by rw [AaJ_comm R c hcA y⁻¹ (AaJ.inv_mem hyA)]; group
    have hby : bAa * y = y⁻¹ * bAa := by
      calc bAa * y = (bAa * y * bAa⁻¹) * bAa := by group
        _ = y⁻¹ * bAa := by rw [hinv]
    have h3 : q 1 * y⁻¹ = y * q 1 := by
      calc q 1 * y⁻¹ = q 1 * (c * bAa * y * (c * bAa)⁻¹) := by rw [hwy]
        _ = (q 1 * (c * bAa) * y) * (c * bAa)⁻¹ := by group
        _ = (y * (q 1 * (c * bAa))) * (c * bAa)⁻¹ := by rw [h1]
        _ = y * q 1 := by group
    calc (q 1 * bAa) * y = q 1 * (bAa * y) := by rw [mul_assoc]
      _ = q 1 * (y⁻¹ * bAa) := by rw [hby]
      _ = (q 1 * y⁻¹) * bAa := by rw [mul_assoc]
      _ = (y * q 1) * bAa := by rw [h3]
      _ = y * (q 1 * bAa) := by rw [mul_assoc]

end Certified

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
