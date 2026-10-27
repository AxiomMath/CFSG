module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe11Loc
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeP

public section

namespace CFSG.ComponentClassification.SolMax.He11

open CFSG Subgroup CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {Y : Type*} [Group Y]

theorem he_local
    (Φ : Y ≃* heP) {s : MulAut Y}
    (hΦs : MulAut.congr Φ s = heConjR ⟨heAutU, heAutU_mem_heAutGroup⟩) {L N : Subgroup Y}
    (hL : L ≤ fixedSubgroup s) (hLp : ⁅L, L⁆ = L) (h2520 : 2520 ∣ Nat.card L) (hNL : N ≤ L)
    (hNn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) (hNodd : Odd (Nat.card N)) :
    (∀ g : Y, s g = g → (∀ q ∈ L, q⁻¹ * (g * q * g⁻¹) ∈ N) → g ∈ L ∧ g ^ 3 = 1) ∧
      (∀ φ : MulAut Y, φ * s = s * φ → (∀ q ∈ L, q⁻¹ * φ q ∈ N) →
        φ ^ 3 = 1 ∨ (φ * s) ^ 3 = 1) ∧
      Nat.card L < Nat.card (fixedSubgroup s) := by
  set u' : heAutGroup := ⟨heAutU, heAutU_mem_heAutGroup⟩ with hu'def
  set ι : Y →* Equiv.Perm (Fin 8330) := heP.subtype.comp Φ.toMonoidHom with hιdef
  have hι : Function.Injective ι := heP.subtype_injective.comp Φ.injective
  have hF : (fixedSubgroup s).map ι = heOuterC := by
    rw [hιdef, ← Subgroup.map_map, FiveFHe.map_fixedSubgroup_congr Φ s, hΦs,
      map_fixedSubgroup_heConjR, heOuterC_eq]
  have hfixι : ∀ y ∈ fixedSubgroup s, ι y ∈ heOuterC := fun y hy => hF ▸ mem_map_of_mem ι hy
  have hLD : L.map ι = heOuterD := by
    apply eq_heOuterD_of_perfect
    · rw [← hF]
      exact map_mono hL
    · rw [← map_commutator, hLp]
    · rw [card_map_of_injective hι]
      exact h2520
  have hNC : ∀ n ∈ N.map ι, ∀ d ∈ heOuterD, n * d = d * n := by
    apply commute_of_odd_normal
    · rw [← hLD]
      exact map_mono hNL
    · rw [← hLD]
      rintro _ ⟨l, hl, rfl⟩ _ ⟨n, hn, rfl⟩
      exact ⟨l * n * l⁻¹, hNn l hl n hn, by simp only [map_mul, map_inv]⟩
    · rw [card_map_of_injective hι]
      exact hNodd
  have hcent : ∀ z : Equiv.Perm (Fin 8330),
      (∀ q ∈ L, (ι q)⁻¹ * (z * ι q * z⁻¹) ∈ N.map ι) → ∀ d ∈ heOuterD, z * d = d * z := by
    intro z hz
    apply commute_of_perfect heOuterD_perfect
    intro d hd
    rw [← hLD] at hd
    obtain ⟨q, hq, rfl⟩ := hd
    have h1 := hz q hq
    refine ⟨?_, fun e he => hNC _ h1 e he⟩
    rw [← hLD]
    exact map_mono hNL h1
  refine ⟨fun g hg hgN => ?_, fun φ hφs hφN => ?_, ?_⟩
  ·
    have hzD := hcent (ι g) fun q hq => by
      have h1 := mem_map_of_mem ι (hgN q hq)
      simpa only [map_mul, map_inv] using h1
    obtain ⟨hgD, hg3⟩ := mem_heOuterD_of_commute (hfixι g hg) hzD
    rw [← hLD] at hgD
    obtain ⟨q, hq, hqg⟩ := hgD
    exact ⟨hι hqg ▸ hq, hι (by rw [map_pow, hg3, map_one])⟩
  ·
    have hbij := ctbh_full_automorphism_permutation_model.1
    obtain ⟨z, hz⟩ := hbij.2 (MulAut.congr Φ φ)
    have hzu : z * u' = u' * z := hbij.1 (by
      rw [map_mul, map_mul, hz, ← hΦs, ← map_mul, ← map_mul, hφs])
    have hzapp : ∀ y, (z : Equiv.Perm (Fin 8330)) * ι y * (z : Equiv.Perm (Fin 8330))⁻¹ =
        ι (φ y) := fun y => by
      have h1 : heConjR z (Φ y) = Φ (φ y) := by
        rw [hz]
        simp [MulAut.congr_apply]
      have h2 := congrArg (fun p : heP => (p : Equiv.Perm (Fin 8330))) h1
      simp only [heConjR_apply] at h2
      exact h2
    have hzD := hcent z fun q hq => by
      have h1 := mem_map_of_mem ι (hφN q hq)
      rw [hzapp q]
      simpa only [map_mul, map_inv] using h1
    obtain ⟨hP, hnP⟩ := cube_of_commute z.2 (congrArg Subtype.val hzu) hzD
    by_cases hzP : (z : Equiv.Perm (Fin 8330)) ∈ heP
    · left
      obtain ⟨-, hz3⟩ := hP hzP
      have hz3' : z ^ 3 = 1 := Subtype.ext (by rw [coe_pow]; exact hz3)
      apply (MulAut.congr Φ).injective
      rw [map_pow, ← hz, ← map_pow, hz3', map_one, map_one]
    · right
      obtain ⟨-, hzu3⟩ := hnP hzP
      have hz3' : (z * u') ^ 3 = 1 := Subtype.ext (by rw [coe_pow, coe_mul]; exact hzu3)
      apply (MulAut.congr Φ).injective
      rw [map_pow, map_mul, ← hz, hΦs, ← map_mul, ← map_pow, hz3', map_one, map_one]
  ·
    have h1 : Nat.card L = 7560 := by rw [← card_map_of_injective hι, hLD, card_heOuterD]
    have h2 : Nat.card (fixedSubgroup s) = 15120 := by
      rw [← card_map_of_injective hι, hF, card_heOuterC]
    omega

end CFSG.ComponentClassification.SolMax.He11
