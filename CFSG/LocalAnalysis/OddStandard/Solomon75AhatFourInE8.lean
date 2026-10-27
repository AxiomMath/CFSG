module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FirstConn
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatFourInE8Perm
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatFourInE8Lift

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS Equiv Equiv.Perm
open CFSG.OddStandard.Solomon75.AhatData

namespace FourPartner

section Transfer

variable {n : ℕ} {K : Type} [Group K]

theorem map_le_alt (C : CoverSetup n K) (T : Subgroup K) :
    T.map C.ρ ≤ alternatingGroup (Fin n) := by
  rintro _ ⟨t, -, rfl⟩
  exact Perm.mem_alternatingGroup.2 (C.sign_ρ t)

theorem isPGroup_ker_ρ (C : CoverSetup n K) : IsPGroup 2 C.ρ.ker := by
  rintro ⟨g, hg⟩
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have hgc : g ∈ center K := (C.ρ_eq_one_iff).1 hg
  show g ^ 2 ^ 1 = 1
  rw [pow_one, pow_two]
  exact C.sq_of_mem_center hgc

theorem isPGroup_center_of_cover (C : CoverSetup n K) : IsPGroup 2 (center K) := by
  rintro ⟨g, hg⟩
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show g ^ 2 ^ 1 = 1
  rw [pow_one, pow_two]
  exact C.sq_of_mem_center hg

theorem sylow_image_max (C : CoverSetup n K) (T : Sylow 2 K) {S' : Subgroup (Perm (Fin n))}
    (hA : S' ≤ alternatingGroup (Fin n)) (h2 : IsPGroup 2 S')
    (hle : (T : Subgroup K).map C.ρ ≤ S') : S' = (T : Subgroup K).map C.ρ := by
  have hT' : IsPGroup 2 (S'.comap C.ρ) := h2.comap_of_ker_isPGroup C.ρ (isPGroup_ker_ρ C)
  have hTle : (T : Subgroup K) ≤ S'.comap C.ρ := fun t ht => hle ⟨t, ht, rfl⟩
  have heq : S'.comap C.ρ = T := T.is_maximal' hT' hTle
  have hrange : S' ≤ C.ρ.range := by
    intro g hg
    obtain ⟨y, hy⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1 (hA hg))
    exact ⟨y, hy⟩
  rw [← Subgroup.map_comap_eq_self hrange, heq]

theorem sylow_image_data (C : CoverSetup n K) (T : Sylow 2 K) :
    (T : Subgroup K).map C.ρ ≤ alternatingGroup (Fin n) ∧
      IsPGroup 2 ((T : Subgroup K).map C.ρ) ∧
      ∀ S' : Subgroup (Perm (Fin n)), S' ≤ alternatingGroup (Fin n) → IsPGroup 2 S' →
        (T : Subgroup K).map C.ρ ≤ S' → S' = (T : Subgroup K).map C.ρ :=
  ⟨map_le_alt C _, T.isPGroup'.map C.ρ, fun S' hA h2 hle => sylow_image_max C T hA h2 hle⟩

theorem ρ_involutive (C : CoverSetup n K) {y : K} (hy : y * y = 1) :
    ∀ w, C.ρ y (C.ρ y w) = w := by
  intro w
  have : C.ρ (y * y) = 1 := by rw [hy, map_one]
  simpa [map_mul, Perm.mul_apply] using congrArg (fun p => p w) this

open CFSG.ComponentClassification.HarrisLit.T1.S74.L38 in
theorem exists_elemAbelian_eight {n : ℕ} (hn : 12 ≤ n) {K : Type} [Group K] [Finite K]
    (C : CoverSetup n K) (T : Sylow 2 K) {z : K} (hz : z ∈ center K) (hz1 : z ≠ 1)
    (hzT : z ∈ (T : Subgroup K)) {b : K} (hbT : b ∈ (T : Subgroup K)) (hb2 : b * b = 1)
    (hbc : b ∉ center K) :
    ∃ E : Subgroup K, E ≤ T ∧ Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ b ∈ E ∧ z ∈ E := by
  obtain ⟨hSA, hS2, hmax⟩ := sylow_image_data C T
  have hσ2 := ρ_involutive C hb2
  have h8 : 8 ∣ (C.ρ b).support.card := (C.sq_eq_one_iff (by omega) hσ2).1 hb2
  obtain ⟨τ, hτS, hτ2, hστ, hτ8, h8', hne⟩ :=
    exists_partner_of_sylow hn hSA hS2 hmax (σ := C.ρ b) ⟨b, hbT, rfl⟩ hσ2 h8
  obtain ⟨y, hyT, hyτ⟩ := hτS
  have hy2' : ∀ w, C.ρ y (C.ρ y w) = w := by
    rw [hyτ]
    exact hτ2
  have hy2 : y * y = 1 := (C.sq_eq_one_iff (by omega) hy2').2 (by rw [hyτ, hτ8])
  have hby2' : ∀ w, C.ρ (b * y) (C.ρ (b * y) w) = w := by
    intro w
    simp only [map_mul, Perm.mul_apply, hyτ]
    rw [hστ w, hτ2 (C.ρ b w)]
    exact hσ2 w
  have hby8 : 8 ∣ (C.ρ (b * y)).support.card := by
    rw [map_mul, hyτ]
    exact h8'
  have hby2 : (b * y) * (b * y) = 1 := (C.sq_eq_one_iff (by omega) hby2').2 hby8
  have hcomm : Commute b y := by
    have h1 : (b * y)⁻¹ = b * y := inv_eq_of_mul_eq_one_right hby2
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    show b * y = y * b
    calc b * y = (b * y)⁻¹ := h1.symm
      _ = y⁻¹ * b⁻¹ := mul_inv_rev b y
      _ = y * b := by rw [hbi, hyi]
  have hτ1 : τ ≠ 1 := fun h => by
    rw [h] at hτ8
    simp at hτ8
  have hb1 : b ≠ 1 := fun h => hbc (h ▸ one_mem _)
  have hy1 : y ≠ 1 := fun h => hτ1 (by rw [← hyτ, h, map_one])
  have hby : b ≠ y := by
    intro h
    apply hne
    subst h
    ext w
    rw [← hyτ]
    simp [Perm.mul_apply, hσ2 w]
  have hV4 : Nat.card (four b y hb2 hy2 hcomm) = 4 := card_four hb2 hy2 hcomm hb1 hy1 hby
  have hρz : C.ρ z = 1 := (C.ρ_eq_one_iff).2 hz
  have hzV : z ∉ four b y hb2 hy2 hcomm := by
    intro h
    rcases mem_four.1 h with h | h | h | h
    · apply hne
      have : C.ρ (b * y) = 1 := by rw [← h, hρz]
      rwa [map_mul, hyτ] at this
    · exact hbc (h ▸ hz)
    · exact hτ1 (by rw [← hyτ, ← h, hρz])
    · exact hz1 h
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_sup_zpowers (isElemAbelian_four b y hb2 hy2 hcomm)
    (C.sq_of_mem_center hz) hzV (fun v _ => mem_center_iff.1 hz v)
  refine ⟨four b y hb2 hy2 hcomm ⊔ zpowers z,
    sup_le (four_le hbT hyT) (Subgroup.zpowers_le.2 hzT), hEab, ?_,
    Subgroup.mem_sup_left left_mem_four, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  rw [hEcard, hV4]

theorem exists_noncentral_invol {n : ℕ} (hn : 12 ≤ n) {K : Type} [Group K]
    (C : CoverSetup n K) (T : Sylow 2 K) :
    ∃ y ∈ (T : Subgroup K), y * y = 1 ∧ y ∉ center K := by
  obtain ⟨hSA, hS2, hmax⟩ := sylow_image_data C T
  obtain ⟨τ, hτS, hτ2, -, hτ8, -, -⟩ := exists_partner_of_sylow hn hSA hS2 hmax
    (σ := 1) (Subgroup.one_mem _) (fun _ => rfl) (by simp)
  obtain ⟨y, hyT, hyτ⟩ := hτS
  have hy2' : ∀ w, C.ρ y (C.ρ y w) = w := by
    rw [hyτ]
    exact hτ2
  refine ⟨y, hyT, (C.sq_eq_one_iff (by omega) hy2').2 (by rw [hyτ, hτ8]), fun hc => ?_⟩
  have h1 : C.ρ y = 1 := (C.ρ_eq_one_iff).2 hc
  rw [hyτ] at h1
  rw [h1] at hτ8
  simp at hτ8

end Transfer

end FourPartner

open FourPartner

theorem ahatFourInE8_of_twelve_le {n : ℕ} (hn : 12 ≤ n) : AhatFourInE8 n := by
  intro K _ _ hK T
  classical
  let C := CoverSetup.ofCover hK
  obtain ⟨z, hz, hz1, hzu⟩ := C.exists_central_generator
  have hzT : z ∈ (T : Subgroup K) :=
    IsPGroup.le_sylow_of_normal (isPGroup_center_of_cover C) T hz
  have hz2 : z * z = 1 := C.sq_of_mem_center hz
  refine fourInE8_of_invol hzT hz2 hz1 (fun p _ => mem_center_iff.1 hz p) ?_
  intro b hbT hb2
  have hb2' : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb2, pow_two] at this
  by_cases hbc : b ∈ center K
  · have hb1 : b ≠ 1 := fun h => by
      rw [h, orderOf_one] at hb2
      omega
    have hbz : b = z := (hzu b hbc).resolve_left hb1
    obtain ⟨y, hyT, hy2, hyc⟩ := exists_noncentral_invol hn C T
    obtain ⟨E, hET, hEab, hE8, -, hzE⟩ :=
      exists_elemAbelian_eight hn C T hz hz1 hzT hyT hy2 hyc
    exact ⟨E, hET, hEab, hE8, hbz ▸ hzE⟩
  · obtain ⟨E, hET, hEab, hE8, hbE, -⟩ :=
      exists_elemAbelian_eight hn C T hz hz1 hzT hbT hb2' hbc
    exact ⟨E, hET, hEab, hE8, hbE⟩

theorem ahatFourInE8_holds (n : ℕ) (hn : 8 ≤ n) :
    AhatFourInE8 n := by
  by_cases h12 : 12 ≤ n
  · exact ahatFourInE8_of_twelve_le h12
  · have : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact ahatFourInE8_of_coverSylowData coverSylowData_eight_of_certificate
    · exact ahatFourInE8_of_coverSylowData coverSylowData_nine_of_certificate
    · exact ahatFourInE8_of_coverSylowData coverSylowData_ten_of_certificate
    · exact ahatFourInE8_of_coverSylowData coverSylowData_eleven_of_certificate

end CFSG.OddStandard.Solomon75
