module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Models5

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

structure NabModel (M : Type*) [Group M] : Prop where
  card : Nat.card M = 64
  comm_central : ∀ a b c : M, ⁅a, b⁆ * c = c * ⁅a, b⁆
  central_card : ∀ Z : Subgroup M, (∀ z ∈ Z, ∀ c : M, z * c = c * z) → Nat.card Z ≤ 4
  Q : ∀ w : M, (∃ h : M, w * h ≠ h * w) → ∀ z : M, (∀ c : M, z * c = c * z) →
    ∃ h : M, ⁅w, h⁆ = z

theorem NabModel.of_equiv {M N : Type*} [Group M] [Group N] (e : M ≃* N) (h : NabModel N) :
    NabModel M := by
  obtain ⟨hcard, hcomm, hcen⟩ := transport_nonabelian e h.card h.comm_central h.central_card
  refine ⟨hcard, hcomm, hcen, ?_⟩
  intro w hw z hz
  obtain ⟨h0, hh0⟩ := hw
  have hw' : ∃ h' : N, e w * h' ≠ h' * e w := by
    refine ⟨e h0, fun h1 => hh0 (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h1
  have hz' : ∀ c : N, e z * c = c * e z := by
    intro c
    obtain ⟨c', rfl⟩ := e.surjective c
    rw [← map_mul, ← map_mul, hz c']
  obtain ⟨h', hh'⟩ := h.Q (e w) hw' (e z) hz'
  refine ⟨e.symm h', e.injective ?_⟩
  rw [map_commutatorElement, MulEquiv.apply_symm_apply]
  exact hh'

theorem UT3_Q (w z : UT3 (GaloisField 2 2)) (hw : ∃ h, w * h ≠ h * w)
    (hz : ∀ c, z * c = c * z) : ∃ h : UT3 (GaloisField 2 2), ⁅w, h⁆ = z := by
  obtain ⟨hza, hzb⟩ := UT3.central_ab z hz
  have hw' : w.a ≠ 0 ∨ w.b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h, hh⟩ := hw
    apply hh
    ext <;> simp [hcon.1, hcon.2]; ring
  by_cases ha : w.a = 0
  · have hb : w.b ≠ 0 := by tauto
    refine ⟨⟨-(z.c / w.b), 0, 0⟩, ?_⟩
    rw [UT3.commutator_eq]
    ext
    · simp [hza]
    · simp [hzb]
    · simp [ha]
      field_simp
  · refine ⟨⟨0, z.c / w.a, 0⟩, ?_⟩
    rw [UT3.commutator_eq]
    ext
    · simp [hza]
    · simp [hzb]
    · simp
      field_simp

theorem SylSU34_Q (w z : SylSU34) (hw : ∃ h : SylSU34, w * h ≠ h * w)
    (hz : ∀ c : SylSU34, z * c = c * z) : ∃ h : SylSU34, ⁅w, h⁆ = z := by
  have hza : (z : UT3 (GaloisField 2 4)).a = 0 := SylSU34_central_a z hz
  have hzb : (z : UT3 (GaloisField 2 4)).b = 0 := by
    rw [((mem_SylSU34_iff _).1 z.2).1, hza]; simp
  have hzc : (z : UT3 (GaloisField 2 4)).c + (z : UT3 (GaloisField 2 4)).c ^ 4 = 0 := by
    have h := ((mem_SylSU34_iff _).1 z.2).2
    rw [hza] at h
    simpa using h
  have hwb : (w : UT3 (GaloisField 2 4)).b = (w : UT3 (GaloisField 2 4)).a ^ 4 :=
    ((mem_SylSU34_iff _).1 w.2).1
  have hwa : (w : UT3 (GaloisField 2 4)).a ≠ 0 := by
    intro hwa0
    obtain ⟨h, hh⟩ := hw
    apply hh
    apply Subtype.ext
    have hwb0 : (w : UT3 (GaloisField 2 4)).b = 0 := by rw [hwb, hwa0]; simp
    show (w : UT3 (GaloisField 2 4)) * h = h * w
    ext <;> simp [hwa0, hwb0]
    ring
  obtain ⟨a, ha⟩ : ∃ a : GaloisField 2 4, a = (w : UT3 (GaloisField 2 4)).a := ⟨_, rfl⟩
  rw [← ha] at hwa hwb
  obtain ⟨zc, hzcdef⟩ : ∃ zc : GaloisField 2 4, zc = (z : UT3 (GaloisField 2 4)).c := ⟨_, rfl⟩
  rw [← hzcdef] at hzc
  have hz4 : zc ^ 4 = zc := by linear_combination hzc + (-zc) * gf16_char2
  have h20 : a ^ 20 = a ^ 5 := by
    have h16 := gf16_pow16 a
    calc a ^ 20 = a ^ 4 * a ^ 16 := by ring
      _ = a ^ 4 * a := by rw [h16]
      _ = a ^ 5 := by ring
  have hr4 : (zc / a ^ 5) ^ 4 = zc / a ^ 5 := by
    rw [div_pow, ← pow_mul, show 5 * 4 = 20 from rfl, h20, hz4]
  have hr : tauHom (zc / a ^ 5) = 0 := by
    rw [tau_apply, hr4]
    linear_combination (zc / a ^ 5) * gf16_char2
  have hrange : zc / a ^ 5 ∈ tauHom.range := by
    rw [range_tau_eq_ker]
    exact hr
  obtain ⟨s, hs⟩ := hrange
  rw [tau_apply] at hs
  have hs' : a ^ 5 * (s + s ^ 4) = zc := by
    rw [hs]
    field_simp
  obtain ⟨cc, hcc⟩ := exists_tau_eq (a * s)
  let h : SylSU34 := ⟨⟨a * s, (a * s) ^ 4, cc⟩, (mem_SylSU34_iff _).2 ⟨rfl, by
    show cc + cc ^ 4 + (a * s) * (a * s) ^ 4 = 0
    linear_combination hcc + ((a * s) * (a * s) ^ 4) * gf16_char2⟩⟩
  refine ⟨h, ?_⟩
  apply Subtype.ext
  show ⁅(w : UT3 (GaloisField 2 4)), (h : UT3 (GaloisField 2 4))⁆ = (z : UT3 (GaloisField 2 4))
  rw [UT3.commutator_eq]
  ext
  · simp [hza]
  · simp [hzb]
  · show (w : UT3 (GaloisField 2 4)).a * (a * s) ^ 4 - (a * s) * (w : UT3 (GaloisField 2 4)).b =
      (z : UT3 (GaloisField 2 4)).c
    rw [hwb, ← ha, ← hzcdef]
    linear_combination hs' + (-(a ^ 5 * s)) * gf16_char2

theorem nabModel_UT3 : NabModel (UT3 (GaloisField 2 2)) := by
  refine ⟨?_, UT3.comm_central, UT3_gf4_central_card, fun w hw z hz => UT3_Q w z hw hz⟩
  rw [UT3.card_eq]
  have := GaloisField.card 2 2 (by norm_num)
  simp at this
  rw [this]; norm_num

theorem nabModel_Syl : NabModel SylSU34 :=
  ⟨card_SylSU34, SylSU34_comm_central, SylSU34_central_card,
    fun w hw z hz => SylSU34_Q w z hw hz⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
