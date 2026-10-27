module

public import Mathlib.GroupTheory.Sylow
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.GroupTheory

open Subgroup

theorem eq_bot_of_isStronglyEmbeddedOrder {Y : Type*} [Group Y] [Finite Y]
    (hSE : ∀ S : Sylow 2 Y,
      CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (normalizer ((S : Subgroup Y) : Set Y)))
    {B : Subgroup Y} (hB : B ≠ ⊥) (hBodd : Odd (Nat.card B)) {s : Y}
    (hs : ∃ k : ℕ, orderOf s = 2 ^ k) (hinv : ∀ b ∈ B, s * b * s⁻¹ = b⁻¹)
    {R : Subgroup Y} (hR : IsPGroup 2 R) (hBR : B ≤ normalizer (R : Set Y))
    (hsR : s ∈ normalizer (R : Set Y)) : R = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hRne
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  set M : Subgroup Y := normalizer ((S : Subgroup Y) : Set Y) with hMdef
  have hSE' : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := hSE S
  have hSM : (S : Subgroup Y) ≤ M := Subgroup.le_normalizer
  have hNRM : normalizer (R : Set Y) ≤ M := by
    intro g hg
    by_contra hgM
    have hodd : Odd (Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup Y)) :=
      hSE'.2.2 g hgM
    have hRg : R.map (MulAut.conj g).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hle : R ≤ M ⊓ M.map (MulAut.conj g).toMonoidHom := by
      refine le_inf (hRS.trans hSM) ?_
      calc R = R.map (MulAut.conj g).toMonoidHom := hRg.symm
        _ ≤ (S : Subgroup Y).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hRS
        _ ≤ M.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono Subgroup.le_normalizer
    have hdvd : Nat.card R ∣ Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup Y) :=
      Subgroup.card_dvd_of_le hle
    have hoddR : Odd (Nat.card R) := hodd.of_dvd_nat hdvd
    have hR1 : 1 < Nat.card R := (Subgroup.one_lt_card_iff_ne_bot R).mpr hRne
    rcases hR.card_eq_or_dvd with h | h
    · omega
    · exact hoddR.not_two_dvd_nat h
  have hBM : B ≤ M := hBR.trans hNRM
  have hsM : s ∈ M := hNRM hsR
  have hsS : s ∈ (S : Subgroup Y) := by
    obtain ⟨k, hk⟩ := hs
    have hP : IsPGroup 2 (Subgroup.zpowers s) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hinf : Subgroup.zpowers s ⊓ normalizer ((S : Subgroup Y) : Set Y) =
        Subgroup.zpowers s ⊓ (S : Subgroup Y) :=
      IsPGroup.inf_normalizer_sylow (p := 2) hP S
    have hmem : s ∈ Subgroup.zpowers s ⊓ normalizer ((S : Subgroup Y) : Set Y) :=
      ⟨Subgroup.mem_zpowers s, hsM⟩
    rw [hinf] at hmem
    exact hmem.2
  have hBbot : B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    have hbM : b ∈ M := hBM hb
    have hbs : b * s⁻¹ * b⁻¹ ∈ (S : Subgroup Y) :=
      ((Subgroup.mem_normalizer_iff.mp hbM) s⁻¹).mp ((S : Subgroup Y).inv_mem hsS)
    have h1 : s * (b * s⁻¹ * b⁻¹) ∈ (S : Subgroup Y) := (S : Subgroup Y).mul_mem hsS hbs
    have h2 : s * (b * s⁻¹ * b⁻¹) = b⁻¹ * b⁻¹ := by
      rw [← mul_assoc, ← mul_assoc, hinv b hb]
    rw [h2] at h1
    have hb2S : b ^ 2 ∈ (S : Subgroup Y) := by
      have hinv' : (b ^ 2)⁻¹ ∈ (S : Subgroup Y) := by
        simpa only [pow_two, mul_inv_rev] using h1
      exact (S : Subgroup Y).inv_mem_iff.mp hinv'
    have hoddB : Odd (orderOf b) := hBodd.of_dvd_nat (B.orderOf_dvd_natCard hb)
    have hodd2 : Odd (orderOf (b ^ 2)) := hoddB.of_dvd_nat (orderOf_pow_dvd 2)
    have hb2_one : b ^ 2 = 1 := by
      by_contra hne
      have hne' : (⟨b ^ 2, hb2S⟩ : ↥(S : Subgroup Y)) ≠ 1 := by
        intro h
        exact hne (by simpa using congrArg Subtype.val h)
      have h2dvd : 2 ∣ orderOf (⟨b ^ 2, hb2S⟩ : ↥(S : Subgroup Y)) :=
        S.isPGroup'.dvd_orderOf hne'
      rw [Subgroup.orderOf_mk] at h2dvd
      exact hodd2.not_two_dvd_nat h2dvd
    have hdvd2 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one hb2_one
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hoddB
      exact absurd (dvd_refl 2) hoddB.not_two_dvd_nat
  exact hB hBbot

theorem eq_bot_of_prod {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] {B : Subgroup (Y₁ × Y₂)}
    {s : Y₁ × Y₂}
    (h₁ : ∀ R : Subgroup Y₁, IsPGroup 2 R → B.map (MonoidHom.fst Y₁ Y₂) ≤ normalizer (R : Set Y₁) →
      s.1 ∈ normalizer (R : Set Y₁) → R = ⊥)
    (h₂ : ∀ R : Subgroup Y₂, IsPGroup 2 R → B.map (MonoidHom.snd Y₁ Y₂) ≤ normalizer (R : Set Y₂) →
      s.2 ∈ normalizer (R : Set Y₂) → R = ⊥)
    {R : Subgroup (Y₁ × Y₂)} (hR : IsPGroup 2 R) (hBR : B ≤ normalizer (R : Set (Y₁ × Y₂)))
    (hsR : s ∈ normalizer (R : Set (Y₁ × Y₂))) : R = ⊥ := by
  have hs₁ : s.1 ∈ normalizer (R.map (MonoidHom.fst Y₁ Y₂) : Set Y₁) :=
    Subgroup.le_normalizer_map (MonoidHom.fst Y₁ Y₂) ⟨s, hsR, rfl⟩
  have hs₂ : s.2 ∈ normalizer (R.map (MonoidHom.snd Y₁ Y₂) : Set Y₂) :=
    Subgroup.le_normalizer_map (MonoidHom.snd Y₁ Y₂) ⟨s, hsR, rfl⟩
  have h1 : R.map (MonoidHom.fst Y₁ Y₂) = ⊥ :=
    h₁ _ (hR.map _) ((Subgroup.map_mono hBR).trans (Subgroup.le_normalizer_map _)) hs₁
  have h2 : R.map (MonoidHom.snd Y₁ Y₂) = ⊥ :=
    h₂ _ (hR.map _) ((Subgroup.map_mono hBR).trans (Subgroup.le_normalizer_map _)) hs₂
  rw [Subgroup.eq_bot_iff_forall]
  intro r hr
  have h1' : r.1 = 1 := by
    have : r.1 ∈ R.map (MonoidHom.fst Y₁ Y₂) := ⟨r, hr, rfl⟩
    rw [h1] at this
    exact this
  have h2' : r.2 = 1 := by
    have : r.2 ∈ R.map (MonoidHom.snd Y₁ Y₂) := ⟨r, hr, rfl⟩
    rw [h2] at this
    exact this
  exact Prod.ext h1' h2'

end CFSG.GroupTheory

end
