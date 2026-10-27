module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

variable {Y : Type*} [Group Y]

theorem l44_conj_mem {L S : Subgroup Y}
    (hdec : ∀ y : Y, ∃ ℓ ∈ L, ∃ d ∈ centralizer (L : Set Y), y = ℓ * d)
    (hDS : centralizer (L : Set Y) ≤ S) {n : Y} (hnL : n ∈ L)
    (hn : n ∈ normalizer ((S ⊓ L : Subgroup Y) : Set Y)) :
    ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
  intro s hs
  obtain ⟨ℓ, hℓL, d, hd, rfl⟩ := hdec s
  have hdS : d ∈ S := hDS hd
  have hℓS : ℓ ∈ S := by simpa using S.mul_mem hs (S.inv_mem hdS)
  have h1 : n * ℓ * n⁻¹ ∈ S ⊓ L := (mem_normalizer_iff.mp hn ℓ).mp ⟨hℓS, hℓL⟩
  have h2 : n * d * n⁻¹ = d := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hd n hnL)
  have h3 : n * (ℓ * d) * n⁻¹ = (n * ℓ * n⁻¹) * (n * d * n⁻¹) := by group
  rw [h3, h2]
  exact S.mul_mem h1.1 hdS

theorem l44_mem_normalizer_sylow {L S : Subgroup Y}
    (hdec : ∀ y : Y, ∃ ℓ ∈ L, ∃ d ∈ centralizer (L : Set Y), y = ℓ * d)
    (hDS : centralizer (L : Set Y) ≤ S) {n : Y} (hnL : n ∈ L)
    (hn : n ∈ normalizer ((S ⊓ L : Subgroup Y) : Set Y)) : n ∈ normalizer (S : Set Y) := by
  have hn' : n⁻¹ ∈ normalizer ((S ⊓ L : Subgroup Y) : Set Y) := (normalizer _).inv_mem hn
  rw [mem_normalizer_iff]
  intro s
  refine ⟨l44_conj_mem hdec hDS hnL hn s, fun hs => ?_⟩
  have h1 := l44_conj_mem hdec hDS (L.inv_mem hnL) hn' _ hs
  have h2 : n⁻¹ * (n * s * n⁻¹) * n⁻¹⁻¹ = s := by group
  rwa [h2] at h1

theorem l44_normalizer_inf_eq {L S Γ : Subgroup Y}
    (hdec : ∀ y : Y, ∃ ℓ ∈ L, ∃ d ∈ centralizer (L : Set Y), y = ℓ * d)
    (hDS : centralizer (L : Set Y) ≤ S) (hΓ : Γ ≠ ⊤) (hNΓ : normalizer (S : Set Y) ≤ Γ)
    (hmax : ∀ Z : Subgroup Y, Z ≤ L → L ⊓ normalizer ((S ⊓ L : Subgroup Y) : Set Y) ≤ Z →
      Z ≤ L ⊓ normalizer ((S ⊓ L : Subgroup Y) : Set Y) ∨ L ≤ Z) :
    ∀ n ∈ Γ, n ∈ L → n ∈ normalizer ((S ⊓ L : Subgroup Y) : Set Y) := by
  have hle : L ⊓ normalizer ((S ⊓ L : Subgroup Y) : Set Y) ≤ Γ ⊓ L := fun n hn =>
    ⟨hNΓ (l44_mem_normalizer_sylow hdec hDS hn.1 hn.2), hn.1⟩
  rcases hmax (Γ ⊓ L) inf_le_right hle with h | h
  · exact fun n hnΓ hnL => (h ⟨hnΓ, hnL⟩).2
  · refine absurd (eq_top_iff.mpr fun y _ => ?_) hΓ
    obtain ⟨ℓ, hℓ, d, hd, rfl⟩ := hdec y
    exact Γ.mul_mem (h hℓ).1 (hNΓ (le_normalizer (hDS hd)))

theorem l44_eq_one_of_mem {S : Subgroup Y} (hS : IsPGroup 3 S) {c : Y} (hcS : c ∈ S)
    (hc : Nat.Coprime 3 (orderOf c)) : c = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨c, hcS⟩
  have hk' : c ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf c ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : Nat.Coprime (orderOf c) (3 ^ k) := (Nat.Coprime.symm hc).pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem l44_eq_bot {L S Γ E : Subgroup Y}
    (hdec : ∀ y : Y, ∃ ℓ ∈ L, ∃ d ∈ centralizer (L : Set Y), y = ℓ * d)
    (hDS : centralizer (L : Set Y) ≤ S) (hS3 : IsPGroup 3 S) (hΓ : Γ ≠ ⊤)
    (hNΓ : normalizer (S : Set Y) ≤ Γ)
    (hC : ∀ ℓ ∈ L, (∀ s ∈ S ⊓ L, ℓ * s = s * ℓ) → ℓ ∈ S)
    (hmax : ∀ Z : Subgroup Y, Z ≤ L → L ⊓ normalizer ((S ⊓ L : Subgroup Y) : Set Y) ≤ Z →
      Z ≤ L ⊓ normalizer ((S ⊓ L : Subgroup Y) : Set Y) ∨ L ≤ Z)
    (hEΓ : E ≤ Γ) (hEn : ∀ g ∈ Γ, ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hE3 : ∀ e ∈ E, Nat.Coprime 3 (orderOf e)) : E = ⊥ := by
  refine eq_bot_iff.mpr fun e he => mem_bot.mpr ?_
  obtain ⟨ℓ, hℓL, d, hd, hed⟩ := hdec e
  have hdS : d ∈ S := hDS hd
  have hℓΓ : ℓ ∈ Γ := by
    have h1 : ℓ = e * d⁻¹ := by rw [hed]; group
    rw [h1]
    exact Γ.mul_mem (hEΓ he) (Γ.inv_mem (hNΓ (le_normalizer hdS)))
  have hℓN := l44_normalizer_inf_eq hdec hDS hΓ hNΓ hmax ℓ hℓΓ hℓL
  have hcomm : ∀ s ∈ S ⊓ L, e * s = s * e := by
    intro s hs
    have hsΓ : s ∈ Γ := hNΓ (l44_mem_normalizer_sylow hdec hDS hs.2 (le_normalizer hs))
    have hcd : Commute s d := mem_centralizer_iff.mp hd s hs.2
    have h1 : s * e⁻¹ * s⁻¹ ∈ E := hEn s hsΓ e⁻¹ (E.inv_mem he)
    have h2 : e * s * e⁻¹ ∈ S ⊓ L := by
      have h3 : e * s * e⁻¹ = ℓ * s * ℓ⁻¹ := by
        have h4 : d * s * d⁻¹ = s := by rw [← hcd.eq]; group
        calc e * s * e⁻¹ = ℓ * (d * s * d⁻¹) * ℓ⁻¹ := by rw [hed]; group
          _ = ℓ * s * ℓ⁻¹ := by rw [h4]
      rw [h3]
      exact (mem_normalizer_iff.mp hℓN s).mp hs
    have hcS : e * s * e⁻¹ * s⁻¹ ∈ S := ((S ⊓ L).mul_mem h2 ((S ⊓ L).inv_mem hs)).1
    have hcE : e * s * e⁻¹ * s⁻¹ ∈ E := by
      have h5 : e * s * e⁻¹ * s⁻¹ = e * (s * e⁻¹ * s⁻¹) := by group
      rw [h5]
      exact E.mul_mem he h1
    have h6 := l44_eq_one_of_mem hS3 hcS (hE3 _ hcE)
    calc e * s = (e * s * e⁻¹ * s⁻¹) * (s * e) := by group
      _ = s * e := by rw [h6, one_mul]
  have hℓS : ℓ ∈ S := by
    refine hC ℓ hℓL fun s hs => ?_
    have hcd0 : Commute s d := mem_centralizer_iff.mp hd s hs.2
    have hcd : Commute s d⁻¹ := hcd0.inv_right
    have h1 : ℓ = e * d⁻¹ := by rw [hed]; group
    calc ℓ * s = e * (d⁻¹ * s) := by rw [h1]; group
      _ = e * (s * d⁻¹) := by rw [hcd.eq]
      _ = (e * s) * d⁻¹ := by group
      _ = (s * e) * d⁻¹ := by rw [hcomm s hs]
      _ = s * ℓ := by rw [h1]; group
  exact l44_eq_one_of_mem hS3 (by rw [hed]; exact S.mul_mem hℓS hdS) (hE3 e he)

end CFSG.LocalAnalysis.RankThreeTheoremC
