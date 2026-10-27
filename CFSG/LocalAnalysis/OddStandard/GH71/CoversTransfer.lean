module

public import CFSG.LocalAnalysis.OddStandard.GH71.Covers
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer

variable {G : Type} [Group G] [Finite G]

theorem fusionIsSylowIn_two_of_sup {N R R' : Subgroup G} (hR : IsPGroup 2 ↥R)
    (hRN : R ≤ normalizer (N : Set G)) (hN : Odd (Nat.card N)) (hR'2 : IsPGroup 2 ↥R')
    (hR'le : R' ≤ N ⊔ R) (hR'card : Nat.card R' = Nat.card R) :
    Open.fusionIsSylowIn 2 R' (N ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hRN
  have hinf : Nat.card (N ⊓ R : Subgroup G) = 1 := by
    obtain ⟨k, hk⟩ := (hR.to_le (inf_le_right : N ⊓ R ≤ R)).exists_card_eq
    have hdvd : Nat.card (N ⊓ R : Subgroup G) ∣ Nat.card N := card_dvd_of_le inf_le_left
    rw [hk] at hdvd ⊢
    rcases k with _ | k
    · rfl
    · exfalso
      have h1 : Odd (2 ^ (k + 1)) := Odd.of_dvd_nat hN hdvd
      have h2 : Even (2 ^ (k + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact (Nat.not_even_iff_odd.mpr h1) h2
  rw [hinf, mul_one] at hcard
  refine ⟨hR'le, hR'2, fun Q hQ hQ2 hR'Q => ?_⟩
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card N * Nat.card R := hcard ▸ card_dvd_of_le hQ
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card N) := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hN)
  have hQR : Nat.card Q ≤ Nat.card R :=
    Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_left hdvd)
  exact (eq_of_le_of_card_ge hR'Q (hR'card ▸ hQR)).symm

theorem covers_transfer {R H H₁ : Subgroup G} (hR : IsPGroup 2 ↥R) (hRH : R ≤ H)
    (hRH₁ : R ≤ H₁)
    (hX : Covers H (normalizer (R : Set G)) (pPrimeCoreOf 2 (normalizer (R : Set G))))
    (hH : Covers H₁ H (pPrimeCoreOf 2 H)) :
    Covers H₁ (normalizer (R : Set G)) (pPrimeCoreOf 2 (normalizer (R : Set G))) := by
  set X := normalizer (R : Set G) with hXdef
  set OX := pPrimeCoreOf 2 X
  set OH := pPrimeCoreOf 2 H
  have hOHH : OH ≤ H := pPrimeCoreOf_le' H
  have hHOH : H ≤ normalizer (OH : Set G) := le_normalizer_pPrimeCoreOf' H
  have hOHodd : Odd (Nat.card OH) := odd_card_pPrimeCoreOf' H
  set N := OH ⊓ H₁ with hNdef
  have hNodd : Odd (Nat.card N) := odd_card_of_le inf_le_left hOHodd
  have hRN : R ≤ normalizer (N : Set G) := fun r hr =>
    inf_normalizer_le_normalizer_inf ⟨hHOH (hRH hr), le_normalizer (hRH₁ hr)⟩
  have step1 : ∀ h ∈ H ⊓ X, ∃ x₁ ∈ H₁ ⊓ X, ∃ o ∈ X ⊓ OH, h = x₁ * o := by
    intro h hh
    obtain ⟨h₁, hh₁, o₁, ho₁, rfl⟩ := (covers_iff (fun y hy => hHOH hy.2)).mp hH h hh.1
    set R' := R.map (MulAut.conj h₁).toMonoidHom with hR'def
    have hhX : h₁ * o₁ ∈ X := hh.2
    have hR'le : R' ≤ N ⊔ R := by
      rintro _ ⟨r, hr, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      set r' := (h₁ * o₁) * r * (h₁ * o₁)⁻¹ with hr'
      have hr'R : r' ∈ R := (mem_normalizer_iff.mp hhX r).mp hr
      set q := (h₁ * o₁) * (r⁻¹ * o₁⁻¹ * r * o₁) * (h₁ * o₁)⁻¹ with hq
      have hqOH : q ∈ OH := by
        have h1 : r⁻¹ * o₁⁻¹ * r ∈ OH := by
          have := (mem_normalizer_iff.mp (hHOH (hRH (R.inv_mem hr))) o₁⁻¹).mp (OH.inv_mem ho₁)
          simpa [mul_assoc] using this
        exact (mem_normalizer_iff.mp (hHOH hh.1) _).mp (OH.mul_mem h1 ho₁)
      have hdec : h₁ * r * h₁⁻¹ = r' * q := by rw [hr', hq]; group
      have hqH₁ : q ∈ H₁ := by
        have : q = r'⁻¹ * (h₁ * r * h₁⁻¹) := by rw [hdec]; group
        rw [this]
        exact H₁.mul_mem (H₁.inv_mem (hRH₁ hr'R))
          (H₁.mul_mem (H₁.mul_mem hh₁.1 (hRH₁ hr)) (H₁.inv_mem hh₁.1))
      have hqN : q ∈ N := ⟨hqOH, hqH₁⟩
      have hq' : r' * q * r'⁻¹ ∈ N := (mem_normalizer_iff.mp (hRN hr'R) q).mp hqN
      rw [hdec, show r' * q = (r' * q * r'⁻¹) * r' by group]
      exact mul_mem (mem_sup_left hq') (mem_sup_right hr'R)
    have hR'card : Nat.card R' = Nat.card R :=
      Subgroup.card_map_of_injective (MulAut.conj h₁).injective
    have hsylR : Open.fusionIsSylowIn 2 R (N ⊔ R) :=
      fusionIsSylowIn_two_of_sup hR hRN hNodd hR le_sup_right rfl
    have hsylR' : Open.fusionIsSylowIn 2 R' (N ⊔ R) :=
      fusionIsSylowIn_two_of_sup hR hRN hNodd (hR.map _) hR'le hR'card
    obtain ⟨c, hc, hcR⟩ := exists_conj_sylow Nat.prime_two hsylR hsylR'
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left N R hRN
    have hc' : c ∈ ((N ⊔ R : Subgroup G) : Set G) := hc
    rw [hset] at hc'
    obtain ⟨n, hn, r₀, hr₀, rfl⟩ := hc'
    set x₁ := n⁻¹ * h₁ with hx₁
    have hx₁R : x₁ ∈ X := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have h1 : h₁ * y * h₁⁻¹ ∈ R' := ⟨y, hy, rfl⟩
        rw [hcR] at h1
        obtain ⟨w, hw, hwy⟩ := h1
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwy
        have e : x₁ * y * x₁⁻¹ = r₀ * w * r₀⁻¹ := by
          rw [hx₁]
          calc n⁻¹ * h₁ * y * (n⁻¹ * h₁)⁻¹ = n⁻¹ * (h₁ * y * h₁⁻¹) * n := by group
            _ = n⁻¹ * (n * r₀ * w * (n * r₀)⁻¹) * n := by rw [← hwy]
            _ = r₀ * w * r₀⁻¹ := by group
        rw [e]
        exact R.mul_mem (R.mul_mem hr₀ hw) (R.inv_mem hr₀)
      · intro hy
        have h1 : n * r₀ * (r₀⁻¹ * (x₁ * y * x₁⁻¹) * r₀) * (n * r₀)⁻¹ ∈
            R.map (MulAut.conj (n * r₀)).toMonoidHom :=
          ⟨_, R.mul_mem (R.mul_mem (R.inv_mem hr₀) hy) hr₀, rfl⟩
        rw [← hcR] at h1
        obtain ⟨w, hw, hwy⟩ := h1
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwy
        have e : y = w := by
          have e1 : h₁ * w * h₁⁻¹ = h₁ * y * h₁⁻¹ := by
            rw [hwy, hx₁]; group
          exact (mul_left_cancel (mul_right_cancel e1)).symm
        rw [e]; exact hw
    have hnH : n ∈ H := hOHH hn.1
    have hx₁H₁ : x₁ ∈ H₁ := H₁.mul_mem (H₁.inv_mem hn.2) hh₁.1
    have hx₁H : x₁ ∈ H := H.mul_mem (H.inv_mem hnH) hh₁.2
    refine ⟨x₁, ⟨hx₁H₁, hx₁R⟩, x₁⁻¹ * (h₁ * o₁), ⟨?_, ?_⟩, by group⟩
    · exact X.mul_mem (X.inv_mem hx₁R) hhX
    · have e : x₁⁻¹ * (h₁ * o₁) = (x₁⁻¹ * n * x₁) * o₁ := by rw [hx₁]; group
      rw [e]
      refine OH.mul_mem ?_ ho₁
      have := (mem_normalizer_iff.mp (hHOH (H.inv_mem hx₁H)) n).mp hn.1
      simpa [mul_assoc] using this
  have step2 : X ⊓ OH ≤ OX := by
    refine le_pPrimeCoreOf_of_covers hX inf_le_left (odd_card_of_le inf_le_right hOHodd) ?_
    intro y hy
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer hy.2, hHOH hy.1⟩
  have hXOX : X ≤ normalizer (OX : Set G) := le_normalizer_pPrimeCoreOf' X
  intro x hx
  obtain ⟨h, hh, oX, hoX, rfl⟩ := (covers_iff (fun y hy => hXOX hy.2)).mp hX x hx
  obtain ⟨x₁, hx₁, o, ho, rfl⟩ := step1 h hh
  rw [mul_assoc]
  exact mul_mem (mem_sup_left hx₁) (mem_sup_right (OX.mul_mem (step2 ho) hoX))

end CFSG.OddStandard.GH71
