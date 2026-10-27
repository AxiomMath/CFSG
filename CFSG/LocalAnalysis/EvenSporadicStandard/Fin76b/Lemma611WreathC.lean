module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611WreathA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611WreathB

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {Γ : Type*} [Group Γ] {N₁ N₂ : Subgroup Γ} {σ : Γ}

theorem eq_eight_or_le_four {n : ℕ} (hn : n ∣ 8) : n = 8 ∨ n ≤ 4 := by
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) hn
  interval_cases n <;> omega

namespace WreathData

variable (h : WreathData N₁ N₂ σ)
include h

theorem eq_of_card_comp (e : ↥N₁ ≃* alternatingGroup (Fin 6)) {C : Subgroup Γ} {t₁ t₂ a₁ a₂ : Γ}
    (ht₁ : t₁ ∈ N₁) (ht₂ : t₂ ∈ N₂) (ha₁ : a₁ ∈ N₁) (ha₂ : a₂ ∈ N₂) (ht₁1 : t₁ ≠ 1)
    (htC : t₁ * t₂ ∈ C) (hac : ∀ c ∈ C, c * (a₁ * a₂) = (a₁ * a₂) * c)
    (htc : ∀ c ∈ C, c * (t₁ * t₂) = (t₁ * t₂) * c) (hσt₁ : σ * t₁ * σ⁻¹ = t₂)
    (ht₁sq : t₁ * t₁ = 1) (hσa₂ : σ * a₂ * σ⁻¹ = a₁ * t₁) (hY : Nat.card (h.comp C) = 8) :
    a₁ * a₂ = t₁ ∨ a₁ * a₂ = t₂ := by
  have ht₁Y : t₁ ∈ h.comp C := h.mem_comp_of_mul_mem ht₁ ht₂ htC
  have hcomm_t : ∀ u ∈ h.comp C, u * t₁ = t₁ * u := by
    rintro u ⟨huN, v, hv, huv⟩
    exact (h.comm_components huN ht₁ hv ht₂ (htc _ huv)).1
  have hcomm_a : ∀ u ∈ h.comp C, u * a₁ = a₁ * u := by
    rintro u ⟨huN, v, hv, huv⟩
    exact (h.comm_components huN ha₁ hv ha₂ (hac _ huv)).1
  obtain ⟨hcent, -, -⟩ := centralizer_dihedral_facts e (h.comp_le C) hY ht₁Y ht₁1
    (fun p hp => (hcomm_t p hp).symm)
  rcases hcent a₁ ha₁ (fun p hp => (hcomm_a p hp).symm) with h1 | h1
  · have h2 : a₂ = t₂ := by
      rw [← h.conj_conj a₂, hσa₂, h1, one_mul, hσt₁]
    right
    rw [h1, h2, one_mul]
  · have h2 : a₂ = 1 := by
      rw [← h.conj_conj a₂, hσa₂, h1, ht₁sq]
      group
    left
    rw [h1, h2, mul_one]

theorem exists_conj_of_sq_eq_one (hidx : (N₁ ⊔ N₂).index = 2) (hσM : σ ∉ N₁ ⊔ N₂) {x : Γ}
    (hx2 : x * x = 1) (hxM : x ∉ N₁ ⊔ N₂) : ∃ n ∈ N₁, n * σ * n⁻¹ = x := by
  have hn : x * σ ∈ N₁ ⊔ N₂ := (mul_mem_iff_of_index_two hidx).2 (iff_of_false hxM hσM)
  obtain ⟨n₁, hn₁, n₂, hn₂, hn⟩ := h.dec hn
  have hxn : x = n₁ * n₂ * σ := by
    calc x = (x * σ) * σ⁻¹ := by group
      _ = n₁ * n₂ * σ⁻¹ := by rw [hn]
      _ = n₁ * n₂ * σ := by rw [h.inv_eq]
  have h1 : (n₁ * n₂) * (σ * (n₁ * n₂) * σ⁻¹) = 1 := by
    calc (n₁ * n₂) * (σ * (n₁ * n₂) * σ⁻¹)
        = (n₁ * n₂) * (σ * (n₁ * n₂) * σ⁻¹) * (σ * σ) := by rw [h.sq, mul_one]
      _ = x * x := by rw [hxn]; group
      _ = 1 := hx2
  have hA := h.swap₁ n₁ hn₁
  have hB := h.swap₂ n₂ hn₂
  have h2 : (n₁ * (σ * n₂ * σ⁻¹)) * (n₂ * (σ * n₁ * σ⁻¹)) = 1 * 1 := by
    rw [one_mul, ← h1]
    calc (n₁ * (σ * n₂ * σ⁻¹)) * (n₂ * (σ * n₁ * σ⁻¹))
        = n₁ * ((σ * n₂ * σ⁻¹) * n₂) * (σ * n₁ * σ⁻¹) := by group
      _ = n₁ * (n₂ * (σ * n₂ * σ⁻¹)) * (σ * n₁ * σ⁻¹) := by
        rw [h.comm _ hB n₂ hn₂]
      _ = n₁ * n₂ * ((σ * n₂ * σ⁻¹) * (σ * n₁ * σ⁻¹)) := by group
      _ = n₁ * n₂ * ((σ * n₁ * σ⁻¹) * (σ * n₂ * σ⁻¹)) := by
        rw [h.comm _ hB _ hA]
      _ = (n₁ * n₂) * (σ * (n₁ * n₂) * σ⁻¹) := by group
  obtain ⟨-, h3⟩ := wreath_uniq h.disj (N₁.mul_mem hn₁ hB) N₁.one_mem (N₂.mul_mem hn₂ hA)
    N₂.one_mem h2
  have h4 : σ * n₁ * σ⁻¹ = n₂⁻¹ := eq_inv_of_mul_eq_one_right h3
  have h5 : σ * n₁⁻¹ * σ⁻¹ = n₂ := by
    calc σ * n₁⁻¹ * σ⁻¹ = (σ * n₁ * σ⁻¹)⁻¹ := by group
      _ = n₂ := by rw [h4, inv_inv]
  refine ⟨n₁, hn₁, ?_⟩
  rw [hxn]
  calc n₁ * σ * n₁⁻¹ = n₁ * (σ * n₁⁻¹ * σ⁻¹) * σ := by group
    _ = n₁ * n₂ * σ := by rw [h5]

theorem exists_small_commutator [Finite Γ] (e₁ : ↥N₁ ≃* alternatingGroup (Fin 6))
    (e₂ : ↥N₂ ≃* alternatingGroup (Fin 6)) (hidx : (N₁ ⊔ N₂).index = 2) (hσM : σ ∉ N₁ ⊔ N₂)
    {C : Subgroup Γ} (hC2 : IsPGroup 2 C) (hC : 64 ≤ Nat.card C) {a t : Γ} (htC : t ∈ C)
    (hac : ∀ c ∈ C, c * a = a * c) (htc : ∀ c ∈ C, c * t = t * c) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hσa : σ * a * σ⁻¹ = a * t) (hσt : σ * t * σ⁻¹ = t) (haM : a ∈ N₁ ⊔ N₂)
    (htM : t ∈ N₁ ⊔ N₂) :
    Nat.card C = 64 ∧ ∃ p ∈ C, p ≠ 1 ∧ p ≠ a ∧ p ≠ t ∧ p ≠ a * t ∧ ∃ ζ, (ζ = a ∨ ζ = a * t) ∧
      ∀ c ∈ C, p * c * p⁻¹ * c⁻¹ = 1 ∨ p * c * p⁻¹ * c⁻¹ = ζ := by
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl, ht₁sq, ht₂sq, hσt₁, hσt₂, ht₁1, ht₂1⟩ :=
    h.exists_components_involution htM hσt ht2 ht1
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl, hσa₂, hσa₁⟩ := h.exists_components_swap ht₁ ht₂ haM hσa
  have hnorm : (N₁ ⊔ N₂).Normal := normal_of_index_eq_two hidx
  have hrel : (N₁ ⊔ N₂).relIndex C ∣ 2 :=
    hidx ▸ relIndex_dvd_index_of_normal (H := N₁ ⊔ N₂) (K := C)
  have h64 := relIndex_mul_card (H := N₁ ⊔ N₂) (K := C)
  have hhalf : 32 ≤ Nat.card ↥((N₁ ⊔ N₂) ⊓ C) := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hrel with h2 | h2 <;> rw [h2] at h64 <;> omega
  have hY1 : Nat.card (h.comp C) ∣ 8 :=
    card_dvd_eight_of_isPGroup e₁ (h.comp_le C) (h.isPGroup_comp hC2)
  have hY2 : Nat.card (h.symm.comp C) ∣ 8 :=
    card_dvd_eight_of_isPGroup e₂ (h.symm.comp_le C) (h.symm.isPGroup_comp hC2)
  have hprod := h.card_inf_le_mul C
  have h8 : Nat.card (h.comp C) = 8 ∨ Nat.card (h.symm.comp C) = 8 := by
    by_contra hcon
    rw [not_or] at hcon
    have h1 := (eq_eight_or_le_four hY1).resolve_left hcon.1
    have h2 := (eq_eight_or_le_four hY2).resolve_left hcon.2
    have := Nat.mul_le_mul h1 h2
    omega
  have hat : a₁ * a₂ = t₁ ∨ a₁ * a₂ = t₂ := by
    rcases h8 with h8 | h8
    · exact h.eq_of_card_comp e₁ ht₁ ht₂ ha₁ ha₂ ht₁1 htC hac htc hσt₁ ht₁sq hσa₂ h8
    · have htC' : t₂ * t₁ ∈ C := by
        rw [← h.comm t₁ ht₁ t₂ ht₂]
        exact htC
      have hac' : ∀ c ∈ C, c * (a₂ * a₁) = (a₂ * a₁) * c := by
        rw [← h.comm a₁ ha₁ a₂ ha₂]
        exact hac
      have htc' : ∀ c ∈ C, c * (t₂ * t₁) = (t₂ * t₁) * c := by
        rw [← h.comm t₁ ht₁ t₂ ht₂]
        exact htc
      have h' := h.symm.eq_of_card_comp e₂ ht₂ ht₁ ha₂ ha₁ ht₂1 htC' hac' htc' hσt₂ ht₂sq hσa₁
        h8
      rw [← h.comm a₁ ha₁ a₂ ha₂] at h'
      exact h'.symm
  have hCM : C ≤ N₁ ⊔ N₂ := by
    intro c hc
    rcases hat with hat | hat
    · refine h.mem_sup_of_comm hidx hσM ht₁ ht₁1 (by rw [hσt₁]; exact ht₂) ?_
      have := hac c hc
      rwa [hat] at this
    · have hidx' : (N₂ ⊔ N₁).index = 2 := by rwa [sup_comm]
      have hσM' : σ ∉ N₂ ⊔ N₁ := by rwa [sup_comm]
      have := h.symm.mem_sup_of_comm hidx' hσM' ht₂ ht₂1 (by rw [hσt₂]; exact ht₁) (u := t₂)
        (c := c) (by have := hac c hc; rwa [hat] at this)
      rwa [sup_comm] at this
  have hCprod : Nat.card C ≤ Nat.card (h.comp C) * Nat.card (h.symm.comp C) := by
    have := h.card_inf_le_mul C
    rwa [inf_eq_right.2 hCM] at this
  have hY1le : Nat.card (h.comp C) ≤ 8 := Nat.le_of_dvd (by norm_num) hY1
  have hY2le : Nat.card (h.symm.comp C) ≤ 8 := Nat.le_of_dvd (by norm_num) hY2
  have hC64 : Nat.card C = 64 := by
    have := Nat.mul_le_mul hY1le hY2le
    omega
  have hY8 : Nat.card (h.comp C) = 8 ∧ Nat.card (h.symm.comp C) = 8 := by
    rcases eq_eight_or_le_four hY1 with h1 | h1 <;> rcases eq_eight_or_le_four hY2 with h2 | h2
    · exact ⟨h1, h2⟩
    · have := Nat.mul_le_mul h1.le h2
      omega
    · have := Nat.mul_le_mul h1 h2.le
      omega
    · have := Nat.mul_le_mul h1 h2
      omega
  have hYC : ∀ u ∈ h.comp C, u ∈ C := fun u hu =>
    h.mem_of_card_comp_le hCM (by rw [hY8.1, hY8.2, hC64]) hu
  have ht₁Y : t₁ ∈ h.comp C := h.mem_comp_of_mul_mem ht₁ ht₂ htC
  have hcomm_t : ∀ u ∈ h.comp C, u * t₁ = t₁ * u := by
    rintro u ⟨huN, v, hv, huv⟩
    exact (h.comm_components huN ht₁ hv ht₂ (htc _ huv)).1
  obtain ⟨-, hcommut, y, hyY, hy1, hyt₁⟩ := centralizer_dihedral_facts e₁ (h.comp_le C)
    hY8.1 ht₁Y ht₁1 (fun p hp => (hcomm_t p hp).symm)
  have hyN : y ∈ N₁ := h.comp_le C hyY
  have hN₂ : ∀ w ∈ N₁, w ∈ N₂ → w = 1 := by
    intro w hw1 hw2
    have : w ∈ N₁ ⊓ N₂ := ⟨hw1, hw2⟩
    rwa [h.disj.eq_bot, mem_bot] at this
  have hyt₂ : y ≠ t₂ := fun hyw => ht₂1 (hyw ▸ hN₂ y hyN (hyw ▸ ht₂))
  have hyt : y ≠ t₁ * t₂ := by
    intro hyw
    have h1 : t₂ ∈ N₁ := by
      have : t₂ = t₁⁻¹ * y := by rw [hyw]; group
      rw [this]
      exact N₁.mul_mem (N₁.inv_mem ht₁) hyN
    exact ht₂1 (hN₂ t₂ h1 ht₂)
  have hA : t₁ * (t₁ * t₂) = t₂ := by rw [← mul_assoc, ht₁sq, one_mul]
  have hB : t₂ * (t₁ * t₂) = t₁ := by
    calc t₂ * (t₁ * t₂) = (t₂ * t₁) * t₂ := by group
      _ = (t₁ * t₂) * t₂ := by rw [← h.comm t₁ ht₁ t₂ ht₂]
      _ = t₁ * (t₂ * t₂) := by group
      _ = t₁ := by rw [ht₂sq, mul_one]
  refine ⟨hC64, y, hYC y hyY, hy1, ?_, hyt, ?_, t₁, ?_, ?_⟩
  · rcases hat with hat | hat
    · rwa [hat]
    · rwa [hat]
  · rcases hat with hat | hat
    · rwa [hat, hA]
    · rwa [hat, hB]
  · rcases hat with hat | hat
    · exact Or.inl hat.symm
    · exact Or.inr (by rw [hat, hB])
  · intro c hc
    obtain ⟨u, hu, v, hv, rfl⟩ := h.dec (hCM hc)
    have huY := h.mem_comp_of_mul_mem hu hv hc
    have hvy : v * y⁻¹ = y⁻¹ * v := (h.comm y⁻¹ (N₁.inv_mem hyN) v hv).symm
    have hcomm : y * (u * v) * y⁻¹ * (u * v)⁻¹ = y * u * y⁻¹ * u⁻¹ := by
      calc y * (u * v) * y⁻¹ * (u * v)⁻¹ = y * u * (v * y⁻¹) * v⁻¹ * u⁻¹ := by group
        _ = y * u * (y⁻¹ * v) * v⁻¹ * u⁻¹ := by rw [hvy]
        _ = y * u * y⁻¹ * u⁻¹ := by group
    rw [hcomm]
    exact hcommut y hyY u huY

end WreathData

end CFSG.EvenSporadicStandard.Fin76b
