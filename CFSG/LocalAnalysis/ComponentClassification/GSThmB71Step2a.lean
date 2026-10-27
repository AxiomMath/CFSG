module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

theorem relIndex_eq_relIndex_sup_of_le_normalizer {H N : Subgroup X}
    (hHN : H ≤ normalizer (N : Set X)) : N.relIndex H = N.relIndex (H ⊔ N) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN).toEquiv

theorem conj_mem_of_mem_normalizer {T : Subgroup X} {y t : X} (hy : y ∈ normalizer (T : Set X))
    (ht : t ∈ T) : y * t * y⁻¹ ∈ T :=
  (mem_normalizer_iff.mp hy t).mp ht

theorem le_normalizer_conjugate {B T : Subgroup X} {y : X} (hy : y ∈ normalizer (T : Set X))
    (hTB : T ≤ normalizer (B : Set X)) : T ≤ normalizer ((conjugate B y : Subgroup X) : Set X) := by
  intro t ht
  have hyt : y * t * y⁻¹ ∈ normalizer (B : Set X) := hTB (conj_mem_of_mem_normalizer hy ht)
  rw [mem_normalizer_iff]
  intro c
  rw [mem_conjugate_iff, mem_conjugate_iff]
  constructor
  · intro hc
    have h1 := (mem_normalizer_iff.mp hyt (y * c * y⁻¹)).mp hc
    rwa [show y * t * y⁻¹ * (y * c * y⁻¹) * (y * t * y⁻¹)⁻¹ = y * (t * c * t⁻¹) * y⁻¹ by group]
      at h1
  · intro hc
    have h1 := (mem_normalizer_iff.mp hyt (y * c * y⁻¹)).mpr
      (by rwa [show y * t * y⁻¹ * (y * c * y⁻¹) * (y * t * y⁻¹)⁻¹ = y * (t * c * t⁻¹) * y⁻¹ by
        group])
    exact h1

theorem card_conjugate_eq (B : Subgroup X) (y : X) : Nat.card (conjugate B y) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective

namespace Hyp52

variable [Finite X] (h : Hyp52 X)

theorem B_le_T' : h.B ≤ h.T := by
  intro y hy
  have h1 := h.B_le hy
  exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp h1).1, le_normalizer hy⟩, h1⟩

theorem T_le_normalizer : h.T ≤ normalizer (h.B : Set X) :=
  fun _ hy => (mem_inf.mp (mem_inf.mp hy).1).2

theorem conj_mem_P' {s y : X} (hs : s ∈ h.S) (hy : y ∈ h.P) : s * y * s⁻¹ ∈ h.P := by
  obtain ⟨hyS, hyC⟩ := mem_inf.mp hy
  have hsJ : s⁻¹ ∈ normalizer (h.J : Set X) := (mem_inf.mp (h.S_le (inv_mem hs))).2
  have h1 := conj_mem_coreActionKernel hsJ hyC
  rw [inv_inv] at h1
  exact mem_inf.mpr ⟨mul_mem (mul_mem hs hyS) (inv_mem hs), h1⟩

theorem card_T (hNP : h.T = h.B ⊔ zpowers h.a ∧ h.B ⊓ zpowers h.a = ⊥ ∧
      ∀ b ∈ h.B, b * h.a = h.a * b) :
    Nat.card h.T = 2 * Nat.card h.B := by
  obtain ⟨hT, hinf, hcomm⟩ := hNP
  have hc : ∀ u ∈ h.B, ∀ v ∈ zpowers h.a, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    exact ((Commute.zpow_right (hcomm u hu) k)).eq
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute h.B (zpowers h.a) hc).1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, h.orderOf_a] at h1
  rw [hT, h1, mul_comm]

theorem not_P_le_normalizer (hNP : h.T = h.B ⊔ zpowers h.a ∧ h.B ⊓ zpowers h.a = ⊥ ∧
      ∀ b ∈ h.B, b * h.a = h.a * b)
    (hB2 : 2 < Nat.card h.B) : ¬ h.P ≤ normalizer (h.B : Set X) := by
  intro hPN
  have hTP : h.T = h.P := le_antisymm inf_le_right
    (le_inf (le_inf inf_le_left hPN) le_rfl)
  have hcard := h.card_T hNP
  have hxP : h.x ∈ normalizer (h.P : Set X) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · exact h.conj_mem_P' h.x_mem
    · intro hy
      have h1 := h.conj_mem_P' (inv_mem h.x_mem) hy
      rwa [show h.x⁻¹ * (h.x * y * h.x⁻¹) * h.x⁻¹⁻¹ = y by group] at h1
  have hBP : h.B ≤ h.P := h.B_le
  have hBxP : conjugate h.B h.x ≤ h.P := by
    intro c hc
    rw [mem_conjugate_iff] at hc
    have h1 := h.conj_mem_P' (inv_mem h.x_mem) (hBP hc)
    rwa [show h.x⁻¹ * (h.x * c * h.x⁻¹) * h.x⁻¹⁻¹ = c by group] at h1
  have hBN : h.B ≤ normalizer ((conjugate h.B h.x : Subgroup X) : Set X) :=
    hBP.trans (le_normalizer_conjugate hxP hPN)
  have h2 := relIndex_eq_relIndex_sup_of_le_normalizer hBN
  have h3 : (conjugate h.B h.x).relIndex h.B = Nat.card h.B := by
    rw [← inf_relIndex_left h.B (conjugate h.B h.x), h.inf_conjugate_x, relIndex_bot_left]
  have h4 := relIndex_mul_card (H := conjugate h.B h.x) (K := h.B ⊔ conjugate h.B h.x)
  rw [inf_eq_left.mpr le_sup_right, ← h2, h3, card_conjugate_eq] at h4
  have h5 : Nat.card (h.B ⊔ conjugate h.B h.x : Subgroup X) ≤ Nat.card h.T := by
    rw [hTP]
    exact Subgroup.card_le_of_le (sup_le hBP hBxP)
  rw [← h4, hcard] at h5
  have hpos : 0 < Nat.card h.B := Nat.card_pos
  have : Nat.card h.B ≤ 2 := Nat.le_of_mul_le_mul_right h5 hpos
  omega

theorem relIndex_inf_conjugate (hNP : h.T = h.B ⊔ zpowers h.a ∧ h.B ⊓ zpowers h.a = ⊥ ∧
      ∀ b ∈ h.B, b * h.a = h.a * b)
    {y : X} (hyN : y ∈ normalizer (h.T : Set X)) (hyB : y ∉ normalizer (h.B : Set X)) :
    (h.B ⊓ conjugate h.B y).relIndex h.B = 2 := by
  have hcard := h.card_T hNP
  have hBT := h.B_le_T'
  set By := conjugate h.B y with hBy
  have hByT : By ≤ h.T := by
    intro c hc
    rw [hBy, mem_conjugate_iff] at hc
    exact (mem_normalizer_iff.mp hyN c).mpr (hBT hc)
  have hBN : h.B ≤ normalizer (By : Set X) :=
    hBT.trans (le_normalizer_conjugate hyN h.T_le_normalizer)
  have h2 := relIndex_eq_relIndex_sup_of_le_normalizer hBN
  rw [inf_relIndex_left, h2]
  have hTBy : By.relIndex h.T = 2 := by
    have h1 := relIndex_mul_card (H := By) (K := h.T)
    rw [inf_eq_left.mpr hByT, hBy, card_conjugate_eq, hcard] at h1
    have hpos : 0 < Nat.card h.B := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hsupT : h.B ⊔ By ≤ h.T := sup_le hBT hByT
  have hmul := relIndex_mul_relIndex By (h.B ⊔ By) h.T le_sup_right hsupT
  rw [hTBy] at hmul
  have hne : By.relIndex (h.B ⊔ By) ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    intro hle
    apply hyB
    have hle' : h.B ≤ By := le_sup_left.trans hle
    have heq : h.B = By := eq_of_le_of_card_ge hle' (by rw [hBy, card_conjugate_eq])
    rw [mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      have h1 : y * c * y⁻¹ ∈ h.B := by
        have : c ∈ By := heq ▸ hc
        rwa [hBy, mem_conjugate_iff] at this
      exact h1
    · intro hc
      have : c ∈ By := by rw [hBy, mem_conjugate_iff]; exact hc
      exact heq ▸ this
  have hdvd : By.relIndex (h.B ⊔ By) ∣ 2 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem lemma71_step2a (hNP : h.T = h.B ⊔ zpowers h.a ∧ h.B ⊓ zpowers h.a = ⊥ ∧
      ∀ b ∈ h.B, b * h.a = h.a * b)
    (hB2 : 2 < Nat.card h.B) :
    ¬ h.P ≤ normalizer (h.B : Set X) ∧
      ∀ y : X, y ∈ normalizer (h.T : Set X) → y ∉ normalizer (h.B : Set X) →
        (h.B ⊓ conjugate h.B y).relIndex h.B = 2 ∧ h.B ⊓ conjugate h.B y ≠ ⊥ := by
  refine ⟨h.not_P_le_normalizer hNP hB2, fun y hyN hyB => ?_⟩
  have h1 := h.relIndex_inf_conjugate hNP hyN hyB
  refine ⟨h1, fun hbot => ?_⟩
  have h2 := relIndex_mul_card (H := h.B ⊓ conjugate h.B y) (K := h.B)
  rw [h1, inf_eq_left.mpr inf_le_left, hbot, Subgroup.card_bot] at h2
  omega

end Hyp52

end CFSG.ComponentClassification.GSThmB
