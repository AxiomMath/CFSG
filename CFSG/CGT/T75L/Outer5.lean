module

public import CFSG.CGT.T75L.Core
public import CFSG.CGT.T75B.Front
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPlus

public section

namespace CFSG.CGT.T75L

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki CFSG.CGT.T75B

theorem sec4I5OuterAction_of (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction) (hC : Sec4I4OuterAction)
    (hW : ∀ (f : ℕ) (P : Type) [Group P] [Finite P], 2 ≤ f → (P ≃* PSU3Model f) →
      Lemma21Input P) : Sec4I5OuterAction := by
  intro G _ _ _ hnab hind T T₁ T₂ a h hq h16 S hS hRS hSN w hwS hwF hwN hwR hout
  obtain ⟨g, hg, a₁, ha₁, b₁, hb₁, hwg⟩ := hwF
  have hwK : w ∈ Subgroup.normalizer (T : Set G) := hSN hwS
  have hwN' : w ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) :=
    h.mem_normalizer_sec4N hwN hwK
  have hNab := h.isElemAbelian_sec4N
  have ha₁N : a₁ ∈ sec4N T T₁ T₂ := normIn_le_sec4N_mid ha₁
  have hb₁N : b₁ ∈ sec4N T T₁ T₂ := normIn_le_sec4N_right hb₁
  have hww : w * w = 1 := by
    have h1 : (a₁ * b₁) * (a₁ * b₁) = 1 :=
      elemAbelian_mul_self hNab ((sec4N T T₁ T₂).mul_mem ha₁N hb₁N)
    rw [hwg]
    calc g * (a₁ * b₁) * g⁻¹ * (g * (a₁ * b₁) * g⁻¹) = g * ((a₁ * b₁) * (a₁ * b₁)) * g⁻¹ := by
          group
      _ = 1 := by rw [h1]; group
  have hclos := h.closure_inter_classD_eq hnab hind hAsc hA hC hq h16 hS hRS
  have hDS : ∀ y, y ∈ classD T → y ∈ S → y ∈ sec4R T T₁ T₂ := fun y hy hyS => by
    rw [← hclos]
    exact Subgroup.subset_closure ⟨hyS, hy⟩
  have ha₁1 : a₁ ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hwg
    by_cases hb1 : b₁ = 1
    · apply hwR
      rw [hwg, hb1]
      simp
    · exact hwR (hDS w (hwg ▸ conj_mem_classD (h.mem_props_normIn₂ hb₁ hb1).2.1 g) hwS)
  have hb₁1 : b₁ ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hwg
    exact hwR (hDS w (hwg ▸ conj_mem_classD (h.mem_props_normIn₁ ha₁ ha₁1).2.1 g) hwS)
  obtain ⟨w', hw'Y, hw'T, hwT₁, hfixT, hfixT₁, hwT₂⟩ :=
    h.exists_normalizing_conj_fix hAsc hq hW hwK hwN' hww hout
  have h' := h.conj_normalizer hw'T
  have hN' : sec4N T (conjSubgroup w' T₁) (conjSubgroup w' T₂) = sec4N T T₁ T₂ :=
    sec4N_conj_of_mem h hw'Y hw'T
  have hTw' : conjSubgroup w' T = T := mem_normalizer_iff_conjSubgroup_eq.1 hw'T
  have hw'K : w' ∈ Subgroup.normalizer (T : Set G) := hw'T
  have hL' : normIn T (conjSubgroup w' T₁) = conjSubgroup w' (normIn T T₁) := by
    have e := normIn_conj w' T T₁
    rwa [hTw'] at e
  have hL₁' : normIn (conjSubgroup w' T₁) T = conjSubgroup w' (normIn T₁ T) := by
    have e := normIn_conj w' T₁ T
    rwa [hTw'] at e
  have hL₂' : normIn (conjSubgroup w' T₂) T = conjSubgroup w' (normIn T₂ T) := by
    have e := normIn_conj w' T₂ T
    rwa [hTw'] at e
  have hq' : 2 * Nat.card (normIn T (conjSubgroup w' T₁)) < Nat.card T := by
    rw [hL', card_conjSubgroup]
    exact hq
  have hE' : EClosure T (conjSubgroup w' T₁) (conjSubgroup w' T₂) := fun U hU hRU hUN =>
    h'.closure_inter_sec4E_eq hnab hind hAsc hA hC hq' h16 hU hRU hUN
  have hg' : g * w'⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem hg ((Subgroup.normalizer (T : Set G)).inv_mem hw'K)
  have ha₁'' : w' * a₁ * w'⁻¹ ∈ normIn (conjSubgroup w' T₁) T := by
    rw [hL₁']
    exact conj_mem_conjSubgroup w' ha₁
  have hb₁'' : w' * b₁ * w'⁻¹ ∈ normIn (conjSubgroup w' T₂) T := by
    rw [hL₂']
    exact conj_mem_conjSubgroup w' hb₁
  have ha₁1' : w' * a₁ * w'⁻¹ ≠ 1 := by
    intro h0
    apply ha₁1
    have : a₁ = w'⁻¹ * (w' * a₁ * w'⁻¹) * w' := by group
    rw [this, h0]
    group
  have hb₁1' : w' * b₁ * w'⁻¹ ≠ 1 := by
    intro h0
    apply hb₁1
    have : b₁ = w'⁻¹ * (w' * b₁ * w'⁻¹) * w' := by group
    rw [this, h0]
    group
  have hwg' : w = (g * w'⁻¹) * ((w' * a₁ * w'⁻¹) * (w' * b₁ * w'⁻¹)) * (g * w'⁻¹)⁻¹ := by
    rw [hwg]
    group
  have hwN'' : w ∈ Subgroup.normalizer
      (sec4N T (conjSubgroup w' T₁) (conjSubgroup w' T₂) : Set G) := by
    rw [hN']
    exact hwN'
  have hfixT'' : ∀ t ∈ T, w * t * w⁻¹ * t⁻¹ ∈ normIn T (conjSubgroup w' T₁) := by
    intro t ht
    have hu : w * t * w⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem (conj_mem_of_mem_normalizer hwK ht) (T.inv_mem ht)
    have hact : w * t * w⁻¹ * t⁻¹ ∈ sec4Ker T (conjSubgroup w' T₁) (conjSubgroup w' T₂) :=
      (sec4ActsTriv_conj_iff h hw'Y hw'T).2 (hfixT t ht)
    have : w * t * w⁻¹ * t⁻¹ ∈ T ⊓ sec4Ker T (conjSubgroup w' T₁) (conjSubgroup w' T₂) :=
      ⟨hu, hact⟩
    rwa [h'.inf_sec4Ker_eq] at this
  have hfixT₁'' : ∀ s ∈ conjSubgroup w' T₁, w * s * w⁻¹ * s⁻¹ ∈ normIn (conjSubgroup w' T₁) T := by
    intro s hs
    have hu : w * s * w⁻¹ * s⁻¹ ∈ conjSubgroup w' T₁ :=
      (conjSubgroup w' T₁).mul_mem (conj_mem_of_mem_normalizer hwT₁ hs)
        ((conjSubgroup w' T₁).inv_mem hs)
    have hact : w * s * w⁻¹ * s⁻¹ ∈ sec4Ker T (conjSubgroup w' T₁) (conjSubgroup w' T₂) :=
      (sec4ActsTriv_conj_iff h hw'Y hw'T).2 (hfixT₁ s hs)
    have : w * s * w⁻¹ * s⁻¹ ∈
        conjSubgroup w' T₁ ⊓ sec4Ker T (conjSubgroup w' T₁) (conjSubgroup w' T₂) := ⟨hu, hact⟩
    rwa [h'.inf_sec4Ker_eq₁] at this
  have hR : (∀ n ∈ sec4N T (conjSubgroup w' T₁) (conjSubgroup w' T₂),
      w * n * w⁻¹ * n⁻¹ ∈ T) → w ∈ sec4R T (conjSubgroup w' T₁) (conjSubgroup w' T₂) :=
    fun hcent => h'.mem_sec4R_of_conj_centralizes hnab hind hAsc hA hC hq' h16 hg' ha₁'' hb₁''
      hwK hwg' hcent
  have hwR' : w ∉ sec4R T (conjSubgroup w' T₁) (conjSubgroup w' T₂) := by
    have : sec4R T (conjSubgroup w' T₁) (conjSubgroup w' T₂) = sec4R T T₁ T₂ := by
      unfold sec4R
      rw [hN']
    rw [this]
    exact hwR
  exact h'.false_of_outer5_core hE' hq' hg' ha₁'' hb₁'' ha₁1' hb₁1' hwg' hwK hwN'' hwT₁
    hfixT'' hfixT₁'' hwT₂ hR hwR'

end CFSG.CGT.T75L
