module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316A
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.PGroups
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Gen

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13
open scoped commutatorElement

variable {G : Type} [Group G]

theorem fzc_sy2_four_cosets [Finite G] {W Q : Subgroup G} (hWQ : W ≤ Q)
    (hcard : Nat.card Q = 4 * Nat.card W) (hnrm : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W)
    (hsq : ∀ q ∈ Q, q ^ 2 ∈ W) (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ W)
    {x y : G} (hx : x ∈ Q) (hxW : x ∉ W) (hy : y ∈ Q) (hyW : y ∉ W) (hyx : y * x⁻¹ ∉ W) :
    ∀ q ∈ Q, q ∈ W ∨ q * x⁻¹ ∈ W ∨ q * y⁻¹ ∈ W ∨ q * (x * y)⁻¹ ∈ W := by
  set H : Subgroup G := W ⊔ zpowers x with hHdef
  have hx2 : x * x ∈ W := by simpa [pow_two] using hsq x hx
  have hxN : ∀ w ∈ W, x * w * x⁻¹ ∈ W := fun w hw => hnrm x hx w hw
  have hmemH : ∀ g, g ∈ H ↔ ∃ w ∈ W, g = w ∨ g = w * x := by
    intro g
    rw [hHdef]
    exact mem_sup_zpowers_sq hx2 hxN
  have hyH : y ∉ H := by
    intro hy'
    obtain ⟨w, hw, h | h⟩ := (hmemH y).1 hy'
    · exact hyW (by rw [h]; exact hw)
    · exact hyx (by rw [h]; simpa [mul_assoc] using hw)
  have hysq : y * y ∈ H := (le_sup_left : W ≤ H) (by simpa [pow_two] using hsq y hy)
  have hyN : ∀ g ∈ H, y * g * y⁻¹ ∈ H := by
    intro g hg
    obtain ⟨w, hw, h | h⟩ := (hmemH g).1 hg
    · rw [h]
      exact (le_sup_left : W ≤ H) (hnrm y hy w hw)
    · rw [h]
      have h2 : y * (w * x) * y⁻¹ = (y * w * y⁻¹ * ⁅y, x⁆) * x := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact (hmemH ((y * w * y⁻¹ * ⁅y, x⁆) * x)).2
        ⟨y * w * y⁻¹ * ⁅y, x⁆,
          W.mul_mem (hnrm y hy w hw) (hcomm y hy x hx), Or.inr rfl⟩
  have hcardH : Nat.card H = 2 * Nat.card W := by
    rw [hHdef]
    exact card_sup_zpowers_sq hx2 hxN hxW
  have hcardHy : Nat.card ↥(H ⊔ zpowers y) = 2 * Nat.card H :=
    card_sup_zpowers_sq hysq hyN hyH
  have hleHy : H ⊔ zpowers y ≤ Q := by
    refine sup_le ?_ (zpowers_le.mpr hy)
    rw [hHdef]
    exact sup_le hWQ (zpowers_le.mpr hx)
  have heq : H ⊔ zpowers y = Q := by
    refine Subgroup.eq_of_le_of_card_ge hleHy ?_
    rw [hcardHy, hcardH, hcard]
    exact Nat.le_of_eq (by ring)
  intro q hq
  obtain ⟨h, hh, hqh⟩ := (mem_sup_zpowers_sq hysq hyN).1 (heq.symm ▸ hq)
  obtain ⟨w, hw, hwh | hwh⟩ := (hmemH h).1 hh
  · rcases hqh with hqh | hqh
    · exact Or.inl (by rw [hqh, hwh]; exact hw)
    · refine Or.inr (Or.inr (Or.inl ?_))
      have : q * y⁻¹ = w := by rw [hqh, hwh]; group
      rw [this]; exact hw
  · rcases hqh with hqh | hqh
    · refine Or.inr (Or.inl ?_)
      have : q * x⁻¹ = w := by rw [hqh, hwh]; group
      rw [this]; exact hw
    · refine Or.inr (Or.inr (Or.inr ?_))
      have : q * (x * y)⁻¹ = w := by rw [hqh, hwh]; group
      rw [this]; exact hw

theorem fzc_sy2_phi_le_of_cosets {Q M : Subgroup G} {s : G} (hs : s ∈ Q) (hs2 : s ^ 2 ∈ M)
    (hnrm : ∀ g ∈ Q, ∀ u ∈ M, g * u * g⁻¹ ∈ M) (hcos : ∀ g ∈ Q, g ∈ M ∨ s⁻¹ * g ∈ M) :
    fzlPhi Q ≤ M := by
  have sqmem : ∀ g ∈ Q, g ^ 2 ∈ M := by
    intro g hg
    by_cases hgM : g ∈ M
    · simpa [pow_two] using M.mul_mem hgM hgM
    · rcases hcos g hg with h | h
      · exact absurd h hgM
      · have hg2 : g ^ 2 = (s * (s⁻¹ * g) * s⁻¹) * s ^ 2 * (s⁻¹ * g) := by
          rw [pow_two, pow_two]
          group
        rw [hg2]
        exact M.mul_mem (M.mul_mem (hnrm s hs (s⁻¹ * g) h) hs2) h
  refine fzl_phi_le_of_elem ?_ sqmem
  intro g hg g' hg'
  refine fzl_comm_mem_of_sq (N := M) (sqmem g hg) (sqmem g' hg')
    (sqmem (g * g') (Q.mul_mem hg hg')) ?_
  intro n hn
  simpa using hnrm g'⁻¹ (Q.inv_mem hg') n hn

theorem fzc_sy2_eq_of_mem [Finite G] {W Q H : Subgroup G} (hQ : IsPGroup 2 Q)
    (hΦ : fzlPhi Q = W) (hcard : Nat.card Q = 4 * Nat.card W) (hHQ : H ≤ Q)
    {x y : G} (hx : x ∈ H) (hxW : x ∉ W) (hy : y ∈ H) (hyW : y ∉ W) (hyx : y * x⁻¹ ∉ W) :
    H = Q := by
  have hWQ : W ≤ Q := by
    rw [← hΦ]
    refine fzl_phi_le_of_elem ?_ ?_
    · intro a ha b hb
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
    · intro a ha
      simpa [pow_two] using Q.mul_mem ha ha
  have hsq : ∀ q ∈ Q, q ^ 2 ∈ W := fun q hq => hΦ ▸ fzl_sq_mem_phi (H := Q) hq
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ W :=
    fun a ha b hb => hΦ ▸ fzl_comm_mem_phi (H := Q) ha hb
  have hnrm : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W := by
    intro q hq w hw
    have hcw : ⁅q, w⁆ ∈ W := hcomm q hq w (hWQ hw)
    have hqweq : q * w * q⁻¹ = ⁅q, w⁆ * w := by
      rw [commutatorElement_def]; group
    rw [hqweq]
    exact W.mul_mem hcw hw
  by_contra hne
  obtain ⟨M, s, hHM, hMQ, hsQ, hsM, hs2, hMnrm, hcosW⟩ :=
    CFSG.EvenSporadicStandard.Induction.Junction.exists_index_two hQ hHQ hne
  have hphiM : fzlPhi Q ≤ M := fzc_sy2_phi_le_of_cosets hsQ hs2 hMnrm hcosW
  have hWM : W ≤ M := hΦ ▸ hphiM
  have hfour := fzc_sy2_four_cosets hWQ hcard hnrm hsq hcomm
    (hHQ hx) hxW (hHQ hy) hyW hyx
  have hsM' : s ∈ M := by
    rcases hfour s hsQ with h | h | h | h
    · exact hWM h
    · have : s = (s * x⁻¹) * x := by group
      rw [this]
      exact M.mul_mem (hWM h) (hHM hx)
    · have : s = (s * y⁻¹) * y := by group
      rw [this]
      exact M.mul_mem (hWM h) (hHM hy)
    · have : s = (s * (x * y)⁻¹) * (x * y) := by group
      rw [this]
      exact M.mul_mem (hWM h) (M.mul_mem (hHM hx) (hHM hy))
  exact hsM hsM'

end CFSG.OddStandard.SmallF3.FritzII
