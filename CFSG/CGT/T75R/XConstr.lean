module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB7
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIINorm
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIVals

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem exists_mem_conj_eight (hS : Sec3 T T₁)
    (hcard : Nat.card T = Nat.card (normIn T T₁) * 2) (hL4 : 4 ≤ Nat.card (normIn T T₁))
    {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    ∃ t₀ ∈ T, t₀ ∉ normIn T (conjSubgroup g T₁) ∧ ∃ x : G,
      x ∈ conjSubgroup g (normIn T₁ T) ∧ x ≠ 1 ∧ ⁅t₀, x⁆ ∈ normIn T T₁ := by
  have hS2 := hS.conj_of_mem_normalizer hg
  have hLg : normIn T (conjSubgroup g T₁) = conjSubgroup g (normIn T T₁) :=
    normIn_conj_left_of_mem_normalizer hg T₁
  have hcardU : Nat.card T = Nat.card (normIn T (conjSubgroup g T₁)) * 2 := by
    rw [hLg, card_conjSubgroup]
    exact hcard
  have hwc := hS.cfg.wc
  have hUT : normIn T (conjSubgroup g T₁) ≤ T := normIn_le _ _
  have hLT : normIn T T₁ ≤ T := normIn_le _ _
  have hTnle : ¬ T ≤ normIn T (conjSubgroup g T₁) := by
    intro hle
    have heq : normIn T (conjSubgroup g T₁) = T := le_antisymm hUT hle
    have hpos : 0 < Nat.card T := Nat.card_pos
    rw [heq] at hcardU
    omega
  obtain ⟨t₀, ht₀T, ht₀U⟩ := IsConcreteLE.not_le_iff_exists.1 hTnle
  have ht₀M : t₀ ∉ cfgM T (conjSubgroup g T₁) := fun hM => ht₀U (by
    rw [← hS2.cfg.inf_cfgM]
    exact ⟨ht₀T, hM⟩)
  have hF2 : 2 ≤ Nat.card ↥(normIn T T₁ ⊓ normIn T (conjSubgroup g T₁)) := by
    have h1 := card_le_four_mul_card_inf hLT hUT hcard hcardU
    omega
  have hFne : normIn T T₁ ⊓ normIn T (conjSubgroup g T₁) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hF2
    simp at hF2
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hFne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨l, hl, hlu⟩ := hS2.exists_mem_normIn₁_conj_eq ht₀T ht₀M hu.2
  have hlg : l ∈ conjSubgroup g (normIn T₁ T) := by
    rw [← normIn_conj_right_of_mem_normalizer hg T₁]
    exact hl
  have hcomm : ⁅t₀, l⁆ = u := commutator_eq_of_conj_eq hwc.1 ht₀T (hUT hu.2) hlu
  refine ⟨t₀, ht₀T, ht₀U, l, hlg, ?_, ?_⟩
  · rintro rfl
    apply hu1'
    rw [← hcomm]
    simp [commutatorElement_def]
  · rw [hcomm]
    exact hu.1

theorem Sec4Hyp.exists_x_eight [IsSimpleGroup G] (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : Sec4Hyp T T₁ a T₂)
    (hq : Nat.card T = 2 * Nat.card (normIn T T₁)) (hT8 : Nat.card T = 8) :
    ∃ g ∈ Subgroup.normalizer (T : Set G), ∃ x : G, x ∈ conjSubgroup g (normIn T₁ T) ∧ x ≠ 1 ∧
      x * x = 1 ∧ x ∈ Subgroup.normalizer (T : Set G) ∧
      x ∈ Subgroup.normalizer (normIn T T₁ : Set G) ∧
      (∀ r ∈ T, x * r * x⁻¹ * r⁻¹ ∈ normIn T T₁) ∧ (∃ l ∈ normIn T T₁, x * l ≠ l * x) ∧
      ¬ normIn T T₁ ≤ Subgroup.normalizer ((conjSubgroup g T₁ : Subgroup G) : Set G) := by
  have hcT : Nat.card T = Nat.card (normIn T T₁) * 2 := by rw [hq, mul_comm]
  have hL4 : 4 ≤ Nat.card (normIn T T₁) := by omega
  have hLT : normIn T T₁ ≤ T := normIn_le T T₁
  obtain ⟨g, hg, x₀, hx₀, l₀, hl₀, hx₀l₀⟩ := h.exists_conj_not_comm hTO hBW h214 hInv hnab hq
  obtain ⟨t₀, ht₀T, ht₀U, x, hx, hx1, hx0⟩ := exists_mem_conj_eight h.sec3 hcT hL4 hg
  have hS2 := h.sec3.conj_of_mem_normalizer hg
  have hL₂g : normIn (conjSubgroup g T₁) T = conjSubgroup g (normIn T₁ T) :=
    normIn_conj_right_of_mem_normalizer hg T₁
  have hsqg : ∀ z ∈ conjSubgroup g (normIn T₁ T), z * z = 1 := fun z hz =>
    elemAbelian_mul_self (isElemAbelian_conjSubgroup h.sec3.cfg.wc₁.1 g)
      (conjSubgroup_mono (normIn_le T₁ T) hz)
  have hl₀g : l₀ ∉ normIn T (conjSubgroup g T₁) := by
    intro hl
    apply hx₀l₀
    have hx' : x₀ ∈ normIn (conjSubgroup g T₁) T := by
      rw [hL₂g]
      exact hx₀
    exact (hS2.cfg.comm_L_L₁ hl hx').symm
  have hvals := h.sec3.values_of_mem_conj hcT hg ht₀T ht₀U hx
  have hxx := hsqg x hx
  have hLE := h.sec3.isLElt_conj hg hx hx1
  have haL : ∀ r ∈ T, ⁅r, x⁆ ∈ normIn T T₁ := fun r hr => by
    rcases hvals r hr with h0 | h0
    · rw [h0]
      exact (normIn T T₁).one_mem
    · rw [h0]
      exact hx0
  refine ⟨g, hg, x, hx, hx1, hxx, hLE.transv.1, mem_normalizer_of_values hxx haL hLT, ?_,
    ⟨l₀, hl₀, fun hc => hl₀g (hLE.cent l₀ (hLT hl₀) hc)⟩, ?_⟩
  · intro r hr
    have e : x * r * x⁻¹ * r⁻¹ = (⁅r, x⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (normIn T T₁).inv_mem (haL r hr)
  · intro hle
    exact hl₀g (mem_normIn.2 ⟨hLT hl₀, hle hl₀⟩)

end CFSG.CGT.T75R
