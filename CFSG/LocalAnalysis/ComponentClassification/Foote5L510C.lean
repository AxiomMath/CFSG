module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510B
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteRankThree
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53B
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56J

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem card_le_four_of_le_Q {E : Subgroup G} (hEQ : E ≤ Q) (hEsq : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h.isPGroup_Q.to_le hEQ)
  have hE : CFSG.Open.IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (commute_of_sq_eq_one hEsq a.2 b.2)⟩⟩, fun a ha => by
      rw [sq]; exact hEsq a ha⟩
  have h1 := SectionRank.le_pRank one_lt_two hEQ hE hk
  rw [h.open_pRank_Q] at h1
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h1
    _ = 4 := by norm_num

include ε in
theorem card_le_thirtytwo
    (h𝕊 : FooteSimpleType 𝕊) {E : Subgroup G} (hES : E ≤ S) (hEsq : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 32 := by
  have hEN : E ≤ normalizer (L : Set G) := hES.trans h.S_le
  have h1 := card_eq_card_inf_mul_card_actImage ε hEN
  have hEC : E ⊓ coreActionKernel L = E ⊓ Q := by
    rw [← h.inf_coreActionKernel, ← inf_assoc, inf_of_le_left hES]
  have h2 := h.card_le_four_of_le_Q (E := E ⊓ Q) inf_le_right
    (fun e he => hEsq e (mem_inf.mp he).1)
  have h3 := AutL2Facts.footeAutRankThree 𝕊 h𝕊 (actImage L ε E) (by
    intro α hα
    obtain ⟨e, he, rfl⟩ := (mem_actImage ε hEN).mp hα
    rw [← actG_mul ε (hEN he) (hEN he), hEsq e he, actG_one])
  rw [h1, hEC]
  calc Nat.card ↥(E ⊓ Q) * Nat.card (actImage L ε E) ≤ 4 * 8 := Nat.mul_le_mul h2 h3
    _ = 32 := by norm_num

include ε in
theorem exists_fourgroup_R_of_image (h𝕊 : FooteSimpleType 𝕊) {E : Subgroup G} (hES : E ≤ S)
    (hEsq : ∀ e ∈ E, e * e = 1) (hE8 : 8 ≤ Nat.card (actImage L ε E)) :
    ∃ r₁ ∈ S ⊓ L, ∃ r₂ ∈ S ⊓ L, r₁ * r₁ = 1 ∧ r₂ * r₂ = 1 ∧ r₁ * r₂ = r₂ * r₁ ∧ r₁ ≠ 1 ∧
      r₂ ≠ 1 ∧ r₁ ≠ r₂ ∧ ∀ e ∈ E, e * r₁ = r₁ * e ∧ e * r₂ = r₂ * e := by
  classical
  have hEN : E ≤ normalizer (L : Set G) := hES.trans h.S_le
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => commute_of_sq_eq_one hEsq ha hb
  set Eb := actImage L ε E with hEb
  have hEb2 : ∀ α ∈ Eb, α * α = 1 := by
    intro α hα
    obtain ⟨e, he, rfl⟩ := (mem_actImage ε hEN).mp hα
    rw [← actG_mul ε (hEN he) (hEN he), hEsq e he, actG_one]
  have hI := card_le_two_mul_inf_innAut h𝕊 hEb2
  have hI4 : 4 ≤ Nat.card ↥(Eb ⊓ innAut5 𝕊) := by omega
  obtain ⟨α₁, hα₁, hα₁1⟩ : ∃ α ∈ Eb ⊓ innAut5 𝕊, α ≠ 1 := by
    by_contra hno
    push Not at hno
    have h1 := SmallLocal.card_le_of_forall_mem_finset ({1} : Finset (MulAut 𝕊)) fun α hα => by
      rw [hno α hα]
      exact Finset.mem_singleton_self _
    rw [Finset.card_singleton] at h1
    omega
  obtain ⟨α₂, hα₂, hα₂1, hα₁₂⟩ : ∃ α ∈ Eb ⊓ innAut5 𝕊, α ≠ 1 ∧ α₁ ≠ α := by
    by_contra hno
    push Not at hno
    have h1 := SmallLocal.card_le_of_forall_mem_finset ({1, α₁} : Finset (MulAut 𝕊))
      fun α hα => by
        by_cases hα1 : α = 1
        · rw [hα1]
          exact Finset.mem_insert_self _ _
        · rw [← hno α hα hα1]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h2 : ({1, α₁} : Finset (MulAut 𝕊)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨e₁, he₁, rfl⟩ := (mem_actImage ε hEN).mp (mem_inf.mp hα₁).1
  obtain ⟨e₂, he₂, rfl⟩ := (mem_actImage ε hEN).mp (mem_inf.mp hα₂).1
  obtain ⟨q₁, hq₁, r₁, hr₁, rfl⟩ := h.exists_mul_of_inner ε (hES he₁) (mem_inf.mp hα₁).2
  obtain ⟨q₂, hq₂, r₂, hr₂, rfl⟩ := h.exists_mul_of_inner ε (hES he₂) (mem_inf.mp hα₂).2
  have hQR : ∀ c ∈ Q, c ∈ S ⊓ L → c = 1 := fun c hcQ hcR => by
    have h1 : c ∈ Q ⊓ L := mem_inf.mpr ⟨hcQ, (mem_inf.mp hcR).2⟩
    rwa [h.Q_inf_L, mem_bot] at h1
  have hRN : ∀ r ∈ S ⊓ L, r ∈ normalizer (L : Set G) := fun r hr => h.S_le (mem_inf.mp hr).1
  have hQN : ∀ q ∈ Q, q ∈ normalizer (L : Set G) := fun q hq => h.S_le (h.QS hq)
  have hact : ∀ q ∈ Q, ∀ r ∈ S ⊓ L, actG L ε (q * r) = actG L ε r := by
    intro q hq r hr
    rw [actG_mul ε (hQN q hq) (hRN r hr), (h.actG_eq_one_iff_mem_Q ε (h.QS hq)).mpr hq, one_mul]
  have hR1 : ∀ r ∈ S ⊓ L, actG L ε r = 1 → r = 1 := fun r hr h1 =>
    hQR r ((h.actG_eq_one_iff_mem_Q ε (mem_inf.mp hr).1).mp h1) hr
  have hsqr : ∀ q ∈ Q, ∀ r ∈ S ⊓ L, q * r ∈ E → r * r = 1 := by
    intro q hq r hr hqr
    have hc := h.commute_Q_R hq hr
    have h1 := hEsq _ hqr
    apply hR1 _ (mul_mem hr hr)
    rw [actG_mul ε (hRN r hr) (hRN r hr), ← hact q hq r hr, ← actG_mul ε (hEN hqr) (hEN hqr), h1,
      actG_one]
  have hcom : ∀ r r' : G, r ∈ S ⊓ L → r' ∈ S ⊓ L → actG L ε r * actG L ε r' =
      actG L ε r' * actG L ε r → r * r' = r' * r := by
    intro r r' hr hr' hrr'
    have h1 : actG L ε (r * r' * r⁻¹ * r'⁻¹) = 1 := by
      rw [actG_mul ε (mul_mem (mul_mem (hRN r hr) (hRN r' hr')) (inv_mem (hRN r hr)))
        (inv_mem (hRN r' hr')), actG_mul ε (mul_mem (hRN r hr) (hRN r' hr')) (inv_mem (hRN r hr)),
        actG_mul ε (hRN r hr) (hRN r' hr'), actG_inv ε (hRN r hr), actG_inv ε (hRN r' hr'), hrr']
      group
    have h2 := hR1 _ (mul_mem (mul_mem (mul_mem hr hr') (inv_mem hr)) (inv_mem hr')) h1
    calc r * r' = r * r' * r⁻¹ * r'⁻¹ * (r' * r) := by group
      _ = r' * r := by rw [h2, one_mul]
  refine ⟨r₁, hr₁, r₂, hr₂, hsqr q₁ hq₁ r₁ hr₁ he₁, hsqr q₂ hq₂ r₂ hr₂ he₂, ?_, ?_, ?_, ?_, ?_⟩
  · apply hcom r₁ r₂ hr₁ hr₂
    rw [← hact q₁ hq₁ r₁ hr₁, ← hact q₂ hq₂ r₂ hr₂, ← actG_mul ε (hEN he₁) (hEN he₂),
      ← actG_mul ε (hEN he₂) (hEN he₁), hEc _ he₁ _ he₂]
  · rintro rfl
    exact hα₁1 (by rw [hact q₁ hq₁ 1 (one_mem _), actG_one])
  · rintro rfl
    exact hα₂1 (by rw [hact q₂ hq₂ 1 (one_mem _), actG_one])
  · rintro rfl
    exact hα₁₂ (by rw [hact q₁ hq₁ r₁ hr₁, hact q₂ hq₂ r₁ hr₂])
  · have hcomm' : ∀ q ∈ Q, ∀ r ∈ S ⊓ L, q * r ∈ E → ∀ e ∈ E, e * r = r * e := by
      intro q hq r hr hqr e he
      have heS := hES he
      have h1 := hEc e he _ hqr
      have hq' : e * q * e⁻¹ ∈ Q := h.conj_mem_Q heS hq
      have hr' : e * r * e⁻¹ ∈ S ⊓ L := h.conj_mem_R heS hr
      have h2 : (e * q * e⁻¹) * (e * r * e⁻¹) = q * r := by
        calc (e * q * e⁻¹) * (e * r * e⁻¹) = e * (q * r) * e⁻¹ := by group
          _ = q * r := by rw [h1, mul_inv_cancel_right]
      have h3 : q⁻¹ * (e * q * e⁻¹) = r * (e * r * e⁻¹)⁻¹ := by
        calc q⁻¹ * (e * q * e⁻¹) =
            q⁻¹ * ((e * q * e⁻¹) * (e * r * e⁻¹)) * (e * r * e⁻¹)⁻¹ := by group
          _ = q⁻¹ * (q * r) * (e * r * e⁻¹)⁻¹ := by rw [h2]
          _ = r * (e * r * e⁻¹)⁻¹ := by group
      have h4 := hQR _ (mul_mem (inv_mem hq) hq') (by rw [h3]; exact mul_mem hr (inv_mem hr'))
      rw [h3, mul_inv_eq_one] at h4
      calc e * r = e * r * e⁻¹ * e := by group
        _ = r * e := by rw [← h4]
    exact fun e he => ⟨hcomm' q₁ hq₁ r₁ hr₁ he₁ e he, hcomm' q₂ hq₂ r₂ hr₂ he₂ e he⟩

end Sec5

end CFSG.ComponentClassification.Foote5
