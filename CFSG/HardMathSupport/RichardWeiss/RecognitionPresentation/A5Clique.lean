module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.Clique

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.CGT.PushingUpLit.CGT6 CFSG.ComponentClassification.PresentationLocal

section Generic

variable {J : Type*} [Group J] [DecidableEq J] {D : J → Prop}

@[expose] def AAlt (p q : J) : Prop :=
  (p * q) ^ 5 = 1 ∧ (p * q * p * q⁻¹) ^ 2 = 1 ∧ (p * q⁻¹) ^ 5 = 1 ∧ (p * q⁻¹ * p * q) ^ 2 = 1

theorem exists_clique_three_of_aalt (hD : OrderThreeClass D) {p q : J} (hp : D p) (hq : D q)
    (h : AAlt p q) : ∃ F : Finset J, IsClique D F ∧ 3 ≤ F.card := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hq3 := hD.cube q hq
  set ra := q⁻¹ * p * q with hra
  set rb := q * p * q⁻¹ with hrb
  have hDra : D ra := hD.conj q p hp
  have hDrb : D rb := by simpa using hD.conj q⁻¹ p hp
  have hpra : (p * ra) ^ 2 = 1 := by simpa [hra, mul_assoc] using h4
  have hprb : (p * rb) ^ 2 = 1 := by simpa [hrb, mul_assoc] using h2
  have e1 : q * q = q⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc q * q * q = q * (q * q) := mul_assoc _ _ _
      _ = q ^ 3 := (pow_three q).symm
      _ = 1 := hq3
  have e2 : q⁻¹ * q⁻¹ = q := by rw [← mul_inv_rev, e1, inv_inv]
  have hconj : q * rb * q⁻¹ = ra := by
    calc q * rb * q⁻¹ = (q * q) * p * (q⁻¹ * q⁻¹) := by simp only [hrb]; group
      _ = ra := by rw [e1, e2]
  have hrbra : (rb * ra) ^ 2 = 1 := by
    have : rb * ra = q * (p * rb) * q⁻¹ := by
      calc rb * ra = (q * p * q⁻¹) * (q * rb * q⁻¹) := by rw [hconj]
        _ = q * (p * rb) * q⁻¹ := by simp only [hrb]; group
    rw [this]
    calc (q * (p * rb) * q⁻¹) ^ 2 = q * (p * rb) ^ 2 * q⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hprb]; group
  have hp1 := hD.ne_one p hp
  have hra1 := hD.ne_one _ hDra
  have hrb1 := hD.ne_one _ hDrb
  have hp3 := hD.cube p hp
  have hra3 := hD.cube _ hDra
  have hrb3 := hD.cube _ hDrb
  have hsq : ∀ x : J, x ^ 3 = 1 → x ≠ 1 → (x * x) ^ 2 ≠ 1 := by
    intro x hx3 hx1 h
    apply hx1
    have : (x * x) ^ 2 = x ^ 3 * x := by simp only [pow_two, pow_three]; group
    rw [this, hx3, one_mul] at h
    exact h
  have hne1 : p ≠ ra := fun h => hsq p hp3 hp1 (by simpa [← h] using hpra)
  have hne2 : p ≠ rb := fun h => hsq p hp3 hp1 (by simpa [← h] using hprb)
  have hne3 : rb ≠ ra := fun h => hsq rb hrb3 hrb1 (by simpa [h] using hrbra)
  have hcard : ({p, ra, rb} : Finset J).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨p, ra, rb, hne1, hne2, hne3.symm, rfl⟩
  refine ⟨{p, ra, rb}, ⟨?_, ?_⟩, hcard.ge⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h <;> rw [h] <;> assumption
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with h | h | h <;> rcases hb with h' | h' | h' <;> rw [h, h'] <;> rw [h, h'] at hab
    · exact absurd rfl hab
    · exact hpra
    · exact hprb
    · exact sq_comm_eq_one hpra
    · exact absurd rfl hab
    · exact sq_comm_eq_one hrbra
    · exact sq_comm_eq_one hprb
    · exact hrbra
    · exact absurd rfl hab

end Generic

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
