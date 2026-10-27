module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem e17_Omega1_le_Y (h : L41GPh16 t L S x₁ x₂ lam rho)
    (hab : ∀ a ∈ l41Q1 t x₁ x₂ rho, ∀ b ∈ l41Q1 t x₁ x₂ rho, a * b = b * a) :
    ∀ x ∈ l41Q1 t x₁ x₂ rho, x * x = 1 → x ∈ l41Y t x₁ x₂ rho := by
  let E₀ : Subgroup G :=
    { carrier := {x | x ∈ l41Q1 t x₁ x₂ rho ∧ x * x = 1}
      mul_mem' := by
        intro a b ha hb
        refine ⟨(l41Q1 t x₁ x₂ rho).mul_mem ha.1 hb.1, ?_⟩
        have hcomm : b * a = a * b := (hab a ha.1 b hb.1).symm
        calc (a * b) * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hcomm]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha.2, hb.2, mul_one]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        refine ⟨(l41Q1 t x₁ x₂ rho).inv_mem ha.1, ?_⟩
        have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.2
        simpa [hai] using ha.2 }
  have hEel : CFSG.Open.IsElemAbelian 2 E₀ := by
    refine ⟨?_, ?_⟩
    · exact isMulCommutative_iff.mpr fun a b => Subtype.ext (hab a.1 a.2.1 b.1 b.2.1)
    · intro x hx
      rw [pow_two]
      exact hx.2
  have hYle : l41Y t x₁ x₂ rho ≤ E₀ := fun y hy =>
    ⟨h.q1facts.Y_le hy, z18_Y_sq h.toL41GPh11 hy⟩
  have hnorm : ∀ e ∈ E₀, t * e * t⁻¹ ∈ E₀ := by
    intro e he
    refine ⟨z18_conj_Q1 h.toL41GPh15 (z18_t_mem_M t x₁ x₂ rho) he.1, ?_⟩
    have hsq : (t * e * t⁻¹) * (t * e * t⁻¹) = t * (e * e) * t⁻¹ := by group
    rw [hsq, he.2]
    group
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have htE : t ∉ E₀ := fun ht => h.q1facts.t_not_mem ht.1
  have hno : ∀ E' : Subgroup G, CFSG.Open.IsElemAbelian 2 E' → Nat.card E' = 16 →
      E' ≤ centralizer ({t} : Set G) → False :=
    fun E' he hc hle => l41_no_e16_cent_conj h.toL41GPh1 he hc 1 (by simpa using hle)
  have hnot32 : ¬ 32 ≤ Nat.card E₀ :=
    fun hcard => e17_no_big_elem hEel hcard ht2 htE hnorm hno
  have hYcard : Nat.card ↥(l41Y t x₁ x₂ rho) = 16 := h.yfacts.Y_elem.2
  have hdvd : 16 ∣ Nat.card E₀ := by
    have h1 := Subgroup.card_dvd_of_le hYle
    rwa [hYcard] at h1
  have hle16 : 16 ≤ Nat.card E₀ := by
    have h1 := Subgroup.card_le_of_le hYle
    rwa [hYcard] at h1
  have hcardE : Nat.card E₀ = 16 := by
    have hlt : Nat.card E₀ < 32 := by omega
    obtain ⟨k, hk⟩ := hdvd
    omega
  have hEq : E₀ = l41Y t x₁ x₂ rho :=
    (Subgroup.eq_of_le_of_card_ge hYle (by omega)).symm
  intro x hx hsq
  exact hEq ▸ ⟨hx, hsq⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
