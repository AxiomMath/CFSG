module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionD
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionH

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

theorem B_eq_sup [Finite G] (B W₁ : Subgroup G) (hB : Nat.card ↥B = 9) (hW : Nat.card ↥W₁ = 3)
    (hWB : W₁ ≤ B) (σ : G) (hσB : σ ∈ B) (hσ3 : σ ^ 3 = 1) (hσW : σ ∉ W₁)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    Subgroup.zpowers σ ⊔ W₁ = B := by
  have hσ1 : σ ≠ 1 := fun h => hσW (h ▸ W₁.one_mem)
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hzc : Nat.card ↥(Subgroup.zpowers σ) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hnorm : Subgroup.zpowers σ ≤ Subgroup.normalizer (W₁ : Set G) := by
    refine Subgroup.zpowers_le.mpr (mem_normalizer_of_conj_le (fun w hw => ?_))
    have h : σ * w * σ⁻¹ = w := by
      rw [hcomm σ hσB w (hWB hw), mul_inv_cancel_right]
    rw [h]
    exact hw
  have hinf : Subgroup.zpowers σ ⊓ W₁ = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers σ ⊓ W₁) ∣ 3 := by
      rw [← hzc]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : Subgroup.zpowers σ ⊓ W₁ = Subgroup.zpowers σ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hzc, h])
      have hmem : σ ∈ Subgroup.zpowers σ ⊓ W₁ := by
        rw [heq]
        exact Subgroup.mem_zpowers σ
      exact hσW hmem.2
  have hprod := card_sup_mul_card_inf (Subgroup.zpowers σ) W₁ hnorm
  rw [hinf, Subgroup.card_bot, hzc, hW] at hprod
  have hle : Subgroup.zpowers σ ⊔ W₁ ≤ B := sup_le (Subgroup.zpowers_le.mpr hσB) hWB
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hB]; omega)

theorem closing_contradiction [Finite G] {H H₁ H₂ Pb : Subgroup G} {e : Fin 6 → G}
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (hL : PbarCore e Pb) (hPb : Nat.card Pb = 27)
    (B W₁ Mf Q : Subgroup G) (σ g : G)
    (hBeq : Subgroup.zpowers σ ⊔ W₁ = B)
    (hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hWc : ∀ x ∈ Mf, ∀ n ∈ W₁, x * n * x⁻¹ = n)
    (hσMf : σ ∉ Mf) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hQ : ∀ x ∈ Q, x ∈ Mf ∧ σ * x = x * σ) (hQcard : 27 ≤ Nat.card ↥Q)
    (hg : ∀ x ∈ Psub e, g * x * g⁻¹ ∈ B) : False := by
  have hσB : σ ∈ B := by
    rw [← hBeq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers σ)
  have hσC : Subgroup.zpowers σ ≤ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hBcomm b hb σ hσB
  have hQC : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) := by
    intro x hx
    have hC : B ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [← hBeq]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (hQ h hx).2.symm
      · intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact mul_inv_eq_iff_eq_mul.mp (hWc h (hQ h hx).1 w hw)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : b ∈ Subgroup.centralizer ({x} : Set G) := hC hb
    exact ((Subgroup.mem_centralizer_iff.mp hb') x (Set.mem_singleton x)).symm
  have hKC : Subgroup.zpowers σ ⊔ Q ≤ Subgroup.centralizer (B : Set G) :=
    sup_le hσC (fun x hx => hQC x hx)
  have hnormQ : Subgroup.zpowers σ ≤ Subgroup.normalizer (Q : Set G) := by
    refine Subgroup.zpowers_le.mpr (mem_normalizer_of_conj_le (fun x hx => ?_))
    have h : σ * x * σ⁻¹ = x := by
      rw [(hQ x hx).2, mul_inv_cancel_right]
    rw [h]
    exact hx
  have hzc : Nat.card ↥(Subgroup.zpowers σ) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hσ3 hσ1]
  have hinf : Subgroup.zpowers σ ⊓ Q = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers σ ⊓ Q) ∣ 3 := by
      rw [← hzc]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : Subgroup.zpowers σ ⊓ Q = Subgroup.zpowers σ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hzc, h])
      have hmem : σ ∈ Subgroup.zpowers σ ⊓ Q := by
        rw [heq]
        exact Subgroup.mem_zpowers σ
      exact hσMf (hQ σ hmem.2).1
  have hprodK := card_sup_mul_card_inf (Subgroup.zpowers σ) Q hnormQ
  rw [hinf, Subgroup.card_bot, hzc] at hprodK
  have hK : ∀ y ∈ Subgroup.zpowers σ ⊔ Q, ∀ b ∈ B, y * b = b * y := by
    intro y hy b hb
    have hy' := hKC hy
    exact ((Subgroup.mem_centralizer_iff.mp hy') b hb).symm
  have hle := card_le_centralizer_Psub hg hK
  rw [card_centralizer_Psub hone hlet hL hPb] at hle
  omega

end CFSG.GH74.QTGen4.Recog.G23.P7
