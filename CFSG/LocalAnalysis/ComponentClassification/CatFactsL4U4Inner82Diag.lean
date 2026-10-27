module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner82
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUh

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Inner82

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem mem_centralizer_of_coreKernel_of_bot {H : Type} [Group H] {J₁ : Subgroup H}
    (hO : pPrimeCore 2 ↥J₁ = ⊥) {g : H} (hg : g ∈ coreActionKernel J₁) :
    g ∈ centralizer (J₁ : Set H) := by
  rw [mem_centralizer_iff]
  intro j hj
  have h1 := hg.2 j hj
  rw [hO, Subgroup.map_bot, Subgroup.mem_bot] at h1
  have h2 : g⁻¹ * j * g = j := by
    have e : j⁻¹ * (g⁻¹ * j * g) = 1 := by rw [← h1]; group
    exact (inv_mul_eq_one.1 e).symm
  calc j * g = g * (g⁻¹ * j * g) := by group
    _ = g * j := by rw [h2]

theorem diagCase : DiagCase := by
  intro H _ _ p f hp hp2 hf hsimp hC hcase α β ξ hαα hαc J₁ hJC hcomp hJtype hβ hξ
  classical
  set L := generalizedFitting H with hLdef
  have : L.Normal := LocalCores.generalized_fitting_characteristic.2
  have htype : IsSec82LType ↥L p f := by
    rcases hcase with ⟨hL, -⟩ | ⟨hU, -⟩
    · exact Or.inl hL
    · exact Or.inr (Or.inl hU)
  have hinn : ∀ J : Subgroup (MulAut ↥L), ⁅J, J⁆ = J →
      J ≤ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rcases hcase with ⟨hL, -⟩ | ⟨hU, -⟩
    · obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
      set e' : ↥L ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F :=
        eL.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
          (QuotientGroup.quotientMulEquivOfEq
            (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 F).symm))
      exact AZ.le_inner_of_mulEquiv e' (fun J hJ => DiagL.le_range_conj_of_perfect hJ)
    · obtain ⟨-, K', _, _, hK', ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
      have hUF : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K' :=
        ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
      exact AZ.le_inner_of_mulEquiv eU (fun J hJ => DiagU.le_range_conj_of_perfect_U hUF hp2 hJ)
  have hperf : ∀ J : Subgroup H, ⁅J, J⁆ = J → J ≤ L := fun J hJ =>
    AZ.le_of_perfect_of_le_inner L hC hinn hJ
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact false_of_isPComponent_one hp hp2 hf htype hperf hJC hcomp hJtype
  have hJp : ⁅J₁, J₁⁆ = J₁ := commutator_eq_self_of_isPComponent hJC hcomp
  have hJL := hperf J₁ hJp
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := AZ.exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJtype
  have hsJ₁ : s ∣ Nat.card J₁ := hsJ.trans (Subgroup.card_quotient_dvd_card _)
  have := Fact.mk hs
  obtain ⟨⟨y, hy⟩, hys⟩ := exists_prime_orderOf_dvd_card' (G := J₁) s hsJ₁
  rw [Subgroup.orderOf_mk] at hys
  have h2J := AZ.two_mul_card_of_isSec8JType hp hp2 hJtype
  have hcardQ := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J₁)
  have hQpos : 0 < Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) := Nat.card_pos
  have hOpos : 0 < Nat.card (pPrimeCore 2 ↥J₁) := Nat.card_pos
  have hcard : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J₁ := by
    rw [← h2J, hcardQ]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hOpos)
  obtain ⟨hJ2, hfin⟩ : 2 * Nat.card J₁ ≤ (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ∧
      (β ∈ centralizer (J₁ : Set H) → ξ ∈ centralizer (J₁ : Set H) → False) := by
    rcases hcase with ⟨hL, h1⟩ | ⟨hU, h3⟩
    · obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
      let : Fintype F := Fintype.ofFinite F
      have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
      set e' : ↥L ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F :=
        eL.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
          (QuotientGroup.quotientMulEquivOfEq
            (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 F).symm))
      have e4 : ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 := by ring
      have := DiagL.diag_L4 hC (by rw [hFq]; exact h1) e' hαα hα1 hαc hJL hJC hJp
        (by rw [hF, e4]; exact hcard) hs hs2 (by rw [hF]; exact hsq) hy hys
      rwa [hF, e4] at this
    · obtain ⟨-, K', _, _, hK', ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
      have hUF : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K' :=
        ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
      exact DiagU.diag_U4 hUF hC hp2 h3 eU hαα hα1 hαc hJL hJC hJp hcard hs hs2 hsq hy hys
  have hO1 : Nat.card (pPrimeCore 2 ↥J₁) = 1 := by
    have h1 : 2 * (Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) * Nat.card (pPrimeCore 2 ↥J₁)) ≤
        2 * Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) := by
      rw [← hcardQ, h2J]
      exact hJ2
    have h2 : Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) * Nat.card (pPrimeCore 2 ↥J₁) ≤
        Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) * 1 := by omega
    have h3 := Nat.le_of_mul_le_mul_left h2 hQpos
    omega
  have hO : pPrimeCore 2 ↥J₁ = ⊥ := Subgroup.eq_bot_of_card_eq _ hO1
  exact hfin (mem_centralizer_of_coreKernel_of_bot hO hβ)
    (mem_centralizer_of_coreKernel_of_bot hO hξ)

end Inner82

open CFSG.ComponentClassification.GSThmB

theorem cf82Inner : CF82Inner := cf82Inner_of_diagCase Inner82.diagCase

end CFSG.ComponentClassification.CatFactsL4U4
