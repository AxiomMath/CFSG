module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbalModel
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Tools

public section

namespace CFSG.ComponentClassification.HSFLit.AutL2

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_centralizer_of_unbalancing {a x : G} {J : Subgroup G}
    (htri : GSUnbalancingTriple a x J)
    (htype : IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J)) :
    ∃ y ∈ J ⊓ centralizer ({x} : Set G), orderOf y = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hxo, -, -, -, hxJ, -⟩ := htri
  have hx2 : x * x = 1 := by rw [← pow_two, ← hxo, pow_orderOf_eq_one]
  have hset : {y | ∃ j ∈ J, ∃ d ∈ ({x} : Set G), y = j⁻¹ * d⁻¹ * j * d} =
      {y | ∃ j ∈ J, y = j⁻¹ * x⁻¹ * j * x} := by
    ext y
    simp
  have hxN : x ∈ normalizer (J : Set G) :=
    L34Facts.mem_normalizer_of_closure (hset ▸ hxJ) (Set.mem_singleton x)
  have hJe : 2 ∣ Nat.card J := by
    have hq : Nat.card (J ⧸ pPrimeCore 2 J) = 60 ∨ Nat.card (J ⧸ pPrimeCore 2 J) = 168 := by
      rcases htype with h | h
      · left; rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h]; decide
      · right; rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h]; decide
    have hdvd : Nat.card (J ⧸ pPrimeCore 2 J) ∣ Nat.card J := by
      rw [← Subgroup.index]; exact Subgroup.index_dvd_card _
    rcases hq with h | h <;> rw [h] at hdvd <;> exact (by norm_num : (2 : ℕ) ∣ _).trans hdvd
  obtain ⟨P, hP, hPx, -⟩ := L34Inv.exists_isSylowTwoIn_normalized
    (L34Inv.isPGroup_zpowers_of_mul_self hx2) (zpowers_le.mpr hxN)
  have hP2 : IsPGroup 2 P := GrS5.IsSylowTwoIn.isPGroup hP
  have hP1 : P ≠ ⊥ := by
    intro hPb
    obtain ⟨-, P₀, hP₀⟩ := hP
    have h1 := Sylow.card_eq_multiplicity P₀
    have h2 : Nat.card ↥(P₀ : Subgroup ↥J) = 1 := by
      rw [hP₀, hPb]
      simp
    have h3 : 0 < (Nat.card ↥J).factorization 2 :=
      Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' hJe
    rw [h2] at h1
    have h4 : 2 ≤ 2 ^ (Nat.card ↥J).factorization 2 := le_self_pow₀ (by norm_num) h3.ne'
    omega
  have hR2 : IsPGroup 2 ↥(P ⊔ zpowers x) :=
    hP2.to_sup_of_normal_left' (L34Inv.isPGroup_zpowers_of_mul_self hx2)
      (zpowers_le.mpr (hPx (mem_zpowers x)))
  obtain ⟨y, hyP, hy2, hyR⟩ := FooteLit.exists_involution_inf_center hR2 le_sup_left
    (sup_le le_normalizer (zpowers_le.mpr (hPx (mem_zpowers x)))) hP1
  exact ⟨y, mem_inf.mpr ⟨hP.1 hyP, mem_centralizer_singleton_iff.mpr
    (hyR x (mem_sup_right (mem_zpowers x))).symm⟩, hy2⟩

end CFSG.ComponentClassification.HSFLit.AutL2
