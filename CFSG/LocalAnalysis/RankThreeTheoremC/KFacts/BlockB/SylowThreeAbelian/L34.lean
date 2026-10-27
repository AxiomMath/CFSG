module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB

open CFSG.Open CFSG.AGLEmbeddingD2

namespace SylowThreeAbelian

theorem commute_of_card_eq_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H P Q : Subgroup G} (hPH : P ≤ H) (hQH : Q ≤ H)
    (hP : Nat.card P = p ^ (Nat.card H).factorization p)
    (hQ : Nat.card Q = p ^ (Nat.card H).factorization p)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  let P' : Sylow p H := Sylow.ofCard (P.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, hP])
  let Q' : Sylow p H := Sylow.ofCard (Q.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, hQ])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' Q'
  have hQg : (Q' : Subgroup H) = (P' : Subgroup H).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hmem : ∀ x ∈ P, (g : G) * x * (g : G)⁻¹ ∈ Q := by
    intro x hx
    have h1 : (MulAut.conj g).toMonoidHom ⟨x, hPH hx⟩ ∈ (Q' : Subgroup H) := by
      rw [hQg]
      exact ⟨⟨x, hPH hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 h1
  intro x hx y hy
  have h : (g : G) * (x * y) * (g : G)⁻¹ = (g : G) * (y * x) * (g : G)⁻¹ := by
    calc (g : G) * (x * y) * (g : G)⁻¹
        = ((g : G) * x * (g : G)⁻¹) * ((g : G) * y * (g : G)⁻¹) := by group
      _ = ((g : G) * y * (g : G)⁻¹) * ((g : G) * x * (g : G)⁻¹) :=
          hcomm _ (hmem x hx) _ (hmem y hy)
      _ = (g : G) * (y * x) * (g : G)⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h)

section Main


open CFSG.AGLEmbedding.L34Outer Certificates.L34Outer

theorem kFactSylowThreeAbelian_l34 {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (θ : K ≃* CFSG.ComponentClassification.PSL3Four.S)
    (R : Sylow 3 X) (hcomm : ∀ x ∈ (R : Subgroup X), ∀ y ∈ (R : Subgroup X), x * y = y * x)
    {E : Subgroup X} (hER : E ≤ R) (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    IsElemAbelian 3 (R : Subgroup X) ∧ Nat.card (R : Subgroup X) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ι, hinj, -, hιR⟩ := exists_embedding_l34 hC θ
  have hX : Nat.card X ∣ 241920 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      ← CFSG.ComponentClassification.PSL3Four.card_R]
    exact Subgroup.card_dvd_of_le hιR
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp R.isPGroup'
  have hRX : Nat.card (R : Subgroup X) ∣ 241920 := (Subgroup.card_subgroup_dvd_card _).trans hX
  have h9 : 3 ^ 2 ∣ 3 ^ n := by
    rw [← hn, show (3 : ℕ) ^ 2 = 9 by norm_num, ← hE9]
    exact Subgroup.card_dvd_of_le hER
  have hn2 : 2 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h9
  have hn3 : n ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ∣ 241920 := (pow_dvd_pow 3 (by omega)).trans (hn ▸ hRX)
    norm_num at this
  interval_cases n
  · have hEq : E = R := Subgroup.eq_of_le_of_card_ge hER (by rw [hn, hE9]; norm_num)
    refine ⟨?_, by rw [hn]; norm_num⟩
    rw [← hEq]
    exact hE
  · exfalso
    have facts := l34_outer_check
    have hf : (Nat.card CFSG.ComponentClassification.PSL3Four.R).factorization 3 = 3 := by
      rw [CFSG.ComponentClassification.PSL3Four.card_R]
      exact factorization_eq_of_pow_dvd Nat.prime_three (k := 3) (by norm_num) (by norm_num)
        (by norm_num)
    have hPR : Psub l34OuterData ≤ CFSG.ComponentClassification.PSL3Four.R :=
      facts.P_le_T.trans T_le_R
    have hQR : (R : Subgroup X).map ι ≤ CFSG.ComponentClassification.PSL3Four.R :=
      (Subgroup.map_le_range ι _).trans hιR
    have hQc : Nat.card ((R : Subgroup X).map ι) = 27 := by
      rw [Subgroup.card_map_of_injective hinj, hn]
      norm_num
    have hQcomm : ∀ x ∈ (R : Subgroup X).map ι, ∀ y ∈ (R : Subgroup X).map ι,
        x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha b hb]
    have hPcomm := commute_of_card_eq_sylow (p := 3) hPR hQR
      (by rw [facts.cardP, hf]; norm_num) (by rw [hQc, hf]; norm_num) hQcomm
    have hmem : ∀ w ∈ [l34OuterData.a, l34OuterData.b],
        CFSG.AGLEmbedding.FusD2.wordVal g4 w ∈ Psub l34OuterData := fun w hw =>
      Subgroup.subset_closure (List.mem_map_of_mem hw)
    exact facts.noncomm (hPcomm _ (hmem _ (by simp)) _ (hmem _ (by simp)))

end Main

end SylowThreeAbelian

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB
