module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveThree
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Fi22Certificates


theorem exists_e9_le_inf_of_fi22 {X : Type} [Group X] [Finite X] {N K : Subgroup X}
    [K.Normal] (hN : IsStronglyPEmbedded 5 N)
    (hK : CFSG.AGLEmbedding.IsFi22 ↥K) (hKN : ¬ K ≤ N) :
    (∃ R : Subgroup X, R ≤ N ⊓ K ∧ CFSG.Open.IsElemAbelian 3 R ∧ Nat.card R = 9) ∧
      ¬ 3 ^ 7 ∣ Nat.card ↥(N ⊓ K) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P₀, ⟨-, hP₀p, hP₀i⟩, hP₀N⟩ := hN.exists_isSylowOf_le
  set P : Sylow 5 X := hP₀p.toSylow (by simpa [Subgroup.relIndex_top_right] using hP₀i)
  have hPN : (P : Subgroup X) ≤ N := by
    rw [IsPGroup.toSylow_coe]
    exact hP₀N
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  set Y : Subgroup ↥K := (N ⊓ K).subgroupOf K with hYdef
  have hTY : CFSG.Open.GLBCore 5 1 (T : Subgroup ↥K) ≤ Y := by
    refine sSup_le ?_
    rintro M ⟨Q, hQT, hQ, rfl⟩ k hk
    rw [hYdef, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨?_, k.2⟩
    have hQne : Q.map K.subtype ≠ ⊥ := fun h =>
      CFSG.LocalAnalysis.UniquenessCase.UCK.ne_bot_of_one_le_pRank hQ
        ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h)
    have hQp : IsPGroup 5 ↥(Q.map K.subtype) := (T.isPGroup'.to_le hQT).map K.subtype
    have hQN : Q.map K.subtype ≤ N :=
      (Subgroup.map_mono hQT).trans (by rw [hTmap]; exact inf_le_left.trans hPN)
    exact hN.normalizer_le hQne hQp hQN
      (Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hk))
  have hYne : Y ≠ ⊤ := by
    intro hYt
    apply hKN
    intro x hx
    have hxY : (⟨x, hx⟩ : ↥K) ∈ Y := by rw [hYt]; exact Subgroup.mem_top _
    rw [hYdef, Subgroup.mem_subgroupOf] at hxY
    exact (Subgroup.mem_inf.mp hxY).1
  obtain ⟨hnot, R, hRY, hRabel, hRcard⟩ :=
    CFSG.AGLEmbedding.fi22_gammaOne_three hK T hTY hYne
  have hcardY : Nat.card ↥Y = Nat.card ↥(N ⊓ K) := by
    rw [hYdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  refine ⟨⟨Subgroup.map K.subtype R, ?_, CFSG.Open.IsElemAbelian.map hRabel K.subtype,
    ?_⟩, ?_⟩
  · have h : Subgroup.map K.subtype R ≤ Subgroup.map K.subtype Y :=
      Subgroup.map_mono hRY
    rw [hYdef, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right] at h
    exact h
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hRcard
  · rwa [← hcardY]

theorem not_sylow_three_le_of_fi22 {X : Type} [Group X] [Finite X] {N K : Subgroup X}
    [K.Normal] (hN : IsStronglyPEmbedded 5 N)
    (hK : CFSG.AGLEmbedding.IsFi22 ↥K) (hKN : ¬ K ≤ N) (S : Sylow 3 X) :
    ¬ (S : Subgroup X) ≤ N := by
  intro hSN
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hnot⟩ := exists_e9_le_inf_of_fi22 hN hK hKN
  apply hnot
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal S (N := K)
  have h3K : 3 ^ 9 ∣ Nat.card ↥K :=
    CFSG.AGLEmbedding.three_pow_nine_dvd_card_of_isFi22 hK
  have h3T : 3 ^ 9 ∣ Nat.card (T : Subgroup ↥K) := T.pow_dvd_card_of_pow_dvd_card h3K
  have hcardT : Nat.card (T : Subgroup ↥K) =
      Nat.card ↥((S : Subgroup X) ⊓ K) := by
    rw [hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h37 : 3 ^ 7 ∣ Nat.card ↥((S : Subgroup X) ⊓ K) := by
    rw [← hcardT]
    exact dvd_trans (by norm_num : 3 ^ 7 ∣ 3 ^ 9) h3T
  exact dvd_trans h37 (Subgroup.card_dvd_of_le (inf_le_inf hSN le_rfl))

end Fi22Certificates

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
