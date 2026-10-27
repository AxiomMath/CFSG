module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888YGold
public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldY

public section

open CFSG.Open CFSG.Goldschmidt Subgroup CFSG.GH74.GLS.Th2.P412
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

private theorem s888b_goldschmidtSimpleType_of_mulEquiv {L M : Type} [Group L] [Group M]
    (h : goldschmidtSimpleType L) (e : L ≃* M) : goldschmidtSimpleType M := by
  classical
  simp only [goldschmidtSimpleType] at h ⊢
  rcases h with ⟨f, hf, hne⟩ | ⟨n, hn, hne⟩ | ⟨f, hf, hne⟩ |
    ⟨p, f, hp, hpo, hf, hp5, h8, hne⟩ | ⟨m, hm, hcard⟩ | hne
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans hne.some⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans hne.some⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans hne.some⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, f, hp, hpo, hf, hp5, h8, ⟨e.symm.trans hne.some⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, (Nat.card_congr e.toEquiv).symm.trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans hne.some⟩))))

theorem component_classification {Y : Type} [Group Y] [Finite Y] (hY : IsGoldSemisimple Y)
    (D : Sylow 2 Y) (hDcomm : ∀ a ∈ (D : Subgroup Y), ∀ b ∈ (D : Subgroup Y), a * b = b * a)
    {J : Subgroup Y} (hJ : IsComponentOf J ⊤) {m : ℕ} (hm : 1 ≤ m)
    (hcard : Nat.card ↥((D : Subgroup Y) ⊓ J) = 4 ^ m) :
    (m = 1 ∧ ∃ (p n : ℕ) (_ : Fact p.Prime), Odd p ∧ 0 < n ∧ 5 ≤ p ^ n ∧
        (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) ∧ Nonempty (↥J ≃* PSL(2, GaloisField p n))) ∨
      (∃ f : ℕ, f = 2 * m ∧ 3 ≤ f ∧ Nonempty (↥J ≃* PSL(2, GaloisField 2 f))) := by
  classical
  have hZY : Subgroup.center Y = ⊥ := GoldY.center_eq_bot hY.o2 hY.odd hY.layer
  have hZJ : Subgroup.center ↥J = ⊥ := GoldY.component_center_eq_bot hZY hY.layer hJ
  haveI hJnorm : J.Normal := GoldY.component_normal hY.layer hJ
  let eJ : ↥J ⧸ Subgroup.center ↥J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  haveI : IsSimpleGroup ↥J := eJ.symm.isSimpleGroup
  have htype : goldschmidtSimpleType ↥J :=
    s888b_goldschmidtSimpleType_of_mulEquiv (hY.comps J hJ) eJ
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (D : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, D.isPGroup', by rw [Subgroup.relIndex_top_right]; exact D.not_dvd_index⟩
  obtain ⟨S, hS⟩ := hT.inf_of_le_normalizer (N := J) le_top
    (by rw [Subgroup.normalizer_eq_top])
  have hcardS : Nat.card (S : Subgroup ↥J) = 4 ^ m := by
    rw [← Subgroup.card_map_of_injective J.subtype_injective, hS, hcard]
  have hcommS : ∀ a ∈ (S : Subgroup ↥J), ∀ b ∈ (S : Subgroup ↥J), a * b = b * a := by
    intro a ha b hb
    have haD : J.subtype a ∈ (D : Subgroup Y) := by
      have h : J.subtype a ∈ (S : Subgroup ↥J).map J.subtype :=
        Subgroup.mem_map_of_mem J.subtype ha
      rw [hS] at h
      exact h.1
    have hbD : J.subtype b ∈ (D : Subgroup Y) := by
      have h : J.subtype b ∈ (S : Subgroup ↥J).map J.subtype :=
        Subgroup.mem_map_of_mem J.subtype hb
      rw [hS] at h
      exact h.1
    exact J.subtype_injective (by simpa using hDcomm (J.subtype a) haD (J.subtype b) hbD)
  exact goldtype_elementary_sylow htype S hm hcommS hcardS

end CFSG.OddStandard.SmallF3.Omega
