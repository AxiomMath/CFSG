module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Cls
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48SetupEx
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorCenter
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin KFactProofs.Sp48 CFSG.PreuniquenessRankFour.Helpers

namespace KFactProofs.Sp48

theorem isSimple_sp8_of_index {K : Type} [Group K] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSpFourEightIndex d) (e : K ≃* CatGroup d) (eK : K ≃* Sp8) : IsSimpleGroup Sp8 := by
  obtain ⟨q, -, -, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.B 2 q := hdq
  have : IsSimpleGroup K :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp K 2 q.p q.exponent
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
  exact eK.symm.isSimpleGroup

end KFactProofs.Sp48

theorem kFactSp48Local : KFactSp48Local := by
  intro Y _ _ K d hd hKn he hC T Y₀ h3 hW hY₀
  obtain ⟨e⟩ := he
  obtain ⟨⟨eK⟩, hcardK⟩ := exists_equiv_sp8 hd e
  have hcardS : Nat.card Sp8 = 3 ^ 4 * 13045760 := by
    rw [← hcardK]
    exact Nat.card_congr eK.symm.toEquiv
  have hsimple : IsSimpleGroup Sp8 := isSimple_sp8_of_index hd e eK
  have : K.Normal := hKn
  obtain ⟨e', y, S⟩ := exists_setup K eK hC hcardS T h3
  have hEel : IsElemAbelian 3 spE := by
    refine ⟨IsMulCommutative.of_comm ?_, fun x hx => ((mem_spE_iff_cube x).1 hx).2⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext (comm_spT0 a (spE_le_spT0 ha) b (spE_le_spT0 hb))
  have hcardE : Nat.card (centerOf (T : Subgroup Y)) = 3 ^ 2 := by
    rw [S.center_T, Subgroup.card_map_of_injective (emb_injective e'), card_spE]
    norm_num
  have hQN : Subgroup.normalizer (centerOf (T : Subgroup Y) : Set Y) ≤
      GLBWeakCore 3 (T : Subgroup Y) := by
    refine normalizer_le_weakCore 3 inf_le_left ?_ ?_
    · rw [S.center_T]
      exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEel (emb e')) (k := 2)
        (by rw [← S.center_T]; exact hcardE)
    · refine h3.trans (pRank_mono 3 Nat.prime_three ?_)
      intro x hx
      refine Subgroup.mem_sup_right ⟨hx, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hq.2 x hx).symm
  have hNE : Subgroup.normalizer ((spE.map (emb e') : Subgroup Y) : Set Y) ≤ Y₀ := by
    rw [← S.center_T]
    exact hQN.trans hW
  obtain ⟨θ, hθT, -, hcl⟩ := classify_comap hcardS hsimple hNE hY₀
  have hdich : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
      W = ⊥ ∨ centerOf (T : Subgroup Y) ≤ W := fun W hWY hn => by
    rw [S.center_T]
    exact S.normal_dichotomy hC hθT hNE hcl hWY hn
  refine ⟨⟨?_, hdich, ?_, ?_⟩, ?_⟩
  · intro W hWY hn hcop
    rcases hdich W hWY hn with h | h
    · exact h
    · exfalso
      have h9 : 3 ^ 2 ∣ Nat.card W := by
        have := Subgroup.card_dvd_of_le h
        rwa [hcardE] at this
      have h3W : 3 ∣ Nat.card W := dvd_trans (by norm_num) h9
      have := Nat.Coprime.eq_one_of_dvd hcop h3W
      omega
  · rintro g ⟨-, hg⟩
    refine S.cent_E_le hC fun z hz => ?_
    have hz' : z ∈ centerOf (T : Subgroup Y) := by
      rw [S.center_T]
      exact hz
    exact (Subgroup.mem_centralizer_iff.1 hg z hz').symm
  · intro h
    rw [h, Subgroup.card_bot] at hcardE
    omega
  · rw [S.center_T]
    rintro _ ⟨s, -, rfl⟩
    exact emb_mem e' s

end CFSG.AGLEmbedding
