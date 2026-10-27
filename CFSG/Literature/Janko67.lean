module

public import CFSG.Literature.Janko67NotTwoNormal
public import CFSG.Literature.Janko67Fusion
public import CFSG.Literature.Janko67Simple
public import CFSG.LargeExtraspecial.AS62F431b
public import CFSG.LargeExtraspecial.AS35IMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux
public import CFSG.RankThree.GF2n.Parrott.FusionE16Hayashi

public section

namespace CFSG.Literature.Janko67

open CFSG CFSG.RankThree.GF2n.Parrott CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial

theorem janko_psp43 :
    ∀ (X : Type) [Group X], CFSG.Blueprint.LieModel X .PSp 2 3 1 → ∀ x : X,
      orderOf x = 2 →
      (∃ S : Sylow 2 X, x ∈ (S : Subgroup X) ∧ ∀ s ∈ (S : Subgroup X), x * s = s * x) →
      ∀ (G : Type) [Group G] [Finite G], (∀ N : Subgroup G, N.index ≠ 2) →
        ∀ j : G, orderOf j = 2 →
          Nonempty (Subgroup.centralizer ({j} : Set G) ≃* Subgroup.centralizer ({x} : Set X)) →
            CFSG.Blueprint.LieModel G .PSp 2 3 1 := by
  intro X _ hX x hx hxS G _ _ hidx j hj ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, f, hSz, hf⟩ := exists_setting_mulEquiv hX hx hxS hj e
  subst hSz
  have hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z :=
    S.weaklyClosed_QG_of_equiv_lieModel hX hx hxS e
  obtain ⟨g, hgM, hne⟩ := exists_conj_mem_M_ne hidx S f hf
  obtain ⟨H, hH⟩ := exists_isHStar S f hf hW hgM hne
  have hc : AS62.ConfHyp S H := ⟨S14.aschbacherTwoTwoStmt_of, width_eq_two S f, hW, hH⟩
  have hsG : IsSimpleGroup G := isSimpleGroup S f hf hc
  have hztop : S.zGen = ⊤ := by
    have hn : S.zGen.Normal := S.zGen_normal
    rcases hn.eq_bot_or_eq_top with h | h
    · exact absurd (h ▸ Subgroup.subset_closure (IsConj.refl S.z) : S.z ∈ (⊥ : Subgroup G))
        (by rw [Subgroup.mem_bot]; exact S.z_ne_one)
    · exact h
  have htop : S.zGen ⊔ S.QG = ⊤ := by rw [hztop, top_sup_eq]
  have hsimp : IsSimpleGroup S.zGen := by
    rw [hztop]
    exact Subgroup.topEquiv.isSimpleGroup
  rcases hc.lieModel htop hsimp (card_Mbar_eq S f) with h | h
  · exact CFSG.GH74.Exceptional.lieModel_PSp_two_three_of_lieModel_PSU_four_two h
  · exfalso
    obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
    have h128 : 2 ^ 7 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card
      (by rw [CFSG.OddStandard.SmallF3.Omega.ff_card_model_psl4 h]; norm_num)
    rw [card_sylow_two S f hf P] at h128
    norm_num at h128

end CFSG.Literature.Janko67
