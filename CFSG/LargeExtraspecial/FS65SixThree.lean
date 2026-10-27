module

public import CFSG.LargeExtraspecial.FS65Bar
public import CFSG.LargeExtraspecial.FS65J2
public import CFSG.LargeExtraspecial.AS35CS63J2E
public import CFSG.Timmesfeld.CorollaryBMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld

namespace S14

@[expose] def SmithSixThreeGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), 3 ≤ S.width →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
      ∀ h t : G, h * S.z * h⁻¹ ∈ S.M → h * S.z * h⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa h →
        t ≠ 1 → S.ZInOTwo t

theorem smithSixThreeInput_of_gen (h : SmithSixThreeGenInput) : SmithSixThreeInput :=
  fun G _ _ _ S hn hW => h G S hn hW

theorem smithSixThreeGenInput_of (h55 : S63.Smith55Input) (hL3 : S63.AutL32Input)
    (hA6 : S63.AutA6Input) (h58 : S63.Smith58Input) (h59 : S63.Smith59Input)
    (hJc : S63.J2CentInput) (hJ : S63.J2SchurInput) : SmithSixThreeGenInput := by
  have h57 := S63.smith57Input_of hL3 hA6
  have hJ2in := S63.smithJ2Input_of hJc
  intro G _ _ S hn hW h t hhM hhne htQ hta ht1
  have hW' : S63.WeakCl S := hW
  set P₀ : S63.Pair S := ⟨h, t, hW', hhM, hhne, htQ, hta, ht1⟩ with hP₀
  set K : S63.Six S := ⟨t, hW', htQ, P₀.t_mul_t, ht1, P₀.t_ne_z⟩ with hK
  have hτ := K.exists_conjCent_ne_gen hn hhM hhne hta
  have hSH := K.smithHyp_gen hn hτ
  have hstar : S63.StarHyp K.zeta :=
    ⟨K.zeta_mul_zeta, fun a ha b hb => K.commutator_conjCent_gen hn ha hb, fun τ hτc hne => by
      obtain ⟨f, -, hf1, hf2⟩ := K.exists_fusion_gen hn hτc hne
      exact ⟨_, hf1, hf2⟩⟩
  have hSC : S63.SmithConf K.zeta K.Fbar := ⟨hSH, K.setup_gen hn, hstar, fun τ hτc hne => by
      obtain ⟨f, hfQ, -, hf⟩ := K.exists_fusion_gen hn hτc hne
      exact ⟨_, K.mem_Fbar_of hfQ, hf⟩, hτ⟩
  rcases CorB.main (K.setup_gen hn) with ⟨N, hNU, hNn, hNodd, hU⟩ | h2 | ⟨-, hB⟩ | ⟨hH, hO⟩
  · obtain ⟨τ, hτc, hτne⟩ := hτ
    exact (S63.false_of_oddCore K.zeta_mul_zeta hτc hτne hNU hNn hNodd hU).elim
  · exact K.zInOTwo_of_elemAb h2
  · exact (h55 _ _ _ hSC hB).elim
  · exfalso
    have hζ := S63.not_mem_ZU_of_hyp hH
    have hroot : ∀ f : ℕ, 2 ≤ f →
        ∀ d ∈ QuotientGroup.mk' (center ↥(normalClosure ({K.zeta} : Set (S63.Cbar K.t)))) ''
          CorB.clsIn K.zeta,
        Nat.card (rootGroup (QuotientGroup.mk' (center ↥(normalClosure
          ({K.zeta} : Set (S63.Cbar K.t)))) '' CorB.clsIn K.zeta) d) = 2 ^ f → False := by
      intro f hf d hd hcard
      obtain ⟨e, he, hne⟩ := S63.exists_rootSet_ne hH.root.1 hd hf hcard
      exact hstar.false_of_rootSet hζ rfl hH hd he hne
    rcases hO with ⟨f, hf, ⟨d, hd, hcard⟩, hL3⟩ | ⟨f, hf, ⟨d, hd, hcard⟩, -⟩ |
      ⟨f, hf, ⟨d, hd, hcard⟩, hD4⟩ | hU3 | hA6 | hJ2
    · rcases Nat.lt_or_ge f 2 with hf2 | hf2
      · obtain rfl : f = 1 := by omega
        exact (h57 _ _ _ hSC).1 hL3
      · exact hroot f hf2 d hd hcard
    · exact hroot f hf d hd hcard
    · rcases Nat.lt_or_ge f 2 with hf2 | hf2
      · obtain rfl : f = 1 := by omega
        exact h58 _ _ _ hSC hD4
      · exact hroot f hf2 d hd hcard
    · exact h59 _ _ _ hSC hU3
    · exact (h57 _ _ _ hSC).2 hA6
    · obtain ⟨hFU, hZ⟩ := hJ2in _ _ _ hSC hJ2
      exact K.false_of_J2_gen hn hJ hhM hhne hta hJ2 hFU hZ

end S14

end CFSG.LargeExtraspecial
