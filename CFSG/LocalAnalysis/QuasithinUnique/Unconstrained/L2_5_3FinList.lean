module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRankProof

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Orbits

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem outSolvable_of_isComponentIn_list
    (hsch : Vol2Native.SchreierFactListCat)
    (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z) {K' : Subgroup G}
    (hK' : IsComponentIn K' H) : OutSolvable ↥K' :=
  hsch ↥K' (BenderBranch.isQuasisimple_of_isComponentIn hK')
    (Ch1.sqtkSimpleList_component hs.setting.qtke.1 ht.gamma0.isGamma.1 hK')

theorem lemma253BenderOrbit_list
    (hsch : Vol2Native.SchreierFactListCat) :
    Lemma253BenderOrbit := by
  intro G _ _ T M H S z hs ht K hK hKB L hL
  refine isComponentIn_of_orbit (D := conjJoin H K) (𝒦 := conjFamily H K)
    (le_normalizer_conjJoin H K) (benderRadical_le_conjJoin S H K)
    (isPGroup_benderRadical ht.sylow.isPGroup H K) (benderRadical_le hK.1) conjFamily_gen ?_ hL
  intro K' hK'
  have hKc : IsComponentIn K' H := mem_conjFamily_isComponentIn hK hK'
  obtain ⟨g, rfl⟩ := hK'
  have hsyl : IsSylowTwoOf (S ⊓ K.map (MulAut.conj (g : G)).toMonoidHom)
      (K.map (MulAut.conj (g : G)).toMonoidHom) :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal ht.sylow hKc.1 hKc.2.2
  refine ⟨hKc, S ⊓ K.map (MulAut.conj (g : G)).toMonoidHom, ?_, inf_le_right, ?_,
    isSolvable_inf_centralizer_of_isSylowTwoOf hsyl,
    outSolvable_of_isComponentIn_list hsch hs ht hKc⟩
  · exact le_iSup (fun g : ↥H => S ⊓ K.map (MulAut.conj (g : G)).toMonoidHom) g
  · by_contra hcon
    push Not at hcon
    exact Unc25G2.false_of_isSylowTwoOf_le_centralizer
      (BenderBranch.isQuasisimple_of_isComponentIn hKc) hsyl fun q hq =>
        Subgroup.mem_centralizer_iff.mpr fun k hk => (hcon q hq k hk).symm

theorem lemma253ListOrbit_list
    (h252 : Lemma252) (hsch : Vol2Native.SchreierFactListCat) :
    Lemma253ListOrbit := by
  intro G _ _ T M H S z hs ht K hK hKB L hL
  refine isComponentIn_of_orbit (D := conjJoin H K) (𝒦 := conjFamily H K)
    (le_normalizer_conjJoin H K) (radicalOf_le_conjJoin M H K) (isPGroup_radicalOf M H K)
    (radicalOf_le hK.1) conjFamily_gen ?_ hL
  intro K' hK'
  have hKc : IsComponentIn K' H := mem_conjFamily_isComponentIn hK hK'
  obtain ⟨g, rfl⟩ := hK'
  have hcl := h252 G T M H S z hs ht _ hKc
  obtain ⟨⟨q, hq, k, hk, hqk⟩, hsolv⟩ := list_member_data hs ht hKc hcl
  refine ⟨hKc, pCoreOf 2 (M ⊓ K.map (MulAut.conj (g : G)).toMonoidHom), ?_,
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_right,
    ⟨q, hq, k, hk, hqk⟩, hsolv, outSolvable_of_isComponentIn_list hsch hs ht hKc⟩
  have h := pCoreOf_inf_le_radicalOf (M := M) hKc
  unfold radicalOf at h ⊢
  rwa [conjJoin_map_conj g.2] at h

end Orbits

theorem lemma253Component_of_facts_list
    (h252 : Lemma252) (hBend : Lemma253Bender)
    (hsch : Vol2Native.SchreierFactListCat) (hF1 : RadicalNormalizerCharTwo)
    (hF2 : RadicalCharacteristic) : Lemma253Component :=
  lemma253_of_inputs h252 hBend (lemma253BenderOrbit_list hsch) (lemma253ListOrbit_list h252 hsch)
    (lemma253Core h252 hF1 hF2)

theorem lemma253Component_of_borel_list
    (h252 : Lemma252) (hBend : Lemma253Bender)
    (hsch : Vol2Native.SchreierFactListCat) (hBT : RankTwoBorelFacts) : Lemma253Component :=
  lemma253Component_of_facts_list h252 hBend hsch
    (radicalNormalizerCharTwo_of_facts h252 hBT a6RadicalCharTwo l33M11RadicalCharTwo
      (noCommutingConjugate_of_rank h252 oddRankTwoFacts))
    (radicalCharacteristic_of_q8 h252 (noCommutingConjugate_of_rank h252 oddRankTwoFacts)
      q8Characteristic)

end CFSG.QuasithinUnique.Fin253
