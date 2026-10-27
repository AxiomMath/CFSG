module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatConv
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatLeaf
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTables
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatU45
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9D
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9X1
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9YA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9YB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9YO
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9B

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

section Exotic

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X} {N₁ : Subgroup X}

theorem Setting.t2_false (hF : FiveCat.FivePumpUpInput)
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hs : Setting t J n e E D M) (hn : n = 9) (hCA : ClaimAHolds J n e E)
    (hd : Data t J n e E D M e₀ F DF r) (hP : PumpData M e₀ r N₁) (hfix : conjBy N₁ e₀ = N₁)
    (hexo : ∀ m : ℕ, Odd m → IsEmpty (↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m)))
    (hB : ¬ fixB M t e₀ r ≤ N₁) : False := by
  subst hn
  have he₀H : centralizer ({e₀} : Set X) ≤ Hn E :=
    hCA E hs.sig.le hs.sig.klein D hs.sig.card hs.sig.supp e₀ hd.e₀E hd.e₀1
  obtain ⟨⟨χ5⟩, ⟨hArle, hArpc⟩, -⟩ := pump_holds X t J 9 e E D M hs e₀ F DF r hd he₀H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀sq : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein hs.sig.klein).2 e₀ hd.e₀E
  have he₀2 : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀sq) hd.e₀1
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({r} : Set X)) :=
    hs.isKGroupCat_centralizer hd.r1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  have hAN : fixA M e₀ r ≤ N₁ := by
    have h := hP.cover
    rwa [hfix, sup_idem] at h
  have hnt : fixA M e₀ r ⊔ core N₁ ≠ N₁ := by
    intro h
    obtain ⟨e5⟩ := FiveCat.literal_of_stable hP.le hP.pc hAN χ5 h
    exact (hexo 5 ⟨2, by norm_num⟩).false e5
  have huniq : ∀ T' : Subgroup X, T' ≤ N₁ → T' ≤ centralizer ({e₀} : Set X) →
      IsPComponent 2 (T'.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))) →
      T' = fixA M e₀ r := fun T' hTN hTC hTpc =>
    eq_fixA_of_not_fixB_le hs hd he₀H hB hTN (le_inf (hTN.trans hP.le) hTC) hTpc
  rcases five_pump_type_in hF hK he₀r he₀2 hP.le hP.pc hfix hAN (hArle.trans inf_le_right) hArpc χ5
    hnt huniq with ⟨m, hmo, hm7, ⟨θ⟩⟩ | hna
  · exact (hexo m hmo).false θ
  · obtain ⟨G, hG, φ, hφ, hker⟩ := hs.exists_a9_action rfl hd he₀H hP hfix
    have hq : IsQuasisimple (↥N₁ ⧸ pPrimeCore 2 ↥N₁) :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 N₁ _ hP.le).mp hP.pc).2.2
    have hsec := a9_section_of_action hS hq hna.catalog hG φ hφ hker
    have hd9 : 181440 ∣ Nat.card (↥N₁ ⧸ Open.fusionZStar ↥N₁) := by
      have h := hsec.card_dvd
      rwa [card_alt_nine] at h
    exact FiveCat.FivePumpNonAlt.not_dvd_a9 hna hd9

theorem Setting.t3_false (hF : FiveCat.FiveTwoLayerInput)
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : FiveCat.U45NoA9Section)
    (hs : Setting t J n e E D M) (hn : n = 9) (hCA : ClaimAHolds J n e E)
    (hd : Data t J n e E D M e₀ F DF r) (hP : PumpData M e₀ r N₁) (hfix : conjBy N₁ e₀ = N₁)
    (hB : fixB M t e₀ r ≤ N₁) : False := by
  have he₀H : centralizer ({e₀} : Set X) ≤ Hn E :=
    hCA E hs.sig.le hs.sig.klein D hs.sig.card hs.sig.supp e₀ hd.e₀E hd.e₀1
  obtain ⟨eB⟩ := hs.fixB_type hn hd he₀H
  have hBpc := hs.fixB_isPComponent hn hd he₀H
  have hne := hs.fixB_ne_fixA hn hd he₀H
  subst hn
  obtain ⟨⟨χ5⟩, ⟨hArle, hArpc⟩, -⟩ := pump_holds X t J 9 e E D M hs e₀ F DF r hd he₀H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀sq : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein hs.sig.klein).2 e₀ hd.e₀E
  have he₀2 : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀sq) hd.e₀1
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({r} : Set X)) :=
    hs.isKGroupCat_centralizer hd.r1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  have hAN : fixA M e₀ r ≤ N₁ := by
    have h := hP.cover
    rwa [hfix, sup_idem] at h
  have huniq : ∀ T' : Subgroup X, T' ≤ N₁ → T' ≤ centralizer ({e₀} : Set X) →
      IsPComponent 2 (T'.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))) →
      T' = fixA M e₀ r ∨ T' = fixB M t e₀ r := fun T' hTN hTC hTpc =>
    eq_fixA_or_eq_fixB hs hd he₀H (le_inf (hTN.trans hP.le) hTC) hTpc
  have hout := five_two_layer_type_in hF hK he₀r he₀2 hP.le hP.pc hfix hne hAN hB
    (hArle.trans inf_le_right) ((hs.fixB_le hd).trans inf_le_right) hArpc hBpc χ5 eB huniq
  obtain ⟨G, hG, φ, hφ, hker⟩ := hs.exists_a9_action rfl hd he₀H hP hfix
  have hq : IsQuasisimple (↥N₁ ⧸ pPrimeCore 2 ↥N₁) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 N₁ _ hP.le).mp hP.pc).2.2
  have hsec := a9_section_of_action hS hq hout.catalog hG φ hφ hker
  rcases FiveCat.FiveTwoLayerOutcome.table hout with hU45 | hnd
  · exact hU _ hU45 hsec
  · have hd9 : 181440 ∣ Nat.card (↥N₁ ⧸ Open.fusionZStar ↥N₁) := by
      have h := hsec.card_dvd
      rwa [card_alt_nine] at h
    exact hnd hd9

end Exotic

theorem ys07_of_inputs (hF : FiveCat.FivePumpUpInput)
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    SwapMemberResidueNineExoticT2 := by
  intro X _ _ _ t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow hCA hex
  obtain ⟨e₀, F, DF, r, N₁, hd, hP, hfix, hexo, hB⟩ := hex
  exfalso
  exact Setting.t2_false hF hS ⟨S, hCH, hMH, hMpc, hne, hJM, hMalt, hsmall, hnarrow⟩ hn hCA hd hP
    hfix hexo hB

theorem ys08_of_inputs (hF : FiveCat.FiveTwoLayerInput)
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : FiveCat.U45NoA9Section) : SwapMemberResidueNineExoticT3 := by
  intro X _ _ _ t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow hCA hex
  obtain ⟨e₀, F, DF, r, N₁, hd, hP, hfix, -, hB⟩ := hex
  exfalso
  exact Setting.t3_false hF hS hU ⟨S, hCH, hMH, hMpc, hne, hJM, hMalt, hsmall, hnarrow⟩ hn hCA hd
    hP hfix hB

section ClosedT2


theorem ys07_closed : SwapMemberResidueNineExoticT2 :=
  ys07_of_inputs FiveCat.fivePumpUpInput_holds RankThree.PartOne.SPOR.schreierFor_catalog

end ClosedT2

section ClosedT3


theorem ys08_closed : SwapMemberResidueNineExoticT3 :=
  ys08_of_inputs FiveCat.fiveTwoLayerInput_holds RankThree.PartOne.SPOR.schreierFor_catalog
    u45NoA9Section_holds

end ClosedT3

end CFSG.ComponentClassification.SolMax.SwapP2
