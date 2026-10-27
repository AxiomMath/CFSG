module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicBasic
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34HS
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34ON
public import CFSG.Sporadic.HeldB.OuterCentQS
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuterHN
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSuz
public import CFSG.Sporadic.SuzOddCore.CTIComponents

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.OmegaPilot (orderOf_eq_two_of_conj exists_component_centralizer_of_conj)
open CFSG.Sporadic.HeldB

section HS


theorem catSL2Hyp_false_HS {J : Type} [Group J] [Finite J] (e : J ≃* NativeSporadic.HS)
    {τ : MulAut J} {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨r, hr, ⟨φ⟩⟩ := SporadicRefine.hs_fixedSubgroup_rows e h.1
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := Sporadic.SmallOddCore.hs_involution_centralizers
  have hc : Nat.card (fixedSubgroup τ) = r.centOrder := by
    rw [Nat.card_congr φ.toEquiv, (hrows r hr).2.2.2.2.1]
  rcases QuasithinUnique.Id2519.SporHS.hsRows_cases hr with h1 | ⟨-, -, h1, -⟩ | ⟨-, h1⟩ | h1 <;>
    rw [h1] at hc
  · exact false_of_card_fixedSubgroup h hc (k := 9) (B := 13) (by norm_num) (by norm_num)
      (by decide)
  · exact false_of_card_fixedSubgroup h hc (k := 6) (B := 12) (by norm_num) (by norm_num)
      (by decide)
  · exact false_of_card_fixedSubgroup h hc (k := 7) (B := 16) (by norm_num) (by norm_num)
      (by decide)
  · exact false_of_card_fixedSubgroup h hc (k := 7) (B := 11) (by norm_num) (by norm_num)
      (by decide)

end HS

section He


theorem he_outer_fixedSubgroup_equiv {S : Type} [Group S] (e : S ≃* NativeSporadic.He)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Nonempty (fixedSubgroup σ ≃*
      ↥(heP ⊓ centralizer ({heAutU} : Set (Equiv.Perm (Fin 8330))))) := by
  set θ : S ≃* heP := e.trans heEquivP
  obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
    (MulAut.congr θ σ) (by rw [orderOf_congr, hσ]) (by rwa [congr_mem_range_conj_iff])
  obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
  exact ⟨((fixedSubgroupCongr θ σ).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
    (fixedSubgroupEquivOfConj x hg heAutU hxg)⟩

theorem card_quotient_center_of_isComponent_heOuter
    {L : Subgroup ↥(heP ⊓ centralizer ({heAutU} : Set (Equiv.Perm (Fin 8330))))}
    (hL : IsComponent L) : Nat.card (L ⧸ center L) = 2520 := by
  obtain ⟨hDcomm, hDq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  have hCC : ⁅(heP ⊓ centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))),
      heP ⊓ centralizer {heAutU}⁆ = heOuterD := by
    rw [← heOuterC_eq, ← hDcomm]
  have hDC : heOuterD ≤ heP ⊓ centralizer {heAutU} := by
    rw [← hCC]
    exact Subgroup.commutator_le_self _
  obtain ⟨D', hD'⟩ : ∃ D' : Subgroup ↥(heP ⊓ centralizer {heAutU} :
      Subgroup (Equiv.Perm (Fin 8330))), D' = heOuterD.subgroupOf _ := ⟨_, rfl⟩
  have eD : ↥D' ≃* ↥heOuterD := (MulEquiv.subgroupCongr hD').trans (subgroupOfEquivOfLe hDC)
  have hD'q : IsQuasisimple ↥D' :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr eD).mpr hDq
  obtain ⟨hLq, hLs⟩ := hL
  have : Group.IsPerfect L := hLq.1
  have hLD : L ≤ D' := by
    intro x hx
    have hx' : x ∈ ⁅L, L⁆ := by rw [Subgroup.commutator_eq_self]; exact hx
    have h1 : x ∈ commutator ↥(heP ⊓ centralizer {heAutU} :
        Subgroup (Equiv.Perm (Fin 8330))) := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top hx'
    have h2 : (x : Equiv.Perm (Fin 8330)) ∈ ⁅(heP ⊓ centralizer {heAutU} :
        Subgroup (Equiv.Perm (Fin 8330))), heP ⊓ centralizer {heAutU}⁆ := by
      rw [← Subgroup.map_subtype_commutator]
      exact ⟨x, h1, rfl⟩
    rw [hCC] at h2
    rw [hD']
    exact h2
  have hLs' : (L.subgroupOf D').IsSubnormal := hLs.comap D'.subtype
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hD'q hLs' with
    htop | hcen
  · have hLeq : L = D' := le_antisymm hLD fun x hx => by
      have : (⟨x, hx⟩ : D') ∈ L.subgroupOf D' := htop ▸ mem_top _
      exact this
    rw [TwistedE6Pilot.card_quotient_center_eq_of_mulEquiv
      ((MulEquiv.subgroupCongr hLeq).trans eD), card_heOuterD_quot]
  · exfalso
    have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hLq
    have hcomm : ∀ a b : L, a * b = b * a := fun a b => by
      have ha : (⟨a, hLD a.2⟩ : D') ∈ center ↥D' :=
        hcen (show (⟨a, hLD a.2⟩ : D') ∈ L.subgroupOf D' from a.2)
      have h := congrArg Subtype.val (mem_center_iff.mp ha ⟨b, hLD b.2⟩)
      exact Subtype.ext h.symm
    have hbot : commutator L = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [mem_centralizer_iff]
      intro b _
      exact hcomm b a
    obtain ⟨a, b, hab⟩ := exists_pair_ne L
    have htop' : commutator L = ⊤ := Group.IsPerfect.commutator_eq_top
    have ha : a = 1 := by
      have : a ∈ commutator L := htop' ▸ mem_top a
      rwa [hbot, mem_bot] at this
    have hb : b = 1 := by
      have : b ∈ commutator L := htop' ▸ mem_top b
      rwa [hbot, mem_bot] at this
    exact hab (ha.trans hb.symm)

theorem catSL2Hyp_false_He {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.He) {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, h2⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  by_cases hin : τ ∈ (MulAut.conj : J →* MulAut J).range
  · obtain ⟨s, rfl⟩ := hin
    exact SporadicRefine.he_inner_not_twoSmall e (orderOf_eq_two_of_conj hJ hna hτ)
      hD h2
  · obtain ⟨φ⟩ := he_outer_fixedSubgroup_equiv e hτ hin
    have h1 := card_quotient_center_of_isComponent_heOuter
      (LocalCores.isComponent_map_mulEquiv φ hD)
    rw [← TwistedE6Pilot.card_quotient_center_eq_of_mulEquiv
      (D.equivMapOfInjective φ.toMonoidHom φ.injective), card_of_lieModel_PSL_two_two hDm] at h1
    exact ordA_one_ne_of_check (B := 12) hn (by norm_num) (by decide) h1

end He

section Suz


theorem catSL2Hyp_false_Suz {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Suz) {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) : False := by
  have hn := two_le_of_catSL2Hyp h
  by_cases hin : τ ∈ (MulAut.conj : J →* MulAut J).range
  · obtain ⟨hτ, D, hD, hDm, -⟩ := h
    obtain ⟨u, rfl⟩ := hin
    obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
    have h1 := Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e u
      (orderOf_eq_two_of_conj hJ hna hτ) B hB
    rw [hcard, card_of_lieModel_PSL_two_two hDm] at h1
    exact ordA_one_ne_of_check (B := 15) hn (by norm_num) (by decide) h1
  · rcases SporadicRefine.suz_outer_card_fixedSubgroup e h.1 hin with hc | hc
    · exact false_of_card_fixedSubgroup h hc (k := 7) (B := 18) (by norm_num) (by norm_num)
        (by decide)
    · exact false_of_card_fixedSubgroup h hc (k := 8) (B := 21) (by norm_num) (by norm_num)
        (by decide)

end Suz

section HN


theorem catSL2Hyp_false_HN {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.HN) {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) : False := by
  have hn := two_le_of_catSL2Hyp h
  by_cases hin : τ ∈ (MulAut.conj : J →* MulAut J).range
  · obtain ⟨hτ, D, hD, hDm, -⟩ := h
    obtain ⟨u, rfl⟩ := hin
    obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
    have h1 := ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds J e u
      (orderOf_eq_two_of_conj hJ hna hτ) B hB
    rw [hcard, card_of_lieModel_PSL_two_two hDm] at h1
    exact ordA_one_ne_of_check (B := 26) hn (by norm_num) (by decide) h1
  · obtain ⟨φ⟩ := ComponentClassification.RestrictedStd.Spor.hnOuterFixInput J e τ h.1 hin
    have hfix : Nat.card (fixedSubgroup τ) = 3628800 := by
      have hfs : fixedSubgroup τ = Sporadic.Schreier.fixSub τ := by
        ext x
        exact Iff.rfl
      rw [Nat.card_congr (MulEquiv.subgroupCongr hfs).toEquiv, Nat.card_congr φ.toEquiv,
        Nat.card_perm, Nat.card_fin]
      rfl
    exact false_of_card_fixedSubgroup h hfix (k := 8) (B := 22) (by norm_num) (by norm_num)
      (by decide)

end HN

@[expose] def ONOuterSL2Input : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.ON) →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
      ∀ D : Subgroup (fixedSubgroup σ), IsComponent D → FixedCentralizerTwoSmall σ D →
        ¬ LieModel (D ⧸ center D) .PSL 2 2 2

section ON


theorem autTwoBound_ON {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.ON) {n : ℕ} (hn : 3 ≤ n) :
    AutTwoBound J n := by
  have h1 : Nat.card NativeSporadic.ON = 2 ^ 9 * 900030285 :=
    Sporadic.ON.card_ON.trans (by norm_num)
  have h2 : Nat.card (Outer NativeSporadic.ON) ≤ 4 :=
    Nat.le_of_dvd (by norm_num) Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1
  have h5 : Nat.card J ∣ 2 ^ 9 * 900030285 := by rw [Nat.card_congr e.toEquiv, h1]
  exact autTwoBound_of_card (center_eq_bot_of_simple_nonabelian hJ hna)
    (Nat.odd_iff.mpr (by norm_num)) h5 (Sporadic.Schreier.outer_card_le_of_equiv h2 e)
    (lt_two_mul_pow_four_of_le hn (by norm_num))

theorem catSL2Bound_ON (hON : ONOuterSL2Input) {J : Type} [Group J] [Finite J]
    (hJ : IsSimpleGroup J) (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.ON)
    {τ : MulAut J} {n : ℕ} (h : CatSL2Hyp J τ n) : AutTwoBound J n := by
  have hn := two_le_of_catSL2Hyp h
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    exfalso
    obtain ⟨hτ, D, hD, hDm, h2⟩ := h
    by_cases hin : τ ∈ (MulAut.conj : J →* MulAut J).range
    · obtain ⟨s, rfl⟩ := hin
      exact SporadicRefine.on_inner_not_twoSmall e (orderOf_eq_two_of_conj hJ hna hτ) hD h2
    · exact hON J ⟨e⟩ τ hτ hin D hD h2 hDm
  · exact autTwoBound_ON hJ hna e hn3

end ON

end CFSG.SeitzReduction.RankOne
