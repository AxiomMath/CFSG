module

public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
import CFSG.CGT.PushingUpLit.Glue.CStarBridge

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace CFSG.AGLEmbedding

namespace AscEightSix

open AscEightFive CFSG.CGT.PushingUpLit.BHS

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem cStarIn_le_cgsIn {H : Subgroup G} (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) :
    cStarIn H S ≤ cgsIn H S := by
  refine sup_le ?_ ?_
  · have h := LocalCGT.centralizer_inf_le_cgsIn (X := H) hS hS1
    rw [CFSG.CGT.PushingUpLit.Glue.omegaOneCenterIn_eq, inf_comm] at h
    exact h
  · refine iSup_le fun B => iSup_le fun hBS => iSup_le fun hB => iSup_le fun hBc => ?_
    have hBS' : B ≤ CFSG.RankThree.PartOne.pushingUpS S := by
      rw [CFSG.CGT.PushingUpLit.Glue.pushingUpS_eq_baum]; exact hBS
    have hBc' : (B.subgroupOf (CFSG.RankThree.PartOne.pushingUpS S)).Characteristic := by
      rw [CFSG.CGT.PushingUpLit.Glue.pushingUpS_eq_baum]; exact hBc
    have h := LocalCGT.normalizer_inf_le_cgsIn (X := H) B hB hBS' hBc'
    rw [inf_comm] at h
    exact h

theorem cStarIn_le_normalizer (hyp : Asc81bHyp X S) {H : Subgroup G} (hHX : H ≤ X) :
    cStarIn H S ≤ H ⊓ Subgroup.normalizer (S : Set G) :=
  (cStarIn_le_cgsIn hyp.twoRadical.isPGroup hyp.twoRadical.2.1).trans
    (le_inf (cgsIn_le _ _) ((AscEightFour.cgsIn_mono hHX).trans (hyp.cgs.le.trans inf_le_right)))

theorem cStarIn_le_mGrp5 (hyp : Asc81bHyp X S) :
    cStarIn (hGrp5 X S L) S ≤ mGrp5 X S L :=
  (cStarIn_le_normalizer hyp hGrp5_le).trans le_sup_right

omit [Finite G] in
theorem isSubnormal_of_family {H : Subgroup G} {𝒢 : Set (Subgroup G)} (hle : ∀ E ∈ 𝒢, E ≤ H)
    (hinv : ∀ E ∈ 𝒢, ∀ g ∈ H, CFSG.Quasithin.A1b.conjSub g E ∈ 𝒢)
    (hcomm : ∀ E ∈ 𝒢, ∀ E' ∈ 𝒢, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x)
    {E : Subgroup G} (hE : E ∈ 𝒢) : CFSG.Open.IsSubnormal E H := by
  set N₀ : Subgroup G := ⨆ F ∈ 𝒢, F with hN₀
  have hEN : E ≤ N₀ := le_iSup₂_of_le E hE le_rfl
  have hNH : N₀ ≤ H := iSup₂_le hle
  have hNE : N₀ ≤ Subgroup.normalizer (E : Set G) := by
    refine iSup₂_le fun F hF => ?_
    by_cases hFE : F = E
    · rw [hFE]; exact Subgroup.le_normalizer
    · intro y hy
      exact Subgroup.centralizer_le_normalizer (E : Set G) (Subgroup.mem_centralizer_iff.mpr
        fun x hx => hcomm E hE F hF (Ne.symm hFE) x hx y hy)
  have hHN : H ≤ Subgroup.normalizer (N₀ : Set G) := by
    intro g hg
    have hle' : ∀ g ∈ H, N₀.map (MulAut.conj g).toMonoidHom ≤ N₀ := by
      intro g hg
      rw [hN₀, Subgroup.map_iSup]
      refine iSup_le fun F => ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun hF => le_iSup₂_of_le _ (hinv F hF g hg) le_rfl
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hle' g hg ⟨n, hn, rfl⟩
    · intro hn
      have := hle' g⁻¹ (H.inv_mem hg) ⟨_, hn, rfl⟩
      simpa [mul_assoc] using this
  exact CFSG.Open.IsSubnormal.step hEN
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hEN).mpr hNE)
    (CFSG.Open.IsSubnormal.step hNH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN) (CFSG.Open.IsSubnormal.refl H))

theorem exists_block_not_le_mGrp5 (hBHS : BHSLocalCStar) (hyp : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    ∃ E : Subgroup G, IsBTBlock (hGrp5 X S L) S E ∧
      CFSG.Open.IsSubnormal E (hGrp5 X S L) ∧ ¬ E ≤ mGrp5 X S L ∧
      (((∃ n : ℕ, 2 ≤ n ∧ CFSG.RankThree.PartOne.IsNaturalSLTwoModule ↥E n) ∧
          cStarIn (hGrp5 X S L) S ⊓ E =
            Subgroup.normalizer ((S ⊓ E : Subgroup G) : Set G) ⊓ E) ∨
        (∃ m : ℕ, 1 ≤ m ∧ CFSG.RankThree.PartOne.IsNaturalAltModule ↥E m ∧
          Nonempty ((((cStarIn (hGrp5 X S L) S ⊓ E).subgroupOf E).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥E))) ≃* alternatingGroup (Fin (2 * m))))) := by
  have hHX : hGrp5 X S L ≤ X := hGrp5_le
  have hSH : IsSylowTwoOf S (hGrp5 X S L) := isSylowTwoOf_hGrp5 hyp hL hsyl
  have hch : CharTwo (hGrp5 X S L) := charTwo_of_le hyp twoCore_le_hGrp5 hHX
  have hCM := cStarIn_le_mGrp5 (L := L) hyp
  have hne : cStarIn (hGrp5 X S L) S ≠ hGrp5 X S L := fun h =>
    not_hGrp5_le_mGrp5 hyp hL hsyl (h ▸ hCM)
  obtain ⟨𝒢, hB, hinv, hcomm, hgen, -, -, he⟩ :=
    hBHS G (hGrp5 X S L) S hch (LocalCGT.isSylowOf_of_isSylowTwoOf hSH) hne
  have hex : ∃ E ∈ 𝒢, ¬ E ≤ mGrp5 X S L := by
    by_contra hall
    push Not at hall
    apply not_hGrp5_le_mGrp5 hyp hL hsyl
    rw [← hgen]
    exact sup_le hCM (iSup₂_le fun E hE => hall E hE)
  obtain ⟨E, hE, hEM⟩ := hex
  exact ⟨E, hB E hE, isSubnormal_of_family (fun F hF => (hB F hF).le) hinv hcomm hE, hEM, he E hE⟩

alias eq_conj_of_short := AscEightFive.eq_conj_of_short

end AscEightSix

end CFSG.AGLEmbedding
