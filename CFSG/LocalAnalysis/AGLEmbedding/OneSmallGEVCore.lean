module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKCIn
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallP
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIdent
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVDefs
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Transport

variable {A B : Type} [Group A] [Group B]

omit [Group A] [Group B] in
theorem isAltTwoP_of_mulEquiv [Group A] [Group B] {p : ℕ} (e : A ≃* B) (h : IsAltTwoP p B) :
    IsAltTwoP p A := by
  obtain ⟨f⟩ := h
  exact ⟨e.trans f⟩

omit [Group A] [Group B] in
theorem isSmallUnitary_of_mulEquiv [Group A] [Group B] {p : ℕ} (e : A ≃* B)
    (h : IsSmallUnitary p B) : IsSmallUnitary p A := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.trans f⟩⟩

omit [Group A] [Group B] in
theorem isLinThreeFour_of_mulEquiv [Group A] [Group B] (e : A ≃* B) (h : IsLinThreeFour B) :
    IsLinThreeFour A := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.trans f⟩⟩

omit [Group A] [Group B] in
theorem isFi22_of_mulEquiv [Group A] [Group B] (e : A ≃* B) (h : IsFi22 B) : IsFi22 A := by
  obtain ⟨f⟩ := h
  exact ⟨e.trans f⟩

end Transport

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.not_twoCore_inf_le_of_le_sup (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hFi : ¬ (p = 5 ∧ IsFi22 K))
    (hOR : p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K) :
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) := by
  intro hQz
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut hOR)
  have hexpR := hd.pow_eq_one_of_d1LiftX_decomp hExp hz hdec
  obtain ⟨T₁, hT₁, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  rcases hShape K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small with h2 | ⟨-, hZ⟩
  · have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup _) = p ^ 2 := by
      rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, h2]
    exact hd.false_of_ab' hOrb hz hB0 hQz hdec hexpR hFi hcard
  · exact hd.false_of_na hz hB0 hQz hdec hexpR hT₁ hZ

section Core

variable (hSch : KFactCatalogSchreier) (hK1 : KFactOneLie) (hU : KFactUnitarySylowStructure)
  (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo) (h3 : D1CaseThree)

include hSch hK1 hU hβ hα h2 h3 in
theorem d1SmallGEVCore_of_normal (hGst : StmtSmallGuest) (hN : D1SmallGEVNormal)
    (hN3 : D1SmallGEVNormalThreeS) (hNF : D1SmallGEVNormalFi22)
    (hIb : D1SmallGEVIbNormal) (hIb3 : D1SmallGEVIbNormalThree) : D1SmallGEVCore := by
  intro G _ _ p P M H R Rbar K hd z hz hB0 hEv hIso hR hcomm hnot
  have hgp : ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) :=
    fun h => hGst G p P M H R Rbar K hd (Or.inl h)
  have hgF : ¬ (p = 5 ∧ IsFi22 K ∧ 3 ∈ GLBBetaFour G) :=
    fun h => hGst G p P M H R Rbar K hd (Or.inr h)
  have hV := hd.pCoreOf_two_glbPrimeCore_ne_bot hz
    (twoCore_inf_core_ne_bot_of_comm hd hcomm hnot)
  have hsm := D1OneSmallData.star_smallData_of_card hSch hK1 hU hβ hα h2 h3 hd hz hR hIso
  have hIsoT : ∀ {Ls' : Type} [Group Ls'], (Ls' ≃* K) → D1CzIso p z Ls' := fun eL KC hKC =>
    (hIso KC hKC).map fun f => f.trans eL.symm
  by_cases hex : ∃ Hs : Subgroup G, GLBIsMaxTwoLocal Hs ∧
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs ∧
      ∃ hzHs : z ∈ Hs, (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal
  · obtain ⟨Hs, hHs, hVHs, hzHs, hA⟩ := hex
    obtain ⟨hCHs, Rbars, Ks, hds0, -⟩ :=
      D1OneSmallData.exists_compI_star hSch hK1 hU hβ hα h2 h3 hd hz hR hHs hVHs
    obtain ⟨Ls, hds, hzs, hIas, ⟨eL⟩, hcore⟩ :=
      hd.smallDataIa_of_normal_zpowers hz hIso hCHs hds0.cfg hA
    have hRs : Nat.card R ≤ p * Nat.card ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p))
        ⊓ Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) := by
      rw [card_inf_eq_of_mulEquiv hd hds eL]
      exact hR
    by_cases h3s : p = 3 ∧ (IsAltTwoP 3 K ∨ IsSmallUnitary 3 K ∨ IsLinThreeFour K)
    · obtain ⟨hp3, hK⟩ := h3s
      have hKs : IsAltTwoP 3 Ls ∨ IsSmallUnitary 3 Ls ∨ IsLinThreeFour Ls := by
        rcases hK with h | h | h
        · exact Or.inl (isAltTwoP_of_mulEquiv eL h)
        · exact Or.inr (Or.inl (isSmallUnitary_of_mulEquiv eL h))
        · exact Or.inr (Or.inr (isLinThreeFour_of_mulEquiv eL h))
      exact hN3 G p P M Hs R Rbars Ls hds z hzs hIas hB0 hEv (hIsoT eL) hp3 hKs
        (D1OneSmallData.not_outerR_of_card hds hzs hRs) hcomm hnot hVHs hCHs hcore (fun _ => hA)
    · by_cases hF : p = 5 ∧ IsFi22 K
      · exact hNF G p P M Hs R Rbars Ls hds z hzs hIas hB0 hEv (hIsoT eL) hF.1
          (isFi22_of_mulEquiv eL hF.2) (fun h3m => hgF ⟨hF.1, hF.2, h3m⟩) hcomm hnot hVHs hCHs
          hcore (fun _ => hA)
      · exact hN G p P M Hs R Rbars Ls hds z hzs hIas hB0 hEv (hIsoT eL)
          (fun h => h3s ⟨h.1, Or.inl (isAltTwoP_of_mulEquiv eL.symm h.2)⟩)
          (fun h => h3s ⟨h.1, Or.inr (Or.inl (isSmallUnitary_of_mulEquiv eL.symm h.2))⟩)
          (fun h => h3s ⟨h.1, Or.inr (Or.inr (isLinThreeFour_of_mulEquiv eL.symm h.2))⟩)
          (fun h => hF ⟨h.1, isFi22_of_mulEquiv eL.symm h.2⟩)
          (fun h => hgp ⟨isAltTwoP_of_mulEquiv eL.symm h.1, h.2⟩)
          hcomm hnot hVHs hCHs hcore (fun _ => hA)
  have hall : ∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
      ∀ hzHs : z ∈ Hs, ¬ (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal :=
    fun Hs' hHs' hVHs' hzHs' hA' => hex ⟨Hs', hHs', hVHs', hzHs', hA'⟩
  obtain ⟨Hs, hHs, hVHs, hCHs, -, -⟩ := hd.exists_maxTwoLocal_normalizer_le hz hV
  obtain ⟨Rbars, Ls, hds, hzs, ⟨eL⟩⟩ := hsm Hs hHs hVHs
  have hRs : Nat.card R ≤ p * Nat.card ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p))
      ⊓ Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) := by
    rw [card_inf_eq_of_mulEquiv hd hds eL]
    exact hR
  have hnIa : ¬ D1SmallIa p Hs Ls := fun hIas => hall Hs hHs hVHs (mem_of_centralizer_le hCHs)
    (D1OneSmallData.zpowers_normal_of_ia_of_card hds hzs hRs hIas (mem_of_centralizer_le hCHs))
  have hsmL : D1GEVStarSmall p P M R z Ls := fun Hs' hHs' hVHs' => by
    obtain ⟨Rb', L', hd', hz', ⟨e'⟩⟩ := hsm Hs' hHs' hVHs'
    exact ⟨Rb', L', hd', hz', ⟨e'.trans eL.symm⟩⟩
  by_cases h3s : p = 3 ∧ (IsAltTwoP 3 K ∨ IsSmallUnitary 3 K ∨ IsLinThreeFour K)
  · obtain ⟨hp3, hK⟩ := h3s
    have hKs : IsAltTwoP 3 Ls ∨ IsSmallUnitary 3 Ls ∨ IsLinThreeFour Ls := by
      rcases hK with h | h | h
      · exact Or.inl (isAltTwoP_of_mulEquiv eL h)
      · exact Or.inr (Or.inl (isSmallUnitary_of_mulEquiv eL h))
      · exact Or.inr (Or.inr (isLinThreeFour_of_mulEquiv eL h))
    exact hIb3 G p P M Hs R Rbars Ls hds z hzs hnIa hB0 hEv (hIsoT eL) hp3 hKs
      (D1OneSmallData.not_outerR_of_card hds hzs hRs) hcomm hnot hHs hVHs hsmL hall
  · exact hIb G p P M Hs R Rbars Ls hds z hzs hnIa hB0 hEv (hIsoT eL)
      (fun h => h3s ⟨h.1, Or.inl (isAltTwoP_of_mulEquiv eL.symm h.2)⟩)
      (fun h => h3s ⟨h.1, Or.inr (Or.inl (isSmallUnitary_of_mulEquiv eL.symm h.2))⟩)
      (fun h => h3s ⟨h.1, Or.inr (Or.inr (isLinThreeFour_of_mulEquiv eL.symm h.2))⟩)
      (fun h => hgp ⟨isAltTwoP_of_mulEquiv eL.symm h.1, h.2⟩) hcomm hnot hHs hVHs hsmL hall

end Core

theorem d1SmallEvenA6U33_of_core (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hO : KFactSmallThreeOrders) (hC : D1SmallGEVCore) : D1SmallEvenA6U33 := by
  intro G _ _ p P M H R Rbar K hd _ z hz hp3 hAU hB0 hEv hIso _
  have hL : ¬ (p = 3 ∧ IsLinThreeFour K) := fun ⟨_, hL⟩ =>
    hAU.elim (fun hA => not_l34_of_a6 hO hA hL) (fun hU => (not_l34_and_not_a6_of_u33 hO hU).1 hL)
  obtain ⟨hcardR, -⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  have hFi : ¬ (p = 5 ∧ IsFi22 K) := fun h => by omega
  have hcomm := hd.twoCore_comm_mem_core hNo2 hz hB0 hIso hFi hcardR
  have hnot := D1OneSmallData.not_twoCore_inf_le_of_le_sup hOut hExp hShape hOrb hd hz hB0 hFi
    (fun h3' h => absurd ⟨h3', h⟩ hL)
  exact hC G p P M H R Rbar K hd z hz hB0 hEv hIso hcardR hcomm hnot

theorem d1SmallL34LeftIso_of_core (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hC : D1SmallGEVCore) : D1SmallL34LeftIso := by
  intro G _ _ p P M H R Rbar K hd _ z hz hp3 hL _ hOR _ hIso hB0 hEv
  have hOR' : p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K := fun _ _ => hOR
  obtain ⟨hcardR, -⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut hOR')
  have hFi : ¬ (p = 5 ∧ IsFi22 K) := fun h => by omega
  have hcomm := hd.twoCore_comm_mem_core hNo2 hz hB0 hIso hFi hcardR
  have hnot := D1OneSmallData.not_twoCore_inf_le_of_le_sup hOut hExp hShape hOrb hd hz hB0 hFi hOR'
  exact hC G p P M H R Rbar K hd z hz hB0 hEv hIso hcardR hcomm hnot

end CFSG.AGLEmbedding
