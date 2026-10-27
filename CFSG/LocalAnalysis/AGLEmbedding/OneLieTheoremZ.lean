module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePlusCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorus

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section ZOne

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.false_of_unique (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hZ : D1OneLieResidue)
    (hd : D1OneLieData p P M H R Rbar K)
    (huniq : D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) : False := by
  have huniq' := huniq.toUniqueOver hd.cfg.ext.isPGroup
  have h3 := hd.toPhaseThree hK
  obtain ⟨T₁, hT₁, hF⟩ := hd.oneLieFacts hK
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨hWp, hWR, hWn, hWnC, hWiff⟩ := hd.d1MapPCore_facts hK h84 hD2
  have hV := hWiff.mp hY
  obtain ⟨hDM, hMD, hQD, -⟩ := pCoreCentralizerPreimage_facts p M
  have hNJ := hd.commutator_nclIn_le hK h84 hD2 hY
  by_cases hU : IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
  · exact hZ.2.2 G p P M H R Rbar K hd huniq' hY hU.1 hU.2
  have hNV : K ⊓ Subgroup.normalizer (((T₁ : Subgroup K).map K.subtype : Subgroup _) :
      Set (H ⧸ primeComplementCore (G := H) p)) ≤ Subgroup.normalizer ((d1MapPCore p M H ⊓
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hT₁]
    exact (le_inf hWn inf_le_right).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcent : Subgroup.centralizer ((d1MapPCore p M H ⊓
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rcases centralizer_le_sup_of_oneLieFacts hd.center T₁ hF (hT₁ ▸ inf_le_right) hV hNV with
      h | h
    · rwa [hT₁] at h
    · exact absurd ⟨h.2, by rw [h.1, hT₁]⟩ hU
  have hCW : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p))
      ≤ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) :=
    (Subgroup.centralizer_le inf_le_left).trans hcent
  by_cases hWC : d1MapPCore p M H ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥
  ·
    have hWK : d1MapPCore p M H ≤ K := (le_of_inf_centralizer_eq_bot hd.cfg.red.prime hd.center
      T₁ hT₁ hF hWp (le_sup_of_oneLieFacts hd.center T₁ hT₁ hF hWp hWR hWn) hWn hWC).trans
        inf_le_right
    obtain ⟨hNP, hNPJ⟩ := hd.d1PlusCore_le_and_commutator hK h84 hD2 hY hWK
    obtain ⟨hNPK, hHNP, -⟩ := hd.d1PlusCore_facts
    by_cases hW2 : ∃ W₂ : Subgroup (H ⧸ primeComplementCore (G := H) p),
        W₂ ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ∧
        IsPGroup 2 W₂ ∧ ¬ 2 ∣ (W₂.subgroupOf (Subgroup.centralizer
          (K : Set (H ⧸ primeComplementCore (G := H) p)))).index ∧
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
          Subgroup.normalizer (W₂ : Set (H ⧸ primeComplementCore (G := H) p))
    · obtain ⟨W₂, hW₂C, hW₂2, hW₂idx, hRW₂⟩ := hW2
      obtain ⟨T, hTN, hT2, hTidx, hRT, hST⟩ :=
        hd.exists_sylowTwo_d1PlusCore hW₂C hW₂2 hW₂idx hRW₂
      exact h3.false_of_normal_of_unique_of (hNPK.trans inf_le_left) hHNP hTN hT2 hTidx hRT hST
        hDM hMD hQD hNP (hd.inf_le_sup_d1PlusCore hK hCW) hNPJ huniq' hCGT hD2
    · have hno : ∀ W₂ : Subgroup (H ⧸ primeComplementCore (G := H) p),
          W₂ ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) →
          IsPGroup 2 W₂ → ¬ 2 ∣ (W₂.subgroupOf (Subgroup.centralizer
            (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
          ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
            Subgroup.normalizer (W₂ : Set (H ⧸ primeComplementCore (G := H) p)) :=
        fun W₂ h1 h2 h3 h4 => hW2 ⟨W₂, h1, h2, h3, h4⟩
      by_cases hI : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
          L = K
      · exact hZ.1 G p P M H R Rbar K hd huniq hY hI hWK hU hno
      · push Not at hI
        exact hZ.2.1 G p P M H R Rbar K hd huniq hY hI hWK hU hno
  ·
    have hCR := hd.cfg.red.centralizer_le_of_inf_ne_bot hd.comp hd.center hd.noncyclic hd.z hWp
      hWnC hWC hCW
    exact h3.false_of_normal_of_unique hDM hMD hQD
      (h3.glbPrimeCore_le_pCoreCentralizerPreimage h84 hD2) (hd.inf_le_sup_glbPrimeCore hK hCR) hNJ
      huniq' hCGT hD2

end ZOne

end CFSG.AGLEmbedding
