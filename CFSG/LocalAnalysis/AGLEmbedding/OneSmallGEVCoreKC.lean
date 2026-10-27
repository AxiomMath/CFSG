module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarIa
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKCIn
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVComponents
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M R : Subgroup G}

theorem D1CompI.smallData_of_centralized {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    {Ks : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hds : D1CompI p P M Hs R Rbars Ks) (hzR : z ∈ R) (hzp : orderOf z = p)
    (hzsC : d1StarElt p hCHs ∈ Subgroup.centralizer (Ks : Set _))
    (hsmall : Open.pRank p (⊤ : Subgroup (MulAut Ks)) ≤ 2) :
    D1OneSmallData p P M Hs R Rbars Ks ∧ D1SmallCZElt p Hs R Ks z := by
  have hp := hds.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set zs := d1StarElt p hCHs with hzs
  have hzsp : orderOf zs = p := orderOf_mk_of_coprime hp _ (primeComplementCore_coprime p)
    (by rw [← Subgroup.orderOf_coe]; exact hzp)
  have hzsL : zs ∉ Ks := by
    intro hmem
    have hcen : (⟨zs, hmem⟩ : Ks) ∈ Subgroup.center Ks := Subgroup.mem_center_iff.mpr fun l =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzsC) l l.2)
    rw [hds.center, Subgroup.mem_bot] at hcen
    have h1 : zs = 1 := congrArg Subtype.val hcen
    rw [h1, orderOf_one] at hzsp
    exact hp.one_lt.ne hzsp
  have hzsR : zs ∈ (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) := by
    rw [hds.cfg.rbar]
    exact ⟨⟨z, mem_of_centralizer_le hCHs⟩, hzR, rfl⟩
  exact ⟨⟨hds.cfg, hds.comp, hds.center, hds.noncyclic, ⟨zs, hzsR, hzsL, hzsp, hzsC⟩, hsmall⟩,
    ⟨hzR, hzp, mem_of_centralizer_le hCHs, hzsC⟩⟩

theorem d1SmallKCLeftOut_of_core (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hSch : KFactCatalogSchreier) (hRk : KFactSmallOfRankTwo) (hInvC : KFactSmallInvolveCard)
    (hK1 : KFactOneLie) (hU : KFactUnitarySylowStructure) (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hC : D1SmallGEVCore) : D1SmallKCLeftOut := by
  intro G _ _ p P M H R Rbar K hd _ z hz hnSP _ _ hLa hout hB0 hEv hcomm hnot
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hR, -⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 hLa
  have hV := hd.pCoreOf_two_glbPrimeCore_ne_bot hz
    (twoCore_inf_core_ne_bot_of_comm hd hcomm hnot)
  obtain ⟨Hs, hHs, hVHs, -, -, -⟩ := hd.exists_maxTwoLocal_normalizer_le hz hV
  obtain ⟨hCHs, Rbars, Ks, hds, hzsC⟩ :=
    D1OneSmallData.exists_compI_star hSch hK1 hU hβ hα h2 h3 hd hz hR hHs hVHs
  obtain ⟨KC, hKC, huniq, ⟨eL⟩⟩ :=
    D1OneSmallData.iso_czComponent_of_centralized hd hz hCHs hds.cfg hds.comp hzsC
  obtain ⟨-, T, Pbar, KC', -, -, -, hc⟩ := hd.exists_czReduced hz
  obtain rfl : KC' = KC := huniq KC' hc.comp
  obtain ⟨-, -, -, -, TC, -, -, -, hAut, hTC⟩ :=
    hd.czComponent_facts_of_not_mem hSch hRk hInvC hz hc hnSP (hout KC' hc.comp)
  have hsmall : Open.pRank p (⊤ : Subgroup (MulAut Ks)) ≤ 2 := by
    have h1 := pRank_map_of_injective p hp (MulAut.congr eL).toMonoidHom
      (MulAut.congr eL).injective (⊤ : Subgroup (MulAut Ks))
    rw [Subgroup.map_top_of_surjective _ (MulAut.congr eL).surjective] at h1
    rw [← h1]
    exact hAut
  obtain ⟨hds', hzs'⟩ := D1CompI.smallData_of_centralized hCHs hds hz.1 hz.2.1 hzsC hsmall
  have hIso : D1CzIso p z Ks := fun L hL => by
    obtain rfl := huniq L hL
    exact ⟨eL.symm⟩
  have hRs : Nat.card R ≤ p * Nat.card ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p))
      ⊓ Ks : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) := by
    obtain ⟨Ts, hTs, -⟩ := hds.exists_sylow
    rw [← hTs, Subgroup.card_map_of_injective Ks.subtype_injective, Sylow.card_eq_multiplicity,
      Nat.card_congr eL.toEquiv, ← Sylow.card_eq_multiplicity TC, hTC]
    exact hR
  exact hC G p P M Hs R Rbars Ks hds' z hzs' hB0 hEv hIso hRs hcomm hnot

end CFSG.AGLEmbedding
