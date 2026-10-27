module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0NN
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosTAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatAssembly

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem d1SPLPieceZK_of (hFi : KFactSPLNotFi22) (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hKU2 : KFactUnitarySylowStructure)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock) :
    D1SPLPieceZK := by
  intro G _ _ p P M H R Rbar K z D hzM s hs hs2 hsp
  obtain ⟨hd, huniq, hz, hLA, hSP, -, hVK, hVC, -, hN⟩ := D
  obtain ⟨h3, hY, -, hCW, -⟩ := hd.splPair_facts hFi hUP hSTO hKU2 h84 hD2 hz hLA hSP hVK hVC hN
  have hzN : z ∈ d1PlusCore p H K := by
    obtain ⟨-, -, hzH, hzc⟩ := hz
    exact ⟨⟨z, hzH⟩, hzc, rfl⟩
  have hzJ := hd.mem_nclIn_commutator h3 h84 hCGT hD2 huniq hY hCW hz.1 hzN hz.2.1
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Os := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hOs
  set Cs : Subgroup G := ((Subgroup.centralizer (Os : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap mk).map
    M.subtype with hCs
  have hOsodd : Os ≤ CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) := by
    have : Fact s.Prime := ⟨hs⟩
    refine le_sSup ⟨inferInstance, ?_⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := s) (G := ↥M ⧸ CFSG.pCore 2 ↥M)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hs).mpr (Ne.symm hs2))
  have hOsS := hOsodd.trans (h3.oddCore_le_centralizer h84 hD2)
  have hSM : pCoreOf 2 H ≤ M := h3.twoCore_le
  have hSC : pCoreOf 2 H ≤ Cs := by
    intro x hx
    refine ⟨⟨x, hSM hx⟩, ?_, rfl⟩
    change mk ⟨x, hSM hx⟩ ∈ Subgroup.centralizer (Os : Set (↥M ⧸ CFSG.pCore 2 ↥M))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hOsS hy) (mk ⟨x, hSM hx⟩)
      ⟨⟨x, hSM hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩).symm
  have hCsN : ∀ g ∈ M, ∀ c ∈ Cs, g * c * g⁻¹ ∈ Cs := by
    rintro g hgM _ ⟨c, hc, rfl⟩
    refine ⟨⟨g, hgM⟩ * c * (⟨g, hgM⟩ : M)⁻¹, ?_, rfl⟩
    have hc' : mk c ∈ Subgroup.centralizer (Os : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hc
    have := (Subgroup.normal_centralizer (H := Os)).conj_mem _ hc' (mk ⟨g, hgM⟩)
    change mk (⟨g, hgM⟩ * c * (⟨g, hgM⟩ : M)⁻¹) ∈
      Subgroup.centralizer (Os : Set (↥M ⧸ CFSG.pCore 2 ↥M))
    simpa [map_mul, map_inv] using this
  have hSJ : nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ ≤ Cs :=
    nclIn_le_of_forall_conj_mem fun c hc x hx =>
      hCsN c hc x (hSC (hd.commutator_nclIn_le h3 h84 hD2 hY hx))
  obtain ⟨z', hz'C, hz'z⟩ := hSJ hzJ
  have hz' : z' = ⟨z, hzM⟩ := Subtype.ext hz'z
  subst hz'
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  rintro h rfl
  exact (Subgroup.mem_centralizer_iff.mp hz'C y hy).symm

end CFSG.AGLEmbedding
