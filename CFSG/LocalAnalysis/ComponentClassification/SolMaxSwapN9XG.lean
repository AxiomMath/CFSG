module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatConv
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatLeaf
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTables
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9X1
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9X2
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9XU
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9XS

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

section Exact

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M F : Subgroup X} {DF : Finset (Fin n)} {f : X} {L N : Subgroup X}

theorem ExactData.false (hF : FiveCat.FivePumpUpInput)
    (hG : ExactGenerationInput) (hs : Setting t J n e E D M) (hn : n = 9)
    (hx : ExactData t J n e F DF f L N) : False := by
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({f} : Set X)) :=
    hs.isKGroupCat_centralizer hx.f1
  have htC : t ∈ centralizer ({f} : Set X) := hx.t_mem_centralizer hs
  obtain ⟨eL⟩ := hx.Ltype
  have huniq := hx.unique_layer hs hn
  have hLpc : IsPComponent 2
      (L.subgroupOf (centralizer ({f} : Set X) ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]; exact hx.Lpc
  have hLt : L ≤ centralizer ({t} : Set X) := hx.LC.trans inf_le_left
  have hout := five_pump_type_in hF hK htC hs.orderOf_t hx.NC hx.Npc hx.Nt hx.LN hLt hLpc eL hx.Nnt
    huniq
  rcases hout with ⟨m, hmo, hm7, ⟨θN⟩⟩ | hna
  · exact hx.false_of_alt hs hn hmo hm7 θN
  · rcases FiveCat.FivePumpNonAlt.table hna with hres | hnd
    · have hNH : N ≤ Hn E := by
        have hGN := hG X (centralizer ({f} : Set X)) N L t hx.NC hx.Npc htC hs.orderOf_t hx.Nt hx.LN
          hLt hLpc ⟨eL⟩ hx.Nnt huniq hres (N ⊓ Hn E) inf_le_left
          (le_inf (map_subtype_le _) ((pPrimeCore_le_of_isPComponent hx.NC hx.Npc).trans
            (hx.core_le_Hn hs)))
          (le_inf hx.LN (hx.LJ.trans hs.J_le_Hn))
          (fun u hu hu2 x hxN hxc => ⟨hxN, hs.centralizer_mul_le (hx.LJ hu) hu2 hxc⟩)
        exact inf_eq_left.mp hGN
      exact hs.false_of_pump_le hn (hx.FJ hx.fF) hx.orderOf_f hx.NC hx.Npc hx.Nt hNH
    · exact hnd (hx.dvd_card_zstar hs hn)

end Exact

theorem ys06_of_inputs (hF : FiveCat.FivePumpUpInput)
    (hG : ExactGenerationInput) : SwapMemberResidueNineExact := by
  intro X _ _ _ t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow hex
  exfalso
  obtain ⟨F, DF, f, L, N, hx⟩ := exactFivePump_iff.mp hex
  exact hx.false hF hG ⟨S, hCH, hMH, hMpc, hne, hJM, hMalt, hsmall, hnarrow⟩ hn

section Closed

theorem ys06_of_exactGenerationInput (hG : ExactGenerationInput) :
    SwapMemberResidueNineExact :=
  ys06_of_inputs FiveCat.fivePumpUpInput_holds hG

end Closed

end CFSG.ComponentClassification.SolMax.SwapP2
