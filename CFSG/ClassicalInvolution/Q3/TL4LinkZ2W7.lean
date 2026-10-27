module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W5

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Cit3


theorem tightLinkC264One_of_gaps (hg : Z2GapFacts) {n : ℕ} : TightLinkC264One n := by
  intro hP h4 htw Y _ _ R S t hL hc hT hZ2 hsimp hidx hmod J hJ u hu R₀ T₀ hR₀ hR₀u hT₀ hT₀N
    hA1 hPS
  obtain ⟨P, hR₀P, hT₀P⟩ := hPS
  have hs : Z2Set n R S t J u R₀ T₀ P :=
    ⟨hL, hc, hT, hZ2, hsimp, hidx, hmod, hJ, hu, hR₀, hR₀u, hT₀, hT₀N, hA1, hR₀P, hT₀P⟩
  obtain ⟨W, hs8⟩ := hs.exists_std8
  have hthree := hs.noThreeMeetSylow
  obtain ⟨s, hs2, hst, hsu, hsR, hsT, hsZ, h, hh⟩ := hs.exists_s
  have hsa : s ∈ Subgroup.centralizer ({t * u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc s * (t * u) = s * t * u := by group
      _ = t * s * u := by rw [hst]
      _ = t * (s * u) := by group
      _ = t * (u * s) := by rw [hsu]
      _ = t * u * s := by group
  have hσ := hs.sPropSec_of_s hsa hs2 hsR hsT hsZ
  by_cases hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u)
  · by_cases hO2 : SecInO2 (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) t
    · exact std8_c264One_of_E2 hP h4 hs8 hthree hσ hcj hO2
    · rcases hs8.secTwinOmegaF_or_twinE4 h4
        (PhilipHall.Frame.Thm1RTwinLiftSetEBelow.toSet htw) hcj hO2 with hE4 | hom
      · exact (std8_false_of_twinE4 hg h4 hs8 hthree hσ hcj hO2 hE4).elim
      · exact (std8_false_of_secTwinOmega hg hs h4 hs8 hthree hsa hs2 hsR hsT hsZ hh hcj hO2
          hom).elim
  · obtain ⟨hKN, hJN⟩ := hs8.secImg_normal_of_not_conj h4 hcj
    exact hs8.c264One_of_pair hKN (std8_pair_of_three hs8 hthree hKN hJN)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
