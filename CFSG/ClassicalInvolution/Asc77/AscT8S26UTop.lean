module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectI
import CFSG.ClassicalInvolution.Asc77.AscT8S26UTopEng
public import CFSG.ClassicalInvolution.Asc77.WP2Thm8
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

section Order

variable {Y : Type} [Group Y] [Finite Y]

theorem s26_map_top_of_card {Λ : Set (Subgroup Y)} {c : ℕ}
    (hc : ∀ L ∈ Λ, Nat.card (↥L ⧸ classicalInvolutionOddCore ↥L) = c)
    {L J : Subgroup Y} (hL : L ∈ Λ) (hJ : J ∈ Λ)
    (htop : L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) = ⊤) :
    J.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) = ⊤ := by
  set N := classicalInvolutionOddCore Y with hN
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  have hrange : ∀ H : Subgroup Y, (π.comp H.subtype).range = H.map π := by
    intro H
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hLsurj : Function.Surjective (π.comp L.subtype) := by
    rw [← MonoidHom.range_eq_top, hrange]
    exact htop
  have hOL : classicalInvolutionOddCore ↥L ≤ (π.comp L.subtype).ker := by
    have hnorm : ((classicalInvolutionOddCore ↥L).map (π.comp L.subtype)).Normal :=
      Subgroup.Normal.map inferInstance _ hLsurj
    have hodd : Odd (Nat.card ((classicalInvolutionOddCore ↥L).map (π.comp L.subtype))) :=
      Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥L)
        (Subgroup.card_map_dvd _ _)
    have hle : (classicalInvolutionOddCore ↥L).map (π.comp L.subtype) ≤
        classicalInvolutionOddCore (Y ⧸ N) := le_sSup ⟨hnorm, hodd⟩
    have hcore : classicalInvolutionOddCore (Y ⧸ N) = ⊥ :=
      CFSG.ComponentClassification.OddCore.quotient_corefree Y
    rw [hcore] at hle
    intro x hx
    have := hle (Subgroup.mem_map_of_mem _ hx)
    rwa [Subgroup.mem_bot, ← MonoidHom.mem_ker] at this
  have h1 : Nat.card (Y ⧸ N) ≤ c := by
    have hlift : Function.Surjective
        (QuotientGroup.lift (classicalInvolutionOddCore ↥L) (π.comp L.subtype) hOL) := by
      intro y
      obtain ⟨x, hx⟩ := hLsurj y
      exact ⟨(x : ↥L ⧸ classicalInvolutionOddCore ↥L), by simpa using hx⟩
    rw [← hc L hL]
    exact Nat.card_le_card_of_surjective _ hlift
  have hkerJ : (π.comp J.subtype).ker ≤ classicalInvolutionOddCore ↥J := by
    have hodd : Odd (Nat.card (π.comp J.subtype).ker) := by
      have hle : (π.comp J.subtype).ker.map J.subtype ≤ N := by
        rintro _ ⟨x, hx, rfl⟩
        exact (QuotientGroup.eq_one_iff _).mp hx
      rw [← Subgroup.card_map_of_injective J.subtype_injective]
      exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card Y)
        (Subgroup.card_dvd_of_le hle)
    exact le_sSup ⟨inferInstance, hodd⟩
  have h2 : c ≤ Nat.card (J.map π) := by
    have h3 : (classicalInvolutionOddCore ↥J).index ∣ (π.comp J.subtype).ker.index :=
      Subgroup.index_dvd_of_le hkerJ
    have h4 : Nat.card (↥J ⧸ (π.comp J.subtype).ker) = Nat.card (J.map π) := by
      rw [← hrange J]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
    rw [← hc J hJ, ← h4]
    exact Nat.le_of_dvd Nat.card_pos h3
  have h5 : Nat.card (J.map π) ≤ Nat.card (Y ⧸ N) := Subgroup.card_le_card_group _
  exact Subgroup.eq_top_of_card_eq _ (le_antisymm h5 (h1.trans h2))

end Order

section Section

variable {G : Type} [Group G]

theorem s26_layerHull_omegaNbrGen (Ω : Set (Subgroup G)) (K : Subgroup G) :
    layerHull Ω (omegaNbrGen Ω K) = omegaNbrGen Ω K := by
  refine le_antisymm (iSup₂_le fun L _ => iSup_le fun hLX => hLX) ?_
  refine iSup₂_le fun M hM => ?_
  exact le_layerHull hM.1 (le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) M hM)

end Section

section Top

variable {p f : ℕ} [Fact p.Prime]

theorem s26_top_notMem_of_c26_1 (h1 : C26_1 p f) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω) :
    (⊤ : Subgroup (↥(omegaNbrGen Ω K) ⧸ classicalInvolutionOddCore ↥(omegaNbrGen Ω K))) ∉
      oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K)) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hc : ∀ L'' ∈ restrictFamily Ω (omegaNbrGen Ω K),
      Nat.card (↥L'' ⧸ classicalInvolutionOddCore ↥L'') = Nat.card SL(2, GaloisField p f) := by
    intro L'' hL''
    obtain ⟨z', hz'⟩ := (hΩ.restrict (omegaNbrGen Ω K)).classical L'' hL''
    obtain ⟨e⟩ := hz'.nonempty_equiv
    exact Nat.card_congr e.toEquiv
  exact s26_top_notMem_ofE hs.hJ (h1 G Ω K J S R T W z t hs hdisc)
    (fun hL hJ' htop => s26_map_top_of_card hc hL hJ' htop)

end Top

end CFSG.ClassicalInvolution.Asc77
