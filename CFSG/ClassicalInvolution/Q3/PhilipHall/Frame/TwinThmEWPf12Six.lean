module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf4Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf12Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Six

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

@[expose] def D2Supply : Prop :=
  ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TC.Thin.ThmDAbsBelow 3 (n + 1)

@[expose] def ExactO2Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → z ∈ Q →
        ∀ J ∈ Ω, IsPGroup 2 ↥J

@[expose] def E8ExitQ8 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Δ : Set (Subgroup Y)), TwinDisc.ExitO2.Q8Fam Y Δ →
    (∃ E : Subgroup Y, E8Struct ⊤ E) → T3.DStarConnected Δ

@[expose] def AE5ExitQ8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H → TwinDisc.ExitO2.Q8Fam G Ω →
      Nonempty (AEIdent Ω 5) → False

theorem e18_6NotO2Q8_of (hD : D2Supply) (hEx : ExactO2Q8) (hE8 : E8ExitQ8) (hAE5 : AE5ExitQ8)
    (h5 : E18_5Q8) : E18_6NotO2Q8 := by
  intro G _ _ Ω K S R W H c z hz Q hQn hQ2 hzQ
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hex := hEx G Ω K S R W H c z hz Q hQn hQ2 hzQ
  have htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3Q8 G Ω K S R W H c
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := h5 G Ω K S R W H c
  have F : TwinDisc.ExitO2.Q8Fam G Ω :=
    { hyp := hΩ
      two := hex
      q8 := fun L hL => by
        obtain ⟨P, hP, ⟨e⟩⟩ := c.stand.q8 L hL
        have hPL : L = P := hP.eq_of_le (hex L hL) le_rfl hP.1
        exact ⟨(MulEquiv.subgroupCongr hPL).trans e⟩
      aEmpty := aEmpty_forall_of_transitive hΩ.conjInvariant htrans c.stand.aEmpty
      gen := hgen
      trans := fun L hL L' hL' => by
        obtain ⟨a, rfl⟩ := htrans L hL
        obtain ⟨b, rfl⟩ := htrans L' hL'
        exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
      oddFree := c.oddCore_eq_bot
      inO2 := fun L hL u hu => by
        obtain ⟨g, rfl⟩ := htrans L hL
        refine ⟨Q, hQn, hQ2, ?_⟩
        have hgu : g * z * g⁻¹ = u := (hz.conj g).eq hu
        rw [← hgu]
        exact hQn.conj_mem z hzQ g }
  have hDn := hD (Nat.card G) c.stand.ih.1 c.stand.ih.2
  have hconcl := F.thmDConcl hDn (Nat.lt_succ_self _)
  have hdis : ¬ T3.DStarConnected Ω := by
    obtain ⟨J, hJ, hJn⟩ := (e18_1Q8 G Ω K S R W H c).2
    exact fun hconn => hJn (hconn K c.stand.mem J hJ)
  rcases hconcl with hsingle | ⟨W', hW'⟩ | ⟨E, hE⟩ | hI64 | ⟨n, hn, hIn⟩ | hI29
  · obtain ⟨K', hK'tw, hne, -⟩ := c.stand.twin
    exact hne (hsingle K' hK'tw.1 K c.stand.mem)
  · have hWW : W = W' := by
      have := c.stand.hW.1
      rw [hW'] at this
      exact this
    refine c.proper (eq_top_iff.mpr fun g _ => ?_)
    refine c.mem_of_conjSub_eq_W (etaAbelian_of_gen hΩ) (n := g) ?_
    have hmem := WSet.conj hΩ.conjInvariant c.stand.hW.1 g
    rw [hW'] at hmem
    exact (Set.mem_singleton_iff.mp hmem).trans hWW.symm
  · exact hdis (hE8 G Ω F ⟨E, hE⟩)
  · obtain ⟨I⟩ := hI64
    exact hdis (TwinDisc.ExitO2.fam_dstarConnected_of_e64 F I)
  · obtain ⟨I⟩ := hIn
    by_cases h5' : n = 5
    · subst h5'
      exact hAE5 G Ω K S R W H c F ⟨I⟩
    · exact hdis (TwinDisc.ExitO2.fam_dstarConnected_of_aeIdent F (by omega) I)
  · obtain ⟨I⟩ := hI29
    exact hdis (TwinDisc.ExitO2.fam_dstarConnected_of_e29 F I)

theorem e18_6O2Q8_of_D2 (hD : D2Supply) (hEx : ExactO2Q8) (hE8 : E8ExitQ8) (hAE5 : AE5ExitQ8)
    (h5 : E18_5Q8) : E18_6O2Q8 :=
  e18_6O2Q8_of h5 (e18_6NotO2Q8_of hD hEx hE8 hAE5 h5)

end Six

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
