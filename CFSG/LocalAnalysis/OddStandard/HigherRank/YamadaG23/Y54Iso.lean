module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Sec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54M3b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private noncomputable def y54phiHom (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ↥(M3 c.s) →* ↥(c.s.fr.F) :=
  MonoidHom.mk' (fun m => ⟨f3phi c.s m, y54_phi_mem hH m ((y54_M3_cand c hH).2.1 m.2)⟩)
    (fun a b => Subtype.ext (y54_phi_mul hH a ((y54_M3_cand c hH).2.1 a.2) b
      ((y54_M3_cand c hH).2.1 b.2)))

private theorem y54phiHom_ker (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (m : ↥(M3 c.s)) :
    y54phiHom c hH m = 1 ↔ (m : G) ∈ c.s.fr.F := by
  have hcand := y54_M3_cand c hH
  have hmY : (m : G) ∈ f4Y c.s := hcand.2.1 m.2
  constructor
  · intro h
    have hphi : f3phi c.s (m : G) = 1 := congrArg (fun x : ↥(c.s.fr.F) => (x : G)) h
    have hX0 : (m : G) ∈ f4X0 c.s := (y54_phi_eq_one hH (m : G) hmY).1 hphi
    have hmem : (m : G) ∈ M3 c.s ⊓ f4X0 c.s := ⟨m.2, hX0⟩
    rwa [hcand.2.2.2.1] at hmem
  · intro hF
    have hFX0 : c.s.fr.F ≤ f4X0 c.s := le_sup_left.trans (y54_P_le_X0 hH)
    have hphi : f3phi c.s (m : G) = 1 := (y54_phi_eq_one hH (m : G) hmY).2 (hFX0 hF)
    apply Subtype.ext
    exact hphi

private theorem y54phiHom_surj (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    Function.Surjective (y54phiHom c hH) := by
  intro v
  obtain ⟨m, hmM, hmv⟩ := y54_phi_M (c := c) hH (y54_M3_cand c hH) (v : G) v.2
  refine ⟨⟨m, hmM⟩, ?_⟩
  apply Subtype.ext
  exact hmv

theorem y54_secProp (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    SecProp (M3 c.s) c.s.fr.F (fun Y _ _ π =>
      ∃ φ : Y ≃* ↥c.s.fr.F, ∀ n ∈ normIn c.s.H c.s.fr.F, ∀ m m' : ↥(M3 c.s),
        (m' : G) = n * m * n⁻¹ → ((φ (π m') : ↥c.s.fr.F) : G) = n * (φ (π m) : G) * n⁻¹) := by
  obtain ⟨hn, hbody⟩ := secProp_iso (y54phiHom c hH) (y54phiHom_surj c hH) (y54phiHom_ker c hH)
  obtain ⟨φ, hφ⟩ := hbody
  haveI : (c.s.fr.F.subgroupOf (M3 c.s)).Normal := hn
  refine ⟨hn, φ, ?_⟩
  intro n hnmem m m' hmm'
  show ((φ (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s)) m') : ↥c.s.fr.F) : G) =
    n * ((φ (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s)) m) : ↥c.s.fr.F) : G) * n⁻¹
  rw [hφ m', hφ m]
  have hc' : ((y54phiHom c hH m' : ↥c.s.fr.F) : G) = f3phi c.s (m' : G) := rfl
  have hc : ((y54phiHom c hH m : ↥c.s.fr.F) : G) = f3phi c.s (m : G) := rfl
  rw [hc', hc, hmm']
  exact y54_phi_conj hH n (show n ∈ f4N c.s from hnmem) (m : G)

end CFSG.OddStandard.HigherRank.YamadaG23
