module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Mb

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private noncomputable def y56phiHom (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ↥(C4 c.s) →* ↥(c.s.fr.E) :=
  MonoidHom.mk' (fun m => ⟨f3phi c.s m, y56_phi_mem hH m ((y56_C4_cand c hH).2.1 m.2)⟩)
    (fun a b => Subtype.ext (y56_phi_mul hH a ((y56_C4_cand c hH).2.1 a.2) b
      ((y56_C4_cand c hH).2.1 b.2)))

private theorem y56phiHom_ker (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (m : ↥(C4 c.s)) :
    y56phiHom c hH m = 1 ↔ (m : G) ∈ e4Q c.s := by
  have hcand := y56_C4_cand c hH
  have hmY : (m : G) ∈ e4Y c.s := hcand.2.1 m.2
  constructor
  · intro h
    have hphi : f3phi c.s (m : G) = 1 := congrArg (fun x : ↥(c.s.fr.E) => (x : G)) h
    have hX0 : (m : G) ∈ e4X0 c.s := (y56_phi_eq_one hH (m : G) hmY).1 hphi
    have hmem : (m : G) ∈ C4 c.s ⊓ e4X0 c.s := ⟨m.2, hX0⟩
    rwa [hcand.2.2.2.1] at hmem
  · intro hQ
    have hQX0 : e4Q c.s ≤ e4X0 c.s := y56_Q_le_X0 hH
    have hphi : f3phi c.s (m : G) = 1 := (y56_phi_eq_one hH (m : G) hmY).2 (hQX0 hQ)
    apply Subtype.ext
    exact hphi

private theorem y56phiHom_surj (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    Function.Surjective (y56phiHom c hH) := by
  intro v
  obtain ⟨m, hmM, hmv⟩ := y56_phi_M (c := c) hH (y56_C4_cand c hH) (v : G) v.2
  refine ⟨⟨m, hmM⟩, ?_⟩
  apply Subtype.ext
  exact hmv

theorem y56_secProp (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    SecProp (C4 c.s) (c.s.fr.E ⊔ zpowers c.s.t) (fun Y _ _ π =>
      ∃ φ : Y ≃* ↥c.s.fr.E, ∀ n ∈ normIn c.s.H c.s.fr.E, ∀ m m' : ↥(C4 c.s),
        (m' : G) = n * m * n⁻¹ → ((φ (π m') : ↥c.s.fr.E) : G) = n * (φ (π m) : G) * n⁻¹) := by
  obtain ⟨hn, hbody⟩ := secProp_iso (y56phiHom c hH) (y56phiHom_surj c hH) (y56phiHom_ker c hH)
  obtain ⟨φ, hφ⟩ := hbody
  haveI : ((c.s.fr.E ⊔ zpowers c.s.t).subgroupOf (C4 c.s)).Normal := hn
  refine ⟨hn, φ, ?_⟩
  intro n hnmem m m' hmm'
  show ((φ (QuotientGroup.mk' ((c.s.fr.E ⊔ zpowers c.s.t).subgroupOf (C4 c.s)) m') :
      ↥c.s.fr.E) : G) =
    n * ((φ (QuotientGroup.mk' ((c.s.fr.E ⊔ zpowers c.s.t).subgroupOf (C4 c.s)) m) :
      ↥c.s.fr.E) : G) * n⁻¹
  rw [hφ m', hφ m]
  have hc' : ((y56phiHom c hH m' : ↥c.s.fr.E) : G) = f3phi c.s (m' : G) := rfl
  have hc : ((y56phiHom c hH m : ↥c.s.fr.E) : G) = f3phi c.s (m : G) := rfl
  rw [hc', hc, hmm']
  exact y56_phi_conj hH n (show n ∈ e4N c.s from hnmem) (m : G)

end CFSG.OddStandard.HigherRank.YamadaG23
