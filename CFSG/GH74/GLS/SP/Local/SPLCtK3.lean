module

public import CFSG.GH74.GLS.SP.Local.SPLK3A
public import CFSG.GH74.GLS.SP.Local.SPLK3B
public import CFSG.GH74.GLS.SP.Local.SPLFitA
public import CFSG.GH74.GLS.SP.Local.SPLFitK1
public import CFSG.GH74.GLS.SP.Local.SPLFitK2

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

theorem splCenUAt {G : Type} [Group G] [Finite G] (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) {u : G}
    (hu : u ∈ D.S₁) (hu2 : orderOf u = 2) (huz : u ≠ D.z) (hut : D.t * u = u * D.t)
    (hnorm : ∀ x ∈ D.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D.z) : SPLCenUAt D u := by
  have huK : u ∈ D.K := hu.2
  obtain ⟨hprod, htorus, hinf, hCKcard⟩ := K3_elem D hs huK hu2 huz hut
  have hEcard : Nat.card ↥(D.Eu u) = D.e * D.e := by
    obtain ⟨E₁, E₂, hsup, hinfE, hcomm, -, -, hc₁, hc₂, -, -⟩ := hprod
    rw [← hsup, IVK.Proofs2.card_sup_eq_mul hcomm hinfE, hc₁, hc₂]
  refine ⟨hprod, K3_O2_of D hs hu hu2 huz hut hnorm hCKcard hEcard, hinf, ?_, htorus⟩
  intro Y hYle hYnorm hYodd hYab
  obtain ⟨u₁, hu₁, u₂, hu₂, hdec, hsq₁, hsq₂⟩ := K3_decomp D hs huK hu2 huz hut
  exact fit_of_K1_side D hs hut Y hYle hYnorm hYodd
    (fit_K1_side spl_fit_A1 D hs ⟨u₁, hu₁, u₂, hu₂, hdec, hsq₁, hsq₂⟩ Y hYle hYnorm hYodd hYab)

theorem splInCenU : SPLInCenU := by
  intro G _ _ _ D₁ hs _ u hu hu2 huz hut hnorm
  exact splCenUAt D₁ hs hu hu2 huz hut hnorm

end CFSG.GH74.GLS.SP.Local
