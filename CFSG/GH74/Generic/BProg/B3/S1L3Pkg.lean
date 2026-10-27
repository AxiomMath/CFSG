module

public import CFSG.GH74.Generic.BProg.B3.S1L3PkgPsl2
public import CFSG.GH74.Generic.BProg.B3.S1L3PkgOut

import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  CFSG.GH74.Generic.BProg.B3 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalCores Subgroup
open scoped commutatorElement MatrixGroups

theorem l3_outer_involution_commuting {L : Type} [Group L] [Finite L] (hL : B1.QShape3SD L) {β : L}
    (hβ : orderOf β = 2) (γ : MulAut L) (hγ : γ * γ = 1) (hγβ : γ β = β)
    (hγout : γ ∉ (MulAut.conj : L →* MulAut L).range) :
    ∃ δ : L, orderOf δ = 2 ∧ δ ≠ β ∧ δ * β = β * δ ∧ γ δ = δ := by
  obtain ⟨p, f, k, _, _, N, hp, hp2, hf, h5, hk, hq, hfix, hnorm, ⟨e⟩⟩ :=
    S1L3PkgOut.exists_psl2_fixed hL hγ hγout
  have hβ2 : β * β = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hβ)
  have hβ1 : β ≠ 1 := fun h => by simp [h] at hβ
  obtain ⟨δ, hδN, hδ1, hδβ, hδ2, hδc⟩ :=
    S1L3PkgPsl2.exists_involution_of_psl2 hp hp2 hf hk h5 hq e hβ2 hβ1 (hnorm β hγβ)
  exact ⟨δ, orderOf_eq_prime (by rw [sq]; exact hδ2) hδ1, hδβ, hδc, hfix δ hδN⟩

end CFSG.GH74.Generic.BProg.B3
