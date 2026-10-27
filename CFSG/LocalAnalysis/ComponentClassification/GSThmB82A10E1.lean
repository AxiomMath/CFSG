module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Out
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Aut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SideS6

public section

namespace CFSG.ComponentClassification.GSThmB.A10E1

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Seven CFSG.ComponentClassification.GSThmB.Eight2
open CFSG.ComponentClassification.GSThmB.A10Side

theorem false_of_commutator_le (hSy : CFL2Sylow) (hC : CFL2C) (hJ : CFL2J) (hRank : CFL2Rank)
    (hJo : CFSec8JOrder) {X : Type} [Group X] [Finite X] (s : Setting3 X)
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)))
    (hle : ⁅s.Dt, s.h.S⁆ ≤ s.h.P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z⟩ := exists_zData hSy hC hJ hRank hJo s.case8 s.center_J
  obtain ⟨e, he⟩ := s.exists_isSymSixType hA
  obtain ⟨d, hd, hdP⟩ := exists_mem_Dt_not_mem_P s hA
  have hdS := s.Dt_le_S hd
  have hda : d ∈ centralizer ({s.h.a} : Set X) := (mem_inf.mp (s.h.S_le hdS)).1
  have hdN := mem_normalizer_of_mem_S s hdS
  obtain ⟨σ, hσ⟩ := he d hda (s.Dt_le_G0 hd)
  have hσ' : MulAut.congr e (rhoE s.h.J d) = MulAut.conjNormal σ := by
    rw [rhoE_of_mem hdN]
    exact hσ
  have hsign := sign_eq_neg_one s Z hJo hA e hd hdP hσ'
  have hσ2 := mul_self_eq_one s hA e hd hσ'
  obtain ⟨q, hqs, hq4, hq2, hσq, hqz⟩ := exists_q s Z e hd hσ'
  have hxS := s.h.x_mem
  have hxN := mem_normalizer_of_mem_S s hxS
  have hzN := mem_normalizer_of_mem_S s (s.h.D_le_S Z.hzD)
  have hxd : rhoE s.h.J s.h.x * rhoE s.h.J d = rhoE s.h.J d * rhoE s.h.J s.h.x := by
    have hmem : d * s.h.x * d⁻¹ * s.h.x⁻¹ ∈ s.h.P := by
      apply hle
      rw [← commutatorElement_def]
      exact commutator_mem_commutator hd hxS
    have h1 := rhoE_eq_one_of_mem_P s hmem
    rw [rhoE_mul (mul_mem (mul_mem hdN hxN) (inv_mem hdN)) (inv_mem hxN),
      rhoE_mul (mul_mem hdN hxN) (inv_mem hdN), rhoE_mul hdN hxN, rhoE_inv hdN,
      rhoE_inv hxN] at h1
    calc rhoE s.h.J s.h.x * rhoE s.h.J d = (rhoE s.h.J d * rhoE s.h.J s.h.x *
          (rhoE s.h.J d)⁻¹ * (rhoE s.h.J s.h.x)⁻¹)⁻¹ * (rhoE s.h.J d * rhoE s.h.J s.h.x) := by
          group
      _ = rhoE s.h.J d * rhoE s.h.J s.h.x := by rw [h1, inv_one, one_mul]
  have hxz := rhoE_comm s hxN hzN (Z.hzS _ hxS)
  have h1 : MulAut.congr e (rhoE s.h.J s.h.x) * MulAut.conjNormal σ =
      MulAut.conjNormal σ * MulAut.congr e (rhoE s.h.J s.h.x) := by
    rw [← hσ', ← map_mul, ← map_mul, hxd]
  have h2 : MulAut.congr e (rhoE s.h.J s.h.x) * MulAut.conjNormal (q ^ 2) =
      MulAut.conjNormal (q ^ 2) * MulAut.congr e (rhoE s.h.J s.h.x) := by
    rw [hqz, ← map_mul, ← map_mul, hxz]
  obtain ⟨τ, hτ⟩ := mem_range_conjNormal_of_commute_odd _ hσ2 hsign hqs hq4 hq2 hσq h1 h2
  rw [rhoE_of_mem hxN] at hτ
  exact not_isSymSixType_of_unbalancing s.unbalTriple e
    (Eight.oddBarAction s.h.J ⟨s.h.x, hxN⟩) (fun j => rfl) ⟨τ, hτ⟩

theorem gs82CaseA10Input_of_epsZero (hSy : CFL2Sylow) (hC : CFL2C) (hJ : CFL2J)
    (hRank : CFL2Rank) (hJo : CFSec8JOrder) (h0 : GS82CaseA10EpsZeroInput) :
    GS82CaseA10Input := by
  intro X _ _ s hNS hA
  by_cases hle : ⁅s.Dt, s.h.S⁆ ≤ s.h.P
  · exact false_of_commutator_le hSy hC hJ hRank hJo s hA hle
  · exact h0 X s hNS hA hle

end CFSG.ComponentClassification.GSThmB.A10E1
