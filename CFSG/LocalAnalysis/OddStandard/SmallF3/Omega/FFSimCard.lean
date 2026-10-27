module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IOrd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCenter

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_natCard_piSim (h0 : 0 < Module.finrank (ZMod 3) V) : Nat.card (piSim Q) = 2 := by
  have h := Nat.card_congr (Subgroup.equivMapOfInjective (piGroup Q) (orthToSim Q)
    orthToSim_injective).toEquiv
  change Nat.card ((piGroup Q).map (orthToSim Q)) = 2
  rw [← h]
  exact card_piGroup h0

theorem ff_natCard_projSim_mul (hQ : Q.Nondegenerate) (h0 : 0 < Module.finrank (ZMod 3) V) :
    Nat.card (ProjSim Q) * 2 =
      Nat.card (OGroup Q) * (if Even (Module.finrank (ZMod 3) V) then 2 else 1) := by
  have h1 : Nat.card (simGroup Q) = Nat.card (ProjSim Q) * Nat.card (piSim Q) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (piSim Q)
  have h2 := Subgroup.card_mul_index
    ((TauCeti.QuadraticMap.orthogonalGroup Q).subgroupOf (simGroup Q))
  rw [index_orthogonalGroup_subgroupOf_simGroup hQ h0] at h2
  have h3 : Nat.card ((TauCeti.QuadraticMap.orthogonalGroup Q).subgroupOf (simGroup Q)) =
      Nat.card (OGroup Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe orthogonalGroup_le_simGroup).toEquiv
  rw [h3] at h2
  rw [ff_natCard_piSim h0] at h1
  split_ifs at h2 ⊢ <;> omega

theorem ff_natCard_projSim_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) : Nat.card (ProjSim Q) = 51840 := by
  have h := ff_natCard_projSim_mul hQ (by rw [hdim]; norm_num)
  rw [natCard_oGroup_five hQ hdim, if_neg (by rw [hdim]; decide)] at h
  omega

theorem ff_natCard_projSim_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    Nat.card (ProjSim Q) = 24261120 := by
  have h := ff_natCard_projSim_mul hQ (by rw [hdim]; norm_num)
  rw [natCard_oGroup_six_plus hQ hdim hs, if_pos (by rw [hdim]; decide)] at h
  omega

theorem ff_natCard_projSim_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    Nat.card (ProjSim Q) = 26127360 := by
  have h := ff_natCard_projSim_mul hQ (by rw [hdim]; norm_num)
  rw [natCard_oGroup_six_minus hQ hdim hs, if_pos (by rw [hdim]; decide)] at h
  omega

theorem ff_piOrth_not_mem_omegaGroup_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    piOrth Q ∉ omegaGroup hQ := by
  rw [piOrth_mem_omegaGroup_iff hQ, hdim]
  intro hmem
  rw [hs] at hmem
  have h6 : (6 / 2 : ℕ) = 3 := by norm_num
  have h3 : ((-1 : ℤˣ) ^ 3) = -1 := by decide
  rw [h6, h3] at hmem
  exact (by decide : (1 : ℤˣ) ≠ -1) hmem.2

theorem ff_piOrth_mem_omegaGroup_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    piOrth Q ∈ omegaGroup hQ := by
  rw [piOrth_mem_omegaGroup_iff hQ, hdim]
  refine ⟨by decide, ?_⟩
  rw [hs]
  have h6 : (6 / 2 : ℕ) = 3 := by norm_num
  rw [h6]
  decide

theorem ff_natCard_omegaProj_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    Nat.card (omegaProj hQ) = 6065280 := by
  have h := card_omegaProj_mul hQ (by rw [hdim]; norm_num)
  rw [if_neg (ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hs), mul_one,
    natCard_omegaGroup_six_plus hQ hdim hs] at h
  exact h

theorem ff_natCard_omegaProj_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    Nat.card (omegaProj hQ) = 3265920 := by
  have h := card_omegaProj_mul hQ (by rw [hdim]; norm_num)
  rw [if_pos (ff_piOrth_mem_omegaGroup_six_minus hQ hdim hs),
    natCard_omegaGroup_six_minus hQ hdim hs] at h
  omega

end CFSG.OddStandard.SmallF3.Omega
