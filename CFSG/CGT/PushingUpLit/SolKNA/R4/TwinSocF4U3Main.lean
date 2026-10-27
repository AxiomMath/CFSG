module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Perf
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL3U3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Gen
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Two
public import CFSG.ClassicalInvolution.Q3.TL4MF163LU

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 CFSG.ClassicalInvolution.Q3.TA3.Q5U3
open CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3
open scoped MatrixGroups

theorem socF4U3_holds (r : ℕ) : SocF4U3 r := by
  intro hr A _ _ T _ hT hab hC hE R S z hd hc hnO hed hU3
  haveI := hT
  have hU3' := hU3
  obtain ⟨p, f, hp, hp2, hf, hq3, hm⟩ := hU3
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI := h.finite
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : CharP K p := h.charP
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq5 : 5 ≤ p ^ f := by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hodd' := Nat.odd_iff.mp hodd
    omega
  have hq : 2 < p ^ f := by omega
  obtain ⟨hzT, hzS⟩ := z_mem_of_comm2 hr hC (socleOutAbelian_u3 hU3').comm2 hd hc
  obtain ⟨F⟩ := exists_u3Frame h hp2 e hzT hd.order
  have hF₀card := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  have hF₀ : Odd (Nat.card (LieType.Steinberg.fixedSubfield K p f)) := by
    rw [hF₀card]
    exact hodd
  have h4 : 4 ≤ Nat.card (LieType.Steinberg.fixedSubfield K p f) := by
    rw [hF₀card]
    omega
  obtain ⟨eJ⟩ := nonempty_slPart_equiv h
  have hsc : ScalarsInCore F R := fun r' hr'R hr'T =>
    CFSG.ClassicalInvolution.Q3.TL4.MF163.exists_scalar_of_mem hd F.hrange F.hk (slCentScalar_GU2 h) hF₀ h4 eJ
      hr'R hr'T
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hd F.hrange F.hk hF₀ h4 eJ
  exact socF4_clause_of_parts hzS F.J_le F.comm_le (F.J_perfect h4 eJ) (F.J_centralizes hRJ)
    (two_elts_U3 F hC hr hd hc (socleOutAbelian_u3 hU3').comm2 hsc hq hq5 hp2 hRJ)
    hF₀ h4 (F.Φ eJ) (F.Φ_injective eJ hC) (F.Φ_range eJ)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
