module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltLocal
import CFSG.GH74.KGroups.A6
public import CFSG.GH74.KGroups.Generic

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open

variable {K : Type} [Group K] [Finite K]

theorem autFixInner_of_isAltTwoP_three (hK : IsAltTwoP 3 K)
    (T : Sylow 3 K) : AutFixInner 3 K T := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨e⟩ := hK
  let e6 : K ≃* alternatingGroup (Fin 6) := e
  obtain ⟨eP⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 (K := K) ⟨e6⟩
  intro f hf
  set R : Subgroup (MulAut K) := (T : Subgroup K).map (MulAut.conj : K →* MulAut K) with hR
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    conj_injective_of_center_trivial (center_eq_bot_of_isAltTwoP hp hp2 ⟨e⟩)
  have hTcard : Nat.card T = 3 ^ 2 := sylowSq_of_isAltTwoP hp hp2 ⟨e⟩ T
  have hRab : CFSG.GH74.KGroups.ElemAb 3 R := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm_of_mem_isAltTwoP hp hp2 ⟨e⟩ T ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, pow_eq_one_of_mem_isAltTwoP hp hp2 ⟨e⟩ T ha, map_one]
  have hRcard : Nat.card R = 9 := by
    rw [hR, Subgroup.card_map_of_injective hinj]
    simpa using hTcard
  have hfR : ∀ r ∈ R, f * r = r * f := by
    rintro _ ⟨t, ht, rfl⟩
    refine MulEquiv.ext fun x => ?_
    show f (t * x * t⁻¹) = t * f x * t⁻¹
    rw [map_mul, map_mul, map_inv, hf t ht]
  have hfin : Finite (MulAut K) := CFSG.GH74.KGroups.A6.finite_mulAut eP
  have hodd : Odd (orderOf f) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨m, hm⟩ := hev
    have hmpos : 0 < m := by
      have := orderOf_pos f
      omega
    have hψ : (f ^ m) ^ 2 = 1 := by
      rw [← pow_mul, show m * 2 = orderOf f by omega, pow_orderOf_eq_one]
    have hψ1 : f ^ m = 1 :=
      CFSG.GH74.KGroups.A6.autCentralizer eP R hRab hRcard (f ^ m) hψ fun r hr => by
        have hc : Commute f r := hfR r hr
        exact (hc.pow_left m).eq
    have := orderOf_le_of_pow_eq_one hmpos hψ1
    omega
  have hf6 : Odd (orderOf (MulAut.congr e6 f)) := by
    rwa [MulEquiv.orderOf_eq]
  obtain ⟨a, ha⟩ := CFSG.AGLEmbedding.mem_range_conj_of_odd_orderOf (MulAut.congr e6 f) hf6
  refine ⟨e6.symm a, ?_⟩
  apply (MulAut.congr e6).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ha]

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
