module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeTables

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Fi24PrimeAux

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.Coordinator
 CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Fi24.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24 MR)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem mem_JR_of_orderOf_eq_five
    {r : R} (hr : orderOf r = 5) : r ∈ JR := by
  have hn : JR.Normal := CFSG.Sporadic.Fi24.normal_JR
  have hidx : JR.index = 2 := CFSG.Sporadic.Fi24.index_JR
  have hcard : Nat.card (R ⧸ JR) = 2 := by rw [← Subgroup.index, hidx]
  have h5 : (QuotientGroup.mk r : R ⧸ JR) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow, ← hr, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h2 : (QuotientGroup.mk r : R ⧸ JR) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := R ⧸ JR) (x := QuotientGroup.mk r)
    rwa [hcard] at this
  have h1 : (QuotientGroup.mk r : R ⧸ JR) = 1 := by
    have e : (QuotientGroup.mk r : R ⧸ JR) = ((QuotientGroup.mk r : R ⧸ JR) ^ 2) ^ 3 *
        ((QuotientGroup.mk r : R ⧸ JR) ^ 5)⁻¹ := by
      group
    rw [e, h2, h5]
    simp
  exact (QuotientGroup.eq_one_iff r).1 h1


theorem gLAPPrimeCoreOf_R_eq_bot_of_J {s : CFSG.Sporadic.Fi24.J} (hs : orderOf s = 5) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({jR s} : Set R)) = ⊥ := by
  obtain ⟨e, he, f, hf, h5e, he1, h5f, hcomm, hpow, hgraph⟩ := fi24Five_parts
  obtain ⟨g, a, ha, b, hb, hab, hw⟩ := exists_conj_sylow5 J he hf h5e he1 h5f hcomm hpow
    (m := 50208228367626468851712) (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num) (by norm_num) hs
  have hwo : orderOf (g⁻¹ * s * g) = 5 := by rw [CommutingPair.orderOf_inv_mul_mul, hs]
  obtain ⟨hT0, hT1, hT2⟩ := hgraph a ha b hb hab _ hw
  have hwoR : orderOf (jR (g⁻¹ * s * g)) = 5 := by
    rw [orderOf_injective jR CFSG.Sporadic.Fi24.jR_injective, hwo]
  have hbot := gLAPPrimeCoreOf_fi24_five_eq_bot hwoR hT0 hT1 hT2
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' := @conj_mem_gLAPPrimeCoreOf_centralizer R (inferInstance : Group R) 5 (jR g)⁻¹ (jR s) x hx
  rw [inv_inv] at hx'
  have hconj : (jR g)⁻¹ * jR s * jR g = jR (g⁻¹ * s * g) := by
    rw [map_mul, map_mul, map_inv]
  rw [hconj, hbot, Subgroup.mem_bot] at hx'
  exact CommutingPair.eq_one_of_inv_mul_mul_eq_one hx'

theorem oPrimeCoreTrivialAt_R_five : OPrimeCoreTrivialAt 5 R := by
  intro r hr
  obtain ⟨s, rfl⟩ := exists_jR_of_mem (mem_JR_of_orderOf_eq_five hr)
  exact gLAPPrimeCoreOf_R_eq_bot_of_J (by
    rwa [orderOf_injective jR CFSG.Sporadic.Fi24.jR_injective] at hr)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Fi24PrimeAux
