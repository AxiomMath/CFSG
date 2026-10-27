module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Setup
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Cases
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Main
public import CFSG.HardMathSupport.Solomon.Coordinator.ONGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open scoped commutatorElement

theorem gfr2_center_eq_bot {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : a ∈ Subgroup.center G := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem gapFinalKType_of_pumpup_of_inputs (hR1 : GapFinalLayerON)
    (hOG : UniquenessMaximal.InputONGroup) (h183 : Lemma512Ns.Input18_3) (hP : GapFinalPumpup) :
    GapFinalKType := by
  intro G _ _ m hS hC B' hB b hb hb1 L hL hON hbL hBN a ha haz J hJ hJty hbJ hK
  have hp : Nat.Prime 3 := Nat.prime_three
  have := hS.simple
  have hBe : CFSG.Open.IsElemAbelian 3 B' := hB.1.1
  have hb3 : b ^ 3 = 1 := hBe.2 b hb
  have ha3 : a ^ 3 = 1 := hBe.2 a ha
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have ha1 : a ≠ 1 := fun h => haz (h ▸ Subgroup.one_mem _)
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hab : b * a = a * b := by
    have := hBe.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩
    simpa using congrArg Subtype.val this
  have hbK : b ∈ conjHull a J := gfr2_le_conjHull hbJ
  obtain ⟨J₁, hJ₁, hty₁, hyJ₁⟩ := gfr2_data h183 hS.nonabelian hS.kProper hbo hao hab hL hJ hJty
    hbJ hK hbK
  set K : Subgroup G := conjHull a J with hKdef
  have hCa : Cen a ≠ ⊤ := by
    intro h
    have hac : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Cen a := by rw [h]; trivial
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    rw [gfr2_center_eq_bot hS.nonabelian] at hac
    exact ha1 (Subgroup.mem_bot.1 hac)
  have hKtop : K ≠ ⊤ := fun h => hCa (top_le_iff.1 (h ▸ hK.1))
  have hqY : CFSG.Open.IsQuasisimple (barOf 3 K) :=
    (isQuasisimple_barX_iff hp hK.2.1).1 hK.2.2.1.2.2
  have hKg : CFSG.Open.IsKGroup (barOf 3 K) :=
    isKGroup_quotient' (isKGroup_of_isKProper hS.kProper hKtop) _
  have hcore : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  set yb : barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨b, hbK⟩ with hyb
  have hy3 : yb ^ 3 = 1 := by
    rw [hyb, ← map_pow]
    have : (⟨b, hbK⟩ : ↥K) ^ 3 = 1 := Subtype.ext hb3
    rw [this, map_one]
  rcases gfr2_cases hR1 hOG hP hqY hKg hcore hy3 hJ₁ hty₁ hyJ₁ with hcen | hmjr
  · left
    refine mem_oPrimePOf_of_forall_commutator_mem hp hbK (fun k hk => ?_)
    rw [mem_gLAPPrimeCoreOf_iff 3 K]
    refine ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem (K.mul_mem hbK hk) (K.inv_mem hbK)) (K.inv_mem hk)
    · rw [← QuotientGroup.eq_one_iff]
      have hcomm := Subgroup.mem_center_iff.1 hcen (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨k, hk⟩)
      show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))
        ((⟨b, hbK⟩ : ↥K) * ⟨k, hk⟩ * (⟨b, hbK⟩ : ↥K)⁻¹ * ⟨k, hk⟩⁻¹) = 1
      have h2 : ⁅(QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (⟨b, hbK⟩ : ↥K)),
          (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (⟨k, hk⟩ : ↥K))⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm
      rw [commutatorElement_def, ← map_mul, ← map_inv, ← map_inv, ← map_mul, ← map_mul] at h2
      exact h2
  · right
    exact hmjr

section

set_option linter.unusedSectionVars false


theorem gapFinalKType_of_pumpup (h183 : Lemma512Ns.Input18_3) (hP : GapFinalPumpup) :
    GapFinalKType :=
  gapFinalKType_of_pumpup_of_inputs gapFinalLayerON_holds inputONGroup_holds h183 hP

end

end CFSG.HardMathSupport.Solomon.Coordinator
