module

public import CFSG.GH74.Generic.BProg.B1.Stage3aSD3
public import CFSG.GH74.Generic.BProg.B1.Stage3aSD4
public import CFSG.GH74.Generic.BProg.B1.Stage3aRank
public import CFSG.GH74.Generic.BProg.B1.Stage3aSD2

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

@[expose] def Stage2PumpSS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → IsQuasisimple ↥K →
      ∀ y ∈ CxK x K, orderOf y = 2 → y ≠ x → ⁅K, pPrimeCoreOf 2 (centralizer ({y} : Set G))⁆ = ⊥

theorem stage2PumpSS_of_allow (hAllow : Stage2Allow) : Stage2PumpSS := by
  intro G _ _ hyp noAlt x K hcirc h3 hq y hy hy2 hyx
  have hxm : x ∈ CxK x K := mem_CxK_self hcirc.1.1.1.2.2.1
  have hyC : y ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.1 hy).1
  have hr : 1 < pRank 2 ↥(CxK x K) := by
    have h2 := two_le_pRank_of_two_involutions (P := ↥(CxK x K)) (a := ⟨y, hy⟩) (b := ⟨x, hxm⟩)
      (by rw [Subgroup.orderOf_mk]; exact hy2) (by rw [Subgroup.orderOf_mk]; exact hcirc.1.1.1.1)
      (fun h => hyx (congrArg Subtype.val h))
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hyC))
    omega
  exact (⟨hyp, noAlt, hcirc.1, hq, hr, h3⟩ : S3PairData G x K).pumpSS_of_allow hAllow hy hy2 hyx

theorem noJPrimeFor_shape3_of_pumpSS
    (hQ : Stage2QSFor QShape3) (hS : Stage2PumpSS) : NoJPrimeFor QShape3 := by
  intro G _ _ hyp noAlt x K hJ hr h3
  have hcirc : IsJ2Circ x K := ⟨hJ, Or.inl hr⟩
  have hq := hQ G hyp noAlt x K hcirc h3
  have hdata : S3PairData G x K := ⟨hyp, noAlt, hJ, hq, hr, h3⟩
  exact hdata.false_of_universal (hdata.isUniversalComponent fun y hy hy2 hyx =>
    hS G hyp noAlt x K hcirc h3 hq y hy hy2 hyx)

theorem noJPrimeShape3SD_of_pumpSS
    (hQ : Stage2QSFor QShape3) (hS : Stage2PumpSS) : NoJPrimeShape3SD :=
  fun G _ _ hyp noAlt x K hJ hr h3 =>
    noJPrimeFor_shape3_of_pumpSS hQ hS G hyp noAlt x K hJ hr h3.qShape3

end CFSG.GH74.Generic.BProg.B1
