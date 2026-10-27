module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocU33A
public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocGen
public import CFSG.GH74.Generic.BProg.B3.S3T2A7L3
public import CFSG.GH74.Generic.BProg.B3.S3T2A7Asm
public import CFSG.GH74.KGroups.U33

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

open CFSG Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace U33Cent


theorem autModel_facts :
    ∃ R : Subgroup (Equiv.Perm (Fin 28)), AutModel KGroups.U33.QP.originalSubgroup R ∧
      Nat.card R ≤ 2 * Nat.card KGroups.U33.QP.originalSubgroup ∧
      ∀ τ ∈ R, orderOf τ = 2 →
        CFSG.oddCore ↥(KGroups.U33.QP.originalSubgroup ⊓ centralizer ({τ} : Set _)) = ⊥ := by
  obtain ⟨U, hU2, hUP, hUn, hodd⟩ := outer_facts
  set P := KGroups.U33.QP.originalSubgroup with hPdef
  have hRmem : ∀ x, x ∈ P ⊔ zpowers U ↔ x ∈ P ∨ x * U ∈ P := fun x => mem_sup_zpowers_iff hU2 hUn
  have hRcard : Nat.card ↥(P ⊔ zpowers U) = 2 * Nat.card P := card_sup_zpowers hU2 hUn hUP
  have hC := centralizer_eq_bot
  have hout : Nat.card (Outer ↥P) ≤ 2 := by
    have hinj := conj_injective (center_eq_bot_of_centralizer hC)
    have hInn : Nat.card (inner ↥P) = Nat.card ↥P :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have hAut : Nat.card (MulAut ↥P) = 12096 := KGroups.U33.card_mulAut (MulEquiv.refl _)
    have hcP : Nat.card ↥P = 6048 := card_P
    have h := (inner ↥P).card_eq_card_quotient_mul_card_subgroup
    rw [hAut, hInn, hcP] at h
    change Nat.card (MulAut ↥P ⧸ inner ↥P) ≤ 2
    omega
  obtain ⟨e, he, -⟩ := full_automorphism_model hU2 hUP hUn hC hout
  refine ⟨P ⊔ zpowers U, autModel_of le_sup_left (fun x hx p hp => ?_) e he hC, hRcard.le, hodd⟩
  rcases (hRmem x).1 hx with hxP | hxU
  · exact P.mul_mem (P.mul_mem hxP hp) (P.inv_mem hxP)
  · have hUU : U * U = 1 := by rw [← sq, hU2]
    have hUinv : U⁻¹ = U := inv_eq_of_mul_eq_one_right hUU
    have h1 : U⁻¹ * p * U ∈ P := by
      have := hUn p hp
      rw [hUinv] at this ⊢
      exact this
    have : x * p * x⁻¹ = (x * U) * (U⁻¹ * p * U) * (x * U)⁻¹ := by group
    rw [this]
    exact P.mul_mem (P.mul_mem hxU h1) (P.inv_mem hxU)

end U33Cent

theorem locBal1Two_U33
    {T : Type} [Group T]
    [Finite T] (h : S3T2A7.U33 T) : S3T2A7.LocBal1Two T := by
  obtain ⟨ψ⟩ := KGroups.U33.equiv_of_lieModel h
  obtain ⟨R, hR, hidx, hodd⟩ := U33Cent.autModel_facts
  exact locBal1Two_of_normal_equiv ψ (center_eq_bot_of_centralizer U33Cent.centralizer_eq_bot)
    fun X _ _ S _ hS hC t ht => oddCore_centralizer_eq_bot hR hidx hodd S hS.some hC t ht

theorem locBal1For_U33 :
    S3T2A7.LocBal1For S3T2A7.U33 :=
  fun _ _ _ h => locBal1Two_U33 h

theorem cell125_U33 :
    S3T2A7.Cell125 S3T2A7.U33 :=
  S3T2A7.cell125_of_locBal1For locBal1For_U33

end CFSG.GH74.Generic.BProg.B3.S3T2A7Loc
