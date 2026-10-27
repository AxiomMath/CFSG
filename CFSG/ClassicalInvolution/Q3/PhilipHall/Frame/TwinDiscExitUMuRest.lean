module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

namespace TwinDisc

section Gen

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

@[expose] def TwinOnlyNbr (Φ : Set (Subgroup X)) : Prop :=
  ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ C ∈ omegaNbr Φ A, B = C

theorem twinOnly_of_trans (hconj : ConjInvariant Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {J J' : Subgroup X} (hJ : J ∈ Φ)
    (hnb : ∀ M ∈ omegaNbr Φ J, M = J') : TwinOnlyNbr Φ := by
  intro A hA B hB C hC
  obtain ⟨g, rfl⟩ := htrans J hJ A hA
  have h1 := omegaNbr_conj hconj hB g⁻¹
  have h2 := omegaNbr_conj hconj hC g⁻¹
  rw [conjSub_inv_conjSub] at h1 h2
  have e : conjSub g⁻¹ B = conjSub g⁻¹ C := (hnb _ h1).trans (hnb _ h2).symm
  exact (conjSub_inj g⁻¹).mp e

theorem ker_pGroup_phi (hS : Q8Section X Φ) (φ : ↥(pSpan Φ) →* AEQ n)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ)) : IsPGroup 2 φ.ker := by
  have hgen : pSpan Φ = ⊤ := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  let e : ↥(pSpan Φ) ≃* X := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have hodd : classicalInvolutionOddCore ↥(pSpan Φ) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv e.symm hS.oddFree
  exact (TL4.Vtx.isPGroup_center_of_oddFree hodd).to_le hker

theorem members_two_phi (hn : 5 ≤ n) (hS : Q8Section X Φ) (φ : ↥(pSpan Φ) →* AEQ n)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ))
    (hlabel : ∀ L ∈ Φ, ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map φ = memBar α h b) : ∀ L ∈ Φ, IsPGroup 2 L := by
  intro L hL x
  obtain ⟨α, h, b, hlab⟩ := hlabel L hL
  set y : ↥(pSpan Φ) := ⟨(x : X), le_pSpan hL x.2⟩ with hy
  have hmem : φ y ∈ memBar α h b := by
    rw [← hlab]
    exact ⟨y, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have h8 : (⟨φ y, hmem⟩ : ↥(memBar α h b)) ^ 8 = 1 := by
    have := pow_card_eq_one' (G := ↥(memBar α h b)) (x := ⟨φ y, hmem⟩)
    rwa [natCard_memBar hn] at this
  have hk : y ^ 8 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    simpa using congrArg (fun z : ↥(memBar α h b) => (z : AEQ n)) h8
  obtain ⟨k, hk'⟩ := ker_pGroup_phi hS φ hker ⟨y ^ 8, hk⟩
  refine ⟨k + 3, ?_⟩
  apply Subtype.ext
  have h1 := congrArg (fun z : ↥φ.ker => ((z : ↥(pSpan Φ)) : X)) hk'
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
  have e : ((x : X)) ^ 2 ^ (k + 3) = (((y ^ 8) ^ 2 ^ k : ↥(pSpan Φ)) : X) := by
    simp only [Subgroup.coe_pow, hy]
    rw [← pow_mul]
    congr 1
    rw [pow_add]
    ring
  simpa [e] using h1

end Gen

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
