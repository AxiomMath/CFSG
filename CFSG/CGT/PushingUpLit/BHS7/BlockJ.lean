module

public import CFSG.CGT.PushingUpLit.BHS7.SevenNine
public import CFSG.CGT.PushingUpLit.BHS7.OffenderBlock

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem isElemAbelian_omegaOneCenterOf_gen (X : Subgroup Γ) :
    IsElemAbelian 2 (omegaOneCenterOf X) := by
  have hcomm : ∀ x ∈ omegaOneCenterOf X, ∀ y ∈ omegaOneCenterOf X, x * y = y * x :=
    fun x hx y hy => by
      have h1 := C1GN.omegaOneCenterOf_le_centerOf _ hx
      exact (Subgroup.mem_centralizer_iff.mp h1.2 y (C1GN.omegaOneCenterOf_le_self _ hy)).symm
  refine isElemAbelian_of_forall' hcomm fun x hx => ?_
  unfold omegaOneCenterOf omegaOneOf at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => simp
  | mul x y hx hy hx2 hy2 =>
    have hxy : Commute x y := hcomm x hx y hy
    rw [hxy.mul_pow, hx2, hy2, one_mul]
  | inv x hx hx2 => rw [inv_pow, hx2, inv_one]

theorem omegaOneCenterOf_baum_le_of_isMaxElemAbelian {S A : Subgroup Γ}
    (hA : IsMaxElemAbelian S A) : omegaOneCenterOf (baum S) ≤ A := by
  have hZe : IsElemAbelian 2 (omegaOneCenterOf (baum S)) :=
    isElemAbelian_omegaOneCenterOf_gen (baum S)
  have hAJ : A ≤ thompsonJ S := le_iSup₂_of_le A hA le_rfl
  have hAB : A ≤ baum S := hAJ.trans (B6.thompsonJ_le_baum S)
  have hAZ : A ≤ Subgroup.centralizer (omegaOneCenterOf (baum S) : Set Γ) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc := (C1GN.omegaOneCenterOf_le_centerOf (baum S) hz).2
    exact (Subgroup.mem_centralizer_iff.mp hzc a (hAB ha)).symm
  have hel : IsElemAbelian 2 (A ⊔ omegaOneCenterOf (baum S)) :=
    isElemAbelian_sup_of_le_centralizer hA.2.1 hZe hAZ
  have hZS : omegaOneCenterOf (baum S) ≤ S :=
    (C1GN.omegaOneCenterOf_le_self (baum S)).trans (C1GN.baum_le S)
  have hle : Nat.card ↥(A ⊔ omegaOneCenterOf (baum S)) ≤ Nat.card ↥A :=
    hA.2.2 _ (sup_le hA.1 hZS) hel
  have heq : A ⊔ omegaOneCenterOf (baum S) = A :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
  exact heq ▸ le_sup_right

theorem exists_isMaxElemAbelian_ge_blockW {L S F : Subgroup Γ} (hL : CharTwo L)
    (hS : IsSylowOf 2 S L) (hF : IsBTBlock L S F) (hsub : IsSubnormal F L) :
    ∃ A : Subgroup Γ, IsMaxElemAbelian S A ∧ blockW F ≤ A := by
  classical
  set V' : Subgroup Γ := omegaOneCenterOf (pCoreOf 2 L) with hV'
  have hV'e : IsElemAbelian 2 V' := isElemAbelian_omegaOneCenter_pCoreOf L
  have hLV : L ≤ Subgroup.normalizer (V' : Set Γ) := le_normalizer_omegaOneCenter_pCoreOf L
  have hV'Q : V' ≤ pCoreOf 2 L := omegaOneCenter_le_pCoreOf L
  have hS' : IsSylowTwoOf S L := isSylowTwoOf_of_isSylowOf hS
  have hV'S : V' ≤ S := hV'Q.trans hS'.pCoreOf_le
  have hSL : S ≤ L := hS.1
  have hWV' : blockW F ≤ V' := (six_four_a hL hS hF).2
  have hWS : blockW F ≤ S := hWV'.trans hV'S
  have hne : ⁅F, V'⁆ ≠ ⊥ := commutator_omegaOneCenter_ne_bot hL hS hF
  have hJ : ⁅blockW F, thompsonJ S⁆ ≠ ⊥ := six_four_d hL hS hF
  obtain ⟨A, hA, hWA⟩ : ∃ A : Subgroup Γ, IsMaxElemAbelian S A ∧ ⁅blockW F, A⁆ ≠ ⊥ := by
    by_contra hcon'
    have hcon : ∀ A : Subgroup Γ, IsMaxElemAbelian S A → ⁅blockW F, A⁆ = ⊥ := fun A hA =>
      by_contra fun h' => hcon' ⟨A, hA, h'⟩
    apply hJ
    have hle : thompsonJ S ≤ Subgroup.centralizer (blockW F : Set Γ) := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 : ⁅w, a⁆ ∈ (⁅blockW F, A⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hw ha
      rw [hcon A hA, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw j hj
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hle hj) w hw
  have hAS : A ≤ S := hA.1
  have hAL : A ≤ L := hAS.trans hSL
  have hAnc : ¬ A ≤ Subgroup.centralizer (V' : Set Γ) := by
    intro hc
    apply hWA
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw a ha
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hc ha) w (hWV' hw)
  have hOff : IsOffG V' A := isOffG_of_isMaxElemAbelian hV'e hV'S (hSL.trans hLV) hA hAnc
  rcases offender_block_dichotomy hL hS hF hV'e hV'Q hLV hF.le hAL hsub hne hOff with
    hc | ⟨-, hrel⟩
  · exfalso
    exact hWA (commutator_blockW_eq_bot_of_comm_mod hL hS hF hV'Q hLV hne
      (isPGroup_of_isElemAbelian hA.2.1) hAL hc)
  set W : Subgroup Γ := blockW F with hWdef
  set A₀ : Subgroup Γ := A ⊓ Subgroup.centralizer (W : Set Γ) with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hcomm : ∀ x ∈ A₀, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hel : IsElemAbelian 2 (A₀ ⊔ W) :=
    isElemAbelian_sup' (isElemAbelian_mono' hA.2.1 hA₀A) (isElemAbelian_mono' hV'e hWV') hcomm
  have hcard := card_sup_mul_card_inf' hcomm
  have hrA := Subgroup.relIndex_mul_card A₀ A
  rw [inf_of_le_left hA₀A] at hrA
  have hrW := Subgroup.relIndex_mul_card (W ⊓ Subgroup.centralizer (A : Set Γ)) W
  rw [inf_of_le_left inf_le_left] at hrW
  have hle : A₀ ⊓ W ≤ W ⊓ Subgroup.centralizer (A : Set Γ) := by
    intro x hx
    refine ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact (isElemAbelian_comm' hA.2.1 hx.1.1 ha).symm
  have hpos : 0 < Nat.card ↥(A₀ ⊓ W) := Nat.card_pos
  have h1 : Nat.card ↥A ≤ Nat.card ↥(A₀ ⊔ W) := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card ↥A * Nat.card ↥(A₀ ⊓ W)
        ≤ Nat.card ↥A * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set Γ)) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)
      _ = Nat.card ↥A₀ * Nat.card ↥W := by
          rw [← hrA, ← hrW, hrel]; ring
      _ = Nat.card ↥(A₀ ⊔ W) * Nat.card ↥(A₀ ⊓ W) := hcard.symm
  exact ⟨A₀ ⊔ W, ⟨sup_le (hA₀A.trans hAS) hWS, hel,
    fun B hBS hBe => (hA.2.2 B hBS hBe).trans h1⟩, le_sup_right⟩

theorem commutator_blockW_omegaOneCenter_baum {L S F : Subgroup Γ} (hL : CharTwo L)
    (hS : IsSylowOf 2 S L) (hF : IsBTBlock L S F) (hsub : IsSubnormal F L) :
    ⁅blockW F, omegaOneCenterOf (baum S)⁆ = ⊥ := by
  obtain ⟨A, hA, hWA⟩ := exists_isMaxElemAbelian_ge_blockW hL hS hF hsub
  have hZA : omegaOneCenterOf (baum S) ≤ A := omegaOneCenterOf_baum_le_of_isMaxElemAbelian hA
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro w hw z hz
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact isElemAbelian_comm' hA.2.1 (hWA hw) (hZA hz)

end CFSG.CGT.PushingUpLit.BHS7
