module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Aut
public import CFSG.ClassicalInvolution.Q3.Q3T6MainStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4
  CFSG.ClassicalInvolution.Q3.Q3T6X CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement MatrixGroups


section Lift

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem satU_eq_of_oddCore_eq_bot {L : Subgroup X} {u : X}
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥) :
    satU (.sl2 3 1) L u = L := by
  rw [satU_of_isSolvableType solvableType_three, hO, sup_bot_eq]

theorem oddCore_lift_eq_bot {J L : Subgroup X} {u : X} (h : IsLiftOf J L u)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥) :
    classicalInvolutionOddCore ↥L = ⊥ :=
  h.member.oddCore_eq_bot_of_centralizer (by rw [Balance.involutionOddCore_eq_oddCoreIn]; exact hO)

theorem map_lift_eq (hΩ : HypOmegaGen Φ) {J L : Subgroup X} {u : X} (hJ : J ∈ Φ)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥) (hL : IsLiftOf J L u)
    (σ : X ≃* X) (hσ : ∀ j ∈ J, σ j = j) : L.map σ.toMonoidHom = L := by
  have hu : σ u = u := hσ u hL.inv.mem
  have hL' : IsLiftOf J (L.map σ.toMonoidHom) u :=
    { inv := hL.inv
      le := fun j hj => ⟨j, hL.le hj, hσ j hj⟩
      member := by simpa [hu] using hL.member.map_mulEquiv σ }
  have h1 := satU_mem_liftFam hJ hL
  have h2 := satU_mem_liftFam hJ hL'
  rw [satU_eq_of_oddCore_eq_bot hO] at h1 h2
  exact (liftFam_eq_of_le hΩ h1 h2 hJ hL.le hL'.le).symm

theorem exists_lifted_pair (hΩ : HypOmegaGen Φ) {J₁ J₂ : Subgroup X} (h₁ : J₁ ∈ Φ) (h₂ : J₂ ∈ Φ)
    (hJ₁2 : IsPGroup 2 J₁) (hJ₂2 : IsPGroup 2 J₂)
    (hq₁ : Nonempty (↥J₁ ≃* QuaternionGroup 2)) (hq₂ : Nonempty (↥J₂ ≃* QuaternionGroup 2))
    {u : X} (hu₁ : IsUniqueInvolution J₁ u) (hu₂ : IsUniqueInvolution J₂ u)
    (hl₁ : ∃ L : Subgroup X, IsLiftOf J₁ L u) (hl₂ : ∃ L : Subgroup X, IsLiftOf J₂ L u)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥)
    (hne : J₁ ≠ J₂) (σ : X ≃* X)
    (hσ₁ : ∀ j ∈ J₁, σ j = j) (hσ₂ : ∀ j ∈ J₂, σ j = j) :
    ∃ L₁ L₂ : Subgroup X, IsClassicalMember3 L₁ u ∧ IsClassicalMember3 L₂ u ∧ J₁ ≤ L₁ ∧
      J₂ ≤ L₂ ∧ L₁ ≠ L₂ ∧ (∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) ∧ (∀ l ∈ L₁, σ l = l) ∧
        (∀ l ∈ L₂, σ l = l) := by
  obtain ⟨L₁, hL₁⟩ := hl₁
  obtain ⟨L₂, hL₂⟩ := hl₂
  have hm₁ : L₁ ∈ liftFam Φ := by
    have := satU_mem_liftFam h₁ hL₁
    rwa [satU_eq_of_oddCore_eq_bot hO] at this
  have hm₂ : L₂ ∈ liftFam Φ := by
    have := satU_mem_liftFam h₂ hL₂
    rwa [satU_eq_of_oddCore_eq_bot hO] at this
  have hOL₁ := oddCore_lift_eq_bot hL₁ hO
  have hOL₂ := oddCore_lift_eq_bot hL₂ hO
  have hne' : L₁ ≠ L₂ := by
    intro heq
    have hs₁ := isSylow2In_of_le_liftFam hΩ h₁ hJ₁2 hm₁ hL₁.le
    have hs₂ := isSylow2In_of_le_liftFam hΩ h₂ hJ₂2 hm₁ (heq ▸ hL₂.le)
    exact hne (eq_of_isSylow2In_of_oddCore_eq_bot hL₁.member hOL₁ hs₁ hs₂)
  have hc := Q3T6.comm_le_oddCore_of_twin_u (hypOmegaModU_liftFam hΩ.conjInvariant) hm₁ hm₂ hne'
    (isUniqueInvolution_liftFam_of_le hm₁ hu₁ hL₁.le)
    (isUniqueInvolution_liftFam_of_le hm₂ hu₂ hL₂.le)
  have hoc₁ : oddCoreOf L₁ = ⊥ := by
    unfold oddCoreOf
    rw [hOL₁, Subgroup.map_bot]
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
    intro a ha b hb
    have h0 : ⁅a, b⁆ ∈ (⊥ : Subgroup X) :=
      hoc₁ ▸ (hc (Subgroup.commutator_mem_commutator ha hb)).1
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h0)
  have fix : ∀ {J L : Subgroup X}, J ∈ Φ → IsUniqueInvolution J u → IsLiftOf J L u →
      L ∈ liftFam Φ → IsPGroup 2 J → Nonempty (↥J ≃* QuaternionGroup 2) →
      (∀ j ∈ J, σ j = j) → ∀ l ∈ L, σ l = l := by
    intro J L hJ hu hL hmL hJ2 hq hσ
    have hOL := oddCore_lift_eq_bot hL hO
    have hmap := map_lift_eq hΩ hJ hO hL σ hσ
    have hsyl : IsSylow2In J L := isSylow2In_of_le_liftFam hΩ hJ hJ2 hmL hL.le
    obtain ⟨e⟩ := hq
    have hJc : Nat.card J = 8 := by
      rw [Nat.card_congr e.toEquiv, natCard_quaternionGroup_two]
    obtain ⟨e'⟩ := hL.member.nonempty_equiv_sl2 hOL
    obtain ⟨y, hyL, hy3, hLgen, hyact⟩ := exists_gen_of_sl2 e' hL.le hJc
    have hQn : ∀ l ∈ L, ∀ q ∈ J, l * q * l⁻¹ ∈ J := by
      intro l hl q hq
      have hs' := hsyl.conj l
      rw [conjSub_eq_self_of_mem hl] at hs'
      have hconj : conjSub l J = J := eq_of_isSylow2In_of_oddCore_eq_bot hL.member hOL hs' hsyl
      rw [← hconj]
      exact conj_mem_conjSub hq
    exact fixed_of_normalizes_q8 σ.toMonoidHom hL.le hQn e hLgen hy3 hyact hu.mem hu.ne_one hu.sq
      (fun l hl => hmap ▸ Subgroup.mem_map_of_mem σ.toMonoidHom hl) hσ
  exact ⟨L₁, L₂, hL₁.member, hL₂.member, hL₁.le, hL₂.le, hne', hcomm,
    fix h₁ hu₁ hL₁ hm₁ hJ₁2 hq₁ hσ₁, fix h₂ hu₂ hL₂ hm₂ hJ₂2 hq₂ hσ₂⟩

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
