module

public import CFSG.Monster.Visible.Pair

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Visible
  CFSG.Monster.ScalarKernel

theorem card_le_mul_of_hom {T A : Type*} [Group T] [Group A] [Finite T] [Finite A]
    (ψ : T →* A) (F : Set A) (hF : ∀ t, ψ t ∈ F) {m : ℕ} (hm : Nat.card ψ.ker ≤ m) :
    Nat.card T ≤ m * Nat.card F := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h1
  have h2 : Nat.card ψ.range ≤ Nat.card F :=
    Nat.card_le_card_of_injective (fun x => ⟨(x : A), by
      obtain ⟨t, ht⟩ := x.2
      rw [← ht]
      exact hF t⟩) (fun x y h => Subtype.ext (by
      have h' := congrArg Subtype.val h
      exact h'))
  rw [h1, mul_comm]
  exact Nat.mul_le_mul hm h2

theorem card_fixed_conjQ_le (p : Pvis) :
    Nat.card {r : Q // conjQ p r = r} ≤ 2 * Nat.card {v : L2 // modTwoEnd p.1.2 v = v} := by
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [natCard_Q]; norm_num)
  haveI : Finite (Multiplicative L2) := Finite.of_equiv _ phi.toEquiv
  obtain ⟨T, hT⟩ : ∃ T : Subgroup Q, ∀ r, r ∈ T ↔ conjQ p r = r :=
    ⟨{ carrier := {r | conjQ p r = r}
       mul_mem' := fun {a b} ha hb => by
         have ha' : conjQ p a = a := ha
         have hb' : conjQ p b = b := hb
         show conjQ p (a * b) = a * b
         rw [map_mul, ha', hb']
       one_mem' := by
         show conjQ p 1 = 1
         exact map_one _
       inv_mem' := fun {a} ha => by
         have ha' : conjQ p a = a := ha
         show conjQ p a⁻¹ = a⁻¹
         rw [map_inv, ha'] }, fun r => Iff.rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : T →* Multiplicative L2, ∀ t : T, ψ t = phi (QuotientGroup.mk (t : Q)) :=
    ⟨(phi.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))).comp T.subtype,
      fun t => rfl⟩
  have hF : ∀ t : T, ψ t ∈ {a : Multiplicative L2 |
      modTwoEnd p.1.2 (Multiplicative.toAdd a) = Multiplicative.toAdd a} := by
    intro t
    have ht : conjQ p (t : Q) = (t : Q) := (hT _).1 t.2
    have h1 := phi_conjQ p (t : Q)
    have key : Multiplicative.toAdd (phi (QuotientGroup.mk (conjQ p (t : Q)))) =
        Multiplicative.toAdd (phi (QuotientGroup.mk (t : Q))) :=
      congrArg (fun r : Q => Multiplicative.toAdd (phi (QuotientGroup.mk r))) ht
    have h4 := h1.symm.trans key
    show modTwoEnd p.1.2 (Multiplicative.toAdd (ψ t)) = Multiplicative.toAdd (ψ t)
    rw [hψ t]
    exact h4
  have hker : Nat.card ψ.ker ≤ 2 := by
    have hc : Nat.card (Subgroup.center Q) = 2 := by
      rw [center_Q, Nat.card_zpowers, orderOf_zQ]
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : ψ.ker => (⟨((x : T) : Q), ?_⟩ : Subgroup.center Q)) ?_) hc.le
    · have hx : ψ (x : T) = 1 := x.2
      rw [hψ] at hx
      exact (QuotientGroup.eq_one_iff _).1 ((MulEquiv.map_eq_one_iff phi).1 hx)
    · intro x y h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
  have h := card_le_mul_of_hom ψ _ hF hker
  have e1 : Nat.card {r : Q // conjQ p r = r} = Nat.card T :=
    Nat.card_congr (Equiv.subtypeEquivRight fun r => (hT r).symm)
  have e2 : Nat.card {a : Multiplicative L2 |
      modTwoEnd p.1.2 (Multiplicative.toAdd a) = Multiplicative.toAdd a} =
      Nat.card {v : L2 // modTwoEnd p.1.2 v = v} :=
    Nat.card_congr (Multiplicative.toAdd.subtypeEquiv fun a => Iff.rfl)
  rw [e1, ← e2]
  exact h

end CFSG.HardMathSupport.Dickson.I271.TabMFive
