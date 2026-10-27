module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveQFix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Visible
  CFSG.Monster.ScalarKernel CFSG.HardMathSupport.Dickson.I271.TabMFive

private theorem card_le_two_mul_of_quot {G V : Type*} [Group G] [Finite G] {Z : Subgroup G}
    (hZ : Nat.card Z = 2) (φ : G ⧸ Z → V) (hφ : Function.Bijective φ) (A : G → Prop)
    (B : V → Prop) (hAB : ∀ g, A g → B (φ (QuotientGroup.mk g))) :
    Nat.card {g // A g} ≤ 2 * Nat.card {v // B v} := by
  classical
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Z)).1 hZ
  have hfib : ∀ a b c : G, (QuotientGroup.mk a : G ⧸ Z) = QuotientGroup.mk b →
      (QuotientGroup.mk a : G ⧸ Z) = QuotientGroup.mk c → a ≠ b → a ≠ c → b = c := by
    intro a b c hab hac hb hc
    have h1 : (⟨a⁻¹ * b, QuotientGroup.eq.1 hab⟩ : Z) = y :=
      hy _ fun h => hb (inv_mul_eq_one.1 (congrArg Subtype.val h))
    have h2 : (⟨a⁻¹ * c, QuotientGroup.eq.1 hac⟩ : Z) = y :=
      hy _ fun h => hc (inv_mul_eq_one.1 (congrArg Subtype.val h))
    exact mul_left_cancel (congrArg Subtype.val (h1.trans h2.symm))
  obtain ⟨f, hf⟩ : ∃ f : {g // A g} → {x : G ⧸ Z // B (φ x)},
      ∀ g, (f g).1 = QuotientGroup.mk g.1 :=
    ⟨fun g => ⟨_, hAB g.1 g.2⟩, fun g => rfl⟩
  have hc : Nat.card {x : G ⧸ Z // B (φ x)} = Nat.card {v // B v} :=
    Nat.card_congr ((Equiv.ofBijective φ hφ).subtypeEquiv fun _ => Iff.rfl)
  rcases isEmpty_or_nonempty {g // A g} with hX | hX
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  refine (Nat.card_le_card_of_injective (fun g => (f g, decide (g = Function.invFun f (f g))))
    fun g g' h => ?_).trans_eq ?_
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [h1, decide_eq_decide] at h2
    have hs : f (Function.invFun f (f g')) = f g' := Function.invFun_eq ⟨g', rfl⟩
    by_cases hg : g = Function.invFun f (f g')
    · exact hg.trans (h2.1 hg).symm
    · have hg' : g' ≠ Function.invFun f (f g') := fun h => hg (h2.2 h)
      have e1 := (hf _).symm.trans ((congrArg Subtype.val (hs.trans h1.symm)).trans (hf g))
      have e2 := (hf _).symm.trans ((congrArg Subtype.val hs).trans (hf g'))
      exact Subtype.ext (hfib _ _ _ e1 e2 (fun h => hg (Subtype.ext h).symm)
        (fun h => hg' (Subtype.ext h).symm))
  · rw [Nat.card_prod, hc, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

private theorem natCard_center_Q : Nat.card (Subgroup.center Q) = 2 :=
  (congrArg (fun H : Subgroup Q => Nat.card H) center_Q).trans natCard_zpowers_zQ

private theorem phi_mk_fixed {ι : Type*} (S : ι → Prop) (P : ι → Pvis) (r : Q)
    (hr : ∀ i, S i → conjQ (P i) r = r) (i : ι) (hi : S i) :
    modTwoEnd (P i).1.2 (Multiplicative.toAdd (phi (QuotientGroup.mk r))) =
      Multiplicative.toAdd (phi (QuotientGroup.mk r)) :=
  ((congrArg (fun q : Q => Multiplicative.toAdd (phi (QuotientGroup.mk q))) (hr i hi)).symm.trans
    (phi_conjQ (P i) r)).symm

theorem card_fixed_conjQ_family_le {ι : Type*} (S : ι → Prop) (P : ι → Pvis) :
    Nat.card {r : Q // ∀ i, S i → conjQ (P i) r = r} ≤
      2 * Nat.card {v : L2 // ∀ i, S i → modTwoEnd (P i).1.2 v = v} :=
  haveI : Finite Q :=
    Nat.finite_of_card_ne_zero (natCard_Q.trans_ne (pow_ne_zero 25 two_ne_zero))
  card_le_two_mul_of_quot natCard_center_Q (fun x => Multiplicative.toAdd (phi x))
    (Multiplicative.toAdd.bijective.comp phi.bijective)
    (fun r => ∀ i, S i → conjQ (P i) r = r) (fun v => ∀ i, S i → modTwoEnd (P i).1.2 v = v)
    fun r hr i hi => phi_mk_fixed S P r hr i hi

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
