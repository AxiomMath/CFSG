module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Outer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Defs

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem hyp31Row_fi23 (pf : FiPinned) : Hyp31Row IsKFi23 (IsLS [.Fi24Prime]) := by
  have hfin24 : Finite (Carrier .Fi24Prime) :=
    Nat.finite_of_card_ne_zero (by have := pf.orders.2; omega)
  exact
  { isK_inv := fun X Y _ _ e ⟨hf, hq, ⟨f⟩⟩ =>
      ⟨Finite.of_equiv X e.toEquiv, CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq,
        ⟨(quotientCenterEquiv' e).symm.trans f⟩⟩
    isL_inv := fun _ _ _ _ e h => isLS_of_mulEquiv e h
    quasi_K := fun X _ ⟨hf, hq, hc⟩ => by
      have := hf
      exact ⟨hq, pf.rank23 X hq hc⟩
    quasi_L := by
      intro X _ hX
      obtain ⟨s', hs', hq, hodd, ⟨f⟩⟩ := hX
      obtain rfl : s' = .Fi24Prime := List.mem_singleton.1 hs'
      have hZfin : Finite (center X) := Nat.finite_of_card_ne_zero hodd.pos.ne'
      have hQfin : Finite (X ⧸ center X) := Finite.of_equiv _ f.symm.toEquiv
      have : Finite X := Finite.of_subgroup_quotient (center X)
      refine ⟨hq, le_antisymm (le_sSup ⟨inferInstance, hodd⟩)
        (oddCore_le_center_of_isQuasisimple hq), pf.rank24 X hq ⟨f⟩⟩
    K_not_exc := fun X _ ⟨_, _, hc⟩ => pf.notExc23 _ hc
    K_ne_L := by
      intro X Y _ _ hX hY ⟨e⟩
      obtain ⟨s', hs', hq, -, ⟨f⟩⟩ := hX
      obtain rfl : s' = .Fi24Prime := List.mem_singleton.1 hs'
      obtain ⟨-, hQq, ⟨g⟩⟩ := hY
      have hsimpX := hq.2.1
      have hsimp : IsSimpleGroup (Y ⧸ center Y) := MulEquiv.isSimpleGroup e.symm
      have hOZ : CFSG.oddCore Y ≤ center Y := by
        have hW : ((CFSG.oddCore Y).map (QuotientGroup.mk' (center Y))).Normal :=
          Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
        have := hsimp
        have := hW
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          ((CFSG.oddCore Y).map (QuotientGroup.mk' (center Y))) with h | h
        · intro o ho
          have : QuotientGroup.mk' (center Y) o ∈
              (CFSG.oddCore Y).map (QuotientGroup.mk' (center Y)) := ⟨o, ho, rfl⟩
          rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
          exact this
        · exfalso
          refine false_of_commute_quasisimple hQq fun a b => ?_
          have hc : ∀ y : Y, ∃ z ∈ center Y, (QuotientGroup.mk y : Y ⧸ CFSG.oddCore Y) =
              QuotientGroup.mk z := by
            intro y
            have hy : QuotientGroup.mk' (center Y) y ∈
                (CFSG.oddCore Y).map (QuotientGroup.mk' (center Y)) := by
              rw [h]
              exact Subgroup.mem_top _
            obtain ⟨o, ho, hoy⟩ := hy
            have hz : o⁻¹ * y ∈ center Y := QuotientGroup.eq.1 hoy
            refine ⟨o⁻¹ * y, hz, ?_⟩
            rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (o⁻¹)).2 (Subgroup.inv_mem _ ho),
              one_mul]
          obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective b
          obtain ⟨z, hz, hyz⟩ := hc y
          rw [hyz, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz y']
      have : Group.IsPerfect (Y ⧸ CFSG.oddCore Y) := hQq.1
      let π : (Y ⧸ CFSG.oddCore Y) →* (Y ⧸ center Y) :=
        QuotientGroup.map (CFSG.oddCore Y) (center Y) (MonoidHom.id Y) hOZ
      have hπ : Function.Surjective π := by
        intro z
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
        exact ⟨QuotientGroup.mk y, rfl⟩
      have hker : π.ker ≤ center (Y ⧸ CFSG.oddCore Y) := by
        intro x hx
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
        have hy : y ∈ center Y := (QuotientGroup.eq_one_iff y).1 hx
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective w
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hy y']
      obtain ⟨h1⟩ := cqEquiv_of_central_cover π hπ hker
      have hZ₀ : center (X ⧸ center X) = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (X ⧸ center X)) with h | h
        · exact h
        · exfalso
          obtain ⟨a, b, hab⟩ := hq.2.2
          exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
      let e₀ : ((X ⧸ center X) ⧸ center (X ⧸ center X)) ≃* (X ⧸ center X) :=
        (QuotientGroup.quotientMulEquivOfEq hZ₀).trans QuotientGroup.quotientBot
      have h2 : (Carrier .Fi23) ≃* (Carrier .Fi24Prime) :=
        g.symm.trans (h1.trans ((quotientCenterEquiv' e).symm.trans (e₀.trans f)))
      have h3 := Nat.card_congr h2.toEquiv
      have h4 := pf.orders.2
      omega }

end CFSG.EvenSporadicStandard.Induction.Fi.V3
