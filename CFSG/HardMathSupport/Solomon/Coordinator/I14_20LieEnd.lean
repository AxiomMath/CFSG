module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieSplit
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator.I1420

@[expose] def Fi22IsLie : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex, Nonempty (Fi22G ≃* (TauCeti.CFSGIndex.lie idx).Group)

@[expose] def LieOrderBridge : Prop :=
  ∀ (idx : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G],
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie idx).Group) → Nat.card G = lieOrderFormula idx.1

@[expose] def Fi22LieSSC : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ (idx : TauCeti.ValidLieTypeIndex), Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      idx.1.characteristic ≠ 5 →
      ∀ x : S, x ^ 5 = 1 → x ≠ 1 → Fi22Cfg S (MulAut.conj x) → Fi22IsLie

@[expose] def Fi22LieUnipC : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ (idx : TauCeti.ValidLieTypeIndex), Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      idx.1.characteristic = 5 →
      ∀ x : S, x ^ 5 = 1 → x ≠ 1 → Fi22Cfg S (MulAut.conj x) → Fi22IsLie

@[expose] def Fi22LieOuterC : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ (idx : TauCeti.ValidLieTypeIndex), Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      5 ∣ Nat.card (Outer S) →
      ∀ α : MulAut S, α ^ 5 = 1 → (∀ a : S, MulAut.conj a ≠ α) → Fi22Cfg S α → Fi22IsLie

section Certificates


theorem not_fi22IsLie (hb : LieOrderBridge) : ¬ Fi22IsLie := by
  rintro ⟨idx, ⟨e⟩⟩
  obtain ⟨-, hcard⟩ := fi22_facts
  have hfin : Finite Fi22G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h1 : Nat.card Fi22G = lieOrderFormula idx.1 := hb idx Fi22G ⟨e⟩
  apply lieOrderFormula_ne_fi22Ord idx.2
  rw [← h1, hcard]
  rfl

theorem fi22LieSS_of_comp (hb : LieOrderBridge) (h : Fi22LieSSC) : Fi22LieSS :=
  fun S _ _ _ hnab idx hidx hp x hx5 hx1 hcfg =>
    not_fi22IsLie hb (h S hnab idx hidx hp x hx5 hx1 hcfg)

theorem fi22LieUnip_of_comp (hb : LieOrderBridge) (h : Fi22LieUnipC) : Fi22LieUnip :=
  fun S _ _ _ hnab idx hidx hp x hx5 hx1 hcfg =>
    not_fi22IsLie hb (h S hnab idx hidx hp x hx5 hx1 hcfg)

theorem fi22LieOuter_of_comp (hb : LieOrderBridge) (h : Fi22LieOuterC) : Fi22LieOuter :=
  fun S _ _ _ hnab idx hidx h5 α hα5 hα hcfg =>
    not_fi22IsLie hb (h S hnab idx hidx h5 α hα5 hα hcfg)


theorem input14_20_7_of_comp_BM
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hBM : NoOrderSixtyFiveBM) (hb : LieOrderBridge)
    (hSS : Fi22LieSSC) (hUn : Fi22LieUnipC) (hOut : Fi22LieOuterC) : Input14_20_7 :=
  input14_20_7_of_split_BM hbr hOutS hBM (fi22LieSS_of_comp hb hSS)
    (fi22LieUnip_of_comp hb hUn) (fi22LieOuter_of_comp hb hOut)

end Certificates

end CFSG.HardMathSupport.Solomon.Coordinator
