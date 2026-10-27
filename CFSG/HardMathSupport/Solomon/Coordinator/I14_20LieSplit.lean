module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20BigBM
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator.I1420

@[expose] def Fi22LieAbs : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ (idx : TauCeti.ValidLieTypeIndex), Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ α : MulAut S, α ^ 5 = 1 → α ≠ 1 → ¬ Fi22Cfg S α

@[expose] def Fi22LieSS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ (idx : TauCeti.ValidLieTypeIndex), Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      idx.1.characteristic ≠ 5 →
      ∀ x : S, x ^ 5 = 1 → x ≠ 1 → ¬ Fi22Cfg S (MulAut.conj x)

@[expose] def Fi22LieUnip : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ (idx : TauCeti.ValidLieTypeIndex), Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      idx.1.characteristic = 5 →
      ∀ x : S, x ^ 5 = 1 → x ≠ 1 → ¬ Fi22Cfg S (MulAut.conj x)

@[expose] def Fi22LieOuter : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ (idx : TauCeti.ValidLieTypeIndex), Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      5 ∣ Nat.card (Outer S) →
      ∀ α : MulAut S, α ^ 5 = 1 → (∀ a : S, MulAut.conj a ≠ α) → ¬ Fi22Cfg S α

theorem five_dvd_card_outer_of_not_inner {S : Type} [Group S] {α : MulAut S} (h5 : α ^ 5 = 1)
    (hn : ∀ a : S, MulAut.conj a ≠ α) : 5 ∣ Nat.card (Outer S) := by
  have h5' : (QuotientGroup.mk α : Outer S) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow, h5]
    rfl
  have hne : (QuotientGroup.mk α : Outer S) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    obtain ⟨a, ha⟩ := h
    exact hn a ha
  have hord : orderOf (QuotientGroup.mk α : Outer S) = 5 := orderOf_eq_prime h5' hne
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem fi22LieAbs_of_split (hSS : Fi22LieSS) (hUn : Fi22LieUnip) (hOut : Fi22LieOuter) :
    Fi22LieAbs := by
  intro S _ _ _ hnab idx hidx α h5 h1
  by_cases hα : ∃ a : S, MulAut.conj a = α
  · obtain ⟨x, rfl⟩ := hα
    have hZ := center_eq_bot_of_simple hnab
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact h1 (map_one _)
    have hx5 : x ^ 5 = 1 := by
      have hmem : x ^ 5 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun β : MulAut S => β g) (show MulAut.conj (x ^ 5) = 1 by
          rw [map_pow, h5])
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    by_cases hp : idx.1.characteristic = 5
    · exact hUn S hnab idx hidx hp x hx5 hx1
    · exact hSS S hnab idx hidx hp x hx5 hx1
  · push Not at hα
    exact hOut S hnab idx hidx (five_dvd_card_outer_of_not_inner h5 hα) α h5 hα

section Certificates


theorem input14_20_7_of_lieAbs
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hBM : NoOrderSixtyFiveBM) (hLie : Fi22LieAbs) : Input14_20_7 := by
  have hBig : Fi22FiveCentBig :=
    fi22FiveCentBig_of_noOrderSixtyFive (noOrderSixtyFive_of_BM hbr hBM)
  intro Y _ _ K hq hK _ x hx hnc h5 J hJ hFi
  obtain ⟨α, hα5, hα1, hcfg⟩ := fi22Cfg_of_component K hq hx hnc h5 hJ hFi
  obtain ⟨hnab, i, ⟨e⟩⟩ := catalog_of_quasisimple hq hK
  have hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hα'5 : MulAut.congr e α ^ 5 = 1 := by
    rw [← map_pow, hα5, map_one]
  cases i with
  | cyclic q hq =>
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact noFi22Cfg_alt n hn _ hα'5 (Fi22Cfg.of_mulEquiv e hcfg)
  | lie idx =>
    exact hLie _ hnab idx ⟨e⟩ α hα5 hα1 hcfg
  | sporadic s =>
    exact noFi22Cfg_sporadic hbr hOutS hBig hnab s e α hα5 hα1 hcfg

theorem input14_20_7_of_split_BM
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hBM : NoOrderSixtyFiveBM) (hSS : Fi22LieSS) (hUn : Fi22LieUnip) (hOut : Fi22LieOuter) :
    Input14_20_7 :=
  input14_20_7_of_lieAbs hbr hOutS hBM (fi22LieAbs_of_split hSS hUn hOut)

end Certificates

end CFSG.HardMathSupport.Solomon.Coordinator
