module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

namespace Res

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def CoreAbs (D : Type) [Group D] : Prop :=
  ∃ E : Subgroup D, IsSimpleGroup ↥E ∧ (∃ x y : ↥E, x * y ≠ y * x) ∧
    (∀ T : Subgroup D, ⁅T, T⁆ = T → T ≤ E) ∧ twoPart (Nat.card D) ≤ 2 * twoPart (Nat.card ↥E) ∧
    (IsChevSimple 2 ↥E ∨ Nat.card ↥E = 168)

theorem coreAbs_of_datumCore {D : Type} [Group D] [Finite D] (h : DatumCore D) : CoreAbs D := by
  obtain ⟨E, hs, hna, hperf, hidx, hch⟩ := h
  refine ⟨E, hs, hna, hperf, ?_, hch⟩
  rcases hidx with h | h
  · rw [h]
    have : 1 ≤ twoPart (Nat.card ↥E) := Nat.one_le_two_pow
    omega
  · rw [h]
    unfold twoPart
    rw [Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, pow_add,
      Nat.Prime.factorization_self Nat.prime_two]
    simp

theorem coreSub_of_equiv {S : Type} [Group S] [Finite S] {C : Subgroup S} {D : Type} [Group D]
    (e : ↥C ≃* D) (h : CoreAbs D) : CoreSub C := by
  obtain ⟨E', hs, hna, hperf, h2, hch⟩ := h
  let e1 : ↥E' ≃* ↥(E'.map e.symm.toMonoidHom) :=
    E'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  let e2 : ↥(E'.map e.symm.toMonoidHom) ≃* ↥((E'.map e.symm.toMonoidHom).map C.subtype) :=
    (E'.map e.symm.toMonoidHom).equivMapOfInjective C.subtype C.subtype_injective
  let eE : ↥E' ≃* ↥((E'.map e.symm.toMonoidHom).map C.subtype) := e1.trans e2
  have hcC : Nat.card ↥C = Nat.card D := Nat.card_congr e.toEquiv
  have hcE : Nat.card ↥((E'.map e.symm.toMonoidHom).map C.subtype) = Nat.card ↥E' :=
    (Nat.card_congr eE.toEquiv).symm
  refine ⟨(E'.map e.symm.toMonoidHom).map C.subtype, Subgroup.map_subtype_le _,
    eE.isSimpleGroup_congr.1 hs, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eE x, eE y, fun hh => hxy (eE.injective (by rw [map_mul, map_mul]; exact hh))⟩
  · intro T hTC hTp
    have hTT : (T.subgroupOf C).map C.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTC
    have hT'p : ⁅T.subgroupOf C, T.subgroupOf C⁆ = T.subgroupOf C := by
      apply Subgroup.map_injective C.subtype_injective
      rw [Subgroup.map_commutator, hTT, hTp]
    have hTm : ⁅(T.subgroupOf C).map e.toMonoidHom, (T.subgroupOf C).map e.toMonoidHom⁆ =
        (T.subgroupOf C).map e.toMonoidHom := by
      rw [← Subgroup.map_commutator, hT'p]
    have h1 := hperf _ hTm
    rw [← hTT]
    refine Subgroup.map_mono (fun x hx => ?_)
    exact ⟨e x, h1 ⟨x, hx, rfl⟩, by simp⟩
  · rw [hcE, hcC]
    exact h2
  · rcases hch with hh | hh
    · exact Or.inl (Res.chevSimple_of_equiv eE.symm hh)
    · exact Or.inr (by rw [hcE]; exact hh)

end Res

end FR

end CFSG.LocalAnalysis.GLTheoremA
