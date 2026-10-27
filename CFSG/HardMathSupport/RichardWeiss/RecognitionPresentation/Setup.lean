module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.OrderThreeClass

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.CGT.PushingUpLit.CGT6

variable {S : Type} [Group S]

@[expose] def IsDGen (Y : Subgroup S) (p : S) : Prop :=
  ∃ g : S, Subgroup.zpowers p = Y.map (MulAut.conj g).toMonoidHom

theorem IsDGen.cube {Y : Subgroup S} (hY : Nat.card Y = 3) {p : S} (hp : IsDGen Y p) :
    p ^ 3 = 1 := by
  obtain ⟨g, hg⟩ := hp
  have hcard : Nat.card (Subgroup.zpowers p) = 3 := by
    rw [hg, ← hY]
    exact Nat.card_congr (Subgroup.equivMapOfInjective Y _ (MulAut.conj g).injective).toEquiv.symm
  rw [Nat.card_zpowers] at hcard
  rw [← hcard]
  exact pow_orderOf_eq_one p

theorem IsDGen.ne_one {Y : Subgroup S} (hY : Nat.card Y = 3) {p : S} (hp : IsDGen Y p) :
    p ≠ 1 := by
  intro h
  have h3 := hp.cube hY
  obtain ⟨g, hg⟩ := hp
  have hcard : Nat.card (Subgroup.zpowers p) = 3 := by
    rw [hg, ← hY]
    exact Nat.card_congr (Subgroup.equivMapOfInjective Y _ (MulAut.conj g).injective).toEquiv.symm
  rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hcard
  omega

theorem IsDGen.inv {Y : Subgroup S} {p : S} (hp : IsDGen Y p) : IsDGen Y p⁻¹ := by
  obtain ⟨g, hg⟩ := hp
  exact ⟨g, by rw [Subgroup.zpowers_inv, hg]⟩

theorem IsDGen.conj {Y : Subgroup S} {p : S} (hp : IsDGen Y p) (g : S) :
    IsDGen Y (g⁻¹ * p * g) := by
  obtain ⟨h, hh⟩ := hp
  refine ⟨g⁻¹ * h, ?_⟩
  have : g⁻¹ * p * g = (MulAut.conj g⁻¹).toMonoidHom p := by simp
  rw [this, ← MonoidHom.map_zpowers, hh, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem orderThreeClass_isDGen {Y : Subgroup S} (hY : Nat.card Y = 3)
    (hpair : ∀ g h : S, IsZ3E9A4A5 ↥(pairGen Y g h)) : OrderThreeClass (IsDGen Y) where
  cube := fun _ hp => hp.cube hY
  ne_one := fun _ hp => hp.ne_one hY
  inv := fun _ hp => hp.inv
  conj := fun g _ hp => hp.conj g
  pair := by
    intro p q hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    have hpK : p ∈ pairGen Y g h := by
      refine Subgroup.subset_closure (Or.inl ?_)
      rw [← hg]
      exact Subgroup.mem_zpowers p
    have hqK : q ∈ pairGen Y g h := by
      refine Subgroup.subset_closure (Or.inr ?_)
      rw [← hh]
      exact Subgroup.mem_zpowers q
    have key := PairAlt.of_isZ3E9A4A5 (hpair g h) (p := ⟨p, hpK⟩) (q := ⟨q, hqK⟩)
      (Subtype.ext (by simpa using IsDGen.cube hY ⟨g, hg⟩))
      (Subtype.ext (by simpa using IsDGen.cube hY ⟨h, hh⟩))
    exact PairAlt.map (pairGen Y g h).subtype key

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
