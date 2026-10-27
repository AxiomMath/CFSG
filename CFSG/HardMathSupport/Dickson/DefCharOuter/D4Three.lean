module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.D4ThreeGraph
import CFSG.HardMathSupport.Dickson.DefCharOuter.D4ThreeAux.Model
import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint.Chevalley

private theorem mulAut_congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.conj_apply]


theorem lieDefCharOuter_D4_three (h1 : D4ThreeGraphOuter) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    (hp3 : p = 3)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β ∨ CFSG.Open.GLAPPrimeCoreOf p (fixSubgroup β) = ⊥ := by
  subst hp3
  have hq3 : q.p = 3 := hpc.symm
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent (by have := q.exponent_pos; omega),
      TauCeti.PrimePower.card_def]
  haveI : CharP (GaloisField q.p q.exponent) 3 := CharP.congr q.p hq3
  have hK3 : Nat.card (GaloisField q.p q.exponent) = 3 ^ q.exponent := by
    rw [hcard, TauCeti.PrimePower.card_def, hq3]
  obtain ⟨br⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_adjointQuotient_D4_equiv
    (GaloisField q.p q.exponent) q hv hcard
  let φ : S ≃* adjointGroup Tag.D4 (GaloisField q.p q.exponent) :=
    (e.trans br.symm).trans ((QuotientGroup.quotientMulEquivOfEq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)
  haveI : Finite (adjointGroup Tag.D4 (GaloisField q.p q.exponent)) := Finite.of_equiv S φ.toEquiv
  have hβ' : MulAut.congr φ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : MulAut.congr φ β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup Tag.D4 (GaloisField q.p q.exponent)) := by
    rintro ⟨y, hy⟩
    apply hout (φ.symm y)
    apply (MulAut.congr φ).injective
    rw [mulAut_congr_conj, φ.apply_symm_apply]
    exact hy
  rcases D4ThreeAux.perfectInLayer_or_core_adjointD4_three h1 q.exponent_pos
      (GaloisField q.p q.exponent) hK3 (MulAut.congr φ β) hβ' hout' with h | h
  · exact .inl (LieSemisimple.perfectInLayer_of_congr φ β h)
  · refine .inr ?_
    have hle := map_glaPPrimeCoreOf_fixSubgroup_le (φ : S →* _)
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 φ.injective]; exact bot_le) β (MulAut.congr φ β)
      (fun k => by simp [MulAut.congr_apply]) φ.surjective hp
    rw [h, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 hle

end CFSG.HardMathSupport.Dickson.DefCharOuter
