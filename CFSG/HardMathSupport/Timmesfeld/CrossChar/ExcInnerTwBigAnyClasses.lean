module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTwE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldAny
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyPlane

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE

section Small

theorem dvd_pow_sub_one_of_orderOf_eq {p c e : ℕ} (hc : 1 ≤ c)
    (he : orderOf ((c : ℕ) : ZMod p) = e) : p ∣ c ^ e - 1 := by
  have h1 : ((c : ℕ) : ZMod p) ^ e = 1 := by rw [← he]; exact pow_orderOf_eq_one _
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hc)]
  push_cast
  rw [h1, sub_self]

theorem small_field_order_three {p c : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hc : c = 2 ∨ c = 3)
    (he : orderOf ((c : ℕ) : ZMod p) = 3) : (c = 2 ∧ p = 7) ∨ (c = 3 ∧ p = 13) := by
  have hdvd := dvd_pow_sub_one_of_orderOf_eq (by omega) he
  rcases hc with rfl | rfl
  · exact Or.inl ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using hdvd)⟩
  · refine Or.inr ⟨rfl, ?_⟩
    have h26 : p ∣ 2 * 13 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hp).1 h26 with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h

theorem two_le_card_primePower (q : TauCeti.PrimePower) : 2 ≤ q.card := by
  have := Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
  rw [TauCeti.PrimePower.card_def]
  omega

theorem innerPlaneBalanceSmall_three_of {k : LieFamily}
    (h27 : ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid), q.card = 2 →
      InnerPlaneBalance 7 (CatT ⟨excIndex k q, hv⟩))
    (h313 : ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid), q.card = 3 →
      InnerPlaneBalance 13 (CatT ⟨excIndex k q, hv⟩)) : InnerPlaneBalanceSmall k 3 := by
  intro q hv p hp hp7 _ he hq3
  have hq2 := two_le_card_primePower q
  rcases small_field_order_three hp hp7 (by omega) he with ⟨h2, rfl⟩ | ⟨h3, rfl⟩
  · exact h27 q hv h2
  · exact h313 q hv h3

end Small

section FourFive

@[expose] def BigAnyPBigAtFrobenius (τ : Tag) (w : WeylGroup τ) (p : ℕ) (Q : ℕ → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL τ (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (S : LangSetup τ (AlgebraicClosure K) p),
    S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 → Q (Nat.card K) → BigAnyPBig S

theorem setupRigidAtFrobenius_E8_of_anyKind {w : WeylGroup Tag.E8} {p : ℕ} (hp5 : 5 ≤ p)
    {Q : ℕ → Prop} (hP : BigAnyPBigAtFrobenius .E8 w p fun q => Q q ∧ 4 ≤ q)
    (hAK : AnyKindCommute) : SetupRigidAtFrobenius .E8 w p fun q => Q q ∧ 4 ≤ q := by
  intro K _ _ Fr hFr g0 hg0C hg0 S hSD hQK
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hq : S.D.q = Nat.card K := by rw [hSD]; rfl
  have hq4 : 4 ≤ S.D.q := by rw [hq]; exact hQK.2
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 1 (by rw [hq, pow_one])
  have hPS : BigAnyPBig S := hP K Fr hFr g0 hg0C hg0 S hSD hQK
  exact setupRigid_E8 S (by omega) hAlg
    (fun D₁ hD₁ hc => noFrobeniusInnerAny_of_outer .E8 _ p S (by decide)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hD₁ (hasBigAnyComponent_of_pbig S hq4 hPS hD₁ hc))
    (fun D₁ hD₁ hc => centralizerTrivialAny_of_anyKindCommute hAK .E8 _ p S (by decide)
      (by omega) hD₁
      (bigAnyComponentsGenerate_of_pbig S (Or.inr (Or.inr (Or.inr rfl))) hq4 hPS hD₁ hc))

theorem langTorusPlaneBalance_E8_four_five_of_anyKind (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc)
    (hP : BigAnyPBigAtFrobenius .E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1 ∧ 4 ≤ q)
    (hAK : AnyKindCommute)
    (hsmall : LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => q = 2 ∨ q = 3) :
    LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1 := by
  have hbig : LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1 ∧ 4 ≤ q :=
    langTorusPlaneBalance_of_setupRigidAt (Or.inr (Or.inr (Or.inr rfl)))
      (fun K _ _ => commutator_adjointGroup_E8_eq_top K) e8PhiFourWeyl Nat.prime_five
      (fun q _ hQ => ⟨fun h5 => by
        have h1 : 5 ∣ q ^ 2 := Dvd.dvd.mul_left h5 q |>.trans (by rw [sq])
        have h2 := (Nat.dvd_add_right h1).1 hQ.1
        omega, Or.inl le_rfl⟩)
      (setupRigidAtFrobenius_E8_of_anyKind (by norm_num) hP hAK) hsub hin hsu htw hex
  intro K _ _ hQK
  by_cases h4 : 4 ≤ Nat.card K
  · exact hbig K ⟨hQK, h4⟩
  · have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    refine hsmall K ?_
    interval_cases h : Nat.card K
    · exact Or.inl rfl
    · exact Or.inr rfl

end FourFive

end CFSG.HardMathSupport.Timmesfeld.CrossChar
