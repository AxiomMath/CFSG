module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.BadThreeLang
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE8
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.FiveCharE8

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

set_option linter.unusedSectionVars false

section Rigid

variable {τ : Tag} (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup τ}
  {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
  (hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
  {p : ℕ} (S : LangSetup τ (AlgebraicClosure K) p)
  (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)

include hSD in
theorem steinbergLang_descends (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : S.Descends := by
  have hd := langDescent_ofFrobenius hτ w K hFr hg0C hg0
  rw [← hSD] at hd
  have hι : Function.Injective
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  exact ⟨K, inferInstance, inferInstance, inferInstance, hd.mulEquiv' hι,
    (steinbergLang_q_eq K hFr hg0C hg0 S hSD).symm, fun x => hd.coe_mulEquiv' hι x⟩

include hSD in
theorem steinbergLang_setupRigid_E78 (hτ : τ = .E7 ∨ τ = .E8) (hp : p.Prime)
    (hst : ∀ b : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (hqp : Nat.card K % p = 1 ∨ Nat.card K % p = p - 1) (hK4 : 4 ≤ Nat.card K) :
    SetupRigid S := by
  have hτG : τ ≠ .G2 := by rcases hτ with rfl | rfl <;> decide
  have hsl : SimplyLacedTag τ := by
    rcases hτ with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hdeg : entryDegreeBound τ < Nat.card K := by
    unfold entryDegreeBound
    split_ifs with h
    · exact absurd h hτG
    · omega
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  refine setupRigid_of_descends_E78 S hτ (steinbergLang_descends K hFr hg0C hg0 S hSD hτ')
    (fun D₁ hD₁ hc => ?_) (fun D₁ hD₁ hc => ?_)
  · exact steinbergLang_noFrobeniusInner K hFr hg0C hg0 S hSD hτG hp hst hw₀ hqp hK4
      (Or.inr hsl) hD₁ hc
  · exact steinbergLang_centralizerTrivial K hFr hg0C hg0 S hSD hp hst hw₀ hqp hK4 hdeg hD₁ hc

end Rigid

section Balance

theorem steinbergLang_langTorusPlaneBalance_E78 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime)
    (hst : ∀ (L : Type) [Field L] (b : Fin τ.rank → Lˣ), (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {Q : ℕ → Prop}
    (hQ : ∀ q, 2 ≤ q → Q q → (q % p = 1 ∨ q % p = p - 1) ∧ 4 ≤ q)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) (w : WeylGroup τ) :
    LangTorusPlaneBalance τ w p Q := by
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  refine langTorusPlaneBalance_of_setupRigidAt hτ'
    (fun K _ _ => commutator_adjointGroup_exc_eq_top hτ' K) w hp (fun q hq2 hQq => ?_)
    (fun K _ _ Fr hFr g0 hg0C hg0 S hSD hQK => ?_) hsub hin hsu htw hex
  · obtain ⟨hqp, hq4⟩ := hQ q hq2 hQq
    refine ⟨fun hdvd => ?_, Or.inr hq4⟩
    obtain ⟨c, rfl⟩ := hdvd
    rw [Nat.mul_mod_right] at hqp
    have := hp.two_le
    omega
  · have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
    obtain ⟨hqp, hq4⟩ := hQ _ Finite.one_lt_card hQK
    exact steinbergLang_setupRigid_E78 K hFr hg0C hg0 S hSD hτ hp (hst _) hw₀ hqp hq4

theorem steinbergLang_langTorusPlaneBalance_E8_three
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) (w : WeylGroup Tag.E8) :
    LangTorusPlaneBalance Tag.E8 w 3 ThreeLargeQ :=
  steinbergLang_langTorusPlaneBalance_E78 (Or.inr rfl) Nat.prime_three
    (fun _ _ b hb => (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three b
      hb).le) e8Neg_smul (fun q hq2 hQ => by
        obtain ⟨h3, h2, h4⟩ := hQ
        exact ⟨by omega, by omega⟩) hsub hin hsu htw hex w

theorem steinbergLang_langTorusPlaneBalance_E7_three
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) (w : WeylGroup Tag.E7) :
    LangTorusPlaneBalance Tag.E7 w 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2 :=
  steinbergLang_langTorusPlaneBalance_E78 (Or.inl rfl) Nat.prime_three
    (fun _ _ b hb => (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three b
      hb).le) e7Neg_smul (fun q hq2 hQ => by
        obtain ⟨h3, h2⟩ := hQ
        exact ⟨by omega, by omega⟩) hsub hin hsu htw hex w

theorem steinbergLang_langTorusPlaneBalance_E8_five_split
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) (w : WeylGroup Tag.E8) :
    LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q - 1 :=
  steinbergLang_langTorusPlaneBalance_E78 (Or.inr rfl) Nat.prime_five
    (fun _ _ b hb => (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five b
      hb).le) e8Neg_smul (fun q hq2 hQ => ⟨by omega, by omega⟩) hsub hin hsu htw hex w

theorem steinbergLang_langTorusPlaneBalance_E8_five_neg
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) (w : WeylGroup Tag.E8) :
    LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q + 1 :=
  steinbergLang_langTorusPlaneBalance_E78 (Or.inr rfl) Nat.prime_five
    (fun _ _ b hb => (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five b
      hb).le) e8Neg_smul (fun q hq2 hQ => ⟨by omega, by omega⟩) hsub hin hsu htw hex w

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar
