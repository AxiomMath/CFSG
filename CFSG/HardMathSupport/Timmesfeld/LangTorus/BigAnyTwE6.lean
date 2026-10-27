module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveSpringer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6Three
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRigid

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

section Commute

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem commute_adjointGroup_of_bigAnyGenerate (hAK : AnyKindCommute) (S : LangSetup τ L p)
    (hτ : τ ≠ .G2) (hq3 : 3 ≤ S.D.q) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E)
    (hgen : BigAnyComponentsGenerate S D₁) {z : ModGL τ L}
    (hz : ∀ x ∈ bigComponentSet S D₁, Commute z x) :
    ∀ g ∈ adjointGroup τ L, Commute z g := by
  have hle : rootSpan τ L (bigAnyRoots S D₁) ≤ Subgroup.centralizer {z} := by
    refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨a, haD, ha1, i, hbig, hQ, hγi⟩ := hγ
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hAK τ L p S hτ a (hD₁E haD) i hq3 hQ z (fun x hx => hz x ⟨a, haD, ha1, i, hbig, hx⟩) _
        (pinnedX_mem_rootSpan hγi c)).symm.eq
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (hgen hg))).symm

theorem centralizerTrivial_of_bigAnyGenerate (hAK : AnyKindCommute) (S : LangSetup τ L p)
    (hτ : τ ≠ .G2) (hq3 : 3 ≤ S.D.q) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E)
    (hgen : BigAnyComponentsGenerate S D₁) : CentralizerTrivial S D₁ := by
  intro z hzC hcomm
  have hz := commute_adjointGroup_of_bigAnyGenerate hAK S hτ hq3 hD₁E hgen
    (fun x hx => hcomm x (Or.inl hx))
  have hcent : (⟨z, hzC⟩ : adjointGroup τ L) ∈ Subgroup.center (adjointGroup τ L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hz g g.2).symm.eq
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
  exact congrArg Subtype.val hcent

theorem centralizerTrivialAny_of_anyKindCommute (hAK : AnyKindCommute) (τ : Tag) :
    CentralizerTrivialAny τ := by
  intro L _ _ p S hτ hq3 D₁ hD₁E hgen
  exact centralizerTrivial_of_bigAnyGenerate hAK S hτ hq3 hD₁E hgen

end Commute

section Rigid

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem cosetCentralizerEmpty_of_bigAnyGenerate (hAK : AnyKindCommute) {K : Type} [Field K]
    [Finite K] [Algebra K L] [Algebra.IsAlgebraic K L] (S : LangSetup TwistTag.E6.tag L p)
    (hq3 : 3 ≤ S.D.q) {D₁ : Subgroup (ModGL TwistTag.E6.tag L)} (hD₁E : D₁ ≤ S.E)
    (hgen : BigAnyComponentsGenerate S D₁) :
    CosetCentralizerEmpty S D₁ (diagramMap TwistTag.E6 L) := by
  intro w hw hcomm
  exact not_forall_commute_mul_diagramMap_E6 (K := K) hw
    (commute_adjointGroup_of_bigAnyGenerate hAK S (by decide) hq3 hD₁E hgen
      fun x hx => hcomm x (Or.inl hx))

end Rigid

section Classes

theorem springer_exists_langSetup_twistedE6_six (hF : FrobeniusOnRoots) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (hpq : ¬ p ∣ ℓ ^ f) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 6) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
      (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
          ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord))
      (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p),
      S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr
        ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord) hg0C hg0 ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (twistedE6RootGroup K σ ≃* S.Γ) := by
  have he' := orderOf_neg_natCast_zmod hp (by omega) hpq he
  rw [show ennola 6 = 3 by decide] at he'
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord) • x =
      toMat TwistTag.E6.tag.rank twE6SixMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Six_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have hΦ : ∀ x : ℤ, ((cyclotomic 3 ℤ).eval (-x)).natAbs =
      ((cyclotomic 6 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_six_eq, cyclotomic_three_eq]
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
    congr 1
    ring
  exact springer_exists_lang_twE6_of_blocks hF hℓ hf K hK σ hσ hp (by omega) hpq _ hv
    [6, 6, 6] twE6Six_charpoly (by norm_num) twE6Six_pow (Or.inr (by decide)) he he'
    hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)

theorem InnerPlaneBalanceSmall.of_twistedE6_six_three_seven
    (h : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .twistedE6 q).Valid), q.card = 3 →
      InnerPlaneBalance 7 (CatT ⟨excIndex .twistedE6 q, hv⟩)) :
    InnerPlaneBalanceSmall .twistedE6 6 := by
  intro q hv p hp hp7 _ he hq3
  have hq2 : 2 ≤ q.card := by
    have := Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
    rw [TauCeti.PrimePower.card_def]
    omega
  obtain ⟨h3, rfl⟩ := small_field_order_six hp hp7 (by omega) he
  exact h q hv h3

end Classes

end CFSG.HardMathSupport.Timmesfeld.LangTorus
