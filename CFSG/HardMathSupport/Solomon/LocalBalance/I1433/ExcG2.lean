module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.InnerRank
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SL3Noncentral
public import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndexProof
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
public import CFSG.RankThree.PartOne.K133X.G2
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
import CFSG.RankThree.OddKernel.SimpleQuotient

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer congr_conj)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem commutator_le_inner_of_isCyclic {Γ : Type*} [Group Γ] (h : IsCyclic (Outer Γ)) :
    commutator (MulAut Γ) ≤ inner Γ := by
  letI : CommGroup (Outer Γ) := IsCyclic.commGroup
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' (inner Γ) ⁅g₁, g₂⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem exists_conj_of_mem_commutator_of_le {S Γ : Type} [Group S] [Group Γ] (e : S ≃* Γ)
    (h : commutator (MulAut Γ) ≤ inner Γ) {α : MulAut S} (hα : α ∈ commutator (MulAut S)) :
    ∃ g : S, α = MulAut.conj g := by
  have hmap : (commutator (MulAut S)).map (MulAut.congr e).toMonoidHom = commutator (MulAut Γ) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (MulAut.congr e).surjective]
  have h1 : MulAut.congr e α ∈ inner Γ := h (hmap ▸ Subgroup.mem_map_of_mem _ hα)
  obtain ⟨γ, hγ⟩ := h1
  refine ⟨e.symm γ, ?_⟩
  rw [← congr_conj e.symm γ, hγ]
  ext s
  simp [MulAut.congr_apply]

set_option linter.unusedSectionVars false


theorem false_of_i1433SCfg_G2 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (r : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 r).Valid) (hr3 : r.p ≠ 3)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 r, hv⟩).Group))
    {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S} {q : ℕ} (c : I1433SCfg Q x J q) :
    False := by
  haveI := hs
  have hZ : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hna
  obtain ⟨e0⟩ := he
  set X := (TauCeti.CFSGIndex.lie ⟨.G2 r, hv⟩).Group with hXdef
  have hmodel : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 r.p r.exponent := by
    by_cases hr2 : r.p = 2
    · have h := CFSG.RankThree.PartOne.K133X.chevalleyExceptionalModel_G2_of_isoLie (X := X) hr2
        ⟨hv, ⟨MulEquiv.refl _⟩⟩
      rwa [hr2]
    · exact CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_of_odd r hv hr2
  obtain ⟨K, _, _, hK, ⟨e1⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hmodel.2
  haveI : Fact r.p.Prime := ⟨r.prime_p⟩
  have hKc : Nat.card K = r.p ^ r.exponent := hK
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K r.p :=
    charP_of_card_eq_prime_pow (f := r.exponent) (by rw [← Nat.card_eq_fintype_card, hKc])
  have hringK : ringChar K = r.p := ringChar.eq K r.p
  have hK3 : (3 : K) ≠ 0 := by
    intro h
    have h3 : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K r.p] at h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq r.prime_p Nat.prime_three).1 h3)
  have hq3 : 3 ≤ r.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKc, ← TauCeti.PrimePower.card_def]
    rcases (show r.card = 3 ∨ 4 ≤ r.card by omega) with h3 | h4
    · exfalso
      apply hr3
      have hd : r.p ∣ r.card := by
        rw [TauCeti.PrimePower.card_def]
        exact dvd_pow_self _ r.exponent_pos.ne'
      rw [h3] at hd
      exact (Nat.prime_dvd_prime_iff_eq r.prime_p Nat.prime_three).1 hd
    · exact h4
  have hrank : CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2 := by
    by_cases hr2 : r.p = 2
    · have hm2 : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 r.exponent := hr2 ▸ hmodel
      exact CFSG.RankThree.PartTwo.Sec21.g2EvenThreeRankTwo X r.exponent hm2
    · have hK2 : ringChar K ≠ 2 := by rw [hringK]; exact hr2
      exact CFSG.RankThree.PartTwo.Sec21.Item223RankResProof.pRank_quotient_center_le_two_of_mulEquiv
        e1 CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
        (fun F hF => CFSG.RankThree.PartTwo.Sec21.Item223RankResProof.adjointG2_card_le_nine K hK2 hK3 F hF)
  have hcyc : IsCyclic (Outer (adjointGroup Tag.G2 K)) := by
    haveI := CFSG.RankThree.PartTwo.KFacts.isCyclic_ringEquiv_of_finite K
    exact CFSG.RankThree.PartTwo.KFacts.isCyclic_outer_of_normalForm
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K)
      (CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form (by rw [hringK]; exact hr3) hK4).1
  have hin : ∀ α ∈ Q, ∃ g : S, α = MulAut.conj g := fun α hα =>
    exists_conj_of_mem_commutator_of_le (e0.trans e1) (commutator_le_inner_of_isCyclic hcyc)
      (c.derived hα)
  have h3 := c.three_le_pRank_of_inner hZ hin (IsSL3EpsOver.exists_noncentral_order_three c.sl3)
  haveI : Finite X := Finite.of_equiv S e0.toEquiv
  have hZX : Subgroup.center X = ⊥ := by
    rw [← Subgroup.map_center_eq e0, hZ, Subgroup.map_bot]
  let f : S →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' (Subgroup.center X)).comp e0.toMonoidHom
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (QuotientGroup.mk' (Subgroup.center X)) (e0 a) =
        (QuotientGroup.mk' (Subgroup.center X)) (e0 b) := hab
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hZX,
      Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact e0.injective h1
  have hle := CFSG.RankThree.OddKernel.pRank_le_of_injective (p := 3) (by norm_num) f hf
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hle
  omega

theorem false_of_i1433Cfg_G2 {X : Type} [Group X] [Finite X] {K Q₁ Q J : Subgroup X} {t : X}
    {q : ℕ} (c : I1433Cfg K Q₁ Q J t q) (r : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 r).Valid) (hr3 : r.p ≠ 3)
    (he : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie ⟨.G2 r, hv⟩).Group)) :
    False := by
  obtain ⟨x, Q', J', hcfg⟩ := c.exists_sCfg
  have hq := c.setup.quasisimple
  have hKq : CFSG.Open.IsQuasisimple ↥K := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hKq
  exact false_of_i1433SCfg_G2 hq.2.1 ⟨a, b, hab⟩ r hv hr3 he hcfg

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
