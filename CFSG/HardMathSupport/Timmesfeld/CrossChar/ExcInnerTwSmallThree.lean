module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.AnyKindThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyE8Three

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration

section Pieces

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem noFrobeniusInner_of_q_prime (S : LangSetup τ L p) (hq : S.D.q.Prime)
    (D₁ : Subgroup (ModGL τ L)) : NoFrobeniusInner S D₁ := by
  intro r f j _ _ hqf hj0 hjf _ _
  obtain ⟨-, hf1⟩ := (Nat.Prime.pow_eq_iff hq).1 hqf.symm
  omega

theorem two_lt_ncard_of_rho (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hA1 : ∀ γ, IsRoot τ γ → S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ) :
    2 < (componentRoots (rootCharHom a) i).ncard := by
  classical
  obtain ⟨-, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  rw [hs1] at hs
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨⟨γ, hγk⟩, hγi⟩ := Quotient.exists_rep i
  have hγΨ : γ ∈ componentRoots (rootCharHom a) i := ⟨hγk, hγi⟩
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγΨ
  have hnΨ : -γ ∈ componentRoots (rootCharHom a) i := hΨ.neg_mem γ hγΨ
  have hργ : S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    rw [← hs]
    exact ⟨γ, hγΨ, rfl⟩
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun δ hδ => hΨ.isRoot δ hδ
  have hne : γ ≠ -γ := fun h => hγr.ne_zero (by
    have : (2 : ℤ) • γ = 0 := by rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel γ
    exact (smul_eq_zero.1 this).resolve_left (by norm_num))
  by_contra hle
  push Not at hle
  have hsub : ({γ, -γ} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots (rootCharHom a) i := by
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact hγΨ
    · exact hnΨ
  have hcard2 : ({γ, -γ} : Set (Fin τ.rank → ℤ)).ncard = 2 := Set.ncard_pair hne
  have heq : ({γ, -γ} : Set (Fin τ.rank → ℤ)) = componentRoots (rootCharHom a) i :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard2]; exact hle) hfin
  rw [← heq] at hργ
  rcases hργ with h | h
  · exact (hA1 γ hγr).1 h
  · exact (hA1 γ hγr).2 h

theorem rho_ne_of_weylClass_hex (S : LangSetup τ L p) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hM : M * M = M - 1) (h : S.IsWeylClass M) (γ : Fin τ.rank → ℤ) (hγ : IsRoot τ γ) :
    S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ := by
  obtain ⟨Fr, hFr, hΦ, w, hn, hw, -⟩ := h
  have hρ : S.ρ γ = w • γ := S.rho_eq_smul_of_frob hFr hΦ hn hγ
  have hww : w • w • γ = w • γ - γ := by
    rw [hw, hw, Matrix.mulVec_mulVec, hM, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hρ]
  refine ⟨fun h1 => hγ.ne_zero ?_, fun h1 => hγ.ne_zero ?_⟩
  · rw [h1, h1, sub_self] at hww
    exact hww
  · rw [h1, smul_neg, h1, neg_neg] at hww
    have h3 : (3 : ℤ) • γ = 0 := by
      have : (3 : ℤ) • γ = γ - (-γ - γ) := by module
      rw [this, ← hww, sub_self]
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)

theorem rho_ne_of_weylClass_tri (S : LangSetup τ L p) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hM : M * M = -M - 1) (h : S.IsWeylClass M) (γ : Fin τ.rank → ℤ) (hγ : IsRoot τ γ) :
    S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ := by
  obtain ⟨Fr, hFr, hΦ, w, hn, hw, -⟩ := h
  have hρ : S.ρ γ = w • γ := S.rho_eq_smul_of_frob hFr hΦ hn hγ
  have hww : w • w • γ = -(w • γ) - γ := by
    rw [hw, hw, Matrix.mulVec_mulVec, hM, Matrix.sub_mulVec, Matrix.neg_mulVec,
      Matrix.one_mulVec]
  rw [hρ]
  refine ⟨fun h1 => hγ.ne_zero ?_, fun h1 => hγ.ne_zero ?_⟩
  · rw [h1, h1] at hww
    have h3 : (3 : ℤ) • γ = 0 := by
      have : (3 : ℤ) • γ = γ - (-γ - γ) := by module
      rw [this, ← hww, sub_self]
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)
  · rw [h1, smul_neg, h1, neg_neg, sub_self] at hww
    exact hww

theorem rho_ne_of_frob_sq_neg (S : LangSetup τ L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ) (γ : Fin τ.rank → ℤ)
    (hγ : IsRoot τ γ) : S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ := by
  have hρ : S.ρ γ = w • γ := S.rho_eq_smul_of_frob hFr hΦ hn hγ
  have hww := hw4 γ hγ
  have h2 : γ = -γ → γ = 0 := fun h => by
    have h2 : (2 : ℤ) • γ = 0 := by
      have : (2 : ℤ) • γ = γ - -γ := by module
      rw [this, ← h, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
  rw [hρ]
  refine ⟨fun h1 => hγ.ne_zero (h2 ?_), fun h1 => hγ.ne_zero (h2 ?_)⟩
  · rw [h1, h1] at hww
    exact hww
  · rw [h1, smul_neg, h1, neg_neg] at hww
    exact hww

end Pieces

section Rigid

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem commute_adjointGroup_three_of_pbig (hAK3 : AnyKindCommuteThreeFull)
    (S : LangSetup τ L p) (hsl : SimplyLacedTag τ) (hq : S.D.q = 3) (hP : BigAnyPBig S)
    (hA1 : ∀ γ, IsRoot τ γ → S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) {z : ModGL τ L}
    (hz : ∀ x ∈ bigComponentSet S D₁, Commute z x) :
    ∀ g ∈ adjointGroup τ L, Commute z g := by
  classical
  have hroot : ∀ γ, IsRoot τ γ → γ ∉ planeKernel D₁ → ∀ c : L,
      Commute z (pinnedX τ L γ c) := by
    intro γ hγ hγn c
    obtain ⟨a', ha'D, ha'1⟩ : ∃ a', rootDiagUnit τ a' ∈ D₁ ∧ rootChar a' γ ≠ 1 := by
      by_contra h
      push Not at h
      exact hγn ⟨hγ, fun a ha => h a ha⟩
    obtain ⟨a, haD, ha1, hχ⟩ := S.exists_nontrivial_killing hD₁E hc γ
    have hk : γ ∈ kernelRoots (rootCharHom a) := ⟨hγ, hχ⟩
    have hγi : γ ∈ componentRoots (rootCharHom a) ⟦⟨γ, hk⟩⟧ := ⟨hk, rfl⟩
    have hbig := hP D₁ hD₁E hc a haD a' ha'D γ hγ hχ ha'1 _ hγi
    have hT : rootDiagUnit τ a ∈ S.D.torus := (S.E_le (hD₁E haD)).1
    exact hAK3 τ L p S hsl hq a hT _ (fun hs1 => two_lt_ncard_of_rho S hT _ hs1 hA1) z
      (fun x hx => hz x ⟨a, haD, ha1, _, hbig, hx⟩) _ (pinnedX_mem_rootSpan hγi c)
  have hle : adjointGroup τ L ≤ Subgroup.centralizer {z} := by
    refine (adjointGroup_le_rootSpan_compl hsl (isClosedRoots_planeKernel D₁)
      (S.exists_root_not_mem_planeKernel hD₁E hc)).trans ?_
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hroot γ hγ.1 hγ.2 c).symm.eq
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem centralizerTrivial_three_of_pbig (hAK3 : AnyKindCommuteThreeFull) (S : LangSetup τ L p)
    (hsl : SimplyLacedTag τ) (hq : S.D.q = 3) (hP : BigAnyPBig S)
    (hA1 : ∀ γ, IsRoot τ γ → S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) :
    CentralizerTrivial S D₁ := by
  intro z hzC hcomm
  have hz := commute_adjointGroup_three_of_pbig hAK3 S hsl hq hP hA1 hD₁E hc
    (fun x hx => hcomm x (Or.inl hx))
  have hcent : (⟨z, hzC⟩ : adjointGroup τ L) ∈ Subgroup.center (adjointGroup τ L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hz g g.2).symm.eq
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
  exact congrArg Subtype.val hcent

theorem setupRigid_E8_three_of_pbig
    (hAK3 : AnyKindCommuteThreeFull) (S : LangSetup .E8 L p)
    (hq : S.D.q = 3) (hAlg : S.IsAlgebraic) (hP : BigAnyPBig S)
    (hA1 : ∀ γ, IsRoot .E8 γ → S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ) : SetupRigid S := by
  have hp5 : 5 ≤ p := by
    rcases S.hq with h | h
    · exact h
    · rw [hq] at h
      omega
  exact setupRigid_E8 S (by omega) hAlg
    (fun D₁ _ _ => noFrobeniusInner_of_q_prime S (by rw [hq]; norm_num) D₁)
    (fun D₁ hD₁ hc => centralizerTrivial_three_of_pbig hAK3 S (Or.inr (Or.inr (Or.inr rfl))) hq hP
      hA1 hD₁ hc)

end Rigid

theorem primePower_p_eq_three {q : TauCeti.PrimePower} (hq3 : q.card = 3) : q.p = 3 := by
  rw [TauCeti.PrimePower.card_def] at hq3
  exact ((Nat.Prime.pow_eq_iff Nat.prime_three).1 hq3).1

theorem orderOf_three_zmod_seven : orderOf ((3 : ℕ) : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_three_zmod_thirteen : orderOf ((3 : ℕ) : ZMod 13) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

section Rows

theorem innerPlaneBalance_three_of_class (k : LieFamily) (hk : IsExceptionalFam k) {p e : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (he : orderOf ((3 : ℕ) : ZMod p) = e)
    {C : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ), LangSetup (excTag k) L p → Prop}
    (ha : LangTorusAtAlgClass k (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = e) C)
    (hrig : ∀ (L : Type) [Field L] [IsAlgClosed L] (S : LangSetup (excTag k) L p),
      S.D.q = 3 → S.IsAlgebraic → C L p S → SetupRigid S) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid),
      Subgroup.center (CatT ⟨excIndex k q, hv⟩) = ⊥) :
    ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid), q.card = 3 →
      InnerPlaneBalance p (CatT ⟨excIndex k q, hv⟩) := by
  intro q hv hq3
  have hpq : p ≠ q.p := by
    rw [primePower_p_eq_three hq3]
    omega
  obtain ⟨L, hF, hA, S, hSq, hAlg, hC, hsyl, ⟨ε⟩⟩ :=
    ha hk q hv p hp ⟨hp7, by rw [hq3]; exact he⟩ hpq
  have hinj := conj_injective_of_mulEquiv ε (conj_injective_of_center_bot (hZ q hv))
  exact InnerPlaneBalance.of_mulEquiv ε
    (innerPlaneBalance_of_langSetup_rigid S hsyl (hrig L S (hSq.trans hq3) hAlg hC) hcp hinj)

theorem innerPlaneBalance_E8_six_three (hcp : LangComponentPieces)
    (hAK3 : AnyKindCommuteThreeFull) :
    ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E8 q).Valid), q.card = 3 →
      InnerPlaneBalance 7 (CatT ⟨excIndex .E8 q, hv⟩) :=
  innerPlaneBalance_three_of_class .E8 trivial (by norm_num) le_rfl orderOf_three_zmod_seven
    (langTorusAtAlgClass_E8_six frobeniusOnRoots_proved)
    (fun L _ _ S hq hAlg hC => setupRigid_E8_three_of_pbig hAK3 S hq hAlg
      (S.bigAnyPBig_of_weylClass_hex (Or.inr (Or.inr (Or.inr rfl))) le_rfl e8SixMat_rel hC)
      (rho_ne_of_weylClass_hex S e8SixMat_rel hC)) hcp center_catT_E8_eq_bot

theorem innerPlaneBalance_E8_three_thirteen (hcp : LangComponentPieces)
    (hAK3 : AnyKindCommuteThreeFull) :
    ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E8 q).Valid), q.card = 3 →
      InnerPlaneBalance 13 (CatT ⟨excIndex .E8 q, hv⟩) :=
  innerPlaneBalance_three_of_class .E8 trivial (by norm_num) (by norm_num)
    orderOf_three_zmod_thirteen (langTorusAtAlgClass_E8_three frobeniusOnRoots_proved)
    (fun L _ _ S hq hAlg hC => setupRigid_E8_three_of_pbig hAK3 S hq hAlg
      (S.bigAnyPBig_of_weylClass_tri (Or.inr (Or.inr (Or.inr rfl))) (by norm_num) e8ThreeMat_rel
        hC)
      (rho_ne_of_weylClass_tri S e8ThreeMat_rel hC)) hcp center_catT_E8_eq_bot

end Rows

end CFSG.HardMathSupport.Timmesfeld.CrossChar
