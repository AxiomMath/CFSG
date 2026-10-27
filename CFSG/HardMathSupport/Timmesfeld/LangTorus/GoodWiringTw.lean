module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTwE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTriD4Classes
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodClass
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

@[expose] def LangTorusAtAlgW (k : LieFamily) (R : ℕ → ℕ → Prop)
    (W : ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}, LangSetup (excTag k) L p → Prop) : Prop :=
  IsExceptionalFam k → ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) (p : ℕ),
    p.Prime → R p q.card → p ≠ q.p →
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup (excTag k) L p),
      S.D.q = q.card ∧ S.IsAlgebraic ∧ W S ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (CatT ⟨excIndex k q, hv⟩ ≃* S.Γ)

@[expose] def LangRigidityForAlgW (k : LieFamily) (R : ℕ → ℕ → Prop)
    (W : ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}, LangSetup (excTag k) L p → Prop) : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) (p : ℕ) (L : Type) [Field L]
    [IsAlgClosed L] (S : LangSetup (excTag k) L p), R p q.card → S.D.q = q.card →
      S.IsAlgebraic → W S → Nonempty (CatT ⟨excIndex k q, hv⟩ ≃* S.Γ) → SetupRigid S

theorem innerPlaneBalanceAtP_of_lang_rigid_algW {k : LieFamily} {e : ℕ} (hk : IsExceptionalFam k)
    {R : ℕ → Prop}
    {W : ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}, LangSetup (excTag k) L p → Prop}
    (ha : LangTorusAtAlgW k (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) W)
    (hrig : LangRigidityForAlgW k (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) W)
    (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid),
      Subgroup.center (CatT ⟨excIndex k q, hv⟩) = ⊥) : InnerPlaneBalanceAtP k e R := by
  intro q hv _ hp _ hRp hpq he
  obtain ⟨L, hF, hA, S, hSq, hAlg, hW, hsyl, hε⟩ := ha hk q hv _ hp ⟨hRp, he⟩ hpq
  obtain ⟨ε⟩ := hε
  have hinj := conj_injective_of_mulEquiv ε (conj_injective_of_center_bot (hZ q hv))
  exact InnerPlaneBalance.of_mulEquiv ε
    (innerPlaneBalance_of_langSetup_rigid S hsyl (hrig q hv _ L S ⟨hRp, he⟩ hSq hAlg hW ⟨ε⟩) hcp
      hinj)

@[expose] def TwStructE6 (M : List (List ℤ)) {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup (excTag .twistedE6) L p) : Prop :=
  RhoIs S M ∧ ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr

@[expose] def TwStructD4 (M : List (List ℤ)) {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup (excTag .trialityD4) L p) : Prop :=
  RhoIs S M ∧ ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr

theorem exists_lang_twE6_alg_rho (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag) (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    (hev : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0)
    (hordN : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ ((M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs).factorization p) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.E6 L p),
      S.D.q = ℓ ^ f ∧ S.IsAlgebraic ∧ (∀ γ, IsRoot Tag.E6 γ → S.ρ γ = M *ᵥ γ) ∧
      (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr) ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (twistedE6RootGroup K σ ≃* S.Γ) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L v
  let D : LangDatum Tag.E6 L := LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0
  have hD : D.Φ = twistHom TwistTag.E6 L Fr := rfl
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hd := langDescent_twE6 (K := K) (L := L) hℓ hf hK σ hσ hFr D hD hp hp3
  have hT0 := twistedTorus_E6_eq_map (L := L) Fr v M hv
  set B : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub hℓ (dvd_pow_self ℓ (by omega) : ℓ ∣ ℓ ^ f) M hn0 hpow
  have hcard : Nat.card D.torus = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs := by
    show Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) = _
    rw [hT0, Subgroup.card_map_of_injective CFSG.LieType.Chevalley.rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  have hord : (Nat.card (twistedE6RootGroup K σ)).factorization p ≤
      (Nat.card D.torus).factorization p := by
    rw [hcard]
    exact (Nat.pow_right_injective hp.two_le hordN).le
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 :=
    ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2 (dvd_pow_self ℓ (by omega))⟩
  obtain ⟨S, hSD, hsyl, hequiv⟩ := exists_langSetup_of_descent hF D hp
    (Or.inl (five_le_of_three_lt hp hp3)) hqpow hpq ι hι hd hord
  have hq : S.D.q = ℓ ^ f := by rw [hSD]; rfl
  have hrho : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = M *ᵥ γ := by
    intro γ hγ
    have hFD : FrobRootMap D S.ρ := by
      have := S.frob
      rw [hSD] at this
      exact this
    have hinv : ∀ x : Fin Tag.E6.rank → ℤ,
        permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm x) = x := by
      intro x
      funext i
      change x (TwistTag.E6.perm.symm (TwistTag.E6.perm.symm i)) = x i
      have : ∀ j : Fin TwistTag.E6.tag.rank,
          TwistTag.E6.perm.symm (TwistTag.E6.perm.symm j) = j := by
        intro j
        fin_cases j <;> decide
      rw [this i]
    refine (frobRootMap_ofTwist_apply (by omega) hFr hg0C hg0 hFD hγ).trans ?_
    rw [hv, hinv]
  exact ⟨L, inferInstance, inferInstance, S, hq,
    S.isAlgebraic_of_isAlgClosure K 2 (by rw [hSD]; exact hK), hrho,
    ⟨Fr, fun c => by rw [hq]; exact hFr c, by rw [hSD]; exact hD⟩, hsyl, hequiv⟩

theorem exists_lang_twE6_of_blocks_alg_rho (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag) (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    (ds : List ℕ) {n e e' : ℕ} (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod)
    (hn0 : n ≠ 0) (hpow : M ^ n = 1) (hnd : n = e ∨ n ∈ [1, 2, 3, 4, 6])
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e)
    (he' : orderOf (((-((ℓ ^ f : ℕ) : ℤ) : ℤ)) : ZMod p) = e')
    (hΦ : ∀ x : ℤ, ((cyclotomic e' ℤ).eval (-x)).natAbs = ((cyclotomic e ℤ).eval x).natAbs)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3, 4, 6])
    (hdeg : ∀ d ∈ degreesE Tag.E6, e' ∣ d → ¬ p ∣ d / e')
    (hcount : ((degreesE Tag.E6).filter fun d => e' ∣ d).length = ds.count e) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.E6 L p),
      S.D.q = ℓ ^ f ∧ S.IsAlgebraic ∧ (∀ γ, IsRoot Tag.E6 γ → S.ρ γ = M *ᵥ γ) ∧
      (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr) ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (twistedE6RootGroup K σ ≃* S.Γ) := by
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have h5 := five_le_of_three_lt hp hp3
  have hn : ¬ p ∣ n := by
    rcases hnd with rfl | hn
    · exact not_dvd_of_orderOf hp hpq he
    · exact not_dvd_small hp h5 hn
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  set Q : ℤ := -((ℓ ^ f : ℕ) : ℤ) with hQdef
  have hQ2 : 2 ≤ Q.natAbs := by simpa [hQdef] using hq2
  have hpQ : ¬ (p : ℤ) ∣ Q := fun h => hpq (Int.natCast_dvd_natCast.1 (by simpa [hQdef] using h))
  have he'0 : e' ≠ 0 := by
    have hQ0 : (Q : ZMod p) ≠ 0 := fun h => hpQ ((ZMod.intCast_zmod_eq_zero_iff_dvd Q p).1 h)
    have : Fact p.Prime := ⟨hp⟩
    intro h0
    have hdvd := he' ▸ ZMod.orderOf_dvd_card_sub_one hQ0
    rw [h0, zero_dvd_iff] at hdvd
    have := hp.one_lt
    omega
  have hord : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      (p ^ ((ℓ ^ f) ^ e - 1).factorization p) ^ ds.count e := by
    have hD : ∀ d ∈ degreesE Tag.E6, e' ∣ d → d ≠ 0 ∧ ¬ p ∣ d / e' := fun d hd hed =>
      ⟨by have : ∀ d ∈ degreesE Tag.E6, 0 < d := by decide
          exact (this d hd).ne', hdeg d hd hed⟩
    rw [ordProj_card_twistedE6 hℓ hf K hK σ hσ hp hp3 hpq,
      prod_ordProj_int_pow_sub_one hp (by omega) hQ2 hpQ he' (degreesE Tag.E6) hD, hcount,
      ← ordProj_cyclotomic_int_eval hp hQ2 he' he'0]
    have h1 := ordProj_cyclotomic_eval hp hq2 he he0
    have h2 : ((cyclotomic e' ℤ).eval Q).natAbs =
        ((cyclotomic e ℤ).eval ((ℓ ^ f : ℕ) : ℤ)).natAbs := by
      have := hΦ ((ℓ ^ f : ℕ) : ℤ)
      simpa [hQdef] using this
    rw [h2, h1]
  have hR := not_dvd_cyclotomic_eval_of_mem_small hp h5 he ds hso
  have hpos : 0 < (cyclotomic e ℤ).eval ((ℓ ^ f : ℕ) : ℤ) :=
    cyclotomic_pos' e (by exact_mod_cast hq2)
  have hRne : (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := fun h => hR (by rw [h]; exact dvd_zero _)
  have hev : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    rw [hchar', eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hpos.ne') hRne
  have hordN : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ ((M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs).factorization p := by
    rw [hord, hchar', ordProj_cyclotomic_pow_mul_eval hp hq2 he he0 hR]
  exact exists_lang_twE6_alg_rho hF hℓ hf K hK σ hσ hp hp3 hpq v hv hn0 hpow hev hordN

theorem langTorusAtAlgW_twistedE6_of_model {e : ℕ} {R : ℕ → Prop} (Ml : List (List ℤ))
    (H : ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K], Nat.card K = (ℓ ^ f) ^ 2 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) → ∀ p : ℕ, p.Prime → R p → ¬ p ∣ ℓ ^ f →
      orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.E6 L p),
        S.D.q = ℓ ^ f ∧ S.IsAlgebraic ∧
        (∀ γ, IsRoot Tag.E6 γ → S.ρ γ = toMat Tag.E6.rank Ml *ᵥ γ) ∧
        (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr) ∧
        (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
        Nonempty (twistedE6RootGroup K σ ≃* S.Γ)) :
    LangTorusAtAlgW .twistedE6 (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
      (S : LangSetup (excTag .twistedE6) L p) => TwStructE6 Ml S) := by
  intro _ q hv p hp ⟨hR, he⟩ hpq
  obtain ⟨K, _, σ, hK, hσ, ⟨eq⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpK : ¬ p ∣ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact not_dvd_card_of_ne hp hpq
  have he' : orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = e := by
    rw [← TauCeti.PrimePower.card_def]
    exact he
  obtain ⟨L, hF, hA, S, hq, hAlg, hρ, hΦ, hsyl, ⟨f⟩⟩ := H q.p q.exponent q.prime_p
    q.exponent_pos K hK σ hσ p hp hR hpK he'
  exact ⟨L, hF, hA, S, by rw [hq, TauCeti.PrimePower.card_def], hAlg, ⟨hρ, hΦ⟩, hsyl,
    ⟨eq.trans f⟩⟩
theorem exists_lang_triD4_alg_rho (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ}
    (w : WeylGroup TwistTag.D4.tag)
    (hw : ∀ x, w • x = M *ᵥ permLattice TwistTag.D4.perm.symm x)
    {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    (hev : (M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ)).det ≠ 0)
    (hord : (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p ≤
      ((M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ)).det.natAbs).factorization p) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.D4 L p),
      S.D.q = ℓ ^ f ∧ S.IsAlgebraic ∧ (∀ γ, IsRoot Tag.D4 γ → S.ρ γ = M *ᵥ γ) ∧
      (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr) ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* S.Γ) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L
    (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)
    (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.D4.tag) L w)
  let D : LangDatum Tag.D4 L := LangDatum.ofTwist TwistTag.D4 Fr (ℓ ^ f) hFr w hg0C hg0
  have hD : D.Φ = twistHom TwistTag.D4 L Fr := rfl
  have hι : Function.Injective (triEmb K σ L) := triEmb_injective
  have hd := langDescent_triD4 (K := K) (L := L) hℓ hf hK σ hσ hFr D hD (p := p)
  have hnM : canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∈
      monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L w
  have hv0 : weylQuotientHom TwistTag.D4.tag L
      ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) L w, hnM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hT0 := twistedTorus_D4_eq_map_of_weylImage Fr hnM w hv0 M hw
  set B : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
    M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) with hB
  have hcop := not_dvd_natAbs_det_sub hℓ (dvd_pow_self ℓ (by omega) : ℓ ∣ ℓ ^ f) M hn0 hpow
  have hcard : Nat.card D.torus = B.det.natAbs := by
    show Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)
      (twistHom TwistTag.D4 L Fr)) = _
    rw [hT0, Subgroup.card_map_of_injective CFSG.LieType.Chevalley.rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hev hcop]
  have hord' : (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p ≤
      (Nat.card D.torus).factorization p := by
    rw [hcard]
    exact hord
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 :=
    ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2 (dvd_pow_self ℓ (by omega))⟩
  obtain ⟨S, hSD, hsyl, hequiv⟩ := exists_langSetup_of_descent hF D hp (Or.inl h5) hqpow hpq
    (triEmb K σ L) hι hd hord'
  have hq : S.D.q = ℓ ^ f := by rw [hSD]; rfl
  have hrho : ∀ γ, IsRoot Tag.D4 γ → S.ρ γ = M *ᵥ γ := by
    intro γ hγ
    have hFD : FrobRootMap D S.ρ := by
      have := S.frob
      rw [hSD] at this
      exact this
    have hinv : ∀ x : Fin Tag.D4.rank → ℤ,
        permLattice TwistTag.D4.perm.symm (permLattice TwistTag.D4.perm x) = x := by
      intro x
      funext i
      change x (TwistTag.D4.perm.symm (TwistTag.D4.perm.symm.symm i)) = x i
      simp
    refine (frobRootMap_ofTwist_apply (by omega) hFr hg0C hg0 hFD hγ).trans ?_
    rw [hw, hinv]
  exact ⟨L, inferInstance, inferInstance, S, hq,
    S.isAlgebraic_of_isAlgClosure K 3 (by rw [hSD]; exact hK), hrho,
    ⟨Fr, fun c => by rw [hq]; exact hFr c, by rw [hSD]; exact hD⟩, hsyl, hequiv⟩

theorem exists_lang_triD4_of_class_alg_rho (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (hC : Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ordTrialityD4 (ℓ ^ f))
    {e : ℕ} (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e) (hE : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6)
    {M : Matrix (Fin 4) (Fin 4) ℤ} (w : WeylGroup TwistTag.D4.tag)
    (hw : ∀ x, w • x = M *ᵥ permLattice TwistTag.D4.perm.symm x) {n : ℕ} (hn0 : n ≠ 0)
    (hpow : M ^ n = 1) (R : ℤ[X])
    (hdet : ∀ q : ℤ, (M - q • (1 : Matrix (Fin 4) (Fin 4) ℤ)).det = (cyclotomic e ℤ ^ 2 * R).eval q)
    (hR : ¬ (p : ℤ) ∣ R.eval ((ℓ ^ f : ℕ) : ℤ)) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.D4 L p),
      S.D.q = ℓ ^ f ∧ S.IsAlgebraic ∧ (∀ γ, IsRoot Tag.D4 γ → S.ρ γ = M *ᵥ γ) ∧
      (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr) ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* S.Γ) := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have he0 : e ≠ 0 := by rcases hE with rfl | rfl | rfl | rfl <;> norm_num
  have hpos : 0 < (cyclotomic e ℤ).eval ((ℓ ^ f : ℕ) : ℤ) :=
    cyclotomic_pos' e (by exact_mod_cast hq2)
  have hRne : R.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := fun h => hR (by rw [h]; exact dvd_zero _)
  have hdet' := hdet ((ℓ ^ f : ℕ) : ℤ)
  have hev : (M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)).det ≠ 0 := by
    rw [hdet', eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hpos.ne') hRne
  refine exists_lang_triD4_alg_rho hF hℓ hf K hK σ hσ hp (by omega) hpq w hw hn0 hpow hev ?_
  have h1 := ordProj_ordTrialityD4 hp h7 hq2 hpq he hE
  have h2 := ordProj_cyclotomic_pow_mul_eval (m := 2) hp hq2 he he0 hR
  rw [← hdet'] at h2
  rw [hC]
  exact (Nat.pow_right_injective hp.two_le (h1.trans h2.symm)).le

theorem langTorusAtAlgW_trialityD4_of_model {e : ℕ} {R : ℕ → Prop} (Ml : List (List ℤ))
    (H : ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K], Nat.card K = (ℓ ^ f) ^ 3 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) → ∀ p : ℕ, p.Prime → R p → ¬ p ∣ ℓ ^ f →
      Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ordTrialityD4 (ℓ ^ f) →
      orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.D4 L p),
        S.D.q = ℓ ^ f ∧ S.IsAlgebraic ∧
        (∀ γ, IsRoot Tag.D4 γ → S.ρ γ = toMat Tag.D4.rank Ml *ᵥ γ) ∧
        (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr) ∧
        (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
        Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* S.Γ)) :
    LangTorusAtAlgW .trialityD4 (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
      (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 Ml S) := by
  intro _ q hv p hp ⟨hR, he⟩ hpq
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eq⟩⟩ := exists_catEquiv_trialityD4 q hv
  have hpK : ¬ p ∣ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact not_dvd_card_of_ne hp hpq
  have he' : orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = e := by
    rw [← TauCeti.PrimePower.card_def]
    exact he
  have hC : Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      ordTrialityD4 (q.p ^ q.exponent) := by
    rw [← Nat.card_congr eq.toEquiv]
    exact card_cat_trialityD4 q hv
  obtain ⟨L, hF, hA, S, hq, hAlg, hρ, hΦ, hsyl, ⟨f⟩⟩ := H q.p q.exponent q.prime_p
    q.exponent_pos K hK σ hσ p hp hR hpK hC he'
  exact ⟨L, hF, hA, S, by rw [hq, TauCeti.PrimePower.card_def], hAlg, ⟨hρ, hΦ⟩, hsyl,
    ⟨eq.trans f⟩⟩
theorem langTorusAtAlgW_twistedE6_1 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgW .twistedE6 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 1) (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
      (S : LangSetup (excTag .twistedE6) L p) => TwStructE6 twE6OneMat S) :=
  langTorusAtAlgW_twistedE6_of_model twE6OneMat fun ℓ f hℓ hf K _ hK σ hσ p hp (h7 : 7 ≤ p) hpq he => by
    have he' := orderOf_neg_natCast_zmod hp (by omega) hpq he
    rw [show ennola 1 = 2 by decide] at he'
    have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord) • x =
        toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
      rw [wordProd_smul_eq_wordMat_mulVec, twE6One_wordMat, toMat_lmul, permLattice_E6_eq,
        Matrix.mulVec_mulVec]
    have hΦ : ∀ x : ℤ, ((cyclotomic 2 ℤ).eval (-x)).natAbs =
        ((cyclotomic 1 ℤ).eval x).natAbs := fun x => by
      rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
        show -x + 1 = -(x - 1) by ring, Int.natAbs_neg]
    exact exists_lang_twE6_of_blocks_alg_rho hF hℓ hf K hK σ hσ hp (by omega) hpq _ hv
      [1, 1, 1, 1, 2, 2] twE6One_charpoly (by norm_num) twE6One_pow (Or.inr (by decide)) he he'
      hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)

theorem langTorusAtAlgW_twistedE6_2 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgW .twistedE6 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 2) (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
      (S : LangSetup (excTag .twistedE6) L p) => TwStructE6 twE6TwoMat S) :=
  langTorusAtAlgW_twistedE6_of_model twE6TwoMat fun ℓ f hℓ hf K _ hK σ hσ p hp (h7 : 7 ≤ p) hpq he => by
    have he' := orderOf_neg_natCast_zmod hp (by omega) hpq he
    rw [show ennola 2 = 1 by decide] at he'
    have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord) • x =
        toMat TwistTag.E6.tag.rank twE6TwoMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
      rw [wordProd_smul_eq_wordMat_mulVec, twE6Two_wordMat, toMat_lmul, permLattice_E6_eq,
        Matrix.mulVec_mulVec]
    have hΦ : ∀ x : ℤ, ((cyclotomic 1 ℤ).eval (-x)).natAbs =
        ((cyclotomic 2 ℤ).eval x).natAbs := fun x => by
      rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
        show -x - 1 = -(x + 1) by ring, Int.natAbs_neg]
    exact exists_lang_twE6_of_blocks_alg_rho hF hℓ hf K hK σ hσ hp (by omega) hpq _ hv
      [2, 2, 2, 2, 2, 2] twE6Two_charpoly (by norm_num) twE6Two_pow (Or.inr (by decide)) he he'
      hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)

theorem langTorusAtAlgW_trialityD4_1 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgW .trialityD4 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 1) (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
      (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4OneMat S) :=
  langTorusAtAlgW_trialityD4_of_model triD4OneMat fun ℓ f hℓ hf K _ hK σ hσ p hp (h7 : 7 ≤ p) hpq hC he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hΦ, hsyl, hequiv⟩ :=
      exists_lang_triD4_of_class_alg_rho hF hℓ hf K hK σ hσ hp h7 hpq hC he (Or.inl rfl)
      ((coxeterSystem TwistTag.D4.tag).wordProd d4OneWord) d4One_hw (by norm_num) d4One_pow (cyclotomic 3 ℤ) d4One_det
      (not_dvd_cyclotomic_eval_of_ne hp he (by norm_num) (fun h => by
        have := Nat.le_of_dvd (by norm_num) h
        omega))
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hΦ, hsyl, hequiv⟩
    rw [hρ γ hγ]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem langTorusAtAlgW_trialityD4_2 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgW .trialityD4 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 2) (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
      (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4TwoMat S) :=
  langTorusAtAlgW_trialityD4_of_model triD4TwoMat fun ℓ f hℓ hf K _ hK σ hσ p hp (h7 : 7 ≤ p) hpq hC he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hΦ, hsyl, hequiv⟩ :=
      exists_lang_triD4_of_class_alg_rho hF hℓ hf K hK σ hσ hp h7 hpq hC he (by decide)
      ((coxeterSystem TwistTag.D4.tag).wordProd d4TwoWord) d4Two_hw (by norm_num)
      d4Two_pow (cyclotomic 6 ℤ) d4Two_det
      (not_dvd_cyclotomic_eval_of_ne hp he (by norm_num) (fun h => by
        have := Nat.le_of_dvd (by norm_num) h
        omega))
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hΦ, hsyl, hequiv⟩
    rw [hρ γ hγ]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem langRigidityForAlgW_trialityD4_1 :
    LangRigidityForAlgW .trialityD4 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 1) (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
      (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4OneMat S) :=
  fun _ _ _ L _ _ S hR hq hAlg hW _ =>
    setupRigid_triD4_one S hR.1 hW.2 hAlg (by rw [hq]; exact hR.2) hW.1

theorem innerPlaneBalanceAtP_trialityD4_1 (hF : FrobeniusOnRoots) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .trialityD4 q).Valid),
      Subgroup.center (CatT ⟨excIndex .trialityD4 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .trialityD4 1 fun p => 7 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algW (k := .trialityD4) trivial (langTorusAtAlgW_trialityD4_1 hF)
    langRigidityForAlgW_trialityD4_1 hcp hZ

theorem langRigidityForAlgW_trialityD4_2 :
    LangRigidityForAlgW .trialityD4 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 2) (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
      (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4TwoMat S) :=
  fun _ _ _ L _ _ S hR hq hAlg hW _ =>
    setupRigid_triD4_two S hR.1 hW.2 hAlg (by rw [hq]; exact hR.2) hW.1

theorem innerPlaneBalanceAtP_trialityD4_2 (hF : FrobeniusOnRoots) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .trialityD4 q).Valid),
      Subgroup.center (CatT ⟨excIndex .trialityD4 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .trialityD4 2 fun p => 7 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algW (k := .trialityD4) trivial (langTorusAtAlgW_trialityD4_2 hF)
    langRigidityForAlgW_trialityD4_2 hcp hZ

end CFSG.HardMathSupport.Timmesfeld.LangTorus
