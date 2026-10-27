module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodClass
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Lattice Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

@[expose] def LangTorusAtAlgM (k : LieFamily) (R : ℕ → ℕ → Prop) (M : List (List ℤ)) : Prop :=
  IsExceptionalFam k → ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) (p : ℕ),
    p.Prime → R p q.card → p ≠ q.p →
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup (excTag k) L p),
      S.D.q = q.card ∧ S.IsAlgebraic ∧ RhoIs S M ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (CatT ⟨excIndex k q, hv⟩ ≃* S.Γ)

@[expose] def LangRigidityForAlgM (k : LieFamily) (R : ℕ → ℕ → Prop) (M : List (List ℤ)) : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) (p : ℕ) (L : Type) [Field L]
    [IsAlgClosed L] (S : LangSetup (excTag k) L p), R p q.card → S.D.q = q.card →
      S.IsAlgebraic → RhoIs S M → Nonempty (CatT ⟨excIndex k q, hv⟩ ≃* S.Γ) → SetupRigid S

theorem innerPlaneBalance_cat_of_lang_rigid_algM {k : LieFamily} (hk : IsExceptionalFam k)
    {R : ℕ → ℕ → Prop} {M : List (List ℤ)} (ha : LangTorusAtAlgM k R M)
    (hrig : LangRigidityForAlgM k R M) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid),
      Subgroup.center (CatT ⟨excIndex k q, hv⟩) = ⊥)
    (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) {p : ℕ} (hp : p.Prime)
    (hR : R p q.card) (hpq : p ≠ q.p) : InnerPlaneBalance p (CatT ⟨excIndex k q, hv⟩) := by
  obtain ⟨L, hF, hA, S, hSq, hAlg, hρ, hsyl, hε⟩ := ha hk q hv p hp hR hpq
  obtain ⟨ε⟩ := hε
  have hinj := conj_injective_of_mulEquiv ε (conj_injective_of_center_bot (hZ q hv))
  exact InnerPlaneBalance.of_mulEquiv ε
    (innerPlaneBalance_of_langSetup_rigid S hsyl (hrig q hv p L S hR hSq hAlg hρ ⟨ε⟩) hcp hinj)

theorem innerPlaneBalanceAtP_of_lang_rigid_algM {k : LieFamily} {e : ℕ} (hk : IsExceptionalFam k)
    {R : ℕ → Prop} {M : List (List ℤ)}
    (ha : LangTorusAtAlgM k (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) M)
    (hrig : LangRigidityForAlgM k (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) M)
    (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid),
      Subgroup.center (CatT ⟨excIndex k q, hv⟩) = ⊥) : InnerPlaneBalanceAtP k e R :=
  fun q hv _ hp _ hRp hpq he =>
    innerPlaneBalance_cat_of_lang_rigid_algM hk ha hrig hcp hZ q hv hp ⟨hRp, he⟩ hpq

theorem exists_lang_untw_alg_rho (hF : FrobeniusOnRoots) {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hM : CFSG.RankThree.PartOne.KE.IsWeylMatrix τ M) {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    (hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0)
    (hordN : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      p ^ ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p)
    (hperf : Group.IsPerfect ↥(adjointGroup τ K)) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup τ L p),
      S.D.q = Nat.card K ∧ S.IsAlgebraic ∧ (∀ γ, IsRoot τ γ → S.ρ γ = M *ᵥ γ) ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (adjointGroup τ K ≃* S.Γ) := by
  classical
  obtain ⟨w, hw⟩ := hM
  have hperf' : commutator ↥(adjointGroup τ K) = ⊤ := hperf.commutator_eq_top
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  let D : LangDatum τ L := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  have hD : D.Φ = Units.map (entrywiseHom Fr) := rfl
  let ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hd := langDescent_untw (K := K) (L := L) d hτ hFr D hD hp hp3 hperf'
  have hT0 : D.torus = (fixedCharTuples M Fr).map (rootDiagUnitHom τ L) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
      refine ⟨a, ?_, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
      exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
    · rintro ⟨a, ha, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr] at ha
      exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a,
        mem_twistedFixedTuples_iff_conj.1 ha⟩
  set B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
    M - (Nat.card K : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval (Nat.card K : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub hℓ hℓq M hn0 hpow
  have hcard : Nat.card D.torus = (M.charpoly.eval (Nat.card K : ℤ)).natAbs := by
    rw [hT0, Subgroup.card_map_of_injective CFSG.LieType.Chevalley.rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  have hord : (Nat.card (adjointGroup τ K)).factorization p ≤
      (Nat.card D.torus).factorization p := by
    rw [hcard]
    exact (Nat.pow_right_injective hp.two_le hordN).le
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 :=
    ⟨by rw [show D.q = Fintype.card K from Nat.card_eq_fintype_card]
        exact FiniteField.isPrimePow_card K, hK0⟩
  obtain ⟨S, hSD, hsyl, hequiv⟩ := exists_langSetup_of_descent hF D hp
    (Or.inl (five_le_of_three_lt hp hp3)) hqpow hpq ι hι hd hord
  have hrho : ∀ γ, IsRoot τ γ → S.ρ γ = M *ᵥ γ := by
    intro γ hγ
    have hFD : FrobRootMap D S.ρ := by
      have := S.frob
      rw [hSD] at this
      exact this
    rw [frobRootMap_ofFrobenius_apply Nat.card_pos hFr hg0C hg0 hFD hγ, hw γ]
  exact ⟨L, inferInstance, inferInstance, S, by rw [hSD]; rfl,
    S.isAlgebraic_of_isAlgClosure K 1 (by rw [pow_one, hSD]; rfl), hrho, hsyl, hequiv⟩

theorem exists_lang_untw_of_blocks_alg_rho (hF : FrobeniusOnRoots) {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hM : IsWeylMatrix τ M) (ds : List ℕ) {e : ℕ}
    (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod) (hpow : M ^ e = 1)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e)
    (hother : ∀ d ∈ ds, d ≠ e → ¬ p ∣ d)
    (hdeg : ∀ d ∈ degreesE τ, e ∣ d → ¬ p ∣ d / e)
    (hcount : ((degreesE τ).filter fun d => e ∣ d).length = ds.count e)
    (hperf : Group.IsPerfect ↥(adjointGroup τ K)) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup τ L p),
      S.D.q = Nat.card K ∧ S.IsAlgebraic ∧ (∀ γ, IsRoot τ γ → S.ρ γ = M *ᵥ γ) ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (adjointGroup τ K ≃* S.Γ) := by
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have hn : ¬ p ∣ e := not_dvd_of_orderOf hp hpq he
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : ∀ d ∈ degreesE τ, 0 < d := by
    rcases hτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hR : ¬ (p : ℤ) ∣ (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      (Nat.card K : ℤ) := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [eval_list_prod, hpz.dvd_prod_iff]
    rintro ⟨a, ha, hpa⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_filter] at hd
    have hde : d ≠ e := by simpa using hd.2
    exact not_dvd_cyclotomic_eval_of_ne hp he hde (hother d hd.1 hde) hpa
  have hord : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      (p ^ (Nat.card K ^ e - 1).factorization p) ^ ds.count e := by
    rw [ordProj_card_adjointGroup_E (by rcases hτ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hp
      hp3 hpq, prod_ordProj_pow_sub_one hp (by omega) hpq hq2 he (degreesE τ)
      (fun d hd hed => ⟨(hcard d hd).ne', hdeg d hd hed⟩), hcount]
  have hpos : 0 < (cyclotomic e ℤ).eval (Nat.card K : ℤ) :=
    cyclotomic_pos' e (by exact_mod_cast hq2)
  have hRne : (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      (Nat.card K : ℤ) ≠ 0 := fun h => hR (by rw [h]; exact dvd_zero _)
  have hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0 := by
    rw [hchar', eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hpos.ne') hRne
  have hordN : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      p ^ ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p := by
    rw [hord, hchar', ordProj_cyclotomic_pow_mul_eval hp hq2 he he0 hR]
  exact exists_lang_untw_alg_rho hF d hτ K hp hp3 hpq hM he0 hpow hev hordN hperf

theorem langTorusAtAlgM_E8_of_adjoint (Ml : List (List ℤ)) {e : ℕ} {R : ℕ → Prop}
    (H : ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → R p → ¬ p ∣ Nat.card K →
      orderOf ((Nat.card K : ℕ) : ZMod p) = e →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.E8 L p),
        S.D.q = Nat.card K ∧ S.IsAlgebraic ∧
        (∀ γ, IsRoot Tag.E8 γ → S.ρ γ = toMat Tag.E8.rank Ml *ᵥ γ) ∧
        (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
        Nonempty (adjointGroup Tag.E8 K ≃* S.Γ)) :
    LangTorusAtAlgM .E8 (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) Ml := by
  intro _ q hv p hp ⟨hR, he⟩ hpq
  obtain ⟨K, _, _, hK, -, ⟨eq⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  obtain ⟨L, hF, hA, S, hq, hAlg, hρ, hsyl, ⟨f⟩⟩ := H K p hp hR hpK he
  exact ⟨L, hF, hA, S, hq.trans hK, hAlg, hρ, hsyl, ⟨eq.trans f⟩⟩

theorem langTorusAtAlgM_E7_of_adjoint (Ml : List (List ℤ)) {e : ℕ} {R : ℕ → Prop}
    (H : ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → R p → ¬ p ∣ Nat.card K →
      orderOf ((Nat.card K : ℕ) : ZMod p) = e →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.E7 L p),
        S.D.q = Nat.card K ∧ S.IsAlgebraic ∧
        (∀ γ, IsRoot Tag.E7 γ → S.ρ γ = toMat Tag.E7.rank Ml *ᵥ γ) ∧
        (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
        Nonempty (adjointGroup Tag.E7 K ≃* S.Γ)) :
    LangTorusAtAlgM .E7 (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) Ml := by
  intro _ q hv p hp ⟨hR, he⟩ hpq
  obtain ⟨K, _, _, hK, -, ⟨eq⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  obtain ⟨L, hF, hA, S, hq, hAlg, hρ, hsyl, ⟨f⟩⟩ := H K p hp hR hpK he
  exact ⟨L, hF, hA, S, hq.trans hK, hAlg, hρ, hsyl, ⟨eq.trans f⟩⟩

theorem langTorusAtAlgM_E8_2 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgM .E8 (fun p c => 11 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 2) e8TwoMat :=
  langTorusAtAlgM_E8_of_adjoint e8TwoMat fun K _ _ p hp (h11 : 11 ≤ p) hpK he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hsyl, hequiv⟩ :=
      exists_lang_untw_of_blocks_alg_rho hF 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E8 e8TwoWord) [2, 2, 2, 2, 2, 2, 2, 2] e8Two_charpoly e8Two_pow he
      (not_dvd_of_blocks hp (by omega : 7 ≤ p) (by decide)) (not_dvd_div_of_5040 hp h11 (by decide)) (by decide)
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K).1
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hsyl, hequiv⟩
    rw [hρ γ hγ, e8Two_wordMat]

theorem langTorusAtAlgM_E8_4 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgM .E8 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 4) e8FourMat :=
  langTorusAtAlgM_E8_of_adjoint e8FourMat fun K _ _ p hp (h7 : 7 ≤ p) hpK he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hsyl, hequiv⟩ :=
      exists_lang_untw_of_blocks_alg_rho hF 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E8 e8FourWord) [4, 4, 4, 4] e8Four_charpoly e8Four_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K).1
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hsyl, hequiv⟩
    rw [hρ γ hγ, e8Four_wordMat]

theorem langTorusAtAlgM_E8_8 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgM .E8 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 8) e8EightMat :=
  langTorusAtAlgM_E8_of_adjoint e8EightMat fun K _ _ p hp (h7 : 7 ≤ p) hpK he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hsyl, hequiv⟩ :=
      exists_lang_untw_of_blocks_alg_rho hF 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E8 e8EightWord) [8, 8] e8Eight_charpoly e8Eight_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K).1
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hsyl, hequiv⟩
    rw [hρ γ hγ, e8Eight_wordMat]

theorem langTorusAtAlgM_E7_2 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgM .E7 (fun p c => 11 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 2) e7TwoMat :=
  langTorusAtAlgM_E7_of_adjoint e7TwoMat fun K _ _ p hp (h11 : 11 ≤ p) hpK he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hsyl, hequiv⟩ :=
      exists_lang_untw_of_blocks_alg_rho hF 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E7 e7TwoWord) [2, 2, 2, 2, 2, 2, 2] e7Two_charpoly e7Two_pow he
      (not_dvd_of_blocks hp (by omega : 7 ≤ p) (by decide)) (not_dvd_div_of_5040 hp h11 (by decide)) (by decide)
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hsyl, hequiv⟩
    rw [hρ γ hγ, e7Two_wordMat]

theorem langTorusAtAlgM_E7_3 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgM .E7 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 3) e7ThreeMat :=
  langTorusAtAlgM_E7_of_adjoint e7ThreeMat fun K _ _ p hp (h7 : 7 ≤ p) hpK he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hsyl, hequiv⟩ :=
      exists_lang_untw_of_blocks_alg_rho hF 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E7 e7ThreeWord) [1, 3, 3, 3] e7Three_charpoly e7Three_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hsyl, hequiv⟩
    rw [hρ γ hγ, e7Three_wordMat]

theorem langTorusAtAlgM_E7_6 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgM .E7 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 6) e7SixMat :=
  langTorusAtAlgM_E7_of_adjoint e7SixMat fun K _ _ p hp (h7 : 7 ≤ p) hpK he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hsyl, hequiv⟩ :=
      exists_lang_untw_of_blocks_alg_rho hF 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E7 e7SixWord) [2, 6, 6, 6] e7Six_charpoly e7Six_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hsyl, hequiv⟩
    rw [hρ γ hγ, e7Six_wordMat]

theorem langRigidityForAlgM_E8_two :
    LangRigidityForAlgM .E8 (fun p c => 11 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 2) e8TwoMat :=
  fun _ _ _ _ _ _ S hR hq hAlg hρ _ =>
    setupRigid_E8_two S (by have := hR.1; omega) hAlg (by rw [hq]; exact hR.2) hρ

theorem innerPlaneBalanceAtP_E8_two (hF : FrobeniusOnRoots) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E8 q).Valid),
      Subgroup.center (CatT ⟨excIndex .E8 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .E8 2 fun p => 11 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algM (k := .E8) trivial (langTorusAtAlgM_E8_2 hF)
    langRigidityForAlgM_E8_two hcp hZ

theorem langRigidityForAlgM_E8_four :
    LangRigidityForAlgM .E8 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 4) e8FourMat :=
  fun _ _ _ _ _ _ S hR hq hAlg hρ _ =>
    setupRigid_E8_four S (by have := hR.1; omega) hAlg (by rw [hq]; exact hR.2) hρ

theorem innerPlaneBalanceAtP_E8_four (hF : FrobeniusOnRoots) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E8 q).Valid),
      Subgroup.center (CatT ⟨excIndex .E8 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .E8 4 fun p => 7 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algM (k := .E8) trivial (langTorusAtAlgM_E8_4 hF)
    langRigidityForAlgM_E8_four hcp hZ

theorem langRigidityForAlgM_E8_eight (hS : SmallQ_E8_eight) :
    LangRigidityForAlgM .E8 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 8) e8EightMat :=
  fun _ _ _ _ _ _ S hR hq hAlg hρ _ =>
    setupRigid_E8_eight hS S (by have := hR.1; omega) hAlg (by rw [hq]; exact hR.2) hρ

theorem innerPlaneBalanceAtP_E8_eight (hS : SmallQ_E8_eight) (hF : FrobeniusOnRoots)
    (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E8 q).Valid),
      Subgroup.center (CatT ⟨excIndex .E8 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .E8 8 fun p => 7 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algM (k := .E8) trivial (langTorusAtAlgM_E8_8 hF)
    (langRigidityForAlgM_E8_eight hS) hcp hZ

theorem langRigidityForAlgM_E7_two :
    LangRigidityForAlgM .E7 (fun p c => 11 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 2) e7TwoMat :=
  fun _ _ _ _ _ _ S hR hq hAlg hρ _ =>
    setupRigid_E7_two S (by have := hR.1; omega) hAlg (by rw [hq]; exact hR.2) hρ

theorem innerPlaneBalanceAtP_E7_two (hF : FrobeniusOnRoots) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E7 q).Valid),
      Subgroup.center (CatT ⟨excIndex .E7 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .E7 2 fun p => 11 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algM (k := .E7) trivial (langTorusAtAlgM_E7_2 hF)
    langRigidityForAlgM_E7_two hcp hZ

theorem langRigidityForAlgM_E7_three (hS : SmallQ_E7_three) :
    LangRigidityForAlgM .E7 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 3) e7ThreeMat :=
  fun _ _ _ _ _ _ S hR hq hAlg hρ _ =>
    setupRigid_E7_three hS S (by have := hR.1; omega) hAlg (by rw [hq]; exact hR.2) hρ

theorem innerPlaneBalanceAtP_E7_three (hS : SmallQ_E7_three) (hF : FrobeniusOnRoots)
    (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E7 q).Valid),
      Subgroup.center (CatT ⟨excIndex .E7 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .E7 3 fun p => 7 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algM (k := .E7) trivial (langTorusAtAlgM_E7_3 hF)
    (langRigidityForAlgM_E7_three hS) hcp hZ

theorem langRigidityForAlgM_E7_six :
    LangRigidityForAlgM .E7 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 6) e7SixMat :=
  fun _ _ _ _ _ _ S hR hq hAlg hρ _ =>
    setupRigid_E7_six S (by have := hR.1; omega) hAlg (by rw [hq]; exact hR.2) hρ

theorem innerPlaneBalanceAtP_E7_six (hF : FrobeniusOnRoots) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E7 q).Valid),
      Subgroup.center (CatT ⟨excIndex .E7 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .E7 6 fun p => 7 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algM (k := .E7) trivial (langTorusAtAlgM_E7_6 hF)
    langRigidityForAlgM_E7_six hcp hZ

end CFSG.HardMathSupport.Timmesfeld.LangTorus
