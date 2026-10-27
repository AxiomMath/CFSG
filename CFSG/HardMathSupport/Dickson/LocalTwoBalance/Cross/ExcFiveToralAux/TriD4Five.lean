module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.GoodRootOdd
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodWiringTw

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KGD Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

theorem orderOf_two_ne_one_two {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (he : e = 1 ∨ e = 2) :
    orderOf (((2 : ℕ)) : ZMod p) ≠ e := by
  intro h
  have h1 : ((2 : ℕ) : ZMod p) ^ e = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  rcases he with rfl | rfl
  · have h2 : ((1 : ℕ) : ZMod p) = 0 := by
      push_cast at h1 ⊢
      linear_combination h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((ZMod.natCast_eq_zero_iff 1 p).1 h2))
  · have h2 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast at h1 ⊢
      linear_combination h1
    have h3 := (ZMod.natCast_eq_zero_iff 3 p).1 h2
    have := Nat.le_of_dvd (by norm_num) h3
    omega

section Setups


theorem ordProj_ordTrialityD4_odd {p q e : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hq2 : 2 ≤ q)
    (hpq : ¬ p ∣ q) (he : orderOf (q : ZMod p) = e) (hE : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6) :
    p ^ (ordTrialityD4 q).factorization p = (p ^ (q ^ e - 1).factorization p) ^ 2 := by
  have he0 : e ≠ 0 := by rcases hE with rfl | rfl | rfl | rfl <;> norm_num
  have hcount : ([1, 1, 2, 2, 3, 3, 6, 6, 12] : List ℕ).count e = 2 := by
    rcases hE with rfl | rfl | rfl | rfl <;> decide
  have hsplit := prod_cyclotomic_split e [1, 1, 2, 2, 3, 3, 6, 6, 12]
  have hR : ¬ (p : ℤ) ∣ ((X ^ 12 : ℤ[X]) *
      ((([1, 1, 2, 2, 3, 3, 6, 6, 12] : List ℕ).filter fun d => d ≠ e).map
        fun d => cyclotomic d ℤ).prod).eval (q : ℤ) := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [eval_mul, eval_pow, eval_X, eval_list_prod, hpz.dvd_mul]
    rintro (h | h)
    · exact hpq (Int.natCast_dvd_natCast.1 (hpz.dvd_of_dvd_pow h))
    · rw [hpz.dvd_prod_iff] at h
      obtain ⟨a, ha, hpa⟩ := h
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      rw [List.mem_filter] at hd
      have hde : d ≠ e := by simpa using hd.2
      have hd12 : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 ∨ d = 12 := by
        simpa using hd.1
      have hpd : ¬ p ∣ d := fun h' => by
        have hle := Nat.le_of_dvd (by rcases hd12 with rfl | rfl | rfl | rfl | rfl <;> norm_num) h'
        rcases hd12 with rfl | rfl | rfl | rfl | rfl <;>
          first | omega | (interval_cases p <;> first | omega | exact absurd hp (by norm_num))
      exact not_dvd_cyclotomic_eval_of_ne hp he hde hpd hpa
  have h1 := ordProj_cyclotomic_pow_mul_eval (m := 2) hp hq2 he he0 hR
  have h2 : ((ordTrialityD4 q : ℕ) : ℤ).natAbs = ordTrialityD4 q := Int.natAbs_natCast _
  rw [← h2, ordTrialityD4_eq_eval q (by omega), hsplit, hcount]
  rw [← h1]
  congr 3
  ring_nf

section Rigid

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem three_le_q_of_class_odd (S : LangSetup TwistTag.D4.tag L p) (hp5 : 5 ≤ p) {e : ℕ}
    (he : e = 1 ∨ e = 2) (hord : orderOf ((S.D.q : ℕ) : ZMod p) = e) : 3 ≤ S.D.q := by
  refine three_le_q_of_ne_two S fun h2 => ?_
  rw [h2] at hord
  exact orderOf_two_ne_one_two S.hp hp5 he hord

theorem setupRigid_triD4_of_check_odd (S : LangSetup TwistTag.D4.tag L p) (hp3 : 3 ≤ p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) {M : List (List ℤ)} {e : ℕ} {cert : List (ℕ × ℕ × ℕ)}
    (hq3 : 3 ≤ S.D.q) (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) (hρ : RhoIs S M)
    (h : classCheck Tag.D4.rank (cartanList Tag.D4) M Tag.D4.artifactRoots e cert = true)
    (hP : NoTriCosetCentralizes TwistTag.D4.tag L (diagramMap TwistTag.D4 L)) : SetupRigid S :=
  setupRigid_triD4_of_goodRoots S hΦ hAlg
    (goodRootsGenerate_of_classCheck_odd S (Or.inl rfl) (toMat_cartanList _) hρ hq3 hp3 he h) hP

theorem setupRigid_triD4_one_odd (S : LangSetup TwistTag.D4.tag L p) (hp5 : 5 ≤ p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 1)
    (hρ : RhoIs S triD4OneMat) : SetupRigid S :=
  setupRigid_triD4_of_check_odd S (by omega) hΦ hAlg (three_le_q_of_class_odd S hp5 (Or.inl rfl) he)
    he hρ triD4One_classCheck noTriCosetCentralizes_D4

theorem setupRigid_triD4_two_odd (S : LangSetup TwistTag.D4.tag L p) (hp5 : 5 ≤ p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 2)
    (hρ : RhoIs S triD4TwoMat) : SetupRigid S :=
  setupRigid_triD4_of_check_odd S (by omega) hΦ hAlg
    (three_le_q_of_class_odd S hp5 (Or.inr rfl) he) he hρ triD4Two_classCheck
    noTriCosetCentralizes_D4

end Rigid

theorem exists_lang_triD4_of_class_alg_rho_odd (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
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
  refine exists_lang_triD4_alg_rho hF hℓ hf K hK σ hσ hp h5 hpq w hw hn0 hpow hev ?_
  have h1 := ordProj_ordTrialityD4_odd hp h5 hq2 hpq he hE
  have h2 := ordProj_cyclotomic_pow_mul_eval (m := 2) hp hq2 he he0 hR
  rw [← hdet'] at h2
  rw [hC]
  exact (Nat.pow_right_injective hp.two_le (h1.trans h2.symm)).le

theorem langTorusAtAlgW_trialityD4_1_odd (hF : FrobeniusOnRoots) :
    LangTorusAtAlgW .trialityD4 (fun p c => 5 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 1)
      (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
        (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4OneMat S) :=
  langTorusAtAlgW_trialityD4_of_model triD4OneMat
    fun ℓ f hℓ hf K _ hK σ hσ p hp (h5 : 5 ≤ p) hpq hC he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hΦ, hsyl, hequiv⟩ :=
      exists_lang_triD4_of_class_alg_rho_odd hF hℓ hf K hK σ hσ hp h5 hpq hC he (Or.inl rfl)
      ((coxeterSystem TwistTag.D4.tag).wordProd d4OneWord) d4One_hw (by norm_num) d4One_pow
      (cyclotomic 3 ℤ) d4One_det
      (not_dvd_cyclotomic_eval_of_ne hp he (by norm_num) (fun h => by
        have := Nat.le_of_dvd (by norm_num) h
        omega))
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hΦ, hsyl, hequiv⟩
    rw [hρ γ hγ]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem langTorusAtAlgW_trialityD4_2_odd (hF : FrobeniusOnRoots) :
    LangTorusAtAlgW .trialityD4 (fun p c => 5 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 2)
      (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
        (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4TwoMat S) :=
  langTorusAtAlgW_trialityD4_of_model triD4TwoMat
    fun ℓ f hℓ hf K _ hK σ hσ p hp (h5 : 5 ≤ p) hpq hC he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hΦ, hsyl, hequiv⟩ :=
      exists_lang_triD4_of_class_alg_rho_odd hF hℓ hf K hK σ hσ hp h5 hpq hC he (by decide)
      ((coxeterSystem TwistTag.D4.tag).wordProd d4TwoWord) d4Two_hw (by norm_num)
      d4Two_pow (cyclotomic 6 ℤ) d4Two_det
      (not_dvd_cyclotomic_eval_of_ne hp he (by norm_num) (fun h => by
        have := Nat.le_of_dvd (by norm_num) h
        have h6 : p ≤ 6 := this
        interval_cases p <;> first | omega | exact absurd hp (by norm_num)))
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hΦ, hsyl, hequiv⟩
    rw [hρ γ hγ]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem langRigidityForAlgW_trialityD4_1_odd :
    LangRigidityForAlgW .trialityD4 (fun p c => 5 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 1)
      (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
        (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4OneMat S) :=
  fun _ _ _ L _ _ S hR hq hAlg hW _ =>
    setupRigid_triD4_one_odd S hR.1 hW.2 hAlg (by rw [hq]; exact hR.2) hW.1

theorem langRigidityForAlgW_trialityD4_2_odd :
    LangRigidityForAlgW .trialityD4 (fun p c => 5 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 2)
      (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
        (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4TwoMat S) :=
  fun _ _ _ L _ _ S hR hq hAlg hW _ =>
    setupRigid_triD4_two_odd S hR.1 hW.2 hAlg (by rw [hq]; exact hR.2) hW.1

theorem innerPlaneBalance_of_lang_rigid_algW_odd {k : LieFamily} {e : ℕ}
    (hk : IsExceptionalFam k) {R : ℕ → Prop}
    {W : ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}, LangSetup (excTag k) L p → Prop}
    (ha : LangTorusAtAlgW k (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) W)
    (hrig : LangRigidityForAlgW k (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) W)
    (hcp : LangComponentPieces) (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid)
    (hinj : Function.Injective
      (MulAut.conj : CatT ⟨excIndex k q, hv⟩ →* MulAut (CatT ⟨excIndex k q, hv⟩)))
    {p : ℕ} (hp : p.Prime) (hRp : R p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = e) :
    InnerPlaneBalance p (CatT ⟨excIndex k q, hv⟩) := by
  obtain ⟨L, hF, hA, S, hSq, hAlg, hW, hsyl, hε⟩ := ha hk q hv _ hp ⟨hRp, he⟩ hpq
  obtain ⟨ε⟩ := hε
  exact InnerPlaneBalance.of_mulEquiv ε
    (innerPlaneBalance_of_langSetup_rigid S hsyl (hrig q hv _ L S ⟨hRp, he⟩ hSq hAlg hW ⟨ε⟩) hcp
      (conj_injective_of_mulEquiv ε hinj))

theorem innerPlaneBalance_trialityD4_one_odd (q : TauCeti.PrimePower)
    (hv : (excIndex .trialityD4 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 1) (hcp : LangComponentPieces) :
    InnerPlaneBalance p (CatT ⟨excIndex .trialityD4 q, hv⟩) :=
  innerPlaneBalance_of_lang_rigid_algW_odd (k := .trialityD4) trivial
    (langTorusAtAlgW_trialityD4_1_odd frobeniusOnRoots_proved) langRigidityForAlgW_trialityD4_1_odd
    hcp q hv (conj_injective_cat_trialityD4 q hv) hp hp5 hpq he

theorem innerPlaneBalance_trialityD4_two_odd (q : TauCeti.PrimePower)
    (hv : (excIndex .trialityD4 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 2) (hcp : LangComponentPieces) :
    InnerPlaneBalance p (CatT ⟨excIndex .trialityD4 q, hv⟩) :=
  innerPlaneBalance_of_lang_rigid_algW_odd (k := .trialityD4) trivial
    (langTorusAtAlgW_trialityD4_2_odd frobeniusOnRoots_proved) langRigidityForAlgW_trialityD4_2_odd
    hcp q hv (conj_injective_cat_trialityD4 q hv) hp hp5 hpq he

end Setups

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
