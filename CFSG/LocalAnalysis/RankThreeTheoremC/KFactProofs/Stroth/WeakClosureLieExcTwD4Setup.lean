module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTriD4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus Polynomial
open scoped Matrix commutatorElement

set_option linter.unusedSectionVars false


theorem tw_ordProj_ordTrialityD4 {p q e : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hq2 : 2 ≤ q)
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

theorem exists_lang_triD4_data (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ}
    (w : WeylGroup TwistTag.D4.tag)
    (hw : ∀ x, w • x = M *ᵥ permLattice TwistTag.D4.perm.symm x)
    {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    (hev : (M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ)).det ≠ 0)
    (hord : (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p ≤
      ((M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ)).det.natAbs).factorization p) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (_ : ∀ c, Fr c = c ^ (ℓ ^ f))
      (D : LangDatum TwistTag.D4.tag L), D.Φ = twistHom TwistTag.D4 L Fr ∧
      D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∧ D.model ≤ D.Γ ∧
      (∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* D.Γ) := by
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
  have hrange := triEmb_range (K := K) (σ := σ) (L := L) hℓ hf hK hσ Fr hFr
  have hfix : D.fix = (triEmb K σ L).range := by
    rw [hrange]
    ext x
    rw [LangDatum.mem_fix, hD]
    rfl
  have hmodel : D.model ≤ D.Γ := by
    have h1 : D.Γ.map (MulAut.conj D.g0).toMonoidHom = D.fix := by
      rw [LangDatum.map_conj_Γ, hd.derived]
      exact hfix.symm
    have h2 : D.model.map (MulAut.conj D.g0).toMonoidHom = D.fix := LangDatum.map_conj_model D
    intro x hx
    have hx' : (MulAut.conj D.g0) x ∈ D.fix := by
      rw [← h2]
      exact ⟨x, hx, rfl⟩
    rw [← h1] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := (MulAut.conj D.g0).injective hyx
    rwa [← this]
  exact ⟨L, inferInstance, inferInstance, Fr, hFr, S.D, by rw [hSD]; exact hD, by rw [hSD]; rfl,
    by rw [hSD]; exact hmodel, hsyl, hequiv⟩

theorem exists_lang_triD4_data_of_class (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (hC : Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ordTrialityD4 (ℓ ^ f))
    {e : ℕ} (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e) (hE : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6)
    {M : Matrix (Fin 4) (Fin 4) ℤ} (w : WeylGroup TwistTag.D4.tag)
    (hw : ∀ x, w • x = M *ᵥ permLattice TwistTag.D4.perm.symm x) {n : ℕ} (hn0 : n ≠ 0)
    (hpow : M ^ n = 1) (R : ℤ[X])
    (hdet : ∀ q : ℤ, (M - q • (1 : Matrix (Fin 4) (Fin 4) ℤ)).det =
      (cyclotomic e ℤ ^ 2 * R).eval q)
    (hR : ¬ (p : ℤ) ∣ R.eval ((ℓ ^ f : ℕ) : ℤ)) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (_ : ∀ c, Fr c = c ^ (ℓ ^ f))
      (D : LangDatum TwistTag.D4.tag L), D.Φ = twistHom TwistTag.D4 L Fr ∧
      D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∧ D.model ≤ D.Γ ∧
      (∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* D.Γ) := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have he0 : e ≠ 0 := by rcases hE with rfl | rfl | rfl | rfl <;> norm_num
  have hpos : 0 < (cyclotomic e ℤ).eval ((ℓ ^ f : ℕ) : ℤ) :=
    cyclotomic_pos' e (by exact_mod_cast hq2)
  have hRne : R.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := fun h => hR (by rw [h]; exact dvd_zero _)
  have hdet' := hdet ((ℓ ^ f : ℕ) : ℤ)
  have hev : (M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)).det ≠ 0 := by
    rw [hdet', eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hpos.ne') hRne
  refine exists_lang_triD4_data hF hℓ hf K hK σ hσ hp h5 hpq w hw hn0 hpow hev ?_
  have h1 := tw_ordProj_ordTrialityD4 hp h5 hq2 hpq he hE
  have h2 := ordProj_cyclotomic_pow_mul_eval (m := 2) hp hq2 he he0 hR
  rw [← hdet'] at h2
  rw [hC]
  exact (Nat.pow_right_injective hp.two_le (h1.trans h2.symm)).le

theorem exists_lang_triD4_model {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (w : WeylGroup TwistTag.D4.tag) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L ℓ) (Fr : L →+* L)
      (_ : ∀ c, Fr c = c ^ (ℓ ^ f)) (D : LangDatum TwistTag.D4.tag L),
      D.Φ = twistHom TwistTag.D4 L Fr ∧ D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∧
      D.model ≤ D.Γ ∧ Finite D.model ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* D.Γ) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  haveI hLchar : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L
    (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)
    (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.D4.tag) L w)
  let D : LangDatum Tag.D4 L := LangDatum.ofTwist TwistTag.D4 Fr (ℓ ^ f) hFr w hg0C hg0
  have hD : D.Φ = twistHom TwistTag.D4 L Fr := rfl
  have hι : Function.Injective (triEmb K σ L) := triEmb_injective
  have hd := langDescent_triD4 (K := K) (L := L) hℓ hf hK σ hσ hFr D hD (p := 3)
  have hrange := triEmb_range (K := K) (σ := σ) (L := L) hℓ hf hK hσ Fr hFr
  have hfix : D.fix = (triEmb K σ L).range := by
    rw [hrange]
    ext x
    rw [LangDatum.mem_fix, hD]
    rfl
  have hmodel : D.model ≤ D.Γ := by
    have h1 : D.Γ.map (MulAut.conj D.g0).toMonoidHom = D.fix := by
      rw [LangDatum.map_conj_Γ, hd.derived]
      exact hfix.symm
    have h2 : D.model.map (MulAut.conj D.g0).toMonoidHom = D.fix := LangDatum.map_conj_model D
    intro x hx
    have hx' : (MulAut.conj D.g0) x ∈ D.fix := by
      rw [← h2]
      exact ⟨x, hx, rfl⟩
    rw [← h1] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := (MulAut.conj D.g0).injective hyx
    rwa [← this]
  exact ⟨L, inferInstance, inferInstance, hLchar, Fr, hFr, D, hD, rfl, hmodel, hd.finite_model,
    ⟨hd.mulEquiv hι⟩⟩

theorem tw_hv_of_hw {t : TwistTag} {w : WeylGroup t.tag}
    {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hw : ∀ x, w • x = M *ᵥ permLattice t.perm.symm x) :
    ∀ x, w • permLattice t.perm x = M *ᵥ x := fun x => by
  rw [hw, CFSG.LieType.Chevalley.permLattice_symm_permLattice]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
