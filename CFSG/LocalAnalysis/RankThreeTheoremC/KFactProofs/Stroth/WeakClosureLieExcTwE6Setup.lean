module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTwE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.LieType.SeitzGeneration.ExcTorusTw

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus Polynomial
open scoped Matrix commutatorElement

set_option linter.unusedSectionVars false

theorem tw_not_dvd_of_dvd_144 {p x : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hx : x ∣ 144) : ¬ p ∣ x := by
  intro h
  have h1 : p ∣ 12 ^ 2 := h.trans hx
  have h2 : p ∣ 12 := hp.dvd_of_dvd_pow h1
  have h3 := Nat.le_of_dvd (by norm_num) h2
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem tw_not_dvd_div_of_144 {p e : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {D : List ℕ}
    (h : ∀ d ∈ D, e ∣ d → d / e ∣ 144) : ∀ d ∈ D, e ∣ d → ¬ p ∣ d / e :=
  fun d hd hed => tw_not_dvd_of_dvd_144 hp h5 (h d hd hed)

theorem exists_lang_twE6_data (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag) (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    (hev : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0)
    (hordN : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ ((M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs).factorization p) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (_ : ∀ c, Fr c = c ^ (ℓ ^ f))
      (D : LangDatum TwistTag.E6.tag L), D.Φ = twistHom TwistTag.E6 L Fr ∧
      D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L v ∧
      (∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) ∧
      Nonempty (twistedE6RootGroup K σ ≃* D.Γ) := by
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
  exact ⟨L, inferInstance, inferInstance, Fr, hFr, S.D, by rw [hSD]; exact hD, by rw [hSD]; rfl,
    hsyl, hequiv⟩

theorem exists_lang_twE6_data_of_blocks (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
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
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (_ : ∀ c, Fr c = c ^ (ℓ ^ f))
      (D : LangDatum TwistTag.E6.tag L), D.Φ = twistHom TwistTag.E6 L Fr ∧
      D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L v ∧
      (∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) ∧
      Nonempty (twistedE6RootGroup K σ ≃* D.Γ) := by
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
  exact exists_lang_twE6_data hF hℓ hf K hK σ hσ hp hp3 hpq v hv hn0 hpow hev hordN

theorem exists_lang_twE6_model {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (v : WeylGroup TwistTag.E6.tag) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L ℓ) (Fr : L →+* L)
      (_ : ∀ c, Fr c = c ^ (ℓ ^ f)) (D : LangDatum TwistTag.E6.tag L),
      D.Φ = twistHom TwistTag.E6 L Fr ∧ D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L v ∧
      Finite D.model ∧ Nonempty (twistedE6RootGroup K σ ≃* D.Γ) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  haveI hLchar : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L v
  let D : LangDatum Tag.E6 L := LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0
  have hD : D.Φ = twistHom TwistTag.E6 L Fr := rfl
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hd := langDescent_twE6 (K := K) (L := L) hℓ hf hK σ hσ hFr D hD (p := 5) (by norm_num)
    (by norm_num)
  exact ⟨L, inferInstance, inferInstance, hLchar, Fr, hFr, D, hD, rfl, hd.finite_model,
    ⟨hd.mulEquiv hι⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
