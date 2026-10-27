module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTwE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangG2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairE6

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

section Untwisted

theorem springer_exists_lang_untw (hF : FrobeniusOnRoots) {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (w : WeylGroup τ) (hw : ∀ u, w • u = M *ᵥ u) {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    (hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0)
    (hordN : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      p ^ ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p)
    (hperf : Group.IsPerfect ↥(adjointGroup τ K)) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
      (g0 : ModGL τ (AlgebraicClosure K)) (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
      (S : LangSetup τ (AlgebraicClosure K) p),
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (adjointGroup τ K ≃* S.Γ) := by
  classical
  have hperf' : commutator ↥(adjointGroup τ K) = ⊤ := hperf.commutator_eq_top
  have : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
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
  exact ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, hequiv⟩

theorem springer_exists_lang_untw_of_blocks (hF : FrobeniusOnRoots) {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (w : WeylGroup τ) (hw : ∀ u, w • u = M *ᵥ u) (ds : List ℕ) {e : ℕ}
    (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod) (hpow : M ^ e = 1)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e)
    (hother : ∀ d ∈ ds, d ≠ e → ¬ p ∣ d)
    (hdeg : ∀ d ∈ degreesE τ, e ∣ d → ¬ p ∣ d / e)
    (hcount : ((degreesE τ).filter fun d => e ∣ d).length = ds.count e)
    (hperf : Group.IsPerfect ↥(adjointGroup τ K)) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
      (g0 : ModGL τ (AlgebraicClosure K)) (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
      (S : LangSetup τ (AlgebraicClosure K) p),
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 ∧
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
  exact springer_exists_lang_untw hF d hτ K hp hp3 hpq w hw he0 hpow hev hordN hperf

theorem springer_exists_langSetup_E6_two (hF : FrobeniusOnRoots) (K : Type) [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
      (g0 : ModGL Tag.E6 (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6PhiTwoWeyl)
      (S : LangSetup Tag.E6 (AlgebraicClosure K) p),
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiTwoWeyl hg0C hg0 ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (adjointGroup Tag.E6 K ≃* S.Γ) :=
  springer_exists_lang_untw_of_blocks hF 3 (Or.inl ⟨rfl, rfl⟩) K hp (by omega) hpK
    e6PhiTwoWeyl (wordProd_smul_eq_wordMat_mulVec Tag.E6 e6TwoWord) [1, 1, 2, 2, 2, 2]
    e6Two_charpoly e6Two_pow he (not_dvd_of_blocks hp h7 (by decide))
    (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K).1

end Untwisted

section Twisted

theorem springer_exists_lang_twE6 (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag) (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    (hev : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0)
    (hordN : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ ((M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs).factorization p) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
      (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
      (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p),
      S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0 ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (twistedE6RootGroup K σ ≃* S.Γ) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
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
  exact ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, hequiv⟩

theorem springer_exists_lang_twE6_of_blocks (hF : FrobeniusOnRoots) {ℓ f : ℕ} (hℓ : ℓ.Prime)
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
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
      (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
      (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p),
      S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0 ∧
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
  exact springer_exists_lang_twE6 hF hℓ hf K hK σ hσ hp hp3 hpq v hv hn0 hpow hev hordN

theorem springer_exists_langSetup_twistedE6_one (hF : FrobeniusOnRoots) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (hpq : ¬ p ∣ ℓ ^ f) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 1) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
      (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6PhiOneWeyl)
      (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p),
      S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr twE6PhiOneWeyl hg0C hg0 ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (twistedE6RootGroup K σ ≃* S.Γ) := by
  have he' := orderOf_neg_natCast_zmod hp (by omega) hpq he
  rw [show ennola 1 = 2 by decide] at he'
  have hΦ : ∀ x : ℤ, ((cyclotomic 2 ℤ).eval (-x)).natAbs =
      ((cyclotomic 1 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
      show -x + 1 = -(x - 1) by ring, Int.natAbs_neg]
  exact springer_exists_lang_twE6_of_blocks hF hℓ hf K hK σ hσ hp (by omega) hpq
    twE6PhiOneWeyl twE6PhiOneWeyl_smul [1, 1, 1, 1, 2, 2] twE6One_charpoly (by norm_num)
    twE6One_pow (Or.inr (by decide)) he he' hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide))
    (by decide)

end Twisted

section Consumers

theorem innerPlaneBalanceAt_E6_two_of_lang (hcp : LangComponentPieces) :
    InnerPlaneBalanceAt .E6 2 := by
  intro q hv p hp hp7 _ hpq he
  obtain ⟨K, _, _, hK, -, ⟨eq⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  obtain ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, ⟨ε⟩⟩ :=
    springer_exists_langSetup_E6_two frobeniusOnRoots_proved K hp hp7 hpK he
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hpq1 : p ∣ Nat.card K + 1 := dvd_add_one_of_orderOf_eq_two hp he
  have hle := Nat.le_of_dvd (Nat.succ_pos _) hpq1
  have hK8 : Nat.card K ≠ 8 := by
    intro h8
    rw [h8] at hpq1
    have h9 := Nat.le_of_dvd (by norm_num) hpq1
    interval_cases p
    · norm_num at hpq1
    · norm_num at hp
    · norm_num at hp
  have hrig := setupRigid_E6_two hFr hg0C hg0 (by omega) hK8 (by omega) hpq1 S hSD
  have hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) :=
    conj_injective_of_mulEquiv ε.symm (mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K))
  exact InnerPlaneBalance.of_mulEquiv (eq.trans ε)
    (innerPlaneBalance_of_langSetup_rigid S hsyl hrig hcp hinj)

theorem innerPlaneBalanceAt_twistedE6_one_of_lang (hcp : LangComponentPieces) :
    InnerPlaneBalanceAt .twistedE6 1 := by
  intro q hv p hp hp7 _ hpq he
  obtain ⟨K, _, σ, hK, hσ, ⟨eq⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpK : ¬ p ∣ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact not_dvd_card_of_ne hp hpq
  have he' : orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = 1 := by
    rw [← TauCeti.PrimePower.card_def]
    exact he
  obtain ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, ⟨ε⟩⟩ :=
    springer_exists_langSetup_twistedE6_one frobeniusOnRoots_proved q.prime_p q.exponent_pos K
      hK σ hσ hp hp7 hpK he'
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hq2 : 2 ≤ q.p ^ q.exponent := Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
  have hpq1 : p ∣ q.p ^ q.exponent - 1 := dvd_sub_one_of_orderOf_eq_one (by omega) he'
  have hq8 : 8 ≤ q.p ^ q.exponent := by
    have := Nat.le_of_dvd (by omega) hpq1
    omega
  have hrig := setupRigid_twistedE6_one q.prime_p q.exponent_pos hK hσ hFr hg0C hg0 hq8
    (by omega) hpq1 S hSD
  have hC : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)
  have hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) :=
    conj_injective_of_mulEquiv ε.symm hC
  exact InnerPlaneBalance.of_mulEquiv (eq.trans ε)
    (innerPlaneBalance_of_langSetup_rigid S hsyl hrig hcp hinj)

theorem springer_exists_langSetup_twistedE6_two (hF : FrobeniusOnRoots) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (hpq : ¬ p ∣ ℓ ^ f) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 2) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
      (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6PhiTwoWeyl)
      (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p),
      S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr twE6PhiTwoWeyl hg0C hg0 ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (twistedE6RootGroup K σ ≃* S.Γ) := by
  have he' := orderOf_neg_natCast_zmod hp (by omega) hpq he
  rw [show ennola 2 = 1 by decide] at he'
  have hΦ : ∀ x : ℤ, ((cyclotomic 1 ℤ).eval (-x)).natAbs =
      ((cyclotomic 2 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
      show -x - 1 = -(x + 1) by ring, Int.natAbs_neg]
  exact springer_exists_lang_twE6_of_blocks hF hℓ hf K hK σ hσ hp (by omega) hpq
    twE6PhiTwoWeyl twE6PhiTwoWeyl_smul [2, 2, 2, 2, 2, 2] twE6Two_charpoly (by norm_num)
    twE6Two_pow (Or.inr (by decide)) he he' hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide))
    (by decide)

theorem innerPlaneBalanceAt_twistedE6_two_of_lang (hcp : LangComponentPieces) :
    InnerPlaneBalanceAt .twistedE6 2 := by
  intro q hv p hp hp7 _ hpq he
  obtain ⟨K, _, σ, hK, hσ, ⟨eq⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpK : ¬ p ∣ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact not_dvd_card_of_ne hp hpq
  have he' : orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact he
  obtain ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, ⟨ε⟩⟩ :=
    springer_exists_langSetup_twistedE6_two frobeniusOnRoots_proved q.prime_p q.exponent_pos K
      hK σ hσ hp hp7 hpK he'
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hpq1 : p ∣ q.p ^ q.exponent + 1 := dvd_add_one_of_orderOf_eq_two hp he'
  have hle := Nat.le_of_dvd (Nat.succ_pos _) hpq1
  have hq8 : q.p ^ q.exponent ≠ 8 := by
    intro h8
    rw [h8] at hpq1
    have h9 := Nat.le_of_dvd (by norm_num) hpq1
    interval_cases p
    · norm_num at hpq1
    · norm_num at hp
    · norm_num at hp
  have hrig := setupRigid_twistedE6_neg q.prime_p q.exponent_pos hK hσ hFr
    twE6PhiTwoWeyl_smul_neg hg0C hg0 (by omega) hq8 (by omega) hpq1 S hSD
  have hC : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)
  have hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) :=
    conj_injective_of_mulEquiv ε.symm hC
  exact InnerPlaneBalance.of_mulEquiv (eq.trans ε)
    (innerPlaneBalance_of_langSetup_rigid S hsyl hrig hcp hinj)

end Consumers

end CFSG.HardMathSupport.Timmesfeld.CrossChar
