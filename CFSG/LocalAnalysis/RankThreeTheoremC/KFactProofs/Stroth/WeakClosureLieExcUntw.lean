module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcFpf
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcFrame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice
  Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

theorem sylowFrame_untw {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (w : WeylGroup τ)
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hw : ∀ u, w • u = M *ᵥ u) {n : ℕ} (hn0 : n ≠ 0)
    (hpow : M ^ n = 1) (hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0)
    (hordN : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      p ^ ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) : SylowFrame τ K p w := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨L, _, _, _, D, Fr, hFr, hD, hDq, hDn, hK0, hd⟩ :=
    exists_untw_frame d hτ K hp hp3 w hperf
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  have hι : Function.Injective ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hT : D.torus = twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr := by
    show twistedTorusOf D.n D.Φ = _
    rw [hD, hDn]
  have hT0 : D.torus = (fixedCharTuples M Fr).map (rootDiagUnitHom τ L) := by
    rw [hT]
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
  have hsyl := exists_sylow_of_hord D hp _ hι hd ⟨D.torus, le_rfl, hord⟩
  exact ⟨L, inferInstance, inferInstance, Fr, D, hFr, hD, hDn, ⟨hd.mulEquiv hι⟩, hsyl⟩

theorem hordN_of_blocks {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (ds : List ℕ) {e : ℕ}
    (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e)
    (hother : ∀ d ∈ ds, d ≠ e → ¬ p ∣ d)
    (hdeg : ∀ d ∈ degreesE τ, e ∣ d → ¬ p ∣ d / e)
    (hcount : ((degreesE τ).filter fun d => e ∣ d).length = ds.count e) :
    M.charpoly.eval (Nat.card K : ℤ) ≠ 0 ∧
      p ^ (Nat.card (adjointGroup τ K)).factorization p =
        p ^ ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p := by
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : ∀ d ∈ degreesE τ, 0 < d := by
    rcases hτ with rfl | rfl | rfl <;> decide
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
    rw [ordProj_card_adjointGroup_E hτ hp hp3 hpq, prod_ordProj_pow_sub_one hp (by omega) hpq hq2
      he (degreesE τ) (fun d hd hed => ⟨(hcard d hd).ne', hdeg d hd hed⟩), hcount]
  have hpos : 0 < (cyclotomic e ℤ).eval (Nat.card K : ℤ) :=
    cyclotomic_pos' e (by exact_mod_cast hq2)
  have hRne : (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      (Nat.card K : ℤ) ≠ 0 := fun h => hR (by rw [h]; exact dvd_zero _)
  have hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0 := by
    rw [hchar', eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hpos.ne') hRne
  refine ⟨hev, ?_⟩
  rw [hord, hchar', ordProj_cyclotomic_pow_mul_eval hp hq2 he he0 hR]

theorem sylowFrame_untw_blocks {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (word : List (Fin τ.rank)) (ds : List ℕ) {e : ℕ}
    (hchar : (wordMat τ word).charpoly = (ds.map fun d => cyclotomic d ℤ).prod)
    (hpow : wordMat τ word ^ e = 1) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e)
    (hother : ∀ d ∈ ds, d ≠ e → ¬ p ∣ d) (hdeg : ∀ d ∈ degreesE τ, e ∣ d → ¬ p ∣ d / e)
    (hcount : ((degreesE τ).filter fun d => e ∣ d).length = ds.count e)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) : SylowFrame τ K p (wp τ word) := by
  obtain ⟨hev, hordN⟩ := hordN_of_blocks hτ K hp hp3 hpq ds hchar he hother hdeg hcount
  have hn0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have hw : ∀ u, wp τ word • u = (wordMat τ word) *ᵥ u := fun u =>
    wordProd_smul_eq_wordMat_mulVec τ word u
  rcases hτ with rfl | rfl | rfl
  · exact sylowFrame_untw 3 (Or.inl ⟨rfl, rfl⟩) K hp hp3 (wp _ word) hw hn0 hpow hev hordN hperf
  · exact sylowFrame_untw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3 (wp _ word) hw hn0 hpow hev
      hordN hperf
  · exact sylowFrame_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3 (wp _ word) hw hn0 hpow hev
      hordN hperf

theorem not_dvd_of_dvd_12 {p x : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hx : x ∣ 12) : ¬ p ∣ x := by
  intro h
  have h12 : p ∣ 12 := h.trans hx
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases p <;> first | omega | (norm_num at hp)

theorem not_dvd_div_of_12 {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {D : List ℕ}
    (h : ∀ d ∈ D, e ∣ d → d / e ∣ 12) : ∀ d ∈ D, e ∣ d → ¬ p ∣ d / e :=
  fun d hd hed => not_dvd_of_dvd_12 hp hp5 (h d hd hed)

theorem not_dvd_of_blocks_small {p e : ℕ} (hp5 : 5 ≤ p) {ds : List ℕ}
    (h : ∀ d ∈ ds, d ≠ e → d ≤ 4 ∧ d ≠ 0) : ∀ d ∈ ds, d ≠ e → ¬ p ∣ d := fun d hd hde hpd => by
  have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (h d hd hde).2) hpd
  have h2 := (h d hd hde).1
  omega

theorem five_or_seven_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : p = 5 ∨ 7 ≤ p := by
  rcases (by omega : p = 5 ∨ p = 6 ∨ 7 ≤ p) with h | h | h
  · exact Or.inl h
  · subst h
    norm_num at hp
  · exact Or.inr h

theorem seven_or_eleven_le {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : p = 7 ∨ 11 ≤ p := by
  rcases (by omega : p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ 11 ≤ p) with h | h | h | h | h
  · exact Or.inl h
  · subst h
    norm_num at hp
  · subst h
    norm_num at hp
  · subst h
    norm_num at hp
  · exact Or.inr h

theorem orderOf_dvd_sub_one' {p q e : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q)
    (he : orderOf (q : ZMod p) = e) : e ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  exact he ▸ ZMod.orderOf_dvd_card_sub_one hq0

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
