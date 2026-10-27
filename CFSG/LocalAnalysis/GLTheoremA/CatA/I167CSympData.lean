module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)

private theorem i167CS_data_aux1 {K : Type} [Field K] [Finite K] {N : ℕ}
    (hN : 1 ≤ N) (hcard : Nat.card K = 2 ^ N) : (2 : K) = 0 := by
  haveI := Fintype.ofFinite K
  obtain ⟨q, hq, k, hqp, hqcard⟩ := FiniteField.card' K
  have hc2 := hcard
  rw [Nat.card_eq_fintype_card, hqcard] at hc2
  have hdvd : q ∣ 2 ^ N := by
    rw [← hc2]
    exact dvd_pow_self q (PNat.ne_zero k)
  have hq2 : q = 2 :=
    (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
  subst hq2
  exact_mod_cast CharP.cast_eq_zero K 2

private theorem i167CS_data_aux2 {S : Type} [Group S] {K : Type} [Field K] [Finite K]
    {m p : ℕ} {α : MulAut S} (hcen : Subgroup.center S = ⊥) (hαp : α ^ p = 1)
    (hα1 : α ≠ 1) (h2 : (2 : K) = 0) {e : S ≃* StatedProj (StatedSp m K)}
    {A : gsp m K} (hαu : ∀ l : S, e (α l) = conjAut m K A (e l)) :
    ∃ x : StatedSp m K, x ^ p = 1 ∧ x ≠ 1 ∧
      MulAut.congr e α = MulAut.conj (proj m K x) := by
  obtain ⟨x, hx⟩ := Y10GInnSympRed.exists_conjAut_eq_conj h2 A
  have hMEq : MulAut.congr e α = MulAut.conj (proj m K x) := by
    rw [← hx]
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hZ : Subgroup.center (StatedProj (StatedSp m K)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hz (e g)
    rw [hcen, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hz'
  have hpow : MulAut.conj (proj m K x) ^ p = 1 := by
    rw [← hMEq, ← map_pow, hαp, map_one]
  have hxp : x ^ p = 1 :=
    Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hα1
    ext s
    have h := hαu s
    rw [hx, hx1, map_one, MulAut.conj_apply, inv_one, mul_one, one_mul] at h
    simpa using e.injective h
  exact ⟨x, hxp, hx1, hMEq⟩

private theorem i167CS_data_aux3 {S : Type} [Group S] [Finite S] {labK : GLALabel}
    {α : MulAut S} {p : ℕ} (hp : p.Prime) (hcen : Subgroup.center S = ⊥)
    (hαp : α ^ p = 1) (hα1 : α ≠ 1) {J : Subgroup S}
    (hJ : GLAPComponent p (fixSubgroup α) J) (hm : 2 ≤ labK.rank)
    {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2 ^ labK.n)
    (hc : (canonLabel labK).n = labK.n)
    (θ : S ⧸ Subgroup.center S ≃* StatedProj (StatedSp labK.rank K))
    (u : MulAut (StatedProj (StatedSp labK.rank K)))
    (A : gsp labK.rank K) (hA : conjAut labK.rank K A = u)
    (hind : CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s) u) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (n m : ℕ) (x : StatedSp m K)
      (J' : Subgroup (StatedProj (StatedSp m K))),
      1 ≤ n ∧ Nat.card K = 2 ^ n ∧ (2 : K) = 0 ∧ 2 ≤ m ∧ x ^ p = 1 ∧ x ≠ 1 ∧
      GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) J' ∧
      Nonempty (PQuot p J ≃* PQuot p J') := by
  let e : S ≃* StatedProj (StatedSp labK.rank K) :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans
      QuotientGroup.quotientBot).symm.trans θ
  have hαu : ∀ l : S, e (α l) = conjAut labK.rank K A (e l) := by
    intro l
    rw [hA]
    exact (hind l (α l) rfl).symm
  have hcard' : Nat.card K = 2 ^ (canonLabel labK).n := by rw [hc]; exact hcard
  have hn : 1 ≤ (canonLabel labK).n := by
    rcases Nat.eq_zero_or_pos (canonLabel labK).n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard'
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have h2 : (2 : K) = 0 := i167CS_data_aux1 hn hcard'
  obtain ⟨x, hxp, hx1, hMEq⟩ := i167CS_data_aux2 hcen hαp hα1 h2 hαu
  have hJ' : GLAPComponent p (fixSubgroup (MulAut.conj (proj labK.rank K x)))
      (J.map e.toMonoidHom) := by
    rw [← hMEq, ← CFSG.LocalAnalysis.GLTheoremA.Y10F.fixSubgroup_map_congr e α]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff hp e.injective).mpr hJ
  have hkerbot : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  have hequiv : Nonempty (PQuot p J ≃* PQuot p (J.map e.toMonoidHom)) := by
    refine nonempty_pQuot_equiv_map hp (ψ := e.toMonoidHom) ?_ J
    rw [hkerbot, Subgroup.card_bot]
    exact hp.not_dvd_one
  exact ⟨K, inferInstance, inferInstance, (canonLabel labK).n, labK.rank, x, J.map e.toMonoidHom,
    hn, hcard', h2, hm, hxp, hx1, hJ', hequiv⟩

theorem i167CS_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S} {p : ℕ}
    (hp : p.Prime) (hcen : Subgroup.center S = ⊥) (hFam : labK.tag = .B ∨ labK.tag = .C)
    (hαp : α ^ p = 1) (hα1 : α ≠ 1) (hin : InnDiagKind S labK α) {J : Subgroup S}
    (hJ : GLAPComponent p (fixSubgroup α) J) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (n m : ℕ) (x : StatedSp m K)
      (J' : Subgroup (StatedProj (StatedSp m K))),
      1 ≤ n ∧ Nat.card K = 2 ^ n ∧ (2 : K) = 0 ∧ 2 ≤ m ∧ x ^ p = 1 ∧ x ≠ 1 ∧
      GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) J' ∧
      Nonempty (PQuot p J ≃* PQuot p J') := by
  unfold InnDiagKind CFSG.Assembly.LargeEvenMarking at hin
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ht
  all_goals
    have hm : 2 ≤ labK.rank := by
      have h := hlam
      simp only [LargeEvenInLambda2, ht] at h
      exact h.2.1
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, ht]
    unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeSymplectic at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, hA⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hu
    exact i167CS_data_aux3 hp hcen hαp hα1 hJ hm hcard hc θ u A hA hind

end CFSG.LocalAnalysis.GLTheoremA.I167

end
