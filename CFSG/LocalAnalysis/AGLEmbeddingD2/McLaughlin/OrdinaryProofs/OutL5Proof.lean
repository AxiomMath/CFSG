module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowClauseO
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeRank
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.ComponentClassification.OuterAutomorphisms

theorem mulAut_pow_apply_iterate {G : Type} [Group G] (ψ : MulAut G) (m : ℕ) (x : G) :
    (ψ ^ m) x = ψ^[m] x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Function.iterate_succ_apply, ← ih]
    rfl

theorem autThreePowInner_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : AutThreePowInner Y) : AutThreePowInner X := by
  intro ψ k hψ
  let φ : Y ≃* Y := e.symm.trans (ψ.trans e)
  have hiter : ∀ (n : ℕ) (y : Y), φ^[n] y = e (ψ^[n] (e.symm y)) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp [φ]
  obtain ⟨a, ha⟩ := hY φ k (fun y => by rw [hiter, hψ]; simp)
  refine ⟨e.symm a, fun x => ?_⟩
  have hx := ha (e x)
  simp only [φ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hx
  apply e.injective
  rw [hx]
  simp [map_mul, map_inv]

theorem autThreePowInner_of_not_three_dvd_outer {G : Type} [Group G]
    (h3 : ¬ 3 ∣ Nat.card (Outer G)) : AutThreePowInner G := by
  intro ψ k hψ
  have hfin : Finite (Outer G) := Nat.finite_of_card_ne_zero (fun h0 => h3 (h0 ▸ dvd_zero 3))
  have hpow1 : (ψ : MulAut G) ^ (3 ^ k) = 1 := by
    apply MulEquiv.ext
    intro x
    rw [mulAut_pow_apply_iterate, hψ]
    rfl
  have hq : (QuotientGroup.mk (s := inner G) (ψ : MulAut G) : Outer G) ^ (3 ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hpow1]
    exact one_mem _
  have hdvd1 : orderOf (QuotientGroup.mk (s := inner G) (ψ : MulAut G) : Outer G) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one hq
  have hdvd2 : orderOf (QuotientGroup.mk (s := inner G) (ψ : MulAut G) : Outer G)
      ∣ Nat.card (Outer G) :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (Outer G)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  have hord : orderOf (QuotientGroup.mk (s := inner G) (ψ : MulAut G) : Outer G) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hdvd2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hord
  obtain ⟨a, ha⟩ := hord
  exact ⟨a, fun x => by
    have hx := congrArg (fun φ : MulAut G => φ x) ha
    simp only [MulAut.conj_apply] at hx
    exact hx.symm⟩

theorem autThreePowInner_projSL_gf2 {n : ℕ} (hn : 3 ≤ n) :
    AutThreePowInner (CFSG.Assembly.RankThreeEven.projSL n (GaloisField 2 1)) :=
  autThreePowInner_of_not_three_dvd_outer
    (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 hn)

theorem outL5_proved : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutL5 := by
  intro X _ hX
  obtain ⟨d, ⟨q, hq2, hd⟩, ⟨e⟩⟩ := hX
  obtain ⟨t, hv⟩ := d
  simp only at hd
  subst hd
  have hA := CFSG.AGLEmbedding.KFactProofs.CoverFive.statedClassicalModel_psl_of_typeA 4 q hv e
  have hcard : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
  have hdvd : q.p ∣ 2 := hcard ▸ dvd_pow_self q.p q.exponent_pos.ne'
  have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  have hexp : q.exponent = 1 := by
    rw [hp2] at hcard
    exact Nat.pow_right_injective (le_refl 2) (by simpa using hcard)
  rw [hp2, hexp] at hA
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel hA
  exact autThreePowInner_of_mulEquiv φ (autThreePowInner_projSL_gf2 (by norm_num))

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
