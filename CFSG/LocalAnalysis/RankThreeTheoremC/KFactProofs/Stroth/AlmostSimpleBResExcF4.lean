module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcE
public import CFSG.LieType.SeitzGeneration.ExcTorusF4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Arith

variable {p : ℕ} (hp : p.Prime)

include hp

theorem dvd_of_orderOf_three {q : ℕ} (he : orderOf ((q : ℕ) : ZMod p) = 3) :
    p ∣ q ^ 2 + q + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := (q : ZMod p) with hxdef
  have hx3 : x ^ 3 = 1 := by rw [← he]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at he
    omega
  have h0 : x ^ 2 + x + 1 = 0 := by
    have h : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hx1
    · exact h
  exact (ZMod.natCast_eq_zero_iff (q ^ 2 + q + 1) p).1 (by push_cast; exact h0)

theorem dvd_of_orderOf_four {q : ℕ} (he : orderOf ((q : ℕ) : ZMod p) = 4) :
    p ∣ q ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := (q : ZMod p) with hxdef
  have hx4 : x ^ 4 = 1 := by rw [← he]; exact pow_orderOf_eq_one x
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    omega
  have h0 : x ^ 2 + 1 = 0 := by
    have h : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by linear_combination hx4
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hx2
    · exact h
  exact (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) p).1 (by push_cast; exact h0)

theorem dvd_of_orderOf_six {q : ℕ} (hq : 1 ≤ q) (he : orderOf ((q : ℕ) : ZMod p) = 6) :
    p ∣ q ^ 2 - q + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := (q : ZMod p) with hxdef
  have hx6 : x ^ 6 = 1 := by rw [← he]; exact pow_orderOf_eq_one x
  have hx3 : x ^ 3 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    omega
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    omega
  have hx3' : x ^ 3 + 1 = 0 := by
    have h : (x ^ 3 - 1) * (x ^ 3 + 1) = 0 := by linear_combination hx6
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hx3
    · exact h
  have hxm : x + 1 ≠ 0 := by
    intro h
    have h1 : x = -1 := eq_neg_of_add_eq_zero_left h
    apply hx2
    rw [h1]
    norm_num
  have h0 : x ^ 2 - x + 1 = 0 := by
    have h : (x + 1) * (x ^ 2 - x + 1) = 0 := by linear_combination hx3'
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hxm
    · exact h
  have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  refine (ZMod.natCast_eq_zero_iff (q ^ 2 - q + 1) p).1 ?_
  push_cast [Nat.cast_sub hle]
  exact h0

end Arith

section


theorem exists_elemAbelian_sq_F4 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpk : ¬ p ∣ Nat.card k)
    (hcnt : degCount Tag.F4 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ∃ E : Subgroup (adjointGroup Tag.F4 k), IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card k : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpk
  have hle : e ≤ 30 := by
    by_contra h
    have : degCount Tag.F4 e = 0 := by
      unfold degCount degreesW
      simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
      intro d hd hed
      have hd' : d ≤ 12 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        omega
      have := Nat.le_of_dvd (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        omega) hed
      omega
    omega
  have h346 : e = 3 ∨ e = 4 ∨ e = 6 := by
    interval_cases e <;> first | (left; rfl) | (right; left; rfl) | (right; right; rfl) |
      exact absurd hcnt (by decide)
  have hk1 : 1 ≤ Nat.card k := Nat.card_pos
  rcases h346 with rfl | rfl | rfl
  · exact (sylowTorus_F4_three k hp hp3 (dvd_of_orderOf_three hp he)).exists_elemAbelian
  · exact (sylowTorus_F4_four k hp hp3 (dvd_of_orderOf_four hp he)).exists_elemAbelian
  · exact (sylowTorus_F4_six k hp hp3 (dvd_of_orderOf_six hp hk1 he)).exists_elemAbelian

theorem rankTwoData_F4 : RankTwoData Tag.F4 := by
  intro p hp hp3 K _ _ hpK hnr1 hr2 k _ _ hpk hord
  have h1 : 2 ≤ degCount Tag.F4 (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
    by_contra h
    exact hnr1 (rankLE1_F4 K hp hpK (by omega))
  have h3 : degCount Tag.F4 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 2 := by
    by_contra h
    exact not_rankLE2_F4 K hp hp3 hpK (by omega) hr2
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_F4 k hp hp3 hpk (by rw [hord]; omega)
  exact hasIndepPair_of_elemAbelian_sq hp hE hEc

theorem fixesPair_adjointF4 {f p : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk1 : ¬ RankLE1 p (adjointGroup Tag.F4 K)) (hrk2 : RankLE2 p (adjointGroup Tag.F4 K))
    {α : MulAut (adjointGroup Tag.F4 K)} (hαp : α ^ p = 1) (hα : α ∉ inner (adjointGroup Tag.F4 K)) :
    FixesIndepPair p α := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hαo : orderOf α = p := orderOf_eq_prime hαp (fun h1 => hα (h1 ▸
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 K)).one_mem))
  obtain ⟨σ, ψ, hσ, hψ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.even_F4_odd_prime_field_descent hf K hK hp hp2 α hαo hα
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd'))
  obtain ⟨hdvd, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two hf hK σ
  rw [hσ] at hdvd hc
  haveI : Finite (fixSubfield σ) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (pow_pos (by norm_num) _).ne')
  have hFk : Nat.card K = Nat.card (fixSubfield σ) ^ p := by
    rw [hK, hc, ← pow_mul, Nat.div_mul_cancel hdvd]
  have hpk : ¬ p ∣ Nat.card (fixSubfield σ) := fun h => hpK (by rw [hFk]; exact h.pow hp.ne_zero)
  have hord : orderOf ((Nat.card (fixSubfield σ) : ℕ) : ZMod p) =
      orderOf ((Nat.card K : ℕ) : ZMod p) := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [hFk]
    push_cast
    rw [ZMod.pow_card]
  exact fixesPair_of_entrywise_conj (r := 1) (j := 1) σ (by simp) (by rw [pow_one]; exact hψ)
    (rankTwoData_F4 p hp (by omega) K hpK hrk1 hrk2 (fixSubfield σ) hpk hord)

theorem chevTwoOuterFixesPair_F4 : ChevTwoOuterFixesPair LieIndexF4 := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | F4 q =>
    have hq2 : q.p = 2 := hchar
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_F4_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
        exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
      haveI : CharP K 2 := hq2 ▸ hchK
      let θ : L ≃* adjointGroup Tag.F4 K := e.trans eK
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
      exact FixesIndepPair.of_mulEquiv θ
        (fixesPair_adjointF4 q.exponent_pos K hK2 hp hp5 (not_rankLE1_of_sq hp hE hEc) hrk2
          (α := MulAut.congr θ α) (by rw [← map_pow, hαp, map_one])
          ((congr_mem_inner_iff θ α).not.2 hα))
  | A _ _ => exact absurd hF (by simp [LieIndexF4])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexF4])
  | B _ _ => exact absurd hF (by simp [LieIndexF4])
  | C _ _ => exact absurd hF (by simp [LieIndexF4])
  | D _ _ => exact absurd hF (by simp [LieIndexF4])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexF4])
  | E6 _ => exact absurd hF (by simp [LieIndexF4])
  | E7 _ => exact absurd hF (by simp [LieIndexF4])
  | E8 _ => exact absurd hF (by simp [LieIndexF4])
  | G2 _ => exact absurd hF (by simp [LieIndexF4])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexF4])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexF4])
  | suzuki _ => exact absurd hF (by simp [LieIndexF4])
  | reeG2 _ => exact absurd hF (by simp [LieIndexF4])
  | reeF4 _ => exact absurd hF (by simp [LieIndexF4])
  | tits => exact absurd hF (by simp [LieIndexF4])

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
