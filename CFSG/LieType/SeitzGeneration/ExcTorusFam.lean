module

public import CFSG.LieType.SeitzGeneration.ExcTorusUntw
public import CFSG.RankThree.SteinbergR3EOrdinaryECrossPrimeParts

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice Polynomial

@[expose] def degreesE : Tag → List ℕ
  | .E6 => [2, 5, 6, 8, 9, 12]
  | .E7 => [2, 6, 8, 10, 12, 14, 18]
  | .E8 => [2, 8, 12, 14, 18, 20, 24, 30]
  | _ => []

theorem not_dvd_of_orderOf {p q e : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q)
    (he : orderOf (q : ZMod p) = e) : ¬ p ∣ e := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hdvd : e ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  intro h
  have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) h
  have h2 := Nat.le_of_dvd (by have := hp.one_lt; omega) hdvd
  omega

theorem not_dvd_of_orderOf_pos {p q e : ℕ} (hp : p.Prime) (he : orderOf (q : ZMod p) = e)
    (he0 : e ≠ 0) : ¬ p ∣ q := fun h => he0 (by
  have : Fact p.Prime := ⟨hp⟩
  rw [← he, (ZMod.natCast_eq_zero_iff q p).2 h, orderOf_zero])

theorem orderOf_lt_prime {p q e : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q)
    (he : orderOf (q : ZMod p) = e) : e < p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hdvd : e ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have h2 := Nat.le_of_dvd (by have := hp.one_lt; omega) hdvd
  have := hp.pos
  omega

theorem not_dvd_cyclotomic_eval_of_ne {p q e d : ℕ} (hp : p.Prime) (he : orderOf (q : ZMod p) = e)
    (hde : d ≠ e) (hpd : ¬ p ∣ d) : ¬ (p : ℤ) ∣ (cyclotomic d ℤ).eval (q : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have hz : ((eval (q : ℤ) (cyclotomic d ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
  have hne : NeZero (d : ZMod p) := ⟨fun h0 => hpd ((ZMod.natCast_eq_zero_iff d p).1 h0)⟩
  have hroot : (cyclotomic d (ZMod p)).IsRoot (q : ZMod p) := by
    have h1 := cyclotomic.eval_apply (q : ℤ) d (Int.castRingHom (ZMod p))
    have h2 : (Int.castRingHom (ZMod p)) (q : ℤ) = (q : ZMod p) := by simp
    have h3 : (Int.castRingHom (ZMod p)) (eval (q : ℤ) (cyclotomic d ℤ)) = 0 := hz
    rw [h2, h3] at h1
    exact h1
  have hprim := (isRoot_cyclotomic_iff).1 hroot
  exact hde (hprim.eq_orderOf.trans he)

theorem ordProj_card_adjointGroup_E
    {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K) :
    p ^ (Nat.card (adjointGroup τ K)).factorization p =
      ((degreesE τ).map fun d => p ^ (Nat.card K ^ d - 1).factorization p).prod := by
  have h := CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts
    (K := K) hp hp3 hpq
  rcases hτ with rfl | rfl | rfl
  exacts [h.1, h.2.1, h.2.2]

theorem prod_cyclotomic_split (e : ℕ) : ∀ ds : List ℕ,
    (ds.map fun d => cyclotomic d ℤ).prod =
      cyclotomic e ℤ ^ ds.count e * ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod
  | [] => by simp
  | d :: ds => by
    by_cases h : d = e
    · subst h
      simp only [List.map_cons, List.prod_cons, List.count_cons_self, List.filter_cons,
        ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        prod_cyclotomic_split d ds, pow_succ]
      ring
    · simp only [List.map_cons, List.prod_cons, List.count_cons, h, beq_iff_eq,
        add_zero, List.filter_cons, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
        prod_cyclotomic_split e ds]
      ring

theorem not_dvd_small {p k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hk : k ∈ [1, 2, 3, 4, 6]) :
    ¬ p ∣ k := by
  intro h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  have hk0 : 0 < k := by omega
  have hle := Nat.le_of_dvd hk0 h
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

section Main


theorem sylowTorus_of_blocks {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : IsWeylMatrix τ M) (ds : List ℕ) {e : ℕ}
    (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod) (hpow : M ^ e = 1)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (he4 : 4 ≤ e)
    (hother : ∀ d ∈ ds, d ≠ e → ¬ p ∣ d)
    (hdeg : ∀ d ∈ degreesE τ, e ∣ d → ¬ p ∣ d / e)
    (hcount : ((degreesE τ).filter fun d => e ∣ d).length = ds.count e) :
    SylowTorus (adjointGroup τ K) p (ds.count e) := by
  have he0 : e ≠ 0 := by omega
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he he0
  have hlt : e < p := orderOf_lt_prime hp hpq he
  have hp3 : 3 < p := by omega
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
  exact sylowTorus_untwisted d hτ K hp hp3 hpq hM _ he0 hpow hn hchar' he hR hord

theorem sylowTorus_of_blocks' {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : IsWeylMatrix τ M) (ds : List ℕ) {e : ℕ}
    (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod) (hpow : M ^ e = 1)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (he4 : 4 ≤ e)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3])
    (hQ : ∀ d ∈ degreesE τ, e ∣ d → d / e ∈ [1, 2, 3, 4, 6])
    (hcount : ((degreesE τ).filter fun d => e ∣ d).length = ds.count e) :
    SylowTorus (adjointGroup τ K) p (ds.count e) := by
  have he0 : e ≠ 0 := by omega
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he he0
  have hlt : e < p := orderOf_lt_prime hp hpq he
  have h5 : 5 ≤ p := by omega
  refine sylowTorus_of_blocks d hτ K hp hM ds hchar hpow he he4 (fun d hd hde => ?_)
    (fun d hd hed => not_dvd_small hp h5 (hQ d hd hed)) hcount
  have := hso d hd hde
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  intro hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

end Main

end CFSG.LieType.SeitzGeneration
