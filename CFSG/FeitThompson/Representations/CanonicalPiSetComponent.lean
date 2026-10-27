module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic

namespace CFSG.FeitThompson.CoprimeComponent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {M : Type*} [Monoid M] {M' : Type*} [Monoid M'] {G : Type*} [Group G]
variable {a b m n N p : ℕ} {pi : Set ℕ}

def IsPiNumber (pi : Set ℕ) (n : ℕ) : Prop := 0 < n ∧ ∀ p ∈ n.primeFactors, p ∈ pi

def IsPiPrimeNumber (pi : Set ℕ) (n : ℕ) : Prop := IsPiNumber piᶜ n

theorem isPiPrimeNumber_iff : IsPiPrimeNumber pi n ↔ IsPiNumber piᶜ n := Iff.rfl

theorem IsPiNumber.pos (h : IsPiNumber pi n) : 0 < n := h.1

theorem IsPiNumber.ne_zero (h : IsPiNumber pi n) : n ≠ 0 := h.1.ne'

theorem IsPiNumber.mem_of_prime_dvd (h : IsPiNumber pi n) (hp : p.Prime) (hpn : p ∣ n) : p ∈ pi :=
  h.2 p (Nat.mem_primeFactors.2 ⟨hp, hpn, h.ne_zero⟩)

theorem isPiNumber_iff_forall_prime :
    IsPiNumber pi n ↔ 0 < n ∧ ∀ p, p.Prime → p ∣ n → p ∈ pi :=
  and_congr_right fun hn =>
    ⟨fun h p hp hpn => h p (Nat.mem_primeFactors.2 ⟨hp, hpn, hn.ne'⟩),
      fun h p hp => h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)⟩

theorem isPiPrimeNumber_iff_forall_prime :
    IsPiPrimeNumber pi n ↔ 0 < n ∧ ∀ p, p.Prime → p ∣ n → p ∉ pi :=
  isPiNumber_iff_forall_prime

theorem isPiNumber_one : IsPiNumber pi 1 := ⟨one_pos, by simp⟩

theorem isPiPrimeNumber_one : IsPiPrimeNumber pi 1 := isPiNumber_one

theorem IsPiNumber.of_dvd (h : IsPiNumber pi n) (hmn : m ∣ n) : IsPiNumber pi m := by
  have hm : m ≠ 0 := fun hm => h.ne_zero (by simpa [hm] using hmn)
  exact ⟨Nat.pos_of_ne_zero hm, fun q hq => h.2 q (Nat.primeFactors_mono hmn h.ne_zero hq)⟩

theorem IsPiNumber.mul (ha : IsPiNumber pi a) (hb : IsPiNumber pi b) : IsPiNumber pi (a * b) := by
  refine ⟨Nat.mul_pos ha.pos hb.pos, fun q hq => ?_⟩
  rw [Nat.primeFactors_mul ha.ne_zero hb.ne_zero, Finset.mem_union] at hq
  exact hq.elim (ha.2 q) (hb.2 q)

theorem IsPiNumber.coprime (ha : IsPiNumber pi a) (hb : IsPiNumber piᶜ b) : a.Coprime b := by
  rw [← Nat.disjoint_primeFactors ha.ne_zero hb.ne_zero]
  exact Finset.disjoint_left.2 fun q hqa hqb => hb.2 q hqb (ha.2 q hqa)

theorem IsPiNumber.eq_of_mul_eq_mul {m' n' : ℕ} (h : m * n = m' * n') (hm : IsPiNumber pi m)
    (hn : IsPiNumber piᶜ n) (hm' : IsPiNumber pi m') (hn' : IsPiNumber piᶜ n') :
    m = m' ∧ n = n' := by
  have hmm' : m = m' :=
    Nat.dvd_antisymm ((hm.coprime hn').dvd_of_dvd_mul_right ⟨n, h.symm⟩)
      ((hm'.coprime hn).dvd_of_dvd_mul_right ⟨n', h⟩)
  subst hmm'
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hm.pos h⟩

def IsPiSubgroup (pi : Set ℕ) (H : Subgroup G) : Prop := IsPiNumber pi (Nat.card H)

theorem isPiSubgroup_iff {H : Subgroup G} : IsPiSubgroup pi H ↔ IsPiNumber pi (Nat.card H) :=
  Iff.rfl

theorem isPiSubgroup_bot : IsPiSubgroup pi (⊥ : Subgroup G) := by
  simpa [IsPiSubgroup] using isPiNumber_one (pi := pi)

theorem IsPiSubgroup.isPiNumber_orderOf {H : Subgroup G} (hH : IsPiSubgroup pi H) {x : G}
    (hx : x ∈ H) : IsPiNumber pi (orderOf x) := by
  refine hH.of_dvd ?_
  rw [← Subgroup.orderOf_mk x hx]
  exact orderOf_dvd_natCard _

noncomputable def piPart (pi : Set ℕ) (N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors, pi.mulIndicator (fun q => q ^ N.factorization q) p

theorem piPart_pos (pi : Set ℕ) (N : ℕ) : 0 < piPart pi N := by
  refine Finset.prod_pos fun q hq => ?_
  by_cases h : q ∈ pi <;> simp [h, Nat.pos_of_mem_primeFactors hq]

theorem piPart_ne_zero (pi : Set ℕ) (N : ℕ) : piPart pi N ≠ 0 := (piPart_pos pi N).ne'

@[simp] theorem piPart_zero (pi : Set ℕ) : piPart pi 0 = 1 := by simp [piPart]

@[simp] theorem piPart_one (pi : Set ℕ) : piPart pi 1 = 1 := by simp [piPart]

theorem piPart_mul_piPart_compl (hN : N ≠ 0) : piPart pi N * piPart piᶜ N = N := by
  rw [piPart, piPart, ← Finset.prod_mul_distrib]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hN]
  refine Finset.prod_congr rfl fun q _ => ?_
  by_cases h : q ∈ pi <;> simp [h]

theorem isPiNumber_piPart (pi : Set ℕ) (N : ℕ) : IsPiNumber pi (piPart pi N) := by
  refine ⟨piPart_pos pi N, fun q hq => ?_⟩
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hdvd : q ∣ piPart pi N := Nat.dvd_of_mem_primeFactors hq
  rw [piPart] at hdvd
  obtain ⟨r, hr, hqr⟩ := hqp.prime.exists_mem_finset_dvd hdvd
  by_cases hrpi : r ∈ pi
  · rw [Set.mulIndicator_of_mem hrpi] at hqr
    have : q = r :=
      (Nat.prime_dvd_prime_iff_eq hqp (Nat.prime_of_mem_primeFactors hr)).1
        (hqp.dvd_of_dvd_pow hqr)
    exact this ▸ hrpi
  · rw [Set.mulIndicator_of_notMem hrpi] at hqr
    exact absurd (Nat.eq_one_of_dvd_one hqr) hqp.ne_one

theorem isPiPrimeNumber_piPart_compl (pi : Set ℕ) (N : ℕ) : IsPiPrimeNumber pi (piPart piᶜ N) :=
  isPiNumber_piPart piᶜ N

theorem coprime_piPart_piPart_compl (pi : Set ℕ) (N : ℕ) :
    (piPart pi N).Coprime (piPart piᶜ N) :=
  (isPiNumber_piPart pi N).coprime (isPiNumber_piPart piᶜ N)

theorem piPart_dvd_self (pi : Set ℕ) (hN : N ≠ 0) : piPart pi N ∣ N :=
  ⟨_, (piPart_mul_piPart_compl (pi := pi) hN).symm⟩

theorem piPart_compl_eq_one_of_isPiNumber (h : IsPiNumber pi N) : piPart piᶜ N = 1 :=
  Finset.prod_eq_one fun q hq => Set.mulIndicator_of_notMem (by simpa using h.2 q hq) _

theorem piPart_eq_self_of_isPiNumber (h : IsPiNumber pi N) : piPart pi N = N := by
  have h' := piPart_mul_piPart_compl (pi := pi) h.ne_zero
  rwa [piPart_compl_eq_one_of_isPiNumber h, mul_one] at h'

theorem eq_piPart_of_mul_eq (h : m * n = N) (hm : IsPiNumber pi m) (hn : IsPiPrimeNumber pi n) :
    m = piPart pi N ∧ n = piPart piᶜ N := by
  have hN : N ≠ 0 := by rw [← h]; exact (Nat.mul_pos hm.pos hn.pos).ne'
  exact IsPiNumber.eq_of_mul_eq_mul (h.trans (piPart_mul_piPart_compl hN).symm) hm hn
    (isPiNumber_piPart _ _) (isPiNumber_piPart _ _)

noncomputable def piComponent (pi : Set ℕ) (x : M) : M :=
  x ^ (piPart piᶜ (orderOf x) ^ Nat.totient (piPart pi (orderOf x)))

theorem piComponent_mem_powers (pi : Set ℕ) (x : M) : piComponent pi x ∈ Submonoid.powers x :=
  ⟨_, rfl⟩

theorem commute_self_piComponent (pi : Set ℕ) (x : M) : Commute x (piComponent pi x) :=
  (Commute.refl x).pow_right _

theorem commute_piComponent_piComponent_compl (pi : Set ℕ) (x : M) :
    Commute (piComponent pi x) (piComponent piᶜ x) :=
  (Commute.refl x).pow_pow _ _

@[simp] theorem piComponent_one (pi : Set ℕ) : piComponent pi (1 : M) = 1 := by
  simp [piComponent]

theorem orderOf_piComponent {x : M} (hx : IsOfFinOrder x) (pi : Set ℕ) :
    orderOf (piComponent pi x) = piPart pi (orderOf x) := by
  obtain ⟨m, n, hm, hn⟩ : ∃ m n, piPart pi (orderOf x) = m ∧ piPart piᶜ (orderOf x) = n :=
    ⟨_, _, rfl, rfl⟩
  have hord : orderOf x = m * n := by
    rw [← hm, ← hn, piPart_mul_piPart_compl hx.orderOf_pos.ne']
  have hcop : m.Coprime n := hm ▸ hn ▸ coprime_piPart_piPart_compl pi (orderOf x)
  have hmpos : 0 < m := hm ▸ piPart_pos _ _
  have hnpos : 0 < n := hn ▸ piPart_pos _ _
  rw [piComponent, hm, hn, orderOf_pow' _ (pow_ne_zero _ hnpos.ne'), hord,
    Nat.Coprime.gcd_mul_left_cancel n (hcop.pow_right _),
    Nat.gcd_eq_left (dvd_pow_self n (Nat.totient_pos.2 hmpos).ne'),
    Nat.mul_div_cancel _ hnpos]

theorem isPiNumber_orderOf_piComponent {x : M} (hx : IsOfFinOrder x) (pi : Set ℕ) :
    IsPiNumber pi (orderOf (piComponent pi x)) := by
  rw [orderOf_piComponent hx]; exact isPiNumber_piPart _ _

theorem isPiPrimeNumber_orderOf_piComponent_compl {x : M} (hx : IsOfFinOrder x) (pi : Set ℕ) :
    IsPiPrimeNumber pi (orderOf (piComponent piᶜ x)) :=
  isPiNumber_orderOf_piComponent hx piᶜ

theorem piComponent_mul_piComponent_compl {x : M} (hx : IsOfFinOrder x) (pi : Set ℕ) :
    piComponent pi x * piComponent piᶜ x = x := by
  obtain ⟨m, n, hm, hn⟩ : ∃ m n, piPart pi (orderOf x) = m ∧ piPart piᶜ (orderOf x) = n :=
    ⟨_, _, rfl, rfl⟩
  have hord : orderOf x = m * n := by
    rw [← hm, ← hn, piPart_mul_piPart_compl hx.orderOf_pos.ne']
  have hcop : m.Coprime n := hm ▸ hn ▸ coprime_piPart_piPart_compl pi (orderOf x)
  have hmpos : 0 < m := hm ▸ piPart_pos _ _
  have hnpos : 0 < n := hn ▸ piPart_pos _ _
  have hcompl : piPart piᶜᶜ (orderOf x) = m := by rw [compl_compl]; exact hm
  rw [piComponent, piComponent, hm, hn, hcompl, ← pow_add]
  have key : n ^ Nat.totient m + m ^ Nat.totient n ≡ 1 [MOD orderOf x] := by
    rw [hord, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    refine ⟨?_, ?_⟩
    · calc n ^ Nat.totient m + m ^ Nat.totient n
          ≡ 1 + 0 [MOD m] :=
            Nat.ModEq.add (Nat.ModEq.pow_totient hcop.symm)
              (Nat.modEq_zero_iff_dvd.2 (dvd_pow_self _ (Nat.totient_pos.2 hnpos).ne'))
        _ = 1 := by ring
    · calc n ^ Nat.totient m + m ^ Nat.totient n
          ≡ 0 + 1 [MOD n] :=
            Nat.ModEq.add
              (Nat.modEq_zero_iff_dvd.2 (dvd_pow_self _ (Nat.totient_pos.2 hmpos).ne'))
              (Nat.ModEq.pow_totient hcop)
        _ = 1 := by ring
  simpa using hx.pow_eq_pow_iff_modEq.2 key

theorem piComponent_eq_of_commute {y u : M} (h : Commute y u) (hy : IsPiNumber pi (orderOf y))
    (hu : IsPiPrimeNumber pi (orderOf u)) : piComponent pi (y * u) = y := by
  have hyfin : IsOfFinOrder y := orderOf_pos_iff.1 hy.pos
  have hcop : (orderOf y).Coprime (orderOf u) := hy.coprime hu
  have hord : orderOf (y * u) = orderOf y * orderOf u :=
    h.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hparts : orderOf y = piPart pi (orderOf (y * u)) ∧
      orderOf u = piPart piᶜ (orderOf (y * u)) :=
    eq_piPart_of_mul_eq hord.symm hy hu
  rw [piComponent, ← hparts.1, ← hparts.2, h.mul_pow]
  have hu1 : u ^ orderOf u ^ Nat.totient (orderOf y) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (dvd_pow_self _ (Nat.totient_pos.2 hy.pos).ne')
  have hy1 : y ^ orderOf u ^ Nat.totient (orderOf y) = y := by
    have hy1' : y ^ orderOf u ^ Nat.totient (orderOf y) = y ^ 1 :=
      hyfin.pow_eq_pow_iff_modEq.2 (Nat.ModEq.pow_totient hcop.symm)
    simpa using hy1'
  rw [hu1, hy1, mul_one]

theorem piComponent_compl_eq_of_commute {y u : M} (h : Commute y u)
    (hy : IsPiNumber pi (orderOf y)) (hu : IsPiPrimeNumber pi (orderOf u)) :
    piComponent piᶜ (y * u) = u := by
  have h' : piComponent piᶜ (u * y) = u :=
    piComponent_eq_of_commute h.symm hu (by rwa [isPiPrimeNumber_iff, compl_compl])
  rwa [h.symm.eq] at h'

theorem eq_piComponent_of_mul_eq {x y u : M} (h : Commute y u) (hx : y * u = x)
    (hy : IsPiNumber pi (orderOf y)) (hu : IsPiPrimeNumber pi (orderOf u)) :
    y = piComponent pi x ∧ u = piComponent piᶜ x := by
  subst hx
  exact ⟨(piComponent_eq_of_commute h hy hu).symm, (piComponent_compl_eq_of_commute h hy hu).symm⟩

theorem piComponent_eq_self_of_isPiNumber {x : M} (hx : IsPiNumber pi (orderOf x)) :
    piComponent pi x = x := by
  rw [piComponent, piPart_compl_eq_one_of_isPiNumber hx, one_pow, pow_one]

theorem piComponent_compl_eq_one_of_isPiNumber {x : M} (hx : IsPiNumber pi (orderOf x)) :
    piComponent piᶜ x = 1 := by
  rw [piComponent, compl_compl, piPart_eq_self_of_isPiNumber hx,
    piPart_compl_eq_one_of_isPiNumber hx, Nat.totient_one, pow_one, pow_orderOf_eq_one]

theorem piComponent_map (e : M ≃* M') (pi : Set ℕ) (x : M) :
    piComponent pi (e x) = e (piComponent pi x) := by
  rw [piComponent, piComponent, e.orderOf_eq, map_pow]

theorem piComponent_conj (pi : Set ℕ) (g x : G) :
    piComponent pi (g * x * g⁻¹) = g * piComponent pi x * g⁻¹ := by
  simpa using piComponent_map (MulAut.conj g) pi x

end

end CFSG.FeitThompson.CoprimeComponent
