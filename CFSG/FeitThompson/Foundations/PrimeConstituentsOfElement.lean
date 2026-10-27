module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.Defs

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset Function

section Aux

variable {ι : Type*}

theorem modEq_sum {s : Finset ι} {f g : ι → ℕ} {m : ℕ} (h : ∀ i ∈ s, f i ≡ g i [MOD m]) :
    ∑ i ∈ s, f i ≡ ∑ i ∈ s, g i [MOD m] := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [Nat.ModEq.refl]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem modEq_prod {s : Finset ι} {f : ι → ℕ} {a b : ℕ}
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j))
    (h : ∀ i ∈ s, a ≡ b [MOD f i]) : a ≡ b [MOD ∏ i ∈ s, f i] := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [Nat.modEq_one]
  | cons c s hc ih =>
    rw [Finset.prod_cons]
    refine (Nat.modEq_and_modEq_iff_modEq_mul ?_).1
      ⟨h c (by simp), ih (fun i hi j hj hij => hcop i (by simp [hi]) j (by simp [hj]) hij)
        fun i hi => h i (by simp [hi])⟩
    exact Nat.Coprime.prod_right fun i hi =>
      hcop c (by simp) i (by simp [hi]) fun hh => hc (hh ▸ hi)

variable {X : Type*} [Group X]

theorem noncommProd_pow {s : Finset ι} {f : ι → X} (comm) (c : ℕ)
    (comm' : (s : Set ι).Pairwise (Commute on fun i => f i ^ c)) :
    (s.noncommProd f comm) ^ c = s.noncommProd (fun i => f i ^ c) comm' := by
  induction c with
  | zero =>
    rw [pow_zero, Finset.noncommProd_eq_pow_card _ _ _ 1 (fun _ _ => pow_zero _), one_pow]
  | succ c ih =>
    rw [pow_succ, ih (fun i hi j hj hij => (comm hi hj hij).pow_pow c c),
      ← Finset.noncommProd_mul_distrib (s := s) (fun i => f i ^ c) f
        (fun i hi j hj hij => (comm hi hj hij).pow_pow c c) comm
        (fun i hi j hj hij => (comm hi hj hij).pow_right c)]
    exact Finset.noncommProd_congr rfl (fun i _ => (pow_succ (f i) c).symm) _

theorem noncommProd_eq_of_eq_one {s : Finset ι} {f : ι → X} (comm) {i : ι} (hi : i ∈ s)
    (h : ∀ j ∈ s, j ≠ i → f j = 1) : s.noncommProd f comm = f i := by
  classical
  have H := Finset.noncommProd_erase_mul s hi f comm
  generalize_proofs c at H
  rw [Finset.noncommProd_eq_pow_card _ _ c 1 (fun j hj =>
    h j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)), one_pow, one_mul] at H
  exact H.symm

theorem noncommProd_pow_eq_pow_sum (s : Finset ι) (x : X) (g : ι → ℕ) (comm) :
    s.noncommProd (fun i => x ^ g i) comm = x ^ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.noncommProd_cons _ _ _ ha, ih, Finset.sum_cons, pow_add]

theorem orderOf_noncommProd_dvd {s : Finset ι} {f : ι → X} (comm) :
    orderOf (s.noncommProd f comm) ∣ ∏ i ∈ s, orderOf (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hc : Commute (f a)
        (s.noncommProd f (comm.mono (by intro z hz; simpa using Or.inr hz))) :=
      Finset.noncommProd_commute _ _ _ _ fun z hz =>
        comm (by simp) (by simp [hz]) fun h => ha (h ▸ hz)
    rw [Finset.noncommProd_cons _ _ _ ha, Finset.prod_cons]
    exact hc.orderOf_mul_dvd_mul_orderOf.trans (Nat.mul_dvd_mul_left _ (ih _))

theorem orderOf_noncommProd_of_coprime {s : Finset ι} {f : ι → X} (comm)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (orderOf (f i)).Coprime (orderOf (f j))) :
    orderOf (s.noncommProd f comm) = ∏ i ∈ s, orderOf (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hsub : (s : Set ι) ⊆ ((Finset.cons a s ha : Finset ι) : Set ι) := by
      intro z hz; simpa using Or.inr hz
    have hc : Commute (f a) (s.noncommProd f (comm.mono hsub)) :=
      Finset.noncommProd_commute _ _ _ _ fun z hz =>
        comm (by simp) (by simp [hz]) fun h => ha (h ▸ hz)
    have hrest := ih (comm.mono hsub)
      (fun i hi j hj hij => hcop i (by simp [hi]) j (by simp [hj]) hij)
    rw [Finset.noncommProd_cons _ _ _ ha, Finset.prod_cons,
      hc.orderOf_mul_eq_mul_orderOf_of_coprime (by
        rw [hrest]
        exact Nat.Coprime.prod_right fun i hi =>
          hcop a (by simp) i (by simp [hi]) fun h => ha (h ▸ hi)), hrest]

end Aux

open scoped Classical in
noncomputable def piPart (π : Set ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with p ∈ π, p ^ n.factorization p

section PiPart

variable {ι : Type*} {π π' : Set ℕ} {m n q : ℕ}

theorem piPart_eq_prod (π : Set ℕ) [DecidablePred (· ∈ π)] (n : ℕ) :
    piPart π n = ∏ p ∈ n.primeFactors with p ∈ π, p ^ n.factorization p := by
  unfold piPart
  congr 1
  exact Finset.filter_congr_decidable _ _ _

theorem piPart_pos (π : Set ℕ) (n : ℕ) : 0 < piPart π n := by
  classical
  rw [piPart_eq_prod]
  exact Finset.prod_pos fun p hp =>
    pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_filter.1 hp).1) _

theorem piPart_ne_zero (π : Set ℕ) (n : ℕ) : piPart π n ≠ 0 := (piPart_pos π n).ne'

private theorem factorization_piPart_aux (π : Set ℕ) [DecidablePred (· ∈ π)] (n q : ℕ) :
    (piPart π n).factorization q =
      if q ∈ n.primeFactors ∧ q ∈ π then n.factorization q else 0 := by
  rw [piPart_eq_prod, Nat.factorization_prod (fun p hp =>
    pow_ne_zero _ (Nat.pos_of_mem_primeFactors (Finset.mem_filter.1 hp).1).ne'),
    Finsupp.finsetSum_apply]
  have h : ∀ p ∈ {p ∈ n.primeFactors | p ∈ π},
      ((p ^ n.factorization p).factorization) q = if p = q then n.factorization p else 0 := by
    intro p hp
    rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).factorization_pow]
    simp [Finsupp.single_apply]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' _ q]
  simp [Finset.mem_filter]

@[simp]
theorem factorization_piPart_of_mem (hq : q ∈ π) (n : ℕ) :
    (piPart π n).factorization q = n.factorization q := by
  classical
  rw [factorization_piPart_aux]
  by_cases h : q ∈ n.primeFactors
  · simp [h, hq]
  · rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at h
    simp [h]

@[simp]
theorem factorization_piPart_of_notMem (hq : q ∉ π) (n : ℕ) :
    (piPart π n).factorization q = 0 := by
  classical
  rw [factorization_piPart_aux]
  simp [hq]

theorem primeFactors_piPart_subset (π : Set ℕ) (n : ℕ) :
    ((piPart π n).primeFactors : Set ℕ) ⊆ π := by
  intro q hq
  by_contra h
  rw [Finset.mem_coe, ← Nat.support_factorization, Finsupp.mem_support_iff] at hq
  exact hq (factorization_piPart_of_notMem h n)

theorem piPart_dvd (π : Set ℕ) (n : ℕ) : piPart π n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  refine (Nat.factorization_le_iff_dvd (piPart_ne_zero π n) hn).1 fun q => ?_
  by_cases hq : q ∈ π
  · simp [factorization_piPart_of_mem hq]
  · simp [factorization_piPart_of_notMem hq]

@[simp]
theorem piPart_zero (π : Set ℕ) : piPart π 0 = 1 := by
  classical
  rw [piPart_eq_prod]
  simp

theorem dvd_piPart (hn : n ≠ 0) (hd : m ∣ n) (hm : m ≠ 0)
    (h : (m.primeFactors : Set ℕ) ⊆ π) : m ∣ piPart π n := by
  refine (Nat.factorization_le_iff_dvd hm (piPart_ne_zero π n)).1 fun q => ?_
  by_cases hq : q ∈ π
  · rw [factorization_piPart_of_mem hq]
    exact (Nat.factorization_le_iff_dvd hm hn).2 hd q
  · rw [factorization_piPart_of_notMem hq]
    by_contra hne
    refine hq (h ?_)
    rw [Finset.mem_coe, ← Nat.support_factorization, Finsupp.mem_support_iff]
    omega

theorem piPart_dvd_piPart_of_subset (h : π ⊆ π') (n : ℕ) : piPart π n ∣ piPart π' n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact dvd_piPart hn (piPart_dvd π n) (piPart_ne_zero π n)
      ((primeFactors_piPart_subset π n).trans h)

theorem coprime_piPart (h : Disjoint π π') (n : ℕ) : (piPart π n).Coprime (piPart π' n) := by
  rw [← Nat.disjoint_primeFactors (piPart_ne_zero π n) (piPart_ne_zero π' n),
    Finset.disjoint_left]
  intro q hq hq'
  exact Set.disjoint_left.1 h (primeFactors_piPart_subset π n hq)
    (primeFactors_piPart_subset π' n hq')

theorem piPart_mul_piPart (h : Disjoint π π') (n : ℕ) :
    piPart π n * piPart π' n = piPart (π ∪ π') n := by
  refine Nat.eq_of_factorization_eq (mul_ne_zero (piPart_ne_zero _ n) (piPart_ne_zero _ n))
    (piPart_ne_zero _ n) fun q => ?_
  rw [Nat.factorization_mul (piPart_ne_zero _ n) (piPart_ne_zero _ n)]
  simp only [Finsupp.add_apply]
  by_cases hq : q ∈ π
  · have hq' : q ∉ π' := Set.disjoint_left.1 h hq
    rw [factorization_piPart_of_mem hq, factorization_piPart_of_notMem hq',
      factorization_piPart_of_mem (Or.inl hq)]
    simp
  · by_cases hq' : q ∈ π'
    · rw [factorization_piPart_of_notMem hq, factorization_piPart_of_mem hq',
        factorization_piPart_of_mem (Or.inr hq')]
      simp
    · rw [factorization_piPart_of_notMem hq, factorization_piPart_of_notMem hq',
        factorization_piPart_of_notMem (by simpa using ⟨hq, hq'⟩)]

theorem piPart_eq_self (hn : n ≠ 0) (h : (n.primeFactors : Set ℕ) ⊆ π) : piPart π n = n :=
  Nat.dvd_antisymm (piPart_dvd π n) (dvd_piPart hn dvd_rfl hn h)

theorem piPart_mul_piPart_compl (π : Set ℕ) (hn : n ≠ 0) : piPart π n * piPart πᶜ n = n := by
  rw [piPart_mul_piPart disjoint_compl_right, piPart_eq_self hn (by simp)]

theorem prod_piPart {s : Finset ι} {π : ι → Set ℕ} (hd : (s : Set ι).PairwiseDisjoint π)
    (n : ℕ) : ∏ i ∈ s, piPart (π i) n = piPart (⋃ i ∈ s, π i) n := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [piPart]
  | cons a s ha ih =>
    rw [Finset.prod_cons, ih (hd.subset (by intro z hz; simpa using Or.inr hz))]
    have hdisj : Disjoint (π a) (⋃ i ∈ s, π i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hd (by simp) (by simp [hi]) fun h => ha (h ▸ hi)
    rw [piPart_mul_piPart hdisj]
    congr 1
    simp

end PiPart

def IsPiElement (π : Set ℕ) {X : Type*} [Group X] (x : X) : Prop :=
  ((orderOf x).primeFactors : Set ℕ) ⊆ π

theorem isPiElement_iff {π : Set ℕ} {X : Type*} [Group X] {x : X} :
    IsPiElement π x ↔ ∀ p ∈ (orderOf x).primeFactors, p ∈ π := (Iff.rfl)

theorem isPiElement_one {π : Set ℕ} {X : Type*} [Group X] : IsPiElement π (1 : X) := by
  simp [IsPiElement]

theorem IsPiElement.orderOf_dvd_piPart {π : Set ℕ} {X : Type*} [Group X] {x : X}
    (hx : IsPiElement π x) (hx0 : orderOf x ≠ 0) {n : ℕ} (hn : n ≠ 0) (hd : orderOf x ∣ n) :
    orderOf x ∣ piPart π n :=
  dvd_piPart hn hd hx0 hx

noncomputable def piExponent (π : Set ℕ) (n : ℕ) : ℕ :=
  Nat.chineseRemainder (coprime_piPart (disjoint_compl_right (a := π)) n) 1 0

section PiExponent

variable {π : Set ℕ} {n : ℕ}

theorem piExponent_modEq_one (π : Set ℕ) (n : ℕ) : piExponent π n ≡ 1 [MOD piPart π n] :=
  (Nat.chineseRemainder (coprime_piPart (disjoint_compl_right (a := π)) n) 1 0).2.1

theorem piExponent_modEq_zero (π : Set ℕ) (n : ℕ) : piExponent π n ≡ 0 [MOD piPart πᶜ n] :=
  (Nat.chineseRemainder (coprime_piPart (disjoint_compl_right (a := π)) n) 1 0).2.2

theorem piPart_compl_dvd_piExponent (π : Set ℕ) (n : ℕ) : piPart πᶜ n ∣ piExponent π n :=
  Nat.modEq_zero_iff_dvd.1 (piExponent_modEq_zero π n)

theorem piExponent_modEq_of {a : ℕ} (hn : n ≠ 0) (ha1 : a ≡ 1 [MOD piPart π n])
    (ha0 : a ≡ 0 [MOD piPart πᶜ n]) : a ≡ piExponent π n [MOD n] := by
  have h : a ≡ piExponent π n [MOD piPart π n * piPart πᶜ n] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (coprime_piPart disjoint_compl_right n)).1
      ⟨ha1.trans (piExponent_modEq_one π n).symm, ha0.trans (piExponent_modEq_zero π n).symm⟩
  rwa [piPart_mul_piPart_compl π hn] at h

theorem coprime_piPart_piExponent (π : Set ℕ) (n : ℕ) :
    (piPart π n).Coprime (piExponent π n) := by
  have h := (piExponent_modEq_one π n).gcd_eq
  simp only [Nat.gcd_one_left] at h
  simpa [Nat.Coprime, Nat.gcd_comm] using h

theorem gcd_piExponent (π : Set ℕ) (hn : n ≠ 0) :
    n.gcd (piExponent π n) = piPart πᶜ n := by
  have h : (piPart π n * piPart πᶜ n).gcd (piExponent π n) = piPart πᶜ n :=
    (Nat.Coprime.gcd_mul_left_cancel _ (coprime_piPart_piExponent π n)).trans
      (Nat.gcd_eq_left (piPart_compl_dvd_piExponent π n))
  rwa [piPart_mul_piPart_compl π hn] at h

end PiExponent

section Constituent

variable {X : Type*} [Group X] {π π' : Set ℕ} {x : X}

noncomputable def piConstituent (π : Set ℕ) {X : Type*} [Group X] (x : X) : X :=
  x ^ piExponent π (orderOf x)

theorem piConstituent_mem_zpowers (π : Set ℕ) (x : X) :
    piConstituent π x ∈ Subgroup.zpowers x :=
  ⟨(piExponent π (orderOf x) : ℤ), by simp [piConstituent, zpow_natCast]⟩

theorem piConstituent_eq_pow {a : ℕ} (hx : orderOf x ≠ 0)
    (ha1 : a ≡ 1 [MOD piPart π (orderOf x)])
    (ha0 : a ≡ 0 [MOD piPart πᶜ (orderOf x)]) : piConstituent π x = x ^ a :=
  pow_eq_pow_iff_modEq.2 (piExponent_modEq_of hx ha1 ha0).symm

theorem orderOf_piConstituent (hx : orderOf x ≠ 0) :
    orderOf (piConstituent π x) = piPart π (orderOf x) := by
  rcases eq_or_ne (piExponent π (orderOf x)) 0 with he0 | he0
  ·
    have h1 : piPart π (orderOf x) ∣ 1 := by
      have h := piExponent_modEq_one π (orderOf x)
      rw [he0] at h
      exact Nat.modEq_zero_iff_dvd.1 h.symm
    rw [piConstituent, he0, pow_zero, orderOf_one, Nat.dvd_one.1 h1]
  · rw [piConstituent, orderOf_pow' _ he0, gcd_piExponent π hx]
    exact Nat.div_eq_of_eq_mul_left (piPart_pos _ _) (piPart_mul_piPart_compl π hx).symm

theorem commute_piConstituent (π π' : Set ℕ) (x : X) :
    Commute (piConstituent π x) (piConstituent π' x) :=
  Commute.pow_pow_self x _ _

theorem isPiElement_piConstituent (hx : orderOf x ≠ 0) (π : Set ℕ) :
    IsPiElement π (piConstituent π x) := by
  rw [IsPiElement, orderOf_piConstituent hx]
  exact primeFactors_piPart_subset π _

theorem piConstituent_conj (π : Set ℕ) (g x : X) :
    piConstituent π (g * x * g⁻¹) = g * piConstituent π x * g⁻¹ := by
  have h : orderOf (g * x * g⁻¹) = orderOf x :=
    orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  rw [piConstituent, piConstituent, h, conj_pow]

end Constituent

section Main

variable {ι : Type*} {X : Type*} [Group X] {s : Finset ι} {π : ι → Set ℕ} {x : X}

theorem sum_piExponent_modEq_one (hd : (s : Set ι).PairwiseDisjoint π) {n : ℕ} (hn : n ≠ 0)
    (hcov : (n.primeFactors : Set ℕ) ⊆ ⋃ i ∈ s, π i) :
    ∑ i ∈ s, piExponent (π i) n ≡ 1 [MOD n] := by
  classical
  have main : ∑ i ∈ s, piExponent (π i) n ≡ 1 [MOD ∏ j ∈ s, piPart (π j) n] := by
    refine modEq_prod (fun i hi j hj hij => coprime_piPart (hd hi hj hij) n) fun j hj => ?_
    have key : ∀ i ∈ s, piExponent (π i) n ≡ (if i = j then 1 else 0) [MOD piPart (π j) n] := by
      intro i hi
      by_cases hij : i = j
      · subst hij
        simpa using piExponent_modEq_one (π i) n
      · simp only [hij, if_false]
        refine Nat.modEq_zero_iff_dvd.2 (dvd_trans ?_ (piPart_compl_dvd_piExponent (π i) n))
        exact piPart_dvd_piPart_of_subset (Set.disjoint_left.1 (hd hj hi (Ne.symm hij))) n
    refine (modEq_sum key).trans ?_
    rw [Finset.sum_ite_eq' s j (fun _ => 1)]
    simp [hj, Nat.ModEq.refl]
  rwa [prod_piPart hd, piPart_eq_self hn hcov] at main

theorem noncommProd_piConstituent (hd : (s : Set ι).PairwiseDisjoint π) (hx : orderOf x ≠ 0)
    (hcov : ((orderOf x).primeFactors : Set ℕ) ⊆ ⋃ i ∈ s, π i) :
    s.noncommProd (fun i => piConstituent (π i) x)
      (fun i _ j _ _ => commute_piConstituent (π i) (π j) x) = x := by
  refine (noncommProd_pow_eq_pow_sum s x (fun i => piExponent (π i) (orderOf x)) _).trans ?_
  conv_rhs => rw [← pow_one x]
  exact pow_eq_pow_iff_modEq.2 (sum_piExponent_modEq_one hd hx hcov)

theorem eq_piConstituent_of_noncommProd_eq (hd : (s : Set ι).PairwiseDisjoint π)
    (hx : orderOf x ≠ 0) (hcov : ((orderOf x).primeFactors : Set ℕ) ⊆ ⋃ i ∈ s, π i) {y : ι → X}
    (hyfin : ∀ i ∈ s, orderOf (y i) ≠ 0) (hy : ∀ i ∈ s, IsPiElement (π i) (y i))
    (comm : (s : Set ι).Pairwise (Commute on y)) (hprod : s.noncommProd y comm = x)
    {i : ι} (hi : i ∈ s) : y i = piConstituent (π i) x := by
  classical
  set n := orderOf x
  have hcop : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → (orderOf (y j)).Coprime (orderOf (y l)) := by
    intro j hj l hl hjl
    rw [← Nat.disjoint_primeFactors (hyfin j hj) (hyfin l hl), Finset.disjoint_left]
    intro q hq hq'
    exact Set.disjoint_left.1 (hd hj hl hjl) (hy j hj hq) (hy l hl hq')
  have hprodOrder : ∏ j ∈ s, orderOf (y j) = n := by
    rw [← orderOf_noncommProd_of_coprime comm hcop, hprod]
  have hdvdpart : ∀ j ∈ s, orderOf (y j) ∣ piPart (π j) n := fun j hj =>
    (hy j hj).orderOf_dvd_piPart (hyfin j hj) hx (hprodOrder ▸ Finset.dvd_prod_of_mem _ hj)
  have hpartsProd : ∏ j ∈ s, piPart (π j) n = n := by
    rw [prod_piPart hd, piPart_eq_self hx hcov]
  have hEq : ∀ j ∈ s, orderOf (y j) = piPart (π j) n := by
    have hsplit : ∀ j ∈ s,
        piPart (π j) n = orderOf (y j) * (piPart (π j) n / orderOf (y j)) := fun j hj =>
      (Nat.mul_div_cancel' (hdvdpart j hj)).symm
    have h1 : ∏ j ∈ s, (piPart (π j) n / orderOf (y j)) = 1 := by
      have h := hpartsProd
      rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, hprodOrder] at h
      exact (Nat.mul_eq_left hx).1 h
    intro j hj
    have h2 : piPart (π j) n / orderOf (y j) = 1 :=
      Nat.eq_one_of_dvd_one ((Finset.dvd_prod_of_mem _ hj).trans h1.dvd)
    rw [hsplit j hj, h2, mul_one]
  refine (?_ : x ^ piExponent (π i) n = y i).symm
  rw [← hprod, noncommProd_pow comm (piExponent (π i) n)
    (fun j hj l hl hjl => (comm hj hl hjl).pow_pow _ _)]
  refine (noncommProd_eq_of_eq_one _ hi fun j hj hji => ?_).trans ?_
  · refine orderOf_dvd_iff_pow_eq_one.1 (dvd_trans ?_ (piPart_compl_dvd_piExponent (π i) n))
    rw [hEq j hj]
    exact piPart_dvd_piPart_of_subset (Set.disjoint_left.1 (hd hj hi hji)) n
  · have h := pow_eq_pow_iff_modEq (x := y i) (n := piExponent (π i) n) (m := 1)
    rw [pow_one] at h
    exact h.2 (by rw [hEq i hi]; exact piExponent_modEq_one (π i) n)

variable [Finite X]

theorem primeFactors_orderOf_subset_of_natCard_subset
    (hcov : ((Nat.card X).primeFactors : Set ℕ) ⊆ ⋃ i ∈ s, π i) (x : X) :
    ((orderOf x).primeFactors : Set ℕ) ⊆ ⋃ i ∈ s, π i :=
  fun _ hq => hcov (Nat.primeFactors_mono (orderOf_dvd_natCard x) Nat.card_pos.ne' hq)

theorem exists_unique_family_isPiElement_noncommProd_eq
    (hd : (s : Set ι).PairwiseDisjoint π)
    (hcov : ((Nat.card X).primeFactors : Set ℕ) ⊆ ⋃ i ∈ s, π i) (x : X) :
    ∃ y : ι → X, ∃ comm : (s : Set ι).Pairwise (Commute on y),
      (∀ i ∈ s, IsPiElement (π i) (y i)) ∧ s.noncommProd y comm = x ∧
      ∀ z : ι → X, ∀ commz : (s : Set ι).Pairwise (Commute on z),
        (∀ i ∈ s, IsPiElement (π i) (z i)) → s.noncommProd z commz = x →
          ∀ i ∈ s, z i = y i := by
  have hx : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hcov' := primeFactors_orderOf_subset_of_natCard_subset hcov x
  refine ⟨fun i => piConstituent (π i) x,
    fun i _ j _ _ => commute_piConstituent (π i) (π j) x,
    fun i _ => isPiElement_piConstituent hx (π i),
    noncommProd_piConstituent hd hx hcov', fun z commz hz hzprod i hi => ?_⟩
  exact eq_piConstituent_of_noncommProd_eq hd hx hcov'
    (fun j _ => (orderOf_pos (z j)).ne') hz commz hzprod hi

end Main

end

end CFSG.FeitThompson
