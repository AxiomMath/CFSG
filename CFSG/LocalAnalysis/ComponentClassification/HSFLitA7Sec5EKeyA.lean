module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5EFacts

public section

namespace CFSG.ComponentClassification.HSFLit.Sec5E

open Sec8

namespace T2M

@[expose] def SigD.cosetIdx (p : SigD) (a : T2M) : Fin 4 :=
  if (p.reps 0)⁻¹ * a ∈ Zl then 0 else if (p.reps 1)⁻¹ * a ∈ Zl then 1 else
    if (p.reps 2)⁻¹ * a ∈ Zl then 2 else 3

namespace SigD

@[expose] def IdxOk (p : SigD) : Prop :=
  (∀ a ∈ p.S16, (p.reps (p.cosetIdx a))⁻¹ * a ∈ Zl) ∧
    ∀ i : Fin 4, ∀ c ∈ Zl, p.cosetIdx (p.reps i * c) = i

instance (p : SigD) : Decidable (IdxOk p) := by unfold IdxOk; infer_instance

theorem idxOk : ∀ p ∈ repList, IdxOk p := by decide +kernel

end SigD

theorem mul_mem_Zl : ∀ c ∈ Zl, ∀ c' ∈ Zl, c * c' ∈ Zl := by decide +kernel

theorem sq_mul_central (a b c c' : T2M) (hc : c ∈ Zl) (hc' : c' ∈ Zl) :
    a * c * (b * c') * (a * c * (b * c')) = a * b * (a * b) := by
  have hd := mul_mem_Zl c hc c' hc'
  have hcomm := central_of_mem_Zl _ hd
  have h1 : a * c * (b * c') = a * b * (c * c') := by
    rw [mul_assoc a c, ← mul_assoc c b, central_of_mem_Zl c hc b]; group
  calc a * c * (b * c') * (a * c * (b * c')) = a * b * (c * c') * (a * b * (c * c')) := by
        rw [h1]
    _ = a * b * ((c * c') * (a * b)) * (c * c') := by group
    _ = a * b * ((a * b) * (c * c')) * (c * c') := by rw [hcomm (a * b)]
    _ = a * b * (a * b) * ((c * c') * (c * c')) := by group
    _ = a * b * (a * b) := by rw [sq_of_mem_Zl _ hd, mul_one]

theorem sq_mul_central' : ∀ c ∈ Zl, ∀ a : T2M, a * c * (a * c) = a * a := by decide +kernel

theorem k_cases : ∀ c ∈ Zl, c = 1 ∨ c = z ∨ c = k ∨ c = z * k := by decide +kernel

theorem z_mem_Zl : z ∈ Zl := by decide +kernel

theorem k_mem_Zl : k ∈ Zl := by decide +kernel

theorem one_mem_Zl : (1 : T2M) ∈ Zl := by decide +kernel

theorem k_ne_one : k ≠ 1 := by decide +kernel

theorem k_ne_z : k ≠ z := by decide +kernel

theorem kz_ne_k : k * z ≠ k := by decide +kernel

theorem fin4_cube : ∀ π : Fin 4 → Fin 4, (∀ i j, SigD.Match i j ↔ SigD.Match (π i) (π j)) →
    (∀ i, π (π (π i)) = i) → ∀ i, π i = i := by decide +kernel

theorem fin4_twelve : ∀ π : Fin 4 → Fin 4, Function.Injective π → ∀ i, π^[12] i = i := by
  decide +kernel

theorem mul_inv_mem_Zl_of_gens (ν : T2M →* T2M) :
    ∀ (gs : List T2M), (∀ g ∈ gs, ν g * g⁻¹ ∈ Zl) → ∀ bs : List Bool,
      ν (nfProd gs bs) * (nfProd gs bs)⁻¹ ∈ Zl
  | [], _, bs => by cases bs <;> simp [nfProd, one_mem_Zl]
  | g :: gs, h, [] => by simp [nfProd, one_mem_Zl]
  | g :: gs, h, b :: bs => by
    have ih := mul_inv_mem_Zl_of_gens ν gs (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) bs
    have hg := h g List.mem_cons_self
    cases b
    · simpa [nfProd] using ih
    · simp only [nfProd, ite_true, map_mul, mul_inv_rev]
      have := mul_mem_Zl _ hg _ ih
      have hc := central_of_mem_Zl _ ih (ν g)
      rw [show ν g * ν (nfProd gs bs) * ((nfProd gs bs)⁻¹ * g⁻¹) =
          ν g * (ν (nfProd gs bs) * (nfProd gs bs)⁻¹) * g⁻¹ by group, ← hc]
      rwa [show ν (nfProd gs bs) * (nfProd gs bs)⁻¹ * ν g * g⁻¹ =
          ν (nfProd gs bs) * (nfProd gs bs)⁻¹ * (ν g * g⁻¹) by group,
        central_of_mem_Zl _ ih]

namespace SigD

variable {p : SigD}

theorem eq_self_of_odd (hp : p ∈ repList) (ν : T2M →* T2M) (hinj : Function.Injective ν)
    (hS : ∀ a ∈ p.S16, ν a ∈ p.S16) {m : ℕ} (hm : Odd m) (hνm : ∀ a, ν^[m] a = a) (a : T2M) :
    ν a = a := by
  obtain ⟨hidx, huniq⟩ := idxOk p hp
  set π : Fin 4 → Fin 4 := fun i => p.cosetIdx (ν (p.reps i)) with hπ
  have hcov : ∀ i, ν (p.reps i) = p.reps (π i) * ((p.reps (π i))⁻¹ * ν (p.reps i)) ∧
      (p.reps (π i))⁻¹ * ν (p.reps i) ∈ Zl := by
    intro i
    refine ⟨by group, hidx _ (hS _ ?_)⟩
    have := reps_mem p hp i 1 one_mem_Zl
    rwa [mul_one] at this
  have hsurj : Function.Surjective ν := Finite.injective_iff_surjective.mp hinj
  have hZ : ∀ c ∈ Zl, ν c ∈ Zl := by
    intro c hc
    refine mem_Zl_of_central _ fun b => ?_
    obtain ⟨b', rfl⟩ := hsurj b
    rw [← map_mul, ← map_mul, central_of_mem_Zl c hc b']
  have hiter : ∀ j : ℕ, ∀ i, ∃ c ∈ Zl, ν^[j] (p.reps i) = p.reps (π^[j] i) * c := by
    intro j
    induction j with
    | zero => intro i; exact ⟨1, one_mem_Zl, by simp⟩
    | succ j ih =>
      intro i
      obtain ⟨c, hc, hj⟩ := ih i
      obtain ⟨-, hc'⟩ := hcov (π^[j] i)
      refine ⟨(p.reps (π (π^[j] i)))⁻¹ * ν (p.reps (π^[j] i)) * ν c,
        mul_mem_Zl _ hc' _ (hZ c hc), ?_⟩
      rw [Function.iterate_succ_apply', hj, map_mul, Function.iterate_succ_apply']
      group
  have hπm : ∀ i, π^[m] i = i := by
    intro i
    obtain ⟨c, hc, h⟩ := hiter m i
    rw [hνm] at h
    have := huniq (π^[m] i) c hc
    rw [← h] at this
    have h2 := huniq i 1 one_mem_Zl
    rw [mul_one] at h2
    exact this.symm.trans h2
  have hπinj : Function.Injective π := by
    intro i j hij
    obtain ⟨j₀, hj₀⟩ := hm
    have h1 := hπm i
    have h2 := hπm j
    rw [hj₀, Function.iterate_add_apply, Function.iterate_one, hij] at h1
    rw [hj₀, Function.iterate_add_apply, Function.iterate_one] at h2
    exact h1.symm.trans h2
  have hmatch : ∀ i j, Match i j ↔ Match (π i) (π j) := by
    intro i j
    rw [← reps_match p hp i j, ← reps_match p hp (π i) (π j)]
    obtain ⟨hi, hci⟩ := hcov i
    obtain ⟨hj, hcj⟩ := hcov j
    have hsq : ν (p.reps i * p.reps j * (p.reps i * p.reps j)) =
        p.reps (π i) * p.reps (π j) * (p.reps (π i) * p.reps (π j)) := by
      simp only [map_mul]
      rw [hi, hj]
      exact sq_mul_central _ _ _ _ hci hcj
    rw [← hsq]
    constructor
    · intro h h1; exact h (hinj (h1.trans (map_one ν).symm))
    · intro h h1; exact h (by rw [h1, map_one])
  have hπ3 : ∀ i, π (π (π i)) = i := by
    intro i
    have h12 := fin4_twelve π hπinj i
    have hper : Function.IsPeriodicPt π (Nat.gcd m 12) i :=
      Function.IsPeriodicPt.gcd (hπm i) h12
    have hg : Nat.gcd m 12 = 1 ∨ Nat.gcd m 12 = 3 := by
      have hdvd := Nat.gcd_dvd_right m 12
      have hodd : ¬ 2 ∣ Nat.gcd m 12 := fun h2 =>
        (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr (h2.trans (Nat.gcd_dvd_left m 12)))
      have : Nat.gcd m 12 ∈ Nat.divisors 12 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have h12 : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
      rw [h12] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    rcases hg with hg | hg <;> rw [hg] at hper
    · have h1 : π i = i := hper
      rw [h1, h1, h1]
    · exact hper
  have hπid := fin4_cube π hmatch hπ3
  have hgens : ∀ g ∈ [p.reps 0, p.reps 1, p.reps 2, p.reps 3, z, k], ν g * g⁻¹ ∈ Zl := by
    intro g hg
    have hrep : ∀ i, ν (p.reps i) * (p.reps i)⁻¹ ∈ Zl := by
      intro i
      obtain ⟨-, hci⟩ := hcov i
      rw [hπid i] at hci
      have hcen := central_of_mem_Zl _ hci (p.reps i)
      have : ν (p.reps i) * (p.reps i)⁻¹ = (p.reps i)⁻¹ * ν (p.reps i) := by
        calc ν (p.reps i) * (p.reps i)⁻¹
            = p.reps i * ((p.reps i)⁻¹ * ν (p.reps i)) * (p.reps i)⁻¹ := by group
          _ = (p.reps i)⁻¹ * ν (p.reps i) * p.reps i * (p.reps i)⁻¹ := by rw [← hcen]
          _ = (p.reps i)⁻¹ * ν (p.reps i) := by group
      rw [this]; exact hci
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hrep 0
    · exact hrep 1
    · exact hrep 2
    · exact hrep 3
    · exact mul_mem_Zl _ (hZ _ z_mem_Zl) _ (by decide +kernel)
    · exact mul_mem_Zl _ (hZ _ k_mem_Zl) _ (by decide +kernel)
  have hmod : ∀ b, ν b * b⁻¹ ∈ Zl := by
    intro b
    obtain ⟨bs, -, rfl⟩ := reps_gen p hp b
    exact mul_inv_mem_Zl_of_gens ν _ hgens bs
  have hz : ν z = z := by
    have hx := hmod x
    rw [z_eq, map_mul]
    have h := sq_mul_central' _ hx x
    rw [show ν x = x * (x⁻¹ * ν x) by group]
    have hc : x⁻¹ * ν x ∈ Zl := by
      have := central_of_mem_Zl _ hx x⁻¹
      rw [show x⁻¹ * ν x = x⁻¹ * (ν x * x⁻¹) * x by group, ← this]
      simpa using hx
    exact sq_mul_central' _ hc x
  have hzk : ∀ c ∈ Zl, ν c ∈ Zl := hZ
  have hk : ν k = k := by
    have hc : k⁻¹ * ν k ∈ Zl := by
      have := mul_mem_Zl _ (by decide +kernel : k⁻¹ ∈ Zl) _ (hZ k k_mem_Zl)
      exact this
    have hνk : ν k = k * (k⁻¹ * ν k) := by group
    rcases k_cases _ hc with h | h | h | h
    · rw [hνk, h, mul_one]
    · exfalso
      have h1 : ν k = k * z := by rw [hνk, h]
      have hkz : ν (k * z) = k := by
        rw [map_mul, h1, hz, mul_assoc, show z * z = 1 by decide +kernel, mul_one]
      have h2 : ∀ j : ℕ, ν^[2 * j + 1] k = k * z := by
        intro j
        induction j with
        | zero => simpa using h1
        | succ j ih =>
          rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, Function.iterate_add_apply,
            show ν^[2] k = k by rw [Function.iterate_succ_apply, Function.iterate_one, h1, hkz],
            ih]
      obtain ⟨j, rfl⟩ := hm
      exact kz_ne_k ((h2 j).symm.trans (hνm k))
    · exfalso
      have h1 : ν k = 1 := by rw [hνk, h]; decide +kernel
      exact k_ne_one (hinj (h1.trans (map_one ν).symm))
    · exfalso
      have h1 : ν k = ν z := by rw [hνk, h, hz]; decide +kernel
      exact k_ne_z (hinj h1)
  have hfix : ∀ c ∈ Zl, ν c = c := by
    intro c hc
    rcases k_cases c hc with rfl | rfl | rfl | rfl
    · exact map_one ν
    · exact hz
    · exact hk
    · rw [map_mul, hz, hk]
  set c := ν a * a⁻¹ with hcdef
  have hc := hmod a
  have hνa : ν a = c * a := by rw [hcdef]; group
  have hiter2 : ∀ j : ℕ, ν^[j] a = c ^ j * a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hfix c hc, hνa, pow_succ]
      group
  have h := hiter2 m
  rw [hνm] at h
  obtain ⟨j, rfl⟩ := hm
  have hc2 : c * c = 1 := sq_of_mem_Zl c hc
  have hcpow : c ^ (2 * j + 1) = c := by rw [pow_succ, pow_mul, pow_two, hc2, one_pow, one_mul]
  rw [hcpow] at h
  have hc1 : c = 1 := by
    have := congrArg (· * a⁻¹) h
    simpa using this.symm
  rw [hνa, hc1, one_mul]

end SigD

end T2M

end CFSG.ComponentClassification.HSFLit.Sec5E
