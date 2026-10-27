module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Equiv CFSG.CGT.PushingUp

theorem cbp_exists_fixed_of_involution {k : ℕ} (hk : Odd k) {σ : Perm (Fin k)}
    (h : σ * σ = 1) : ∃ r, σ r = r := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End (Fin k) := fun x => σ x
  have h2 : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    refine funext fun x => ?_
    have h3 : σ (σ x) = x := by simpa using congrArg (fun g : Perm (Fin k) => g x) h
    exact h3
  have hmod := Equiv.Perm.card_fixedPoints_modEq h2
  have hfix : Fintype.card ↑(Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨x, hx⟩
    exact hcon x hx
  rw [hfix, Fintype.card_fin] at hmod
  have : k % 2 = 0 := hmod
  rcases hk with ⟨j, rfl⟩
  omega

theorem cbp_four_points {k : ℕ} (S : Finset (Fin k)) (hS : S.card + 4 ≤ k) :
    ∃ j l r n : Fin k, j ∉ S ∧ l ∉ S ∧ r ∉ S ∧ n ∉ S ∧ j ≠ l ∧ j ≠ r ∧ j ≠ n ∧ l ≠ r ∧
      l ≠ n ∧ r ≠ n := by
  classical
  have hc : 4 ≤ (Sᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hc
  obtain ⟨j, T1, hjT, rfl, hT1⟩ := Finset.card_eq_succ.mp hT
  obtain ⟨l, T2, hlT, rfl, hT2⟩ := Finset.card_eq_succ.mp hT1
  obtain ⟨r, T3, hrT, rfl, hT3⟩ := Finset.card_eq_succ.mp hT2
  obtain ⟨n, T4, hnT, rfl, hT4⟩ := Finset.card_eq_succ.mp hT3
  have hjS : j ∉ S := by
    have := hTS (by simp : j ∈ insert j (insert l (insert r (insert n T4))))
    simpa using this
  have hlS : l ∉ S := by
    have := hTS (by simp : l ∈ insert j (insert l (insert r (insert n T4))))
    simpa using this
  have hrS : r ∉ S := by
    have := hTS (by simp : r ∈ insert j (insert l (insert r (insert n T4))))
    simpa using this
  have hnS : n ∉ S := by
    have := hTS (by simp : n ∈ insert j (insert l (insert r (insert n T4))))
    simpa using this
  simp only [Finset.mem_insert, not_or] at hjT hlT hrT
  exact ⟨j, l, r, n, hjS, hlS, hrS, hnS, hjT.1, hjT.2.1, hjT.2.2.1, hlT.1, hlT.2.1, hrT.1⟩


theorem cbp_fix_of_commute {k : ℕ} (hk : 7 ≤ k) {p q : Fin k} {σ : Perm (Fin k)}
    (h : ∀ τ : alternatingGroup (Fin k), τ ∈ altStabilizer k {p, q} →
      σ * (τ : Perm (Fin k)) = (τ : Perm (Fin k)) * σ) {x : Fin k} (hxp : x ≠ p) (hxq : x ≠ q) :
    σ x = x := by
  classical
  obtain ⟨j, l, r, n, hj, hl, hr, hn, hjl, hjr, hjn, hlr, hln, hrn⟩ :=
    cbp_four_points ({x, p, q} : Finset (Fin k))
      (by have := Finset.card_le_three (a := x) (b := p) (c := q); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj hl hr hn
  have hsw : ∀ {u v : Fin k}, u ≠ v → Perm.sign (swap u v) = -1 := fun huv =>
    Perm.sign_swap huv
  have mk : ∀ {u v w : Fin k}, u ≠ v → u ≠ w → v ∉ ({p, q} : Finset (Fin k)) →
      w ∉ ({p, q} : Finset (Fin k)) → u ∉ ({p, q} : Finset (Fin k)) →
      ∃ τ : alternatingGroup (Fin k), τ ∈ altStabilizer k {p, q} ∧
        (τ : Perm (Fin k)) = swap u v * swap u w := by
    intro u v w huv huw hv hw hu
    have hmem : swap u v * swap u w ∈ alternatingGroup (Fin k) := by
      rw [Perm.mem_alternatingGroup, map_mul, hsw huv, hsw huw]
      decide
    refine ⟨⟨_, hmem⟩, ?_, rfl⟩
    rw [mem_altStabilizer_iff]
    intro i hi
    have hiu : i ≠ u := fun h => hu (h ▸ hi)
    have hiv : i ≠ v := fun h => hv (h ▸ hi)
    have hiw : i ≠ w := fun h => hw (h ▸ hi)
    show (swap u v * swap u w) i = i
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hiu hiw, swap_apply_of_ne_of_ne hiu hiv]
  have hxpq : x ∉ ({p, q} : Finset (Fin k)) := by simp [hxp, hxq]
  have key : ∀ {v w : Fin k}, x ≠ v → x ≠ w → v ≠ w → v ∉ ({p, q} : Finset (Fin k)) →
      w ∉ ({p, q} : Finset (Fin k)) → σ x = x ∨ σ x = v ∨ σ x = w := by
    intro v w hxv hxw hvw hv hw
    obtain ⟨τ, hτ, hτe⟩ := mk hxv hxw hv hw hxpq
    have hc := h τ hτ
    rw [hτe] at hc
    by_contra hcon
    push Not at hcon
    have h1 : (swap x v * swap x w) (σ x) = σ x := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcon.1 hcon.2.2,
        swap_apply_of_ne_of_ne hcon.1 hcon.2.1]
    have h2 : (swap x v * swap x w) x = w := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hxw) (Ne.symm hvw)]
    have h3 : σ ((swap x v * swap x w) x) = (swap x v * swap x w) (σ x) := by
      have := congrArg (fun f : Perm (Fin k) => f x) hc
      simpa [Perm.mul_apply] using this
    rw [h1, h2] at h3
    exact hxw (σ.injective h3).symm
  have k1 := key (v := j) (w := l) (Ne.symm hj.1) (Ne.symm hl.1) hjl
    (by simp [hj.2.1, hj.2.2]) (by simp [hl.2.1, hl.2.2])
  have k2 := key (v := r) (w := n) (Ne.symm hr.1) (Ne.symm hn.1) hrn
    (by simp [hr.2.1, hr.2.2]) (by simp [hn.2.1, hn.2.2])
  rcases k1 with h1 | h1 | h1
  · exact h1
  · rcases k2 with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hjr
    · exact absurd (h1.symm.trans h2) hjn
  · rcases k2 with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hlr
    · exact absurd (h1.symm.trans h2) hln

theorem cbp_eq_one_or_swap {k : ℕ} (hk : 7 ≤ k) {p q : Fin k} (hpq : p ≠ q) {σ : Perm (Fin k)}
    (h : ∀ τ : alternatingGroup (Fin k), τ ∈ altStabilizer k {p, q} →
      σ * (τ : Perm (Fin k)) = (τ : Perm (Fin k)) * σ) : σ = 1 ∨ σ = swap p q := by
  have hfix := fun {x : Fin k} hxp hxq => cbp_fix_of_commute hk h (x := x) hxp hxq
  have hp : σ p = p ∨ σ p = q := by
    by_contra hcon
    push Not at hcon
    have h1 := hfix (x := σ p) hcon.1 hcon.2
    exact hcon.1 (σ.injective h1)
  have hq : σ q = p ∨ σ q = q := by
    by_contra hcon
    push Not at hcon
    have h1 := hfix (x := σ q) hcon.1 hcon.2
    exact hcon.2 (σ.injective h1)
  rcases hp with hp | hp
  · left
    have hq' : σ q = q := by
      rcases hq with hq | hq
      · exact absurd (σ.injective (hq.trans hp.symm)) (Ne.symm hpq)
      · exact hq
    refine Equiv.ext fun x => ?_
    by_cases hxp : x = p
    · rw [hxp, hp]; rfl
    by_cases hxq : x = q
    · rw [hxq, hq']; rfl
    · exact hfix hxp hxq
  · right
    have hq' : σ q = p := by
      rcases hq with hq | hq
      · exact hq
      · exact absurd (σ.injective (hq.trans hp.symm)) (Ne.symm hpq)
    refine Equiv.ext fun x => ?_
    by_cases hxp : x = p
    · rw [hxp, hp, swap_apply_left]
    by_cases hxq : x = q
    · rw [hxq, hq', swap_apply_right]
    · rw [hfix hxp hxq, swap_apply_of_ne_of_ne hxp hxq]


theorem cbp_exists_alt_pair {k : ℕ} (hk : 4 ≤ k) {a b p q : Fin k} (hab : a ≠ b) (hpq : p ≠ q) :
    ∃ τ : alternatingGroup (Fin k), (τ : Perm (Fin k)) a = p ∧ (τ : Perm (Fin k)) b = q := by
  classical
  set b' : Fin k := swap a p b with hb'
  have hpb' : p ≠ b' := by
    intro h
    have h2 : swap a p b = p := h.symm
    have h3 : b = a := by
      have := congrArg (swap a p) h2
      simpa using this
    exact hab h3.symm
  have h0a : (swap b' q * swap a p) a = p := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hpb' hpq]
  have h0b : (swap b' q * swap a p) b = q := by
    rw [Perm.mul_apply, ← hb', swap_apply_left]
  by_cases hs : Perm.sign (swap b' q * swap a p) = 1
  · exact ⟨⟨_, Perm.mem_alternatingGroup.mpr hs⟩, h0a, h0b⟩
  ·
    have hcard : 1 < (({p, q} : Finset (Fin k))ᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_two (a := p) (b := q)
      omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hcard
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
    have hsg : Perm.sign (swap c d * (swap b' q * swap a p)) = 1 := by
      rw [map_mul, Perm.sign_swap hcd]
      have : Perm.sign (swap b' q * swap a p) = -1 := by
        rcases Int.units_eq_one_or (Perm.sign (swap b' q * swap a p)) with h | h
        · exact absurd h hs
        · exact h
      rw [this]; decide
    refine ⟨⟨_, Perm.mem_alternatingGroup.mpr hsg⟩, ?_, ?_⟩
    · show (swap c d * (swap b' q * swap a p)) a = p
      rw [Perm.mul_apply, h0a, swap_apply_of_ne_of_ne (Ne.symm hc.1) (Ne.symm hd.1)]
    · show (swap c d * (swap b' q * swap a p)) b = q
      rw [Perm.mul_apply, h0b, swap_apply_of_ne_of_ne (Ne.symm hc.2) (Ne.symm hd.2)]

theorem cbp_exists_comm_involutions (m : ℕ) (hm : 6 ≤ m) :
    ∃ a₁ a₂ : alternatingGroup (Fin m), a₁ ^ 2 = 1 ∧ a₂ ^ 2 = 1 ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧
      a₁ ≠ a₂ ∧ a₁ * a₂ = a₂ * a₁ := by
  have hcomm : ∀ {a b c d : Fin m}, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Commute (swap a b) (swap c d) := by
    intro a b c d hac had hbc hbd
    have : (swap a b).Disjoint (swap c d) := by
      intro x
      by_cases hx : x = a ∨ x = b
      · right
        apply swap_apply_of_ne_of_ne
        · rcases hx with rfl | rfl <;> assumption
        · rcases hx with rfl | rfl <;> assumption
      · left
        simp only [not_or] at hx
        exact swap_apply_of_ne_of_ne hx.1 hx.2
    exact this.commute
  let p : ℕ → Fin m := fun i => if h : i < m then ⟨i, h⟩ else ⟨0, by omega⟩
  have hp : ∀ i j, i < m → j < m → i ≠ j → p i ≠ p j := fun i j hi hj hij h => by
    simp only [p, hi, hj, dite_true, Fin.mk.injEq] at h
    exact hij h
  have h01 := hp 0 1 (by omega) (by omega) (by omega)
  have h23 := hp 2 3 (by omega) (by omega) (by omega)
  have h45 := hp 4 5 (by omega) (by omega) (by omega)
  have hsq : ∀ {a b : Fin m}, a ≠ b → swap a b * swap a b = 1 := fun _ => swap_mul_self _ _
  have c01_23 := hcomm (a := p 0) (b := p 1) (c := p 2) (d := p 3) (hp 0 2 (by omega) (by omega)
    (by omega)) (hp 0 3 (by omega) (by omega) (by omega)) (hp 1 2 (by omega) (by omega) (by omega))
    (hp 1 3 (by omega) (by omega) (by omega))
  have c01_45 := hcomm (a := p 0) (b := p 1) (c := p 4) (d := p 5) (hp 0 4 (by omega) (by omega)
    (by omega)) (hp 0 5 (by omega) (by omega) (by omega)) (hp 1 4 (by omega) (by omega) (by omega))
    (hp 1 5 (by omega) (by omega) (by omega))
  have c23_45 := hcomm (a := p 2) (b := p 3) (c := p 4) (d := p 5) (hp 2 4 (by omega) (by omega)
    (by omega)) (hp 2 5 (by omega) (by omega) (by omega)) (hp 3 4 (by omega) (by omega) (by omega))
    (hp 3 5 (by omega) (by omega) (by omega))
  have mem1 : swap (p 0) (p 1) * swap (p 2) (p 3) ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h23]
    decide
  have mem2 : swap (p 0) (p 1) * swap (p 4) (p 5) ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h45]
    decide
  refine ⟨⟨_, mem1⟩, ⟨_, mem2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (swap (p 0) (p 1) * swap (p 2) (p 3)) ^ 2 = 1
    rw [c01_23.mul_pow, pow_two, pow_two, hsq h01, hsq h23, mul_one]
  · apply Subtype.ext
    show (swap (p 0) (p 1) * swap (p 4) (p 5)) ^ 2 = 1
    rw [c01_45.mul_pow, pow_two, pow_two, hsq h01, hsq h45, mul_one]
  · intro h
    have := congrArg (fun f : alternatingGroup (Fin m) => (f : Perm (Fin m)) (p 0)) h
    simp only [Perm.mul_apply, OneMemClass.coe_one, Perm.coe_one, id_eq] at this
    rw [swap_apply_of_ne_of_ne (hp 0 2 (by omega) (by omega) (by omega))
      (hp 0 3 (by omega) (by omega) (by omega)), swap_apply_left] at this
    exact h01 this.symm
  · intro h
    have := congrArg (fun f : alternatingGroup (Fin m) => (f : Perm (Fin m)) (p 0)) h
    simp only [Perm.mul_apply, OneMemClass.coe_one, Perm.coe_one, id_eq] at this
    rw [swap_apply_of_ne_of_ne (hp 0 4 (by omega) (by omega) (by omega))
      (hp 0 5 (by omega) (by omega) (by omega)), swap_apply_left] at this
    exact h01 this.symm
  · intro h
    have := congrArg (fun f : alternatingGroup (Fin m) => (f : Perm (Fin m)) (p 2)) h
    simp only [Perm.mul_apply] at this
    rw [swap_apply_left, swap_apply_of_ne_of_ne (hp 2 4 (by omega) (by omega) (by omega))
      (hp 2 5 (by omega) (by omega) (by omega)),
      swap_apply_of_ne_of_ne (hp 2 0 (by omega) (by omega) (by omega))
        (hp 2 1 (by omega) (by omega) (by omega)),
      swap_apply_of_ne_of_ne (hp 3 0 (by omega) (by omega) (by omega))
        (hp 3 1 (by omega) (by omega) (by omega))] at this
    exact h23.symm this
  · apply Subtype.ext
    show (swap (p 0) (p 1) * swap (p 2) (p 3)) * (swap (p 0) (p 1) * swap (p 4) (p 5)) =
      (swap (p 0) (p 1) * swap (p 4) (p 5)) * (swap (p 0) (p 1) * swap (p 2) (p 3))
    exact ((Commute.refl (swap (p 0) (p 1))).mul_right c01_45 |>.mul_left
      (c01_23.symm.mul_right c23_45 |>.symm.symm)).eq

end CFSG.CGT.PushingUpLit.CGT6
