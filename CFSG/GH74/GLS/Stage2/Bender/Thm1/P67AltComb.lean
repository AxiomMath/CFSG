module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Equiv Equiv.Perm Subgroup

section Supports

variable {α : Type} [Fintype α] [DecidableEq α]

theorem card_support_ge_of_prime_orderOf {w : Perm α} {s : ℕ} (hs : s.Prime) (hw : orderOf w = s) :
    s ≤ w.support.card := by
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw
    exact hs.one_lt.ne hw
  obtain ⟨x, hx⟩ : ∃ x, w x ≠ x := by
    by_contra h
    push Not at h
    exact hw1 (Equiv.ext h)
  have hcyc : (w.cycleOf x).IsCycle := Equiv.Perm.isCycle_cycleOf w hx
  have hdvd : orderOf (w.cycleOf x) ∣ s := hw ▸ Equiv.Perm.orderOf_cycleOf_dvd_orderOf w x
  have hne : orderOf (w.cycleOf x) ≠ 1 := by
    rw [hcyc.orderOf]
    have := hcyc.two_le_card_support
    omega
  have hord : orderOf (w.cycleOf x) = s := ((Nat.dvd_prime hs).1 hdvd).resolve_left hne
  rw [hcyc.orderOf] at hord
  rw [← hord]
  exact Finset.card_le_card (Equiv.Perm.support_cycleOf_le w x)

omit [DecidableEq α] in
theorem fix_of_pow_apply_eq {σ : Perm α} {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p) {x : α} {k : ℕ}
    (hk : ¬ p ∣ k) (h : (σ ^ k) x = x) : σ x = x := by
  have hcop : Nat.Coprime (orderOf σ) k := by
    rw [hσ]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hk
  have h1 : orderOf (σ ^ k) = p := by rw [Nat.Coprime.orderOf_pow hcop]; exact hσ
  have h2 : zpowers (σ ^ k) ≤ zpowers σ := Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) k)
  have h3 : Nat.card (zpowers (σ ^ k)) = Nat.card (zpowers σ) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, h1, hσ]
  have h4 : zpowers (σ ^ k) = zpowers σ :=
    Subgroup.eq_of_le_of_card_ge h2 (le_of_eq h3.symm)
  have h5 : σ ∈ zpowers (σ ^ k) := h4 ▸ Subgroup.mem_zpowers σ
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h5
  have := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h j
  rwa [hj] at this

omit [DecidableEq α] in
theorem prime_dvd_of_zpow_apply_eq {σ : Perm α} {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p)
    {x : α} (hx : σ x ≠ x) {a : ℤ} (h : (σ ^ a) x = x) : (p : ℤ) ∣ a := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmod : σ ^ (a % (p : ℤ)) = σ ^ a := by
    have := zpow_mod_orderOf σ a
    rwa [hσ] at this
  have hnn : 0 ≤ a % (p : ℤ) := Int.emod_nonneg a hp0
  have hlt : a % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos a (by exact_mod_cast hp.pos)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = a % (p : ℤ) := ⟨(a % (p : ℤ)).toNat, Int.toNat_of_nonneg hnn⟩
  have hk0 : p ∣ k := by
    by_contra hnd
    apply hx
    refine fix_of_pow_apply_eq hp hσ hnd ?_
    rw [← zpow_natCast, hk, hmod]
    exact h
  have hklt : k < p := by exact_mod_cast hk ▸ hlt
  have hk00 : k = 0 := Nat.eq_zero_of_dvd_of_lt hk0 hklt
  apply Int.dvd_of_emod_eq_zero
  rw [← hk, hk00]
  rfl

omit [DecidableEq α] in
theorem prime_dvd_exponent_of_comm {g w : Perm α} {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hg : orderOf g = r) (hw : orderOf w = s) (hcomm : g * w = w * g) {x : α} (hgx : g x ≠ x)
    {a b : ℤ} (h : (g ^ a * w ^ b) x = x) : (r : ℤ) ∣ a := by
  classical
  have hc : Commute g w := hcomm
  have hcc : Commute (g ^ a) (w ^ b) := hc.zpow_zpow a b
  have hs' : (w ^ b) ^ s = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hw, pow_orderOf_eq_one, one_zpow]
  have h1 : ((g ^ a * w ^ b) ^ s) x = x := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h s
  rw [hcc.mul_pow, hs', mul_one, ← zpow_natCast, ← zpow_mul] at h1
  have h2 := prime_dvd_of_zpow_apply_eq hr hg hgx h1
  have hrint : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  rcases hrint.dvd_or_dvd h2 with h3 | h3
  · exact h3
  · exfalso
    have : r ∣ s := by exact_mod_cast h3
    exact hrs ((Nat.prime_dvd_prime_iff_eq hr hs).1 this)

omit [DecidableEq α] in
theorem mul_le_card_of_commuting {g w : Perm α} {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hg : orderOf g = r) (hw : orderOf w = s) (hcomm : g * w = w * g) {x : α} (hgx : g x ≠ x)
    (hwx : w x ≠ x) : r * s ≤ Fintype.card α := by
  classical
  have hc : Commute g w := hcomm
  let F : Fin r × Fin s → α := fun p => (g ^ (p.1 : ℕ) * w ^ (p.2 : ℕ)) x
  have hF : Function.Injective F := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hE : ((g ^ ((i : ℕ) : ℤ) * w ^ ((j : ℕ) : ℤ)) : Perm α) x =
        ((g ^ ((i' : ℕ) : ℤ) * w ^ ((j' : ℕ) : ℤ)) : Perm α) x := by
      simp only [zpow_natCast]; exact h
    have hdiff : ∀ (i i' j j' : ℤ), ((g ^ i * w ^ j : Perm α) x = (g ^ i' * w ^ j' : Perm α) x) →
        ((g ^ (i - i') * w ^ (j - j') : Perm α) x = x) := by
      intro i i' j j' hh
      have hP : (g ^ (-i') * w ^ (-j') : Perm α) * (g ^ i * w ^ j) = g ^ (i - i') * w ^ (j - j') := by
        have hc1 : (w ^ (-j') : Perm α) * g ^ i = g ^ i * w ^ (-j') := ((hc.zpow_zpow i (-j')).symm).eq
        calc (g ^ (-i') * w ^ (-j') : Perm α) * (g ^ i * w ^ j)
            = g ^ (-i') * ((w ^ (-j') : Perm α) * g ^ i) * w ^ j := by group
          _ = g ^ (-i') * (g ^ i * w ^ (-j')) * w ^ j := by rw [hc1]
          _ = (g ^ (-i') * g ^ i) * (w ^ (-j') * w ^ j) := by group
          _ = g ^ (i - i') * w ^ (j - j') := by
            rw [← zpow_add, ← zpow_add]; congr 2 <;> ring
      have hQ : (g ^ (-i') * w ^ (-j') : Perm α) * (g ^ i' * w ^ j') = 1 := by
        have hc1 : (w ^ (-j') : Perm α) * g ^ i' = g ^ i' * w ^ (-j') := ((hc.zpow_zpow i' (-j')).symm).eq
        calc (g ^ (-i') * w ^ (-j') : Perm α) * (g ^ i' * w ^ j')
            = g ^ (-i') * ((w ^ (-j') : Perm α) * g ^ i') * w ^ j' := by group
          _ = g ^ (-i') * (g ^ i' * w ^ (-j')) * w ^ j' := by rw [hc1]
          _ = (g ^ (-i') * g ^ i') * (w ^ (-j') * w ^ j') := by group
          _ = 1 := by simp
      have h3 := congrArg (⇑(g ^ (-i') * w ^ (-j') : Perm α)) hh
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, hP, hQ] at h3
      simpa using h3
    have hd := hdiff _ _ _ _ hE
    have ha : (r : ℤ) ∣ ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) :=
      prime_dvd_exponent_of_comm hr hs hrs hg hw hcomm hgx hd
    have hb : (s : ℤ) ∣ ((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ) := by
      have hd' : (w ^ (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ)) * g ^ (((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ)) : Perm α) x = x := by
        rw [← (hc.zpow_zpow (((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ)) (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ))).eq]; exact hd
      exact prime_dvd_exponent_of_comm hs hr hrs.symm hw hg hcomm.symm hwx hd'
    have hi : ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd ha ?_
      have := i.2; have := i'.2
      rw [abs_lt]; constructor <;> omega
    have hj : ((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hb ?_
      have := j.2; have := j'.2
      rw [abs_lt]; constructor <;> omega
    exact Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext (by dsimp only; omega))
  have := Fintype.card_le_of_injective F hF
  simpa using this

end Supports

section Main

theorem alt_comb {n : ℕ} (hn : n ≤ 11) {r : ℕ} (hr : r.Prime) (hr2 : Odd r)
    (V₁ Z₁ : Subgroup (Perm (Fin n)))
    (hVcomm : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a) (hVpow : ∀ a ∈ V₁, a ^ r = 1)
    (hVcard : Nat.card ↥V₁ = r ^ 2)
    (hZne : Z₁ ≠ ⊥) (hZodd : Odd (Nat.card ↥Z₁)) (hZcop : Nat.Coprime (Nat.card ↥Z₁) r)
    (hcomm : ∀ v ∈ V₁, ∀ w ∈ Z₁, v * w = w * v)
    (hP3 : ∀ v ∈ V₁, v ≠ 1 → ∀ σ τ : Perm (Fin n), Perm.sign σ = 1 → Perm.sign τ = 1 →
      σ * v = v * σ → τ * v = v * τ → σ * τ * σ⁻¹ * τ⁻¹ ∈ normalizer (Z₁ : Set (Perm (Fin n)))) :
    False := by
  classical
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    rcases hr2 with ⟨k, hk⟩
    omega
  obtain ⟨s, hs, hsZ⟩ : ∃ s : ℕ, s.Prime ∧ s ∣ Nat.card ↥Z₁ := by
    have h1 : Nat.card ↥Z₁ ≠ 1 := fun h => hZne (Subgroup.card_eq_one.mp h)
    exact ⟨(Nat.card ↥Z₁).minFac, Nat.minFac_prime h1, Nat.minFac_dvd _⟩
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card' s hsZ
  set w : Perm (Fin n) := (w₀ : Perm (Fin n)) with hwdef
  have hwZ : w ∈ Z₁ := w₀.2
  have hw : orderOf w = s := by rw [hwdef, Subgroup.orderOf_coe]; exact hw₀
  have hsodd : Odd s := Odd.of_dvd_nat hZodd hsZ
  have hs3 : 3 ≤ s := by
    have := hs.two_le
    rcases hsodd with ⟨k, hk⟩
    omega
  have hsr : s ≠ r := by
    intro h
    subst h
    have : s ∣ Nat.gcd (Nat.card ↥Z₁) s := Nat.dvd_gcd hsZ dvd_rfl
    rw [hZcop] at this
    exact hs.one_lt.ne' (Nat.dvd_one.mp this)
  have hrs : n < r * s := by
    by_cases h3 : r = 3
    · have : 5 ≤ s := by
        have h4 : s ≠ 3 := fun h => hsr (h.trans h3.symm)
        have : s ≠ 4 := by rintro rfl; exact absurd hs (by decide)
        omega
      rw [h3]; omega
    · have : 4 ≤ r := by omega
      nlinarith
  have hVord : ∀ v ∈ V₁, v ≠ 1 → orderOf v = r := by
    intro v hv hv1
    have : Fact r.Prime := ⟨hr⟩
    exact orderOf_eq_prime (hVpow v hv) hv1
  have hdisj : ∀ v ∈ V₁, v ≠ 1 → ∀ x, v x ≠ x → w x = x := by
    intro v hv hv1 x hvx
    by_contra hwx
    have := mul_le_card_of_commuting hr hs hsr.symm (hVord v hv hv1) hw (hcomm v hv w hwZ) hvx hwx
    rw [Fintype.card_fin] at this
    omega
  let M : Finset (Fin n) := Finset.univ.filter (fun x => ∃ v ∈ V₁, v x ≠ x)
  have hM : ∀ x, x ∈ M ↔ ∃ v ∈ V₁, v x ≠ x := fun x => by simp [M]
  have hMw : ∀ x ∈ M, w x = x := by
    intro x hx
    obtain ⟨v, hv, hvx⟩ := (hM x).1 hx
    exact hdisj v hv (fun h => hvx (by rw [h]; rfl)) x hvx
  have hinv : ∀ v ∈ V₁, ∀ x, x ∈ M ↔ v x ∈ M := by
    have key : ∀ v ∈ V₁, ∀ x, x ∈ M → v x ∈ M := by
      intro v hv x hx
      obtain ⟨u, hu, hux⟩ := (hM x).1 hx
      refine (hM (v x)).2 ⟨u, hu, ?_⟩
      intro h
      apply hux
      have h1 : u (v x) = v (u x) := by
        have := congrArg (fun f : Perm (Fin n) => f x) (hVcomm u hu v hv)
        simpa using this
      rw [h1] at h
      exact v.injective h
    intro v hv x
    refine ⟨key v hv x, fun h => ?_⟩
    have := key v⁻¹ (V₁.inv_mem hv) (v x) h
    simpa using this
  let ψ : ↥V₁ →* Perm ↥M :=
    { toFun := fun v => (v : Perm (Fin n)).subtypePerm (fun x => (hinv v v.2 x).symm)
      map_one' := by ext x; rfl
      map_mul' := fun a b => by ext x; rfl }
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ M
    · have := congrArg (fun f : Perm ↥M => (f ⟨x, hx⟩ : Fin n)) hv
      simpa [ψ] using this
    · have hx' : ∀ u ∈ V₁, u x = x := by
        intro u hu
        by_contra h
        exact hx ((hM x).2 ⟨u, hu, h⟩)
      have := hx' v v.2
      simpa using this
  have hdvd : r ^ 2 ∣ (M.card).factorial := by
    have h1 := card_dvd_of_injective ψ hψ
    rw [hVcard, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe] at h1
    exact h1
  have hsupp : s ≤ w.support.card := card_support_ge_of_prime_orderOf hs hw
  have hcardle : M.card + w.support.card ≤ n := by
    have hdisjF : Disjoint M w.support := by
      rw [Finset.disjoint_left]
      intro x hxM hxw
      exact (Equiv.Perm.mem_support.1 hxw) (hMw x hxM)
    have := Finset.card_le_univ (M ∪ w.support)
    rw [Finset.card_union_of_disjoint hdisjF, Fintype.card_fin] at this
    exact this
  have hm8 : M.card ≤ 8 := by omega
  have hr3' : r = 3 ∧ 6 ≤ M.card := by
    have hrle : r ≤ M.card := by
      have h1 : r ∣ (M.card).factorial := (dvd_pow_self r two_ne_zero).trans hdvd
      exact (Nat.Prime.dvd_factorial hr).1 h1
    have hr8 : r ≤ 8 := hrle.trans hm8
    generalize M.card = m at *
    interval_cases m <;> interval_cases r <;> first | omega | exact absurd hr (by decide) | (exfalso; revert hdvd; decide)
  obtain ⟨hr3e, hm6⟩ := hr3'
  subst hr3e
  have hs5 : s = 5 := by
    have h4 : s ≠ 3 := hsr
    have h5 : s ≠ 4 := by rintro rfl; exact absurd hs (by decide)
    omega
  subst hs5
  have hMcard : M.card = 6 := by omega
  have hsw : w.support.card = 5 := by omega
  obtain ⟨v₀, hv₀, hv₀1, x₀, hx₀M, hv₀x₀⟩ : ∃ v ∈ V₁, v ≠ 1 ∧ ∃ x ∈ M, v x = x := by
    by_contra hcon
    push Not at hcon
    have hMne : M.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨x₁, hx₁⟩ := hMne
    let f : ↥V₁ → ↥M := fun v => ⟨(v : Perm (Fin n)) x₁, (hinv v v.2 x₁).1 hx₁⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (a : Perm (Fin n)) x₁ = (b : Perm (Fin n)) x₁ := congrArg Subtype.val hab
      have h2 : ((a : Perm (Fin n))⁻¹ * (b : Perm (Fin n))) x₁ = x₁ := by
        rw [Equiv.Perm.mul_apply, ← h1]; simp
      have h3 : (a : Perm (Fin n))⁻¹ * (b : Perm (Fin n)) = 1 := by
        by_contra hne
        exact hcon _ (V₁.mul_mem (V₁.inv_mem a.2) b.2) hne x₁ hx₁ h2
      apply Subtype.ext
      exact inv_mul_eq_one.mp h3
    have := Nat.card_le_card_of_injective f hf
    rw [hVcard, Nat.card_eq_fintype_card (α := ↥M), Fintype.card_coe, hMcard] at this
    omega
  have hfix : ∃ x₁ x₂ : Fin n, x₁ ∈ M ∧ x₂ ∈ M ∧ x₁ ≠ x₂ ∧ v₀ x₁ = x₁ ∧ v₀ x₂ = x₂ := by
    let σ₀ : Perm ↥M := ψ ⟨v₀, hv₀⟩
    have h3 : σ₀ ^ 3 ^ 1 = 1 := by
      have : (⟨v₀, hv₀⟩ : ↥V₁) ^ 3 = 1 := Subtype.ext (hVpow v₀ hv₀)
      rw [pow_one, ← map_pow, this, map_one]
    have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) h3
    rw [Fintype.card_coe, hMcard] at hmod
    have hx₀ : (⟨x₀, hx₀M⟩ : ↥M) ∈ σ₀.supportᶜ := by
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      apply Subtype.ext
      simpa [σ₀, ψ] using hv₀x₀
    have hk1 : 1 ≤ σ₀.supportᶜ.card := Finset.card_pos.2 ⟨_, hx₀⟩
    have hk3 : 3 ≤ σ₀.supportᶜ.card := by
      have : σ₀.supportᶜ.card % 3 = 6 % 3 := hmod
      omega
    obtain ⟨p₁, hp₁, p₂, hp₂, hp12⟩ := Finset.one_lt_card.1 (show 1 < σ₀.supportᶜ.card by omega)
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hp₁ hp₂
    refine ⟨p₁, p₂, p₁.2, p₂.2, fun h => hp12 (Subtype.ext h), ?_, ?_⟩
    · simpa [σ₀, ψ] using congrArg Subtype.val hp₁
    · simpa [σ₀, ψ] using congrArg Subtype.val hp₂
  obtain ⟨x₁, x₂, hx₁M, hx₂M, hx12, hv₀x₁, hv₀x₂⟩ := hfix
  obtain ⟨f, d, e, hfw, hdw, hew, hfd, hfe, hde⟩ := Finset.two_lt_card_iff.1 (show 2 < w.support.card by omega)
  have hwf : w f ≠ f := Equiv.Perm.mem_support.1 hfw
  have hnotw : ∀ x ∈ M, x ∉ w.support := fun x hx hxw => (Equiv.Perm.mem_support.1 hxw) (hMw x hx)
  have hv₀fix : ∀ y ∈ w.support, v₀ y = y := by
    intro y hy
    by_contra h
    exact (Equiv.Perm.mem_support.1 hy) (hdisj v₀ hv₀ hv₀1 y h)
  have hf1 : f ≠ x₁ := fun h => hnotw x₁ hx₁M (h ▸ hfw)
  have hf2 : f ≠ x₂ := fun h => hnotw x₂ hx₂M (h ▸ hfw)
  have hd1 : d ≠ x₁ := fun h => hnotw x₁ hx₁M (h ▸ hdw)
  have hd2 : d ≠ x₂ := fun h => hnotw x₂ hx₂M (h ▸ hdw)
  have he1 : e ≠ x₁ := fun h => hnotw x₁ hx₁M (h ▸ hew)
  have he2 : e ≠ x₂ := fun h => hnotw x₂ hx₂M (h ▸ hew)
  have hswap : ∀ a b : Fin n, v₀ a = a → v₀ b = b → Commute (Equiv.swap a b) v₀ := by
    intro a b ha hb
    have h := Equiv.swap_apply_apply v₀ a b
    rw [ha, hb] at h
    exact (mul_inv_eq_iff_eq_mul.1 h.symm).symm
  set σ : Perm (Fin n) := Equiv.swap f x₁ * Equiv.swap d e with hσ
  set τ : Perm (Fin n) := Equiv.swap f x₂ * Equiv.swap d e with hτ
  have hσs : Perm.sign σ = 1 := by
    rw [hσ, Perm.sign_mul, Perm.sign_swap hf1, Perm.sign_swap hde]; decide
  have hτs : Perm.sign τ = 1 := by
    rw [hτ, Perm.sign_mul, Perm.sign_swap hf2, Perm.sign_swap hde]; decide
  have hσc : σ * v₀ = v₀ * σ :=
    (Commute.mul_left (hswap f x₁ (hv₀fix f hfw) hv₀x₁) (hswap d e (hv₀fix d hdw) (hv₀fix e hew))).eq
  have hτc : τ * v₀ = v₀ * τ :=
    (Commute.mul_left (hswap f x₂ (hv₀fix f hfw) hv₀x₂) (hswap d e (hv₀fix d hdw) (hv₀fix e hew))).eq
  have hcn := hP3 v₀ hv₀ hv₀1 σ τ hσs hτs hσc hτc
  set c : Perm (Fin n) := σ * τ * σ⁻¹ * τ⁻¹ with hcdef
  have hcf : c f = x₁ := by
    simp only [hcdef, hσ, hτ, Equiv.Perm.mul_apply, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_left]
    simp [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_right, Equiv.swap_apply_left, hd2.symm, he2.symm,
      hf2.symm, hx12.symm, hfd, hfe]
  have hu'Z : c * w * c⁻¹ ∈ Z₁ := (Subgroup.mem_normalizer_iff.1 hcn w).1 hwZ
  have hu'ord : orderOf (c * w * c⁻¹) = 5 := by
    have := (MulAut.conj c).orderOf_eq w
    rw [MulAut.conj_apply] at this
    rw [this, hw]
  have hu'x₁ : (c * w * c⁻¹) x₁ ≠ x₁ := by
    intro h
    have h1 : c⁻¹ x₁ = f := by rw [← hcf]; simp
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1] at h
    apply hwf
    apply c.injective
    rw [h, hcf]
  obtain ⟨v', hv', hv'x₁⟩ := (hM x₁).1 hx₁M
  have hv'1 : v' ≠ 1 := fun h => hv'x₁ (by rw [h]; rfl)
  have hbound := mul_le_card_of_commuting hr hs (by decide : 3 ≠ 5) (hVord v' hv' hv'1) hu'ord
    (hcomm v' hv' _ hu'Z) hv'x₁ hu'x₁
  rw [Fintype.card_fin] at hbound
  omega

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
