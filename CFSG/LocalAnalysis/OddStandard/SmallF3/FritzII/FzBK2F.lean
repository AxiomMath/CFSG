module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU

private theorem iterA_lt' {f : Array ℕ} (hb : ∀ y < 64, f[y]! < 64) :
    ∀ n, ∀ x < 64, iterA f n x < 64 := by
  intro n
  induction n with
  | zero => intro x hx; exact hx
  | succ n ih =>
      intro x hx
      show f[iterA f n x]! < 64
      exact hb _ (ih x hx)

private theorem iterA_congr {f g : Array ℕ} (h : ∀ y < 64, f[y]! = g[y]!)
    (hb : ∀ y < 64, f[y]! < 64) :
    ∀ n, ∀ x < 64, iterA f n x = iterA g n x := by
  intro n
  induction n with
  | zero => intro x hx; rfl
  | succ n ih =>
      intro x hx
      have hlt : iterA f n x < 64 := iterA_lt' hb n x hx
      show f[iterA f n x]! = g[iterA g n x]!
      rw [h (iterA f n x) hlt, ih x hx]

private theorem iterA_succ (f : Array ℕ) (n x : ℕ) :
    iterA f (n + 1) x = f[iterA f n x]! := rfl

private theorem iterA_one (f : Array ℕ) (x : ℕ) : iterA f 1 x = f[x]! := rfl

private theorem iterA_two (f : Array ℕ) (x : ℕ) : iterA f 2 x = f[f[x]!]! := rfl

private theorem iterA_three (f : Array ℕ) (x : ℕ) :
    iterA f 3 x = f[f[f[x]!]!]! := rfl

private theorem iterA_four (f : Array ℕ) (x : ℕ) :
    iterA f 4 x = f[f[f[f[x]!]!]!]! := rfl

theorem fzb_faithful {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P) {q s : G}
    (hq : FzbNorm P q) (hs : FzbNorm P s) (hq4 : q ^ 4 = 1)
    (hs2 : ∃ j : ℕ, s ^ 2 = q ^ j) (hsq : s * q * s⁻¹ = q ∨ s * q * s⁻¹ = q⁻¹)
    {aq as : Array ℕ}
    (haq : ∀ x < 64, C.enc (q * C.dec x * q⁻¹) = aq[x]!)
    (has : ∀ x < 64, C.enc (s * C.dec x * s⁻¹) = as[x]!)
    (hq4' : allBelow (fun x => aq[aq[aq[aq[x]!]!]!]! == x) 64 = true)
    (hq2' : anyBelow (fun x => aq[aq[x]!]! != x) 64 = true)
    (hs2' : allBelow (fun x => as[as[x]!]! == x) 64 = true)
    (hsq' : allBelow (fun x => as[aq[x]!]! == aq[aq[aq[as[x]!]!]!]!) 64 = true) :
    s ^ 2 = 1 ∧ s * q * s⁻¹ = q⁻¹ := by
  have hq4p : ∀ x < 64, aq[aq[aq[aq[x]!]!]!]! = x :=
    fun x hx => beq_iff_eq.mp ((fzb_allBelow_iff _ 64).mp hq4' x hx)
  have hq2p : ∃ x < 64, aq[aq[x]!]! ≠ x := by
    obtain ⟨x, hx, hb⟩ := (fzb_anyBelow_iff _ 64).mp hq2'
    exact ⟨x, hx, bne_iff_ne.mp hb⟩
  have hs2p : ∀ x < 64, as[as[x]!]! = x :=
    fun x hx => beq_iff_eq.mp ((fzb_allBelow_iff _ 64).mp hs2' x hx)
  have hsqp : ∀ x < 64, as[aq[x]!]! = aq[aq[aq[as[x]!]!]!]! :=
    fun x hx => beq_iff_eq.mp ((fzb_allBelow_iff _ 64).mp hsq' x hx)
  have haq_lt : ∀ x < 64, aq[x]! < 64 := by
    intro x hx
    rw [← haq x hx]
    exact C.enc_lt _ (hq _ (C.dec_mem x hx))
  have has_lt : ∀ x < 64, as[x]! < 64 := by
    intro x hx
    rw [← has x hx]
    exact C.enc_lt _ (hs _ (C.dec_mem x hx))
  have htabq : ∀ x < 64, (C.tab q)[x]! = aq[x]! := by
    intro x hx
    rw [C.tab_getElem q hx]
    exact haq x hx
  have htabs : ∀ x < 64, (C.tab s)[x]! = as[x]! := by
    intro x hx
    rw [C.tab_getElem s hx]
    exact has x hx
  have hbq : ∀ y < 64, (C.tab q)[y]! < 64 := fun y hy => C.tab_lt hq hy
  obtain ⟨j, hj⟩ := hs2
  have hiter_tab : ∀ x < 64, iterA (C.tab q) j x = x := by
    intro x hx
    have h1 : (C.tab (s ^ 2))[x]! = as[as[x]!]! := by
      rw [pow_two, C.tab_mul hs hs hx, htabs x hx, htabs _ (has_lt x hx)]
    have h2 : (C.tab (q ^ j))[x]! = iterA (C.tab q) j x := C.tab_pow hq j hx
    have h3 : (C.tab (q ^ j))[x]! = (C.tab (s ^ 2))[x]! := by rw [hj]
    rw [← h2, h3, h1, hs2p x hx]
  have hiter_aq : ∀ x < 64, iterA aq j x = x := by
    intro x hx
    rw [← iterA_congr htabq hbq j x hx]
    exact hiter_tab x hx
  have hiter_mod : ∀ x < 64, iterA aq (j % 4) x = x := by
    intro x hx
    have heq : q ^ j = q ^ (j % 4) := pow_eq_pow_mod j hq4
    rw [← iterA_congr htabq hbq (j % 4) x hx,
        ← C.tab_pow hq (j % 4) hx, ← heq, C.tab_pow hq j hx,
        iterA_congr htabq hbq j x hx]
    exact hiter_aq x hx
  have hmod : j % 4 = 0 := by
    by_contra hne0
    have hlt : j % 4 < 4 := Nat.mod_lt j (by norm_num)
    have hcases : j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    obtain ⟨x, hx, hne⟩ := hq2p
    rcases hcases with h1 | h2 | h3
    · have hx1 : aq[x]! = x := by
        have h := hiter_mod x hx
        rw [h1, iterA_one] at h
        exact h
      exact hne (by rw [hx1, hx1])
    · have hx2 : aq[aq[x]!]! = x := by
        have h := hiter_mod x hx
        rw [h2, iterA_two] at h
        exact h
      exact hne hx2
    · have h3i : iterA aq 3 x = x := by
        have h := hiter_mod x hx
        rwa [h3] at h
      have h4i : iterA aq 4 x = x := by
        rw [iterA_four]
        exact hq4p x hx
      have hstep : iterA aq 4 x = aq[iterA aq 3 x]! := by
        rw [show (4 : ℕ) = 3 + 1 from rfl, iterA_succ]
      have hx1 : aq[x]! = x := by
        rw [hstep, h3i] at h4i
        exact h4i
      exact hne (by rw [hx1, hx1])
  have hs2_eq : s ^ 2 = 1 := by
    rw [hj, pow_eq_pow_mod j hq4, hmod, pow_zero]
  refine ⟨hs2_eq, ?_⟩
  rcases hsq with hqconj | hinv
  · exfalso
    have hcomm : s * q = q * s := by
      calc s * q = (s * q * s⁻¹) * s := by group
        _ = q * s := by rw [hqconj]
    have hcomm_tab : ∀ x < 64, as[aq[x]!]! = aq[as[x]!]! := by
      intro x hx
      have h1 : (C.tab (s * q))[x]! = as[aq[x]!]! := by
        rw [C.tab_mul hs hq hx, htabq x hx, htabs _ (haq_lt x hx)]
      have h2 : (C.tab (q * s))[x]! = aq[as[x]!]! := by
        rw [C.tab_mul hq hs hx, htabs x hx, htabq _ (has_lt x hx)]
      have h3 : (C.tab (s * q))[x]! = (C.tab (q * s))[x]! := by rw [hcomm]
      rw [← h1, h3, h2]
    have hfix : ∀ z < 64, aq[aq[z]!]! = z := by
      intro z hz
      have hxz : as[as[z]!]! = z := hs2p z hz
      have hxlt : as[z]! < 64 := has_lt z hz
      have hz1 : aq[z]! = aq[aq[aq[z]!]!]! := by
        have hA := hcomm_tab (as[z]!) hxlt
        have hB := hsqp (as[z]!) hxlt
        rw [hxz] at hA hB
        exact hA.symm.trans hB
      have h2 := congrArg (fun w => aq[w]!) hz1
      exact h2.trans (hq4p z hz)
    obtain ⟨x, hx, hne⟩ := hq2p
    exact hne (hfix x hx)
  · exact hinv

end CFSG.OddStandard.SmallF3.FritzII
