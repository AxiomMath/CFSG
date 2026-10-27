module

public import CFSG.CGT.PushingUpLit.BHS7.AltPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open Equiv Equiv.Perm CFSG.Quasithin CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.Quasithin.G6

variable {n : ℕ} {σ : Perm (Fin n)} {p₀ : Fin n}

theorem cent_le_normalizer_closure (h : IsPairing σ p₀) :
    Cent σ ≤ Subgroup.normalizer ((Subgroup.closure {t : Perm (Fin n) |
      ∃ x, x ≠ p₀ ∧ t = swap x (σ x)} : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
  set Y : Subgroup (Perm (Fin n)) := Subgroup.closure {t : Perm (Fin n) |
      ∃ x, x ≠ p₀ ∧ t = swap x (σ x)} with hY
  have hconj : ∀ ν ∈ Cent σ, ∀ y ∈ Y, ν * y * ν⁻¹ ∈ Y := by
    intro ν hν y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨x, hx, rfl⟩ := ht
      have h1 : ν * swap x (σ x) * ν⁻¹ = swap (ν x) (σ (ν x)) := by
        rw [← apply_sigma_of_mem_cent hν x]
        exact (swap_apply_apply ν x (σ x)).symm
      rw [h1]
      refine Subgroup.subset_closure ⟨ν x, fun e => hx ?_, rfl⟩
      apply ν.injective
      rw [e, apply_p₀_of_mem_cent h hν]
    | one => simp
    | mul a b _ _ ha hb =>
      have : ν * (a * b) * ν⁻¹ = (ν * a * ν⁻¹) * (ν * b * ν⁻¹) := by group
      rw [this]
      exact Y.mul_mem ha hb
    | inv a _ ha =>
      have : ν * a⁻¹ * ν⁻¹ = (ν * a * ν⁻¹)⁻¹ := by group
      rw [this]
      exact Y.inv_mem ha
  intro ν hν
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj ν hν y, fun hy => ?_⟩
  have := hconj ν⁻¹ ((Cent σ).inv_mem hν) _ hy
  simpa [mul_assoc] using this

theorem eq_sigma_of_three (h : IsPairing σ p₀) (hn : n = 3) {x y : Fin n} (hx : x ≠ p₀)
    (hy : y ≠ p₀) (hyx : y ≠ x) : y = σ x := by
  subst hn
  have key : ∀ x y z p : Fin 3, x ≠ p → y ≠ p → y ≠ x → z ≠ x → z ≠ p → y = z := by decide
  exact key x y (σ x) p₀ hx hy hyx (h.sigma_ne_self hx) (h.sigma_ne_p₀ hx)

theorem eq_top_of_stabilizer_le (hn : 2 ≤ n) {M : Subgroup (Perm (Fin n))}
    (hM : ∀ g : Perm (Fin n), g p₀ = p₀ → g ∈ M) {g₁ : Perm (Fin n)} (hg₁ : g₁ ∈ M)
    (hg₁p : g₁ p₀ ≠ p₀) : M = ⊤ := by
  have hnt : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hco : IsCoatom (MulAction.stabilizer (Perm (Fin n)) p₀) :=
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (Perm (Fin n)) p₀
  have hle : MulAction.stabilizer (Perm (Fin n)) p₀ ≤ M := fun g hg => hM g (by simpa using hg)
  have hlt : MulAction.stabilizer (Perm (Fin n)) p₀ < M :=
    lt_of_le_of_ne hle fun e => hg₁p (by
      have : g₁ ∈ MulAction.stabilizer (Perm (Fin n)) p₀ := e ▸ hg₁
      simpa using this)
  exact hco.2 M hlt

theorem apply_p₀_of_isPGroup (h : IsPairing σ p₀) (hn : Odd n) {P : Subgroup (Perm (Fin n))}
    (hP : IsPGroup 2 P) (hY : ∀ x, x ≠ p₀ → swap x (σ x) ∈ P) : ∀ s ∈ P, s p₀ = p₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints (Fin n)
  have hfix : (MulAction.fixedPoints ↥P (Fin n)).Nonempty := by
    by_contra hne
    have h0 : Nat.card (MulAction.fixedPoints ↥P (Fin n)) = 0 := by
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
    rw [h0, Nat.card_eq_fintype_card, Fintype.card_fin] at hmod
    have h2 := (Nat.modEq_zero_iff_dvd.mp hmod)
    obtain ⟨k, hk⟩ := hn
    omega
  obtain ⟨p₁, hp₁⟩ := hfix
  have hp₁eq : p₁ = p₀ := by
    by_contra hne
    have h1 := hp₁ ⟨swap p₁ (σ p₁), hY p₁ hne⟩
    have h2 : swap p₁ (σ p₁) p₁ = σ p₁ := swap_apply_left _ _
    have h3 : (⟨swap p₁ (σ p₁), hY p₁ hne⟩ : ↥P) • p₁ = swap p₁ (σ p₁) p₁ := rfl
    rw [h3, h2] at h1
    exact h.sigma_ne_self hne h1
  intro s hs
  have := hp₁ ⟨s, hs⟩
  rw [hp₁eq] at this
  exact this

theorem coreAct_swap_eq_of_vcoord_eq (u : ↥(coreMod n)) {x y : Fin n}
    (h : vcoord u x = vcoord u y) : coreAct n (swap x y) u = u := by
  refine vcoord_ext fun i => ?_
  rw [vcoord_coreAct, swap_inv]
  by_cases hix : i = x
  · subst hix
    rw [swap_apply_left]
    exact h.symm
  by_cases hiy : i = y
  · subst hiy
    rw [swap_apply_right]
    exact h
  rw [swap_apply_of_ne_of_ne hix hiy]

theorem isSylowTwoOf_map_top {H : Type*} [Group H] [Finite H] (Φ : H →* Perm (Fin n))
    (hΦ : Function.Surjective Φ) {P : Subgroup H} (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) :
    IsSylowTwoOf (P.map Φ) ⊤ := by
  refine ⟨le_top, hP.map Φ, fun hd => hodd ?_⟩
  have h1 : (P.map Φ).relIndex ⊤ = (P.map Φ).index := Subgroup.relIndex_top_right _
  have h2 : 2 ∣ (P.map Φ).index := by
    rw [← h1]
    exact hd
  exact dvd_trans h2 (Subgroup.index_map_dvd P hΦ)

theorem apply_p₀_of_normalizes_fix (hn : 4 ≤ n) {g : Perm (Fin n)}
    (hg : ∀ c ∈ alternatingGroup (Fin n), c p₀ = p₀ → (g⁻¹ * c * g) p₀ = p₀) : g p₀ = p₀ := by
  classical
  by_contra hne
  set q : Fin n := g p₀ with hq
  have hcard : ∀ t : Finset (Fin n), t.card < n → ∃ r, r ∉ t := fun t ht => by
    obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show t.card < (Finset.univ : Finset (Fin n)).card by simpa using ht)
    exact ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hcard {p₀, q} (by
    have := Finset.card_le_two (a := p₀) (b := q)
    omega)
  obtain ⟨s, hs⟩ := hcard {p₀, q, r} (by
    have : ({p₀, q, r} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr hs
  have hqr : q ≠ r := fun e => hr.2 e.symm
  have hrs : r ≠ s := fun e => hs.2.2 e.symm
  have hqs : q ≠ s := fun e => hs.2.1 e.symm
  have hc : swap q r * swap r s ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hqr, Perm.sign_swap hrs]
    decide
  have hcp : (swap q r * swap r s) p₀ = p₀ := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (fun e => hr.1 e.symm) (fun e => hs.1 e.symm),
      swap_apply_of_ne_of_ne (fun e => hne e.symm) (fun e => hr.1 e.symm)]
  have hcq : (swap q r * swap r s) q = r := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hqr hqs, swap_apply_left]
  have h1 := hg _ hc hcp
  have h2 : (swap q r * swap r s) q = q := by
    have := congrArg g h1
    simpa [Perm.mul_apply, hq] using this
  rw [hcq] at h2
  exact hr.2 h2

end CFSG.CGT.PushingUpLit.BHS7
