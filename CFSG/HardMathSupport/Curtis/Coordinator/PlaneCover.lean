module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchIb

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.Plane

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

theorem mem_of_mul_two_elt {H : Type*} [Group H] (N : Subgroup H) [N.Normal] {p k m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {j r t : H} (hr : r ∈ N) (hjrt : j = r * t) (hj : j ^ p ^ k = 1)
    (ht : t ^ 2 ^ m = 1) : j ∈ N := by
  have h0 : QuotientGroup.mk' N r = 1 := (QuotientGroup.eq_one_iff (N := N) r).mpr hr
  have h1 : QuotientGroup.mk' N j = QuotientGroup.mk' N t := by
    rw [hjrt, map_mul, h0, one_mul]
  have h2 : (QuotientGroup.mk' N j) ^ p ^ k = 1 := by rw [← map_pow, hj, map_one]
  have h3 : (QuotientGroup.mk' N j) ^ 2 ^ m = 1 := by
    rw [h1, ← map_pow, ht, map_one]
  have hcop : Nat.Coprime (p ^ k) (2 ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have := pow_gcd_eq_one.mpr ⟨h2, h3⟩
  rw [hcop.gcd_eq_one, pow_one] at this
  exact (QuotientGroup.eq_one_iff j).mp this

theorem exists_perfect_cover {Y : Type*} [Group Y] [Finite Y] (J : Subgroup Y) {X : Type*}
    [Group X] (ψ : ↥J →* X) (hψ : Function.Surjective ψ)
    (hker : ∀ t, ψ t = 1 → ∃ m : ℕ, t ^ 2 ^ m = 1) (B : Subgroup X) (hB : Group.IsPerfect B)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hX : ∀ x : X, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ B) :
    ∃ R : Subgroup Y, R ≤ J ∧ ⁅R, R⁆ = R ∧
      ∀ x ∈ J, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ R := by
  set H : Subgroup ↥J := Subgroup.comap ψ B with hH
  set R₀ : Subgroup ↥J := perfectResidualOf H with hR₀
  have hR₀perf : Group.IsPerfect R₀ := finite_perfectResidualOf_isPerfect H
  have hmap : R₀.map ψ = B := finite_canonical_perfect_preimage_image_eq ψ hψ B hB
  refine ⟨R₀.map J.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hR₀perf]
  · intro x hx ⟨k, hk⟩
    set j : ↥J := ⟨x, hx⟩ with hj
    have hjk : j ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
    have hψj : ψ j ∈ B := hX _ ⟨k, by rw [← map_pow, hjk, map_one]⟩
    have hjH : j ∈ H := hψj
    obtain ⟨r, hr, hrj⟩ : ∃ r ∈ R₀, ψ r = ψ j := by
      have : ψ j ∈ R₀.map ψ := hmap ▸ hψj
      obtain ⟨r, hr, h⟩ := this
      exact ⟨r, hr, h⟩
    obtain ⟨m, hm⟩ := hker (r⁻¹ * j) (by rw [map_mul, map_inv, hrj, inv_mul_cancel])
    obtain ⟨rH, hrH, hrHr⟩ : ∃ rH ∈ perfectResidual ↥H, (rH : ↥J) = r := by
      obtain ⟨rH, hrH, h⟩ := hr
      exact ⟨rH, hrH, h⟩
    have : (perfectResidual ↥H).Characteristic := perfectResidual_characteristic (G := ↥H)
    have : (perfectResidual ↥H).Normal := inferInstance
    have hjR : (⟨j, hjH⟩ : ↥H) ∈ perfectResidual ↥H := by
      refine mem_of_mul_two_elt (perfectResidual ↥H) hp hp2 (r := rH) (t := rH⁻¹ * ⟨j, hjH⟩)
        hrH (by group) (Subtype.ext hjk) (m := m) (Subtype.ext ?_)
      simpa [hrHr] using hm
    refine ⟨j, ⟨⟨j, hjH⟩, hjR, rfl⟩, rfl⟩

theorem false_of_plane_of_cover {Y : Type*} [Group Y] {p : ℕ} (hp : p.Prime) {J : Subgroup Y}
    (hcyc : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ∀ Q : Subgroup Y, Q ≤ V → IsPGroup p Q →
      IsCyclic Q)
    (hcov : ∃ R : Subgroup Y, R ≤ J ∧ ⁅R, R⁆ = R ∧
      ∀ x ∈ J, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ R)
    {E : Subgroup Y} (hEJ : E ≤ J) (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    False := by
  obtain ⟨R, hRJ, hRp, hRx⟩ := hcov
  have hER : E ≤ R := fun x hx => hRx x (hEJ hx) ⟨1, by simpa using hEel.2 x hx⟩
  have : Fact p.Prime := ⟨hp⟩
  exact absurd (hcyc R hRJ hRp E hER (IsPGroup.of_card (n := 2) hEc))
    (ToralCensus.not_isCyclic_of_elemAbelian_pow hp (by norm_num) hEel hEc)

theorem false_of_plane_of_card {Y : Type*} [Group Y] {p : ℕ} {J : Subgroup Y}
    (h : ¬ p ^ 2 ∣ Nat.card J) {E : Subgroup Y} (hEJ : E ≤ J) (hEc : Nat.card E = p ^ 2) :
    False :=
  h (hEc ▸ Subgroup.card_dvd_of_le hEJ)

section Surj

variable {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y} {X : Type*} [Group X]

omit [Finite Y] in
theorem isPGroup_two_ker (ψ : ↥J →* X) (hker : ∀ t, ψ t = 1 → ∃ m : ℕ, t ^ 2 ^ m = 1) :
    IsPGroup 2 ψ.ker := fun t => by
  obtain ⟨m, hm⟩ := hker t t.2
  exact ⟨m, Subtype.ext hm⟩

theorem card_eq_two_pow_mul (ψ : ↥J →* X) (hψ : Function.Surjective ψ)
    (hker : ∀ t, ψ t = 1 → ∃ m : ℕ, t ^ 2 ^ m = 1) :
    ∃ a : ℕ, Nat.card J = 2 ^ a * Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (isPGroup_two_ker ψ hker).exists_card_eq
  refine ⟨a, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, ha, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]

omit [Finite Y] in
theorem eq_one_of_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ψ : ↥J →* X)
    (hψ : Function.Surjective ψ) (hker : ∀ t, ψ t = 1 → ∃ m : ℕ, t ^ 2 ^ m = 1)
    (hX : ∀ z : X, (∀ w, w * z = z * w) → z ^ p = 1 → z = 1) (ζ : ↥J)
    (hζ : ∀ w : ↥J, w * ζ = ζ * w) (hζp : ζ ^ p = 1) : ζ = 1 := by
  have h1 : ψ ζ = 1 := by
    refine hX _ (fun w => ?_) (by rw [← map_pow, hζp, map_one])
    obtain ⟨w', rfl⟩ := hψ w
    rw [← map_mul, ← map_mul, hζ w']
  obtain ⟨m, hm⟩ := hker ζ h1
  have hcop : Nat.Coprime p (2 ^ m) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have := pow_gcd_eq_one.mpr ⟨hζp, hm⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

end Surj

theorem perm_central_eq_one {n : ℕ} (hn : 3 ≤ n) (z : Equiv.Perm (Fin n))
    (hz : ∀ w : Equiv.Perm (Fin n), w * z = z * w) : z = 1 := by
  refine Equiv.ext fun i => ?_
  by_contra hne
  have hzi : z i ≠ i := fun h => hne (by simpa using h)
  obtain ⟨k, hki, hkz⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ z i := by
    by_contra hall
    push Not at hall
    have : Finset.univ ⊆ ({i, z i} : Finset (Fin n)) := fun k _ => by
      by_cases hk : k = i
      · simp [hk]
      · simp [hall k hk]
    have h2 := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have := Finset.card_le_two (a := i) (b := z i)
    omega
  have h1 := congrArg (fun f : Equiv.Perm (Fin n) => f i) (hz (Equiv.swap i k))
  simp only [Equiv.Perm.mul_apply] at h1
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hzi hkz.symm] at h1
  exact hki (z.injective h1).symm

theorem perm_mem_alternatingGroup_of_odd {n p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ^ p ^ k = 1) : σ ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h1 : (Equiv.Perm.sign σ) ^ p ^ k = 1 := by rw [← map_pow, hσ, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact h
  · exfalso
    rw [h, Odd.neg_one_pow ((hp.odd_of_ne_two hp2).pow)] at h1
    exact absurd h1 (by decide)

end CFSG.HardMathSupport.Curtis.Coordinator.Plane
