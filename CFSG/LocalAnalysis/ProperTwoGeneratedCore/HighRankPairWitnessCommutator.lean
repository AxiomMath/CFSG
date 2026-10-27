module

public import CFSG.GroupTheory.OddInversion
public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.OddInversion
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

theorem mem_normalizer_closure {S : Set G} {g : G}
    (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S)
    (hS' : ∀ s ∈ S, g⁻¹ * s * g ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have hmap : ∀ k : G, (∀ s ∈ S, k * s * k⁻¹ ∈ Subgroup.closure S) →
      ∀ x ∈ Subgroup.closure S, k * x * k⁻¹ ∈ Subgroup.closure S := by
    intro k hk x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact hk s hs
    | one => simp
    | mul x y _ _ hx hy =>
      have : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨hmap g hS x, fun hx => ?_⟩
  have h := hmap g⁻¹ (by simpa only [inv_inv] using hS') _ hx
  have heq : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [heq] at h


theorem closure_invertedSet_le (J : Subgroup G) (t : G) :
    Subgroup.closure (invertedSet J t) ≤ J :=
  (Subgroup.closure_le J).mpr fun _ hd => hd.1

theorem invertedSet_closure_invertedSet (J : Subgroup G) (t : G) :
    invertedSet (Subgroup.closure (invertedSet J t)) t = invertedSet J t := by
  ext d
  constructor
  · intro hd
    exact ⟨closure_invertedSet_le J t hd.1, hd.2⟩
  · intro hd
    exact ⟨Subgroup.subset_closure hd, hd.2⟩

theorem mem_normalizer_closure_invertedSet {J : Subgroup G} {t g : G}
    (hgJ : g ∈ Subgroup.normalizer (J : Set G)) (hgt : Commute g t) :
    g ∈ Subgroup.normalizer (Subgroup.closure (invertedSet J t) : Set G) := by
  have hconj : ∀ k : G, k ∈ Subgroup.normalizer (J : Set G) → Commute k t →
      ∀ d ∈ invertedSet J t, k * d * k⁻¹ ∈ invertedSet J t := by
    intro k hkJ hkt d hd
    refine ⟨conj_mem_of_mem_normalizer hkJ hd.1, ?_⟩
    calc t * (k * d * k⁻¹) * t⁻¹ = k * (t * d * t⁻¹) * k⁻¹ := by
          rw [show t * (k * d * k⁻¹) * t⁻¹ = (t * k) * d * (t * k)⁻¹ by group,
            ← hkt.eq]
          group
      _ = (k * d * k⁻¹)⁻¹ := by rw [hd.2]; group
  apply mem_normalizer_closure
  · exact fun d hd => Subgroup.subset_closure (hconj g hgJ hgt d hd)
  · intro d hd
    have := hconj g⁻¹ (Subgroup.inv_mem _ hgJ) hgt.inv_left d hd
    rw [inv_inv] at this
    exact Subgroup.subset_closure this

theorem flip_mem_normalizer_closure_invertedSet {J : Subgroup G} {t : G}
    (htJ : t ∈ Subgroup.normalizer (J : Set G)) :
    t ∈ Subgroup.normalizer (Subgroup.closure (invertedSet J t) : Set G) :=
  mem_normalizer_closure_invertedSet htJ (Commute.refl t)

theorem commutator_closure_invertedSet {J : Subgroup G} {t : G} (hJ : Odd (Nat.card J))
    (htJ : t ∈ Subgroup.normalizer (J : Set G)) :
    ⁅Subgroup.closure (invertedSet J t), Subgroup.zpowers t⁆ =
      Subgroup.closure (invertedSet J t) := by
  set A := Subgroup.closure (invertedSet J t)
  have htA : Subgroup.zpowers t ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr (flip_mem_normalizer_closure_invertedSet htJ)
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (htA hb) a⁻¹).mp (A.inv_mem ha))
  · rw [Subgroup.closure_le]
    intro d hd
    obtain ⟨e, he, rfl⟩ := exists_sq_eq_of_mem_invertedSet hJ hd
    have hcomm : ⁅e, t⁆ = e ^ 2 := by
      calc ⁅e, t⁆ = e * (t * e * t⁻¹)⁻¹ := by rw [commutatorElement_def]; group
        _ = e ^ 2 := by rw [he.2, inv_inv, pow_two]
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure he)
      (Subgroup.mem_zpowers t)

theorem relIndex_closure_invertedSet {J : Subgroup G} {t : G} (hJ : Odd (Nat.card J))
    (htJ : t ∈ Subgroup.normalizer (J : Set G)) (ht : orderOf t = 2) :
    (Subgroup.centralizer {t}).relIndex (Subgroup.closure (invertedSet J t)) =
      (Subgroup.centralizer {t}).relIndex J := by
  have hAJ := closure_invertedSet_le J t
  have hA : Odd (Nat.card (Subgroup.closure (invertedSet J t))) :=
    hJ.of_dvd_nat (Subgroup.card_dvd_of_le hAJ)
  have h1 := (odd_inversion_coset_count hA (flip_mem_normalizer_closure_invertedSet htJ)
    (notMem_of_odd_card hA ht) ht).2.2
  have h2 := (odd_inversion_coset_count hJ htJ (notMem_of_odd_card hJ ht) ht).2.2
  rw [← h1, ← h2, invertedSet_closure_invertedSet]

theorem cyclic_pgroup_conj_eq_or_inv [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup G}
    (hA : IsPGroup p A) (hcyc : IsCyclic A) {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hg2 : g * g = 1) :
    (∀ x ∈ A, g * x * g⁻¹ = x) ∨ (∀ x ∈ A, g * x * g⁻¹ = x⁻¹) := by
  obtain ⟨c, hc⟩ := hcyc.exists_generator
  have hgc : g * (c : G) * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgA c).mp c.2
  obtain ⟨k₀, hk₀⟩ : ∃ k : ℕ, c ^ k = ⟨g * c * g⁻¹, hgc⟩ :=
    (mem_powers_iff_mem_zpowers).mpr (hc ⟨g * c * g⁻¹, hgc⟩)
  set n := orderOf c with hn
  have hnpos : 0 < n := orderOf_pos c
  let k := k₀ + n
  have hk : c ^ k = ⟨g * c * g⁻¹, hgc⟩ := by
    rw [pow_add, pow_orderOf_eq_one, mul_one, hk₀]
  have hk1 : 1 ≤ k := by omega
  have hgcG : g * (c : G) * g⁻¹ = (c : G) ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hkk : c ^ (k * k) = c ^ 1 := by
    apply Subtype.ext
    have h1 : g * ((c : G) ^ k) * g⁻¹ = ((c : G) ^ k) ^ k := by
      rw [← conj_pow, hgcG]
    have h2 : g * (g * (c : G) * g⁻¹) * g⁻¹ = (c : G) := by
      calc g * (g * (c : G) * g⁻¹) * g⁻¹ = (g * g) * c * (g * g)⁻¹ := by group
        _ = c := by rw [hg2, one_mul, inv_one, mul_one]
    rw [hgcG] at h2
    rw [h1, ← pow_mul] at h2
    simpa using h2
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hA
  have hncard : n = p ^ e := by
    rw [hn, orderOf_eq_card_of_forall_mem_zpowers hc, he]
  have hmod : k * k ≡ 1 [MOD n] := (pow_eq_pow_iff_modEq).mp hkk
  have hdvd : p ^ e ∣ (k - 1) * (k + 1) := by
    have h := (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ k * k)).mp hmod.symm
    rw [← hncard]
    have hkk' : k * k - 1 = (k - 1) * (k + 1) := by
      have := Nat.mul_self_sub_mul_self_eq k 1
      rw [one_mul] at this
      rw [this, mul_comm]
    rwa [hkk'] at h
  have hpow : ∀ x ∈ A, ∀ m : ℕ, (c : G) ^ k = (c : G) ^ m →
      g * x * g⁻¹ = x ^ m := by
    intro x hx m hm
    obtain ⟨j, hj⟩ : ∃ j : ℕ, c ^ j = ⟨x, hx⟩ :=
      (mem_powers_iff_mem_zpowers).mpr (hc ⟨x, hx⟩)
    have hxj : x = (c : G) ^ j := by
      have := congrArg Subtype.val hj
      simpa using this.symm
    rw [hxj, ← conj_pow, hgcG, hm, ← pow_mul, ← pow_mul, mul_comm]
  by_cases hpk : p ∣ k + 1
  · right
    have hnot : ¬ p ∣ k - 1 := by
      intro hpk'
      have h2 : p ∣ (k + 1) - (k - 1) := Nat.dvd_sub hpk hpk'
      rw [show (k + 1) - (k - 1) = 2 by omega] at h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    have hcop : Nat.Coprime (p ^ e) (k - 1) :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnot)
    have hk1' : p ^ e ∣ k + 1 := hcop.dvd_of_dvd_mul_left hdvd
    have hck : (c : G) ^ (k + 1) = 1 := by
      have : c ^ (k + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [← hn, hncard]; exact hk1')
      simpa using congrArg Subtype.val this
    intro x hx
    obtain ⟨j, hj⟩ : ∃ j : ℕ, c ^ j = ⟨x, hx⟩ :=
      (mem_powers_iff_mem_zpowers).mpr (hc ⟨x, hx⟩)
    have hxj : x = (c : G) ^ j := by
      have := congrArg Subtype.val hj
      simpa using this.symm
    have hcinv : (c : G) ^ k = (c : G)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hck]
    rw [hxj, ← conj_pow, hgcG, hcinv, inv_pow]
  · left
    have hcop : Nat.Coprime (p ^ e) (k + 1) :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpk)
    have hk1' : p ^ e ∣ k - 1 := hcop.dvd_of_dvd_mul_right hdvd
    have hck : (c : G) ^ (k - 1) = 1 := by
      have : c ^ (k - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [← hn, hncard]; exact hk1')
      simpa using congrArg Subtype.val this
    intro x hx
    have hm : (c : G) ^ k = (c : G) ^ 1 := by
      rw [show k = (k - 1) + 1 by omega, pow_add, hck, one_mul]
    rw [hpow x hx 1 hm, pow_one]

theorem cyclic_pgroup_four_group_centralizes [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup G} (hA : IsPGroup p A) (hcyc : IsCyclic A) {u v : G}
    (hu : u ∈ Subgroup.normalizer (A : Set G)) (hv : v ∈ Subgroup.normalizer (A : Set G))
    (hu2 : u * u = 1) (hv2 : v * v = 1) :
    A ≤ Subgroup.centralizer ({u} : Set G) ∨ A ≤ Subgroup.centralizer ({v} : Set G) ∨
      A ≤ Subgroup.centralizer ({u * v} : Set G) := by
  have hcent : ∀ g : G, (∀ x ∈ A, g * x * g⁻¹ = x) → A ≤ Subgroup.centralizer ({g} : Set G) :=
    fun g hg x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (hg x hx)).symm
  rcases cyclic_pgroup_conj_eq_or_inv hp hp2 hA hcyc hu hu2 with hu' | hu'
  · exact Or.inl (hcent u hu')
  rcases cyclic_pgroup_conj_eq_or_inv hp hp2 hA hcyc hv hv2 with hv' | hv'
  · exact Or.inr (Or.inl (hcent v hv'))
  refine Or.inr (Or.inr (hcent (u * v) fun x hx => ?_))
  calc u * v * x * (u * v)⁻¹ = u * (v * x * v⁻¹) * u⁻¹ := by group
    _ = (u * x * u⁻¹)⁻¹ := by rw [hv' x hx]; group
    _ = x := by rw [hu' x hx, inv_inv]

end CFSG.ProperTwoGeneratedCore.HighRankPair
