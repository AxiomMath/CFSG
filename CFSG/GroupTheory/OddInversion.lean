module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

open scoped Pointwise

namespace CFSG.OddInversion

variable {G : Type*} [Group G]

@[expose] def invertedSet (D : Subgroup G) (t : G) : Set G :=
  {d | d ∈ D ∧ t * d * t⁻¹ = d⁻¹}

theorem mem_invertedSet {D : Subgroup G} {t d : G} :
    d ∈ invertedSet D t ↔ d ∈ D ∧ t * d * t⁻¹ = d⁻¹ :=
  Iff.rfl

theorem inv_eq_self_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : t⁻¹ = t := by
  rw [inv_eq_iff_mul_eq_one, ← sq, ← ht, pow_orderOf_eq_one]

theorem conj_conj_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) (x : G) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
    _ = x := by rw [htt, inv_one, one_mul, mul_one]

theorem mem_invertedSet_iff_of_orderOf_eq_two {D : Subgroup G} {t d : G} (ht : orderOf t = 2) :
    d ∈ invertedSet D t ↔ d ∈ D ∧ t⁻¹ * d * t = d⁻¹ := by
  rw [mem_invertedSet, inv_eq_self_of_orderOf_eq_two ht]

theorem invertedSet_pow {D : Subgroup G} {t d : G} (hd : d ∈ invertedSet D t) (k : ℕ) :
    d ^ k ∈ invertedSet D t :=
  ⟨D.pow_mem hd.1 k, by rw [← conj_pow, hd.2, inv_pow]⟩

theorem invertedSet_inv {D : Subgroup G} {t d : G} (hd : d ∈ invertedSet D t) :
    d⁻¹ ∈ invertedSet D t :=
  ⟨D.inv_mem hd.1, by rw [← conj_inv, hd.2]⟩

theorem invertedSet_mono {D E : Subgroup G} (h : D ≤ E) {t : G} :
    invertedSet D t ⊆ invertedSet E t :=
  fun _ hd => ⟨h hd.1, hd.2⟩

theorem invertedSet_inf {D E : Subgroup G} {t : G} :
    invertedSet (D ⊓ E) t = (D : Set G) ∩ invertedSet E t := by
  ext d
  simp only [mem_invertedSet, Subgroup.mem_inf, Set.mem_inter_iff, SetLike.mem_coe, and_assoc]

theorem finite_of_odd_card {D : Subgroup G} (hD : Odd (Nat.card D)) : Finite D :=
  Nat.finite_of_card_ne_zero (fun h => by rw [h] at hD; exact Nat.not_odd_zero hD)

theorem pow_two_mul_eq_self {D : Subgroup G} (hD : Odd (Nat.card D)) {x : G} (hx : x ∈ D) :
    (x ^ ((Nat.card D + 1) / 2)) ^ 2 = x := by
  have : Finite D := finite_of_odd_card hD
  obtain ⟨k, hk⟩ := hD
  have hcard : x ^ Nat.card D = 1 := by
    have h := pow_card_eq_one' (G := D) (x := ⟨x, hx⟩)
    rw [Subtype.ext_iff, SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    exact h
  rw [← pow_mul, hk, show (2 * k + 1 + 1) / 2 * 2 = 2 * k + 1 + 1 by omega, pow_succ, ← hk,
    hcard, one_mul]

theorem sq_injOn {D : Subgroup G} (hD : Odd (Nat.card D)) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (h : x ^ 2 = y ^ 2) : x = y := by
  rw [← pow_two_mul_eq_self hD hx, ← pow_two_mul_eq_self hD hy, ← pow_mul, ← pow_mul, mul_comm,
    pow_mul, h, ← pow_mul, mul_comm, pow_mul]

theorem exists_sq_eq_of_mem_invertedSet {D : Subgroup G} (hD : Odd (Nat.card D)) {t j : G}
    (hj : j ∈ invertedSet D t) : ∃ d ∈ invertedSet D t, d ^ 2 = j :=
  ⟨_, invertedSet_pow hj _, pow_two_mul_eq_self hD hj.1⟩

theorem conj_mem_of_mem_normalizer {D : Subgroup G} {t d : G}
    (htN : t ∈ Subgroup.normalizer (D : Set G)) (hd : d ∈ D) : t * d * t⁻¹ ∈ D :=
  (Subgroup.mem_normalizer_iff.mp htN d).mp hd

section Coset

variable {D : Subgroup G} {t : G}

theorem orderOf_mul_eq_two_iff (ht : orderOf t = 2) (htD : t ∉ D) {d : G} (hd : d ∈ D) :
    orderOf (d * t) = 2 ↔ d ∈ invertedSet D t := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hne : d * t ≠ 1 := by
    intro h
    apply htD
    rw [eq_inv_of_mul_eq_one_right h]
    exact D.inv_mem hd
  have hsq : (d * t) ^ 2 = d * (t * d * t⁻¹) := by
    calc (d * t) ^ 2 = d * (t * d * t⁻¹) * (t * t) := by rw [sq]; group
      _ = d * (t * d * t⁻¹) := by rw [htt, mul_one]
  constructor
  · intro h2
    refine ⟨hd, ?_⟩
    have h1 : (d * t) ^ 2 = 1 := by rw [← h2, pow_orderOf_eq_one]
    rw [hsq] at h1
    exact eq_inv_of_mul_eq_one_right h1
  · intro hJ
    apply orderOf_eq_prime _ hne
    rw [hsq, hJ.2, mul_inv_cancel]

theorem mul_conj_inv_mem_invertedSet (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (D : Set G)) {d : G} (hd : d ∈ D) :
    d * (t * d * t⁻¹)⁻¹ ∈ invertedSet D t := by
  refine ⟨D.mul_mem hd (D.inv_mem (conj_mem_of_mem_normalizer htN hd)), ?_⟩
  have h := conj_conj_of_orderOf_eq_two ht d
  calc t * (d * (t * d * t⁻¹)⁻¹) * t⁻¹ = (t * d * t⁻¹) * (t * (t * d * t⁻¹) * t⁻¹)⁻¹ := by
        group
    _ = (d * (t * d * t⁻¹)⁻¹)⁻¹ := by rw [h, mul_inv_rev, inv_inv]

theorem mul_conj_inv_eq_iff (t a b : G) :
    a * (t * a * t⁻¹)⁻¹ = b * (t * b * t⁻¹)⁻¹ ↔ a⁻¹ * b * t = t * (a⁻¹ * b) := by
  constructor
  · intro h
    have h1 : Commute (b⁻¹ * a) t := by
      calc b⁻¹ * a * t = b⁻¹ * (a * (t * a * t⁻¹)⁻¹) * t * a := by group
        _ = b⁻¹ * (b * (t * b * t⁻¹)⁻¹) * t * a := by rw [h]
        _ = t * (b⁻¹ * a) := by group
    have h2 := h1.inv_left
    rwa [mul_inv_rev, inv_inv] at h2
  · intro h
    have hc : t * (a⁻¹ * b) * t⁻¹ = a⁻¹ * b := by
      rw [← h]
      group
    calc a * (t * a * t⁻¹)⁻¹
        = a * (a⁻¹ * b) * (t * (a⁻¹ * b) * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹ := by
          rw [hc]
          group
      _ = b * (t * b * t⁻¹)⁻¹ := by group

theorem odd_inversion_coset_count (hD : Odd (Nat.card D))
    (htN : t ∈ Subgroup.normalizer (D : Set G)) (htD : t ∉ D) (ht : orderOf t = 2) :
    {v : G | v * t⁻¹ ∈ D ∧ orderOf v = 2} = {v : G | ∃ d ∈ D, v = d⁻¹ * t * d} ∧
      Set.BijOn (fun d => d * t) (invertedSet D t) {v : G | v * t⁻¹ ∈ D ∧ orderOf v = 2} ∧
      Nat.card (invertedSet D t) = (Subgroup.centralizer {t}).relIndex D := by
  have hinv : ∀ v : G, v * t⁻¹ ∈ D → (orderOf v = 2 ↔ v * t⁻¹ ∈ invertedSet D t) := by
    intro v hv
    have h := orderOf_mul_eq_two_iff ht htD hv
    rwa [inv_mul_cancel_right] at h
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hv, hv2⟩
      have hJ := (hinv v hv).mp hv2
      obtain ⟨d, hdJ, hd⟩ := exists_sq_eq_of_mem_invertedSet hD (invertedSet_inv hJ)
      refine ⟨d, hdJ.1, ?_⟩
      have hconj : d⁻¹ * t * d = d⁻¹ * (t * d * t⁻¹) * t := by group
      rw [hconj, hdJ.2, ← mul_inv_rev, ← sq, hd, inv_inv, inv_mul_cancel_right]
    · rintro ⟨d, hd, rfl⟩
      have hmem : d⁻¹ * t * d * t⁻¹ ∈ D := by
        have : d⁻¹ * t * d * t⁻¹ = d⁻¹ * (t * d * t⁻¹) := by group
        rw [this]
        exact D.mul_mem (D.inv_mem hd) (conj_mem_of_mem_normalizer htN hd)
      refine ⟨hmem, ?_⟩
      have hc : SemiconjBy d⁻¹ t (d⁻¹ * t * d) := by
        change d⁻¹ * t = d⁻¹ * t * d * d⁻¹
        group
      rw [← SemiconjBy.orderOf_eq d⁻¹ hc, ht]
  · refine ⟨fun d hd => ⟨by rw [mul_inv_cancel_right]; exact hd.1, ?_⟩, fun d _ d' _ h => ?_, ?_⟩
    · exact (orderOf_mul_eq_two_iff ht htD hd.1).mpr hd
    · exact mul_right_cancel h
    · rintro v ⟨hv, hv2⟩
      exact ⟨v * t⁻¹, (hinv v hv).mp hv2, inv_mul_cancel_right v t⟩
  ·
    let f : D → invertedSet D t := fun d =>
      ⟨(d : G) * (t * (d : G) * t⁻¹)⁻¹, mul_conj_inv_mem_invertedSet ht htN d.2⟩
    have hf : Function.Surjective f := by
      rintro ⟨j, hj⟩
      obtain ⟨d, hdJ, hd⟩ := exists_sq_eq_of_mem_invertedSet hD hj
      refine ⟨⟨d, hdJ.1⟩, Subtype.ext ?_⟩
      change d * (t * d * t⁻¹)⁻¹ = j
      rw [hdJ.2, inv_inv, ← sq, hd]
    have hfib : ∀ a b : D, f a = f b ↔ a⁻¹ * b ∈ (Subgroup.centralizer {t}).subgroupOf D := by
      intro a b
      simp only [f, Subtype.mk.injEq, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_conj_inv_eq_iff t a b
    have : Finite D := finite_of_odd_card hD
    rw [Subgroup.relIndex, Subgroup.index]
    symm
    calc Nat.card (D ⧸ (Subgroup.centralizer {t}).subgroupOf D)
        = Nat.card (Quotient (Setoid.ker f)) :=
          Nat.card_congr (Quotient.congrRight fun a b => by
            rw [Setoid.ker_def, hfib]
            exact QuotientGroup.leftRel_apply)
      _ = Nat.card (invertedSet D t) := Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf)

end Coset

section Product

variable {A : Subgroup G} {t : G}

theorem notMem_of_odd_card (hA : Odd (Nat.card A)) (ht : orderOf t = 2) : t ∉ A := by
  intro htA
  have : Finite A := finite_of_odd_card hA
  have h := orderOf_dvd_natCard (⟨t, htA⟩ : A)
  rw [Subgroup.orderOf_mk, ht] at h
  exact (Nat.not_even_iff_odd.mpr hA) (even_iff_two_dvd.mpr h)

theorem inv_mul_conj_of_mem {c j : G} (hc : c ∈ Subgroup.centralizer {t})
    (hj : t * j * t⁻¹ = j⁻¹) : (c * j)⁻¹ * (t * (c * j) * t⁻¹) = j⁻¹ * j⁻¹ := by
  have hct : t * c * t⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [← hc]
    group
  calc (c * j)⁻¹ * (t * (c * j) * t⁻¹) = j⁻¹ * c⁻¹ * (t * c * t⁻¹) * (t * j * t⁻¹) := by group
    _ = j⁻¹ * j⁻¹ := by rw [hct, hj]; group

theorem fixed_mul_inverted_bijOn (hA : Odd (Nat.card A)) (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (A : Set G)) :
    Set.BijOn (fun x : G × G => x.1 * x.2)
      (((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ×ˢ invertedSet A t) A := by
  have : Finite A := finite_of_odd_card hA
  have hmaps : Set.MapsTo (fun x : G × G => x.1 * x.2)
      (((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ×ˢ invertedSet A t) A :=
    fun x hx => A.mul_mem (Subgroup.mem_inf.mp hx.1).1 hx.2.1
  have hinj : Set.InjOn (fun x : G × G => x.1 * x.2)
      (((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ×ˢ invertedSet A t) := by
    rintro ⟨c₁, j₁⟩ ⟨hc₁, hj₁⟩ ⟨c₂, j₂⟩ ⟨hc₂, hj₂⟩ h
    simp only at h
    have h1 := inv_mul_conj_of_mem (Subgroup.mem_inf.mp hc₁).2 hj₁.2
    have h2 := inv_mul_conj_of_mem (Subgroup.mem_inf.mp hc₂).2 hj₂.2
    rw [h, h2, ← sq, ← sq] at h1
    have hj : j₁⁻¹ = j₂⁻¹ :=
      (sq_injOn hA (A.inv_mem hj₂.1) (A.inv_mem hj₁.1) h1).symm
    rw [inv_inj] at hj
    subst hj
    rw [mul_right_cancel h]
  refine ⟨hmaps, hinj, ?_⟩
  have himage : (fun x : G × G => x.1 * x.2) ''
      (((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ×ˢ invertedSet A t) = A := by
    apply Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.mpr hmaps) _ (Set.toFinite _)
    have hJ := (odd_inversion_coset_count hA htN (notMem_of_odd_card hA ht) ht).2.2
    have hC : Nat.card (A ⊓ Subgroup.centralizer {t} : Subgroup G) *
        (Subgroup.centralizer {t}).relIndex A = Nat.card A := by
      rw [mul_comm, inf_comm, Subgroup.relIndex_mul_card]
    rw [hinj.ncard_image, Set.ncard_prod, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, hJ, SetLike.coe_sort_coe]
    exact hC.ge
  intro a ha
  rw [← himage] at ha
  exact ha

theorem inverted_mul_fixed_bijOn (hA : Odd (Nat.card A)) (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (A : Set G)) :
    Set.BijOn (fun x : G × G => x.1 * x.2)
      (invertedSet A t ×ˢ ((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G)) A := by
  have h := fixed_mul_inverted_bijOn hA ht htN
  refine ⟨fun x hx => A.mul_mem hx.1.1 (Subgroup.mem_inf.mp hx.2).1, ?_, ?_⟩
  · rintro ⟨j₁, c₁⟩ ⟨hj₁, hc₁⟩ ⟨j₂, c₂⟩ ⟨hj₂, hc₂⟩ hjc
    simp only at hjc
    have hmem₁ : (c₁⁻¹, j₁⁻¹) ∈
        ((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ×ˢ invertedSet A t :=
      ⟨(A ⊓ Subgroup.centralizer {t}).inv_mem hc₁, invertedSet_inv hj₁⟩
    have hmem₂ : (c₂⁻¹, j₂⁻¹) ∈
        ((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ×ˢ invertedSet A t :=
      ⟨(A ⊓ Subgroup.centralizer {t}).inv_mem hc₂, invertedSet_inv hj₂⟩
    have heq := h.injOn hmem₁ hmem₂ (by simp only; rw [← mul_inv_rev, ← mul_inv_rev, hjc])
    simp only [Prod.mk.injEq, inv_inj] at heq
    rw [heq.1, heq.2]
  · intro a ha
    obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ := h.surjOn (A.inv_mem ha)
    refine ⟨(j⁻¹, c⁻¹), ⟨invertedSet_inv hj, (A ⊓ Subgroup.centralizer {t}).inv_mem hc⟩, ?_⟩
    simp only at hcj ⊢
    rw [← mul_inv_rev, hcj, inv_inv]

theorem odd_involution_product_decomposition (hA : Odd (Nat.card A)) (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (A : Set G)) :
    Set.BijOn (fun x : G × G => x.1 * x.2)
        (((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ×ˢ invertedSet A t) A ∧
      Set.BijOn (fun x : G × G => x.1 * x.2)
        (invertedSet A t ×ˢ ((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G)) A ∧
      ∀ A₀ : Subgroup G, A₀ ≤ A → t ∈ Subgroup.normalizer (A₀ : Set G) →
        (A₀ : Set G) = ((A₀ : Set G) ∩ invertedSet A t) *
            ((A₀ ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ∧
          (A₀ : Set G) = ((A₀ ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) *
            ((A₀ : Set G) ∩ invertedSet A t) := by
  refine ⟨fixed_mul_inverted_bijOn hA ht htN, inverted_mul_fixed_bijOn hA ht htN, ?_⟩
  intro A₀ hle htN₀
  have hA₀ : Odd (Nat.card A₀) := Odd.of_dvd_nat hA (Subgroup.card_dvd_of_le hle)
  have hJ₀ : (A₀ : Set G) ∩ invertedSet A t = invertedSet A₀ t := by
    ext d
    simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_invertedSet]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hle h.1, h.2⟩⟩
  have h1 := (inverted_mul_fixed_bijOn hA₀ ht htN₀).image_eq
  have h2 := (fixed_mul_inverted_bijOn hA₀ ht htN₀).image_eq
  rw [Set.image_mul_prod] at h1 h2
  rw [hJ₀]
  exact ⟨h1.symm, h2.symm⟩

end Product

end CFSG.OddInversion
