module

public import CFSG.GH74.GLS.Stage4.Q9.PElements
public import CFSG.GH74.GLS.Stage4.Q9.TIAssembly
public import CFSG.CharacterTheory.DihedralTIFusion.SupportSum
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.GH74.GLS.Stage4.Q9

section Helpers

variable {G : Type*} [Group G]

private theorem orderOf_conj_eq_frob (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g
    (show SemiconjBy g x (g * x * g⁻¹) by simp [SemiconjBy, mul_assoc])).symm

end Helpers

section Count

theorem frobenius_ti_count {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (C : Subgroup G) (D : Set G) (hTI : CFSG.IsTISubset D C)
    (hD : ∀ d ∈ D, ∃ k : ℕ, orderOf d = p ^ k)
    (hcov : ∀ g : G, g ≠ 1 → (∃ k : ℕ, orderOf g = p ^ k) → ∃ a : G, a * g * a⁻¹ ∈ D) :
    p ^ (Nat.card G).factorization p ∣ C.index * Nat.card D + 1 := by
  have hcard : Nat.card ↥(⋃ a : G, (fun y => a⁻¹ * y * a) '' D) = C.index * Nat.card D :=
    (CFSG.DihedralTIFusion.ti_conjugacy_support_sum hTI (fun _ => 1) (fun _ _ => rfl)).2
  have hset : {g : G | ∃ k : ℕ, orderOf g = p ^ k} =
      insert 1 (⋃ a : G, (fun y => a⁻¹ * y * a) '' D) := by
    ext g
    rw [Set.mem_insert_iff]
    constructor
    · intro hg
      by_cases h1 : g = 1
      · exact Or.inl h1
      · obtain ⟨a, ha⟩ := hcov g h1 hg
        exact Or.inr (CFSG.DihedralTIFusion.mem_iUnion_conj_image_iff.2 ⟨a, ha⟩)
    · rintro (rfl | hg)
      · exact ⟨0, by simp⟩
      · obtain ⟨a, ha⟩ := CFSG.DihedralTIFusion.mem_iUnion_conj_image_iff.1 hg
        obtain ⟨k, hk⟩ := hD _ ha
        exact ⟨k, by rw [← hk, orderOf_conj_eq_frob]⟩
  have h1not : (1 : G) ∉ ⋃ a : G, (fun y => a⁻¹ * y * a) '' D := by
    intro h
    obtain ⟨a, ha⟩ := CFSG.DihedralTIFusion.mem_iUnion_conj_image_iff.1 h
    exact hTI.2.1 (by simpa using ha)
  have hcount : Nat.card {g : G // ∃ k : ℕ, orderOf g = p ^ k} = C.index * Nat.card D + 1 := by
    rw [← hcard]
    have h2 : Nat.card {g : G // ∃ k : ℕ, orderOf g = p ^ k} =
        Nat.card ↥(insert (1 : G) (⋃ a : G, (fun y => a⁻¹ * y * a) '' D)) := by
      rw [← hset]
      rfl
    rw [h2, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_insert_of_notMem h1not (Set.toFinite _)]
  rw [← hcount]
  exact card_pElements_dvd_orderOf G p

end Count

section PSet

variable {G : Type*} [Group G]

@[expose] def pSet (p : ℕ) (z : G) (K₁ K₂ : Subgroup G) : Set G :=
  {x | x ∈ Sset z K₁ K₂ ∧ x ≠ 1 ∧ ∃ k : ℕ, orderOf x = p ^ k}

theorem pSet_subset_Sset (p : ℕ) (z : G) (K₁ K₂ : Subgroup G) :
    pSet p z K₁ K₂ ⊆ Sset z K₁ K₂ :=
  fun _ hx => hx.1

theorem one_notMem_pSet (p : ℕ) (z : G) (K₁ K₂ : Subgroup G) : (1 : G) ∉ pSet p z K₁ K₂ :=
  fun h => h.2.1 rfl

private theorem conj_mem_pSet {p : ℕ} {z : G} {K₁ K₂ : Subgroup G}
    (hTI : CFSG.IsTISubset (Sset z K₁ K₂) (Subgroup.centralizer {z}))
    {c : G} (hc : c ∈ Subgroup.centralizer {z}) {x : G} (hx : x ∈ pSet p z K₁ K₂) :
    c * x * c⁻¹ ∈ pSet p z K₁ K₂ := by
  obtain ⟨hxS, hx1, k, hk⟩ := hx
  refine ⟨CFSG.DihedralTIFusion.ti_conj_mem_of_mem hTI hxS hc, ?_, k,
    by rw [orderOf_conj_eq_frob, hk]⟩
  intro h
  apply hx1
  rw [← orderOf_eq_one_iff, ← orderOf_conj_eq_frob c x, h, orderOf_one]

theorem isTISubset_pSet {G : Type*} [Group G] (p : ℕ) {z : G} {K₁ K₂ : Subgroup G}
    (hTI : CFSG.IsTISubset (Sset z K₁ K₂) (Subgroup.centralizer {z}))
    (hne : (pSet p z K₁ K₂).Nonempty) :
    CFSG.IsTISubset (pSet p z K₁ K₂) (Subgroup.centralizer {z}) := by
  refine ⟨hne, one_notMem_pSet p z K₁ K₂, ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      obtain ⟨d, hd⟩ := hne
      have hgd : g * d * g⁻¹ ∈ pSet p z K₁ K₂ := (Subgroup.mem_set_normalizer_iff.mp hg d).mp hd
      exact CFSG.DihedralTIFusion.ti_mem_of_conj_mem hTI hd.1 hgd.1
    · intro hg
      refine Subgroup.mem_set_normalizer_iff.mpr fun n =>
        ⟨fun hn => conj_mem_pSet hTI hg hn, fun hn => ?_⟩
      have h := conj_mem_pSet hTI (inv_mem hg) hn
      rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at h
  · intro g hg
    exact Set.eq_empty_of_subset_empty
      ((Set.inter_subset_inter (pSet_subset_Sset p z K₁ K₂)
        (Set.image_mono (pSet_subset_Sset p z K₁ K₂))).trans (hTI.2.2.2 g hg).le)

end PSet

section Cover

theorem cover_two {G : Type*} [Group G] {z : G} (_hz : orderOf z = 2)
    (hone : ∀ u : G, orderOf u = 2 → IsConj z u) (K₁ K₂ : Subgroup G) :
    ∀ g : G, g ≠ 1 → (∃ k : ℕ, orderOf g = 2 ^ k) →
      ∃ a : G, a * g * a⁻¹ ∈ pSet 2 z K₁ K₂ := by
  rintro g hg1 ⟨k, hk⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hg1 (orderOf_eq_one_iff.1 (by simpa using hk))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hg' : orderOf (g ^ 2 ^ m) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero m two_ne_zero) (hk ▸ pow_dvd_pow 2 (Nat.le_succ m)), hk,
      pow_succ]
    exact Nat.mul_div_cancel_left 2 (by positivity)
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone _ hg')
  have hconj : (c⁻¹ * g * c⁻¹⁻¹) ^ 2 ^ m = z := by
    rw [conj_pow, ← hc]
    group
  have hzmem : z ∈ Subgroup.zpowers (c⁻¹ * g * c⁻¹⁻¹) := by
    rw [← hconj]
    exact pow_mem (Subgroup.mem_zpowers _) _
  have hcomm : c⁻¹ * g * c⁻¹⁻¹ ∈ Subgroup.centralizer {z} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := ((Commute.refl (c⁻¹ * g * c⁻¹⁻¹)).pow_right (2 ^ m)).eq
    rwa [hconj] at h
  refine ⟨c⁻¹, Or.inl (Or.inl ⟨hcomm, hzmem⟩), ?_, m + 1, by rw [orderOf_conj_eq_frob, hk]⟩
  intro h
  apply hg1
  rw [← orderOf_eq_one_iff, ← orderOf_conj_eq_frob c⁻¹ g, h, orderOf_one]

theorem cover_three {G : Type*} [Group G] [Finite G] {z : G}
    (hcard3 : (Nat.card G).factorization 3 =
      (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 3)
    (K₁ K₂ : Subgroup G) :
    ∀ g : G, g ≠ 1 → (∃ k : ℕ, orderOf g = 3 ^ k) →
      ∃ a : G, a * g * a⁻¹ ∈ pSet 3 z K₁ K₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro g hg1 ⟨k, hk⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hg1 (orderOf_eq_one_iff.1 (by simpa using hk))
  let P : Sylow 3 (Subgroup.centralizer ({z} : Set G)) := default
  have hPcard : Nat.card (Subgroup.map (Subgroup.centralizer ({z} : Set G)).subtype
      (P : Subgroup (Subgroup.centralizer ({z} : Set G)))) =
        3 ^ (Nat.card G).factorization 3 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), P.card_eq_multiplicity,
      hcard3]
  let P' : Sylow 3 G := Sylow.ofCard _ hPcard
  have hP' : (P' : Subgroup G) = Subgroup.map (Subgroup.centralizer ({z} : Set G)).subtype
      (P : Subgroup (Subgroup.centralizer ({z} : Set G))) := Sylow.coe_ofCard _ _
  have hgp : IsPGroup 3 (Subgroup.zpowers g) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hgp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G Q P'
  have hmem : a * g * a⁻¹ ∈ ((a • Q : Sylow 3 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul g (MulAut.conj a) _ (hQ (Subgroup.mem_zpowers g))
  have hC : a * g * a⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [ha, hP'] at hmem
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hmem
    rw [← hy]
    exact y.2
  refine ⟨a, Or.inl (Or.inr ⟨hC, ?_⟩), ?_, k, by rw [orderOf_conj_eq_frob, hk]⟩
  · rw [orderOf_conj_eq_frob, hk]
    exact dvd_pow_self 3 hk0
  · intro h
    apply hg1
    rw [← orderOf_eq_one_iff, ← orderOf_conj_eq_frob a g, h, orderOf_one]

theorem cover_five {G : Type*} [Group G] (K₁ K₂ : Subgroup G)
    (h5conj : ∀ g : G, orderOf g = 5 → ∃ h : G, h * g * h⁻¹ ∈ K₁ ∨ h * g * h⁻¹ ∈ K₂)
    (hexp : ∀ g : G, (∃ k : ℕ, orderOf g = 5 ^ k) → orderOf g = 1 ∨ orderOf g = 5) (z : G) :
    ∀ g : G, g ≠ 1 → (∃ k : ℕ, orderOf g = 5 ^ k) →
      ∃ a : G, a * g * a⁻¹ ∈ pSet 5 z K₁ K₂ := by
  rintro g hg1 hg
  have h5 : orderOf g = 5 := by
    rcases hexp g hg with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  obtain ⟨h, hh⟩ := h5conj g h5
  have ho : orderOf (h * g * h⁻¹) = 5 := by rw [orderOf_conj_eq_frob, h5]
  refine ⟨h, Or.inr ⟨hh, ho⟩, ?_, 1, by rw [ho, pow_one]⟩
  intro h1
  rw [h1, orderOf_one] at ho
  omega

end Cover

section Frobenius

theorem frobenius_two {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (hone : ∀ u : G, orderOf u = 2 → IsConj z u) (K₁ K₂ : Subgroup G)
    (hTI : CFSG.IsTISubset (Sset z K₁ K₂) (Subgroup.centralizer {z}))
    (hne : (pSet 2 z K₁ K₂).Nonempty) :
    2 ^ (Nat.card G).factorization 2 ∣
      (Subgroup.centralizer {z}).index * Nat.card (pSet 2 z K₁ K₂) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact frobenius_ti_count 2 _ _ (isTISubset_pSet 2 hTI hne) (fun d hd => hd.2.2)
    (cover_two hz hone K₁ K₂)

theorem frobenius_three {G : Type*} [Group G] [Finite G] {z : G}
    (hcard3 : (Nat.card G).factorization 3 =
      (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 3)
    (K₁ K₂ : Subgroup G)
    (hTI : CFSG.IsTISubset (Sset z K₁ K₂) (Subgroup.centralizer {z}))
    (hne : (pSet 3 z K₁ K₂).Nonempty) :
    3 ^ (Nat.card G).factorization 3 ∣
      (Subgroup.centralizer {z}).index * Nat.card (pSet 3 z K₁ K₂) + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact frobenius_ti_count 3 _ _ (isTISubset_pSet 3 hTI hne) (fun d hd => hd.2.2)
    (cover_three hcard3 K₁ K₂)

theorem frobenius_five {G : Type*} [Group G] [Finite G] {z : G} (K₁ K₂ : Subgroup G)
    (h5conj : ∀ g : G, orderOf g = 5 → ∃ h : G, h * g * h⁻¹ ∈ K₁ ∨ h * g * h⁻¹ ∈ K₂)
    (hexp : ∀ g : G, (∃ k : ℕ, orderOf g = 5 ^ k) → orderOf g = 1 ∨ orderOf g = 5)
    (hTI : CFSG.IsTISubset (Sset z K₁ K₂) (Subgroup.centralizer {z}))
    (hne : (pSet 5 z K₁ K₂).Nonempty) :
    5 ^ (Nat.card G).factorization 5 ∣
      (Subgroup.centralizer {z}).index * Nat.card (pSet 5 z K₁ K₂) + 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact frobenius_ti_count 5 _ _ (isTISubset_pSet 5 hTI hne) (fun d hd => hd.2.2)
    (cover_five K₁ K₂ h5conj hexp z)

end Frobenius

end CFSG.GH74.GLS.Stage4.Q9
