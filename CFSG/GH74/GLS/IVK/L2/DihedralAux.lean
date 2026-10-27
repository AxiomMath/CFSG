module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.GH74.GLS.IVK.DihedralAux

open DihedralGroup

theorem eq_r_half_of_central {k : ℕ} (hk : Even k) (hk2 : k ≠ 2) {a : DihedralGroup k}
    (ha : a ∈ Subgroup.center (DihedralGroup k)) (ha1 : a ≠ 1) :
    a = r ((k / 2 : ℕ) : ZMod k) := by
  rw [center_eq_closure_of_even_ne_two hk hk2] at ha
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨h, hh⟩ := hk
  have hk0 : ((h : ℕ) : ZMod k) + h = 0 := by rw [← Nat.cast_add, ← hh, ZMod.natCast_self]
  have hdiv : k / 2 = h := by omega
  rw [hdiv] at hm ⊢
  rw [r_zpow] at hm
  rcases Int.even_or_odd m with ⟨m', hm'⟩ | ⟨m', hm'⟩
  · exfalso
    apply ha1
    rw [← hm, hm']
    have : ((h : ZMod k) * ((m' + m' : ℤ) : ZMod k)) = 0 := by
      push_cast
      calc (h : ZMod k) * (m' + m') = ((h : ZMod k) + h) * m' := by ring
        _ = 0 := by rw [hk0]; ring
    rw [this]; rfl
  · rw [← hm, hm']
    have : ((h : ZMod k) * ((2 * m' + 1 : ℤ) : ZMod k)) = h := by
      push_cast
      calc (h : ZMod k) * (2 * m' + 1) = ((h : ZMod k) + h) * m' + h := by ring
        _ = h := by rw [hk0]; ring
    rw [this]

theorem sq_eq_central_is_sq {t : ℕ} (ht : 0 < t) {d : DihedralGroup (8 * t)}
    (hd : d * d = r (((8 * t) / 2 : ℕ) : ZMod (8 * t))) :
    ∃ y : DihedralGroup (8 * t), d = y * y := by
  have : NeZero (8 * t) := ⟨by omega⟩
  rcases d with j | j
  · rw [r_mul_r] at hd
    have hj : j + j = ((4 * t : ℕ) : ZMod (8 * t)) := by
      have := r.inj hd
      rw [this]
      congr 2
      omega
    have hv : ((j.val + j.val : ℕ) : ZMod (8 * t)) = ((4 * t : ℕ) : ZMod (8 * t)) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val]
      exact hj
    rw [ZMod.natCast_eq_natCast_iff'] at hv
    have hjv : j.val < 8 * t := ZMod.val_lt j
    have hmod : (j.val + j.val) % (8 * t) = (4 * t) % (8 * t) := hv
    have h4 : (4 * t) % (8 * t) = 4 * t := Nat.mod_eq_of_lt (by omega)
    rw [h4] at hmod
    have hdiv := Nat.div_add_mod (j.val + j.val) (8 * t)
    rw [hmod] at hdiv
    set q := (j.val + j.val) / (8 * t) with hq
    have hv2 : j.val = 4 * t * q + 2 * t := by nlinarith
    refine ⟨r (((4 * t * q + 2 * t) / 2 : ℕ) : ZMod (8 * t)), ?_⟩
    rw [r_mul_r]
    congr 1
    have h2 : (4 * t * q + 2 * t) / 2 + (4 * t * q + 2 * t) / 2 = j.val := by
      have : (4 * t * q + 2 * t) / 2 = 2 * t * q + t := by
        have : 4 * t * q + 2 * t = 2 * (2 * t * q + t) := by ring
        rw [this]; omega
      rw [this]; nlinarith
    have h3 : (((4 * t * q + 2 * t) / 2 : ℕ) : ZMod (8 * t)) +
        (((4 * t * q + 2 * t) / 2 : ℕ) : ZMod (8 * t)) = (j.val : ZMod (8 * t)) := by
      rw [← Nat.cast_add, h2]
    rw [h3, ZMod.natCast_zmod_val]
  · rw [sr_mul_self] at hd
    exfalso
    have h1 : (r 0 : DihedralGroup (8 * t)) = r (((8 * t) / 2 : ℕ) : ZMod (8 * t)) := by
      rw [r_zero]; exact hd
    have h2 := r.inj h1
    have h3 : ((((8 * t) / 2 : ℕ)) : ZMod (8 * t)) = 0 := h2.symm
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega

theorem central_involution_unique {P : Type*} [Group P] {k : ℕ} (φ : P ≃* DihedralGroup k)
    (hk : Even k) (hk2 : k ≠ 2) {a b : P} (ha : ∀ x, a * x = x * a) (hb : ∀ x, b * x = x * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have hc : ∀ {c : P}, (∀ x, c * x = x * c) → φ c ∈ Subgroup.center (DihedralGroup k) := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hc x]
  have h1 : φ a ≠ 1 := fun h => ha1 (φ.injective (by rw [h, map_one]))
  have h2 : φ b ≠ 1 := fun h => hb1 (φ.injective (by rw [h, map_one]))
  have := (eq_r_half_of_central hk hk2 (hc ha) h1).trans
    (eq_r_half_of_central hk hk2 (hc hb) h2).symm
  exact φ.injective this

theorem sq_eq_central_is_sq_of_equiv {Q : Type*} [Group Q] {t : ℕ} (ht : 0 < t)
    (φ : Q ≃* DihedralGroup (8 * t)) {z : Q} (hz : ∀ x, z * x = x * z) (hz1 : z ≠ 1)
    {d : Q} (hd : d * d = z) : ∃ y : Q, d = y * y := by
  have hc : φ z ∈ Subgroup.center (DihedralGroup (8 * t)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hz x]
  have h1 : φ z ≠ 1 := fun h => hz1 (φ.injective (by rw [h, map_one]))
  have hk : Even (8 * t) := ⟨4 * t, by ring⟩
  have hk2 : 8 * t ≠ 2 := by omega
  have hz' := eq_r_half_of_central hk hk2 hc h1
  have hd' : φ d * φ d = r (((8 * t) / 2 : ℕ) : ZMod (8 * t)) := by
    rw [← map_mul, hd, hz']
  obtain ⟨y, hy⟩ := sq_eq_central_is_sq ht hd'
  exact ⟨φ.symm y, by
    apply φ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, ← hy]⟩

theorem exists_central_involution {k : ℕ} (hk : Even k) (hk2 : k ≠ 2) (hk0 : 0 < k) :
    ∃ c : DihedralGroup k, c ∈ Subgroup.center (DihedralGroup k) ∧ c ≠ 1 ∧ c * c = 1 := by
  have : NeZero k := ⟨by omega⟩
  refine ⟨r ((k / 2 : ℕ) : ZMod k), ?_, ?_, ?_⟩
  · rw [center_eq_closure_of_even_ne_two hk hk2]
    exact Subgroup.mem_zpowers _
  · intro h
    rw [one_def] at h
    have h1 := r.inj h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by obtain ⟨m, hm⟩ := hk; omega) h1
    omega
  · rw [r_mul_r, ← Nat.cast_add]
    obtain ⟨m, hm⟩ := hk
    have : k / 2 + k / 2 = k := by omega
    rw [this, ZMod.natCast_self, r_zero]

theorem sq_eq_central_is_sq_of_dvd {Q : Type*} [Group Q] {k : ℕ} (hk : 8 ∣ k) (hk0 : 0 < k)
    (φ : Q ≃* DihedralGroup k) {z : Q} (hz : ∀ x, z * x = x * z) (hz1 : z ≠ 1) {d : Q}
    (hd : d * d = z) : ∃ y : Q, d = y * y := by
  obtain ⟨t, rfl⟩ := hk
  exact sq_eq_central_is_sq_of_equiv (by omega) φ hz hz1 hd

theorem cyclic_unique_involution {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) (ha2 : a * a = 1) (hb2 : b * b = 1) : a = b := by
  classical
  have := Fintype.ofFinite G
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  by_contra hab
  have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · rwa [pow_two]
    · rwa [pow_two]
  have hcard : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha h.symm, fun h => hb h.symm⟩
  have := Finset.card_le_card hsub
  omega

open Subgroup in
theorem pow_mem_iff_even {G : Type*} [Group G] (H : Subgroup G) (hH : H.index = 2) {ρ : G}
    (hρ : ρ ∉ H) (k : ℕ) : ρ ^ k ∈ H ↔ Even k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Subgroup.mul_mem_iff_of_index_two hH, ih, Nat.even_add_one]
    simp [hρ]

open Subgroup in
theorem involution_mem_iff {G : Type*} [Group G] (H : Subgroup G) (hH : H.index = 2)
    (U : Subgroup G) [Finite U] [IsCyclic U] (hU : ¬ U ≤ H) {s : G} (hsU : s ∈ U)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) : s ∈ H ↔ 4 ∣ Nat.card U := by
  classical
  obtain ⟨⟨ρ, hρU⟩, hgen⟩ := IsCyclic.exists_generator (α := U)
  have hρH : ρ ∉ H := by
    intro hρ
    apply hU
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨x, hx⟩)
    have : x = ρ ^ k := by simpa using (congrArg Subtype.val hk).symm
    rw [this]
    exact H.zpow_mem hρ k
  have hord : orderOf (⟨ρ, hρU⟩ : U) = Nat.card U := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hordρ : orderOf ρ = Nat.card U := by rw [← hord, Subgroup.orderOf_mk]
  have hNeven : 2 ∣ Nat.card U := by
    have h2 : orderOf s = 2 := orderOf_eq_prime (by rwa [← pow_two] at hs2) hs1
    rw [← h2]
    exact Subgroup.orderOf_dvd_natCard U hsU
  obtain ⟨M, hM⟩ := hNeven
  have hMpos : 0 < M := by
    have := Nat.card_pos (α := U)
    omega
  have hρM2 : (ρ ^ M) * (ρ ^ M) = 1 := by
    rw [← pow_add, ← two_mul, ← hM, ← hordρ]
    exact pow_orderOf_eq_one ρ
  have hρM1 : ρ ^ M ≠ 1 := by
    intro h1
    have := orderOf_le_of_pow_eq_one hMpos h1
    omega
  have hs' : (⟨ρ ^ M, U.pow_mem hρU M⟩ : U) = ⟨s, hsU⟩ := by
    apply cyclic_unique_involution
    · intro h; apply hρM1; exact congrArg Subtype.val h
    · intro h; apply hs1; exact congrArg Subtype.val h
    · exact Subtype.ext hρM2
    · exact Subtype.ext hs2
  have hseq : s = ρ ^ M := (congrArg Subtype.val hs').symm
  rw [hseq, pow_mem_iff_even H hH hρH]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, by omega⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by omega⟩

open Subgroup in
theorem centralizer_equiv_of_conj {G : Type*} [Group G] {g A s : G} (h : g * A * g⁻¹ = s) :
    Nonempty (↥(centralizer ({A} : Set G)) ≃* ↥(centralizer ({s} : Set G))) := by
  have hmap : (centralizer ({A} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({s} : Set G) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x * A = A * x := hx
      show (g * x * g⁻¹) * s = s * (g * x * g⁻¹)
      rw [← h]
      calc g * x * g⁻¹ * (g * A * g⁻¹) = g * (x * A) * g⁻¹ := by group
        _ = g * (A * x) * g⁻¹ := by rw [hx']
        _ = g * A * g⁻¹ * (g * x * g⁻¹) := by group
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by show g * (g⁻¹ * y * g) * g⁻¹ = y; group⟩
      show (g⁻¹ * y * g) * A = A * (g⁻¹ * y * g)
      have hy' : y * s = s * y := hy
      rw [← h] at hy'
      calc (g⁻¹ * y * g) * A = g⁻¹ * (y * (g * A * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * A * g⁻¹ * y) * g := by rw [hy']
        _ = A * (g⁻¹ * y * g) := by group
  exact ⟨((centralizer ({A} : Set G)).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hmap)⟩

open Subgroup in
theorem centralizer_equiv_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (x : G) :
    Nonempty (↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({φ x} : Set G'))) := by
  have hmap : (centralizer ({x} : Set G)).map φ.toMonoidHom = centralizer ({φ x} : Set G') := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      show φ a * φ x = φ x * φ a
      rw [← map_mul, ← map_mul, ha]
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      show φ.symm y * x = x * φ.symm y
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  exact ⟨(Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem two_mul_eq_zero_iff {k : ℕ} [NeZero k] (i : ZMod k) (h : i + i = 0) :
    i = 0 ∨ i = ((k / 2 : ℕ) : ZMod k) := by
  have hneg : -i = i := neg_eq_of_add_eq_zero_right h
  rcases (ZMod.neg_eq_self_iff i).mp hneg with h0 | h1
  · left; exact h0
  · right
    have hk2 : k % 2 = 0 := by
      have := ZMod.val_lt i
      omega
    rw [← ZMod.natCast_zmod_val i]
    congr 1
    omega

theorem card_le_four_of_elemAbelian {k : ℕ} [NeZero k] (E : Subgroup (DihedralGroup k))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  classical
  by_cases hrefl : ∃ j, sr j ∈ E
  · obtain ⟨j, hj⟩ := hrefl
    have hsub : (E : Set (DihedralGroup k)) ⊆
        (({r 0, r ((k / 2 : ℕ) : ZMod k), sr j, sr (j + ((k / 2 : ℕ) : ZMod k))} :
          Finset (DihedralGroup k)) : Set (DihedralGroup k)) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      have hc := hcomm x hx (sr j) hj
      rcases x with i | m
      · rw [r_mul_sr, sr_mul_r] at hc
        have h2 : i + i = 0 := by
          have := sr.inj hc
          linear_combination (-1 : ZMod k) * this
        rcases two_mul_eq_zero_iff i h2 with h | h
        · left; rw [h]
        · right; left; rw [h]
      · rw [sr_mul_sr, sr_mul_sr] at hc
        have h2 : (m - j) + (m - j) = 0 := by
          have := r.inj hc
          linear_combination (-1 : ZMod k) * this
        rcases two_mul_eq_zero_iff (m - j) h2 with h | h
        · right; right; left
          have : m = j := by linear_combination h
          rw [this]
        · right; right; right
          have : m = j + ((k / 2 : ℕ) : ZMod k) := by linear_combination h
          rw [this]
    calc Nat.card E ≤ Nat.card (↑({r 0, r ((k / 2 : ℕ) : ZMod k), sr j,
          sr (j + ((k / 2 : ℕ) : ZMod k))} : Finset (DihedralGroup k)) : Set (DihedralGroup k)) :=
          Nat.card_mono (Finset.finite_toSet _) hsub
      _ ≤ 4 := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
        exact (Finset.card_le_four)
  · have hrefl' : ∀ m, sr m ∉ E := fun m hm => hrefl ⟨m, hm⟩
    have hsub : (E : Set (DihedralGroup k)) ⊆
        (({r 0, r ((k / 2 : ℕ) : ZMod k)} : Finset (DihedralGroup k)) : Set (DihedralGroup k)) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rcases x with i | m
      · have h1 := hsq _ hx
        rw [r_mul_r] at h1
        have h2 : i + i = 0 := by rw [← r_zero] at h1; exact r.inj h1
        rcases two_mul_eq_zero_iff i h2 with h | h
        · left; rw [h]
        · right; rw [h]
      · exact absurd hx (hrefl' m)
    calc Nat.card E ≤ Nat.card (↑({r 0, r ((k / 2 : ℕ) : ZMod k)} : Finset (DihedralGroup k)) :
          Set (DihedralGroup k)) := Nat.card_mono (Finset.finite_toSet _) hsub
      _ ≤ 4 := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
        exact (Finset.card_le_two).trans (by norm_num)

end CFSG.GH74.GLS.IVK.DihedralAux
