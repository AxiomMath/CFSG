module

public import CFSG.LargeExtraspecial.AS35LLocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35YF

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

variable {k : ℕ}

theorem herm_single_add_single_self {i j : Fin k} (hij : i ≠ j) (a : K) {c : K} (hc : c ≠ 0) :
    herm frob (Pi.single i a + Pi.single j (c * a)) (Pi.single i a + Pi.single j (c * a)) = 0 := by
  simp only [herm_add_left, herm_add_right, herm_single_left, Pi.single_eq_same,
    Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm, add_zero, zero_add, mul_zero, map_mul]
  have h1 := frob_mul_self hc
  linear_combination (frob a * a) * h1 + (frob a * a) * two_eq_zero

theorem mem_of_forall_isotropic (hk : 2 ≤ k) {U : AddSubgroup (Fin k → K)}
    (hU : ∀ y : Fin k → K, herm frob y y = 0 → y ∈ U) (v : Fin k → K) : v ∈ U := by
  rw [← Finset.univ_sum_single v]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨j, hji⟩ : ∃ j : Fin k, j ≠ i := by
    by_cases h : i = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, fun h' => by simp [h, Fin.ext_iff] at h'⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h h'.symm⟩
  have hij : i ≠ j := fun h => hji h.symm
  have h1 := hU _ (herm_single_add_single_self hij (v i) one_ne_zero)
  have h2 := hU _ (herm_single_add_single_self hij (v i) omega_ne_zero)
  have h3 := hU _ (herm_single_add_single_self hij (v i)
    ((map_ne_zero frob).mpr omega_ne_zero))
  have e : (Pi.single i (v i) : Fin k → K) =
      (Pi.single i (v i) + Pi.single j (1 * v i) : Fin k → K) +
      (Pi.single i (v i) + Pi.single j (ω * v i) : Fin k → K) +
      (Pi.single i (v i) + Pi.single j (frob ω * v i) : Fin k → K) := by
    ext l
    simp only [Pi.add_apply]
    by_cases hl : l = i
    · subst hl
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
      linear_combination (-(v l)) * two_eq_zero
    · by_cases hl' : l = j
      · subst hl'
        simp only [Pi.single_eq_same, Pi.single_eq_of_ne hl, zero_add]
        linear_combination (-(v i)) * omega_add_frob + (-(v i)) * two_eq_zero
      · simp [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl']
  rw [e]
  exact add_mem (add_mem h1 h2) h3

theorem K_cases (c : K) : c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω + 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hω1 : (ω + 1 : K) ≠ 1 := by
    intro e
    exact omega_ne_zero (by linear_combination e)
  have hω0 : (ω + 1 : K) ≠ 0 := by
    rw [← frob_omega]
    exact (map_ne_zero frob).mpr omega_ne_zero
  have hωω : (ω + 1 : K) ≠ ω := by
    intro e
    exact one_ne_zero (by linear_combination e)
  have hcard : (({c, 0, 1, ω, ω + 1} : Finset K)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [h0, h1, h2, h3]),
      Finset.card_insert_of_notMem (by simp [omega_ne_zero.symm, hω0.symm]),
      Finset.card_insert_of_notMem (by simp [omega_ne_one.symm, hω1.symm]),
      Finset.card_insert_of_notMem (by simp [hωω.symm]), Finset.card_singleton]
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [card_K]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have hle := Finset.card_le_univ ({c, 0, 1, ω, ω + 1} : Finset K)
  rw [hcard, ← Nat.card_eq_fintype_card, card_K] at hle
  norm_num at hle

theorem smul_mem_of_omega {U : AddSubgroup (Fin k → K)} (hω : ∀ a ∈ U, ω • a ∈ U) (c : K)
    {a : Fin k → K} (ha : a ∈ U) : c • a ∈ U := by
  rcases K_cases c with rfl | rfl | rfl | rfl
  · rw [zero_smul]
    exact zero_mem _
  · rwa [one_smul]
  · exact hω a ha
  · rw [add_smul, one_smul]
    exact add_mem (hω a ha) ha

theorem mem_of_iso_two {U : AddSubgroup (Fin 2 → K)} (hω : ∀ a ∈ U, ω • a ∈ U)
    (htv : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 → ∀ a ∈ U, tvU z • a ∈ U)
    {y₀ : Fin 2 → K} (hy₀U : y₀ ∈ U) (hy₀0 : y₀ ≠ 0) (v : Fin 2 → K) : v ∈ U := by
  obtain ⟨z, hz, hzy⟩ : ∃ z : Fin 2 → K, herm frob z z = 0 ∧ herm frob z y₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hy₀0 (eq_zero_of_forall_isotropic le_rfl h)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hzy (herm_zero_left frob _)
  have hzU : z ∈ U := by
    have h1 := add_mem (htv z hz0 hz y₀ hy₀U) hy₀U
    have e : tvU z • y₀ + y₀ = herm frob z y₀ • z := by
      rw [tvU_smul hz, add_comm, ← add_assoc, ← two_smul K y₀, two_eq_zero, zero_smul, zero_add]
    rw [e] at h1
    have h2 := smul_mem_of_omega hω (herm frob z y₀)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hzy, one_smul] at h2
  have hli : LinearIndependent K ![y₀, z] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (herm frob z) hab
    simp only [herm_add_right, herm_smul_right, hz, mul_zero, add_zero, herm_zero_right] at h1
    have ha : a = 0 := (mul_eq_zero.mp h1).resolve_right hzy
    subst ha
    rw [zero_smul, zero_add] at hab
    exact ⟨rfl, (smul_eq_zero.mp hab).resolve_right hz0⟩
  have hspan : Submodule.span K (Set.range ![y₀, z]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Module.finrank_fin_fun, Fintype.card_fin]
  have hv : v ∈ Submodule.span K {y₀, z} := by
    rw [← Matrix.range_cons_cons_empty, hspan]
    exact Submodule.mem_top
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  exact add_mem (smul_mem_of_omega hω a hy₀U) (smul_mem_of_omega hω b hzU)

theorem smul_v₀_of_commute (hk : 2 ≤ k) {x : SUid frob (k + 2)} (hx2 : ∃ j : ℕ, x ^ 2 ^ j = 1)
    (hxc : (QuotientGroup.mk x : PG (k + 2)) * tq (v₀ k) = tq (v₀ k) * QuotientGroup.mk x) :
    x • v₀ k = v₀ k := by
  have hm : 3 ≤ k + 2 := by omega
  have h1 : tq (v₀ k) = tq (x • v₀ k) := by
    rw [← conj_tq x herm_v₀_v₀, hxc, mul_inv_cancel_right]
  have hx0 : x • v₀ k ≠ 0 := (smul_ne_zero_iff_ne x).2 v₀_ne_zero
  obtain ⟨c, hc⟩ := (tq_eq_tq_iff hm v₀_ne_zero herm_v₀_v₀ hx0
    (by rw [herm_smul_smul, herm_v₀_v₀])).1 h1
  have hpow : ∀ i : ℕ, (x ^ i) • v₀ k = c ^ i • v₀ k := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, mul_smul, hc, smul_comm, ih, smul_smul, pow_succ, mul_comm]
  obtain ⟨j, hj⟩ := hx2
  have hc2 : c ^ 2 ^ j = 1 := by
    have h2 := hpow (2 ^ j)
    rw [hj, one_smul] at h2
    have h3 : (c ^ 2 ^ j - 1) • v₀ k = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right v₀_ne_zero)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ two_ne_zero)] at hc2
    exact zero_ne_one hc2
  have hc3 : c ^ 3 = 1 := by
    have h5 := frob_mul_self hc0
    rw [frob_apply] at h5
    linear_combination h5
  have hcop : Nat.gcd (2 ^ j) 3 = 1 := Nat.Coprime.pow_left j (by norm_num)
  have h6 := pow_gcd_eq_one.mpr ⟨hc2, hc3⟩
  rw [hcop, pow_one] at h6
  rw [hc, h6, one_smul]

theorem eq_of_mk_eq (hm : 3 ≤ k + 2) {y w : SUid frob (k + 2)} (hy : ∃ j : ℕ, y ^ 2 ^ j = 1)
    (hw : ∃ j : ℕ, w ^ 2 ^ j = 1)
    (h : (QuotientGroup.mk y : PG (k + 2)) = QuotientGroup.mk w) : y = w := by
  have hζ : y⁻¹ * w ∈ Subgroup.center (SUid frob (k + 2)) := QuotientGroup.eq.1 h
  obtain ⟨a, ha⟩ := hy
  obtain ⟨b, hb⟩ := hw
  have hwy : w = y * (y⁻¹ * w) := by group
  have hcomm : Commute y (y⁻¹ * w) := ((Subgroup.mem_center_iff.1 hζ) y)
  have hya : y ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
  have hwb : w ^ 2 ^ (a + b) = 1 := by rw [pow_add, mul_comm (2 ^ a), pow_mul, hb, one_pow]
  have hζ2 : (y⁻¹ * w) ^ 2 ^ (a + b) = 1 := by
    have h1 : w ^ 2 ^ (a + b) = y ^ 2 ^ (a + b) * (y⁻¹ * w) ^ 2 ^ (a + b) := by
      conv_lhs => rw [hwy]
      exact hcomm.mul_pow _
    rw [hwb, hya, one_mul] at h1
    exact h1.symm
  have h1 := AS35U.eq_one_of_mem_center hm hζ hζ2
  rw [hwy, h1, mul_one]

theorem rho_trivial (hk : 2 ≤ k) {N : Subgroup (SUid frob (k + 2))}
    (hfix : ∀ x ∈ N, x • v₀ k = v₀ k) (hpow : ∀ x ∈ N, ∃ j : ℕ, x ^ 2 ^ j = 1)
    (hnorm : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ N,
      tvU (ι k z) * x * tvU (ι k z) ∈ N) :
    ∀ x ∈ N, ∀ z, π k (x • ι k z) = z := by
  have hNS : N ≤ Stab k := fun x hx => MulAction.mem_stabilizer_iff.2 (hfix x hx)
  set P : Subgroup (GL (Fin k) K) := (N.subgroupOf (Stab k)).map (rho k) with hP
  have hP2 : IsPGroup 2 P := by
    rintro ⟨p, hp⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    obtain ⟨j, hj⟩ := hpow _ (Subgroup.mem_subgroupOf.1 hx)
    refine ⟨j, Subtype.ext ?_⟩
    have hj' : x ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj)
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hj', map_one]
  have hPn : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ p ∈ P,
      ((tvU z : SUid frob k) : GL (Fin k) K)⁻¹ * p * (tvU z : SUid frob k) ∈ P := by
    intro z hz0 hz p hp
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
    have hvz : herm frob (v₀ k) (ι k z) = 0 := herm_v₀_ι z
    have hρt : rho k ⟨tvU (ι k z), tvU_mem_Stab hz' hvz⟩ =
        ((tvU z : SUid frob k) : GL (Fin k) K) := by
      have := rho_tvU hz' hvz
      rwa [π_ι] at this
    rw [← hρt, ← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, tvU_inv hz']
    exact hnorm z hz0 hz _ (Subgroup.mem_subgroupOf.1 hx)
  have hPbot := eq_bot_of_isPGroup_of_normalized hk hP2 hPn
  intro x hx
  have hmem : rho k ⟨x, hNS hx⟩ ∈ P :=
    Subgroup.mem_map.2 ⟨⟨x, hNS hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [hPbot, Subgroup.mem_bot] at hmem
  exact (rho_eq_one_iff _).1 hmem

@[expose] noncomputable def coordHom {N : Subgroup (SUid frob (k + 2))}
    (hfix : ∀ x ∈ N, x • v₀ k = v₀ k) (hρ : ∀ x ∈ N, ∀ z, π k (x • ι k z) = z) :
    N →* Multiplicative (Fin k → K) where
  toFun x := Multiplicative.ofAdd (π k ((x : SUid frob (k + 2)) • u₀ k))
  map_one' := by simp [π_u₀]
  map_mul' x y := by
    rw [← ofAdd_add]
    congr 1
    exact S12InspPSU.pi_mul_smul_u₀ (hfix x x.2) (hρ x x.2) (hfix y y.2)

theorem coordHom_apply {N : Subgroup (SUid frob (k + 2))}
    (hfix : ∀ x ∈ N, x • v₀ k = v₀ k) (hρ : ∀ x ∈ N, ∀ z, π k (x • ι k z) = z) (x : N) :
    Multiplicative.toAdd (coordHom hfix hρ x) = π k ((x : SUid frob (k + 2)) • u₀ k) := rfl

theorem card_map_of_injOn {A B : Type*} [Group A] [Group B] (f : A →* B) (H : Subgroup A)
    (hinj : ∀ x ∈ H, f x = 1 → x = 1) : Nat.card (H.map f) = Nat.card H := by
  have hfinj : Function.Injective (f.comp H.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).mpr (Subtype.ext (hinj x x.2 hx))
  have hr : H.map f = (f.comp H.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm

theorem tvU_v₀_ne_one : tvU (v₀ k) ≠ 1 := by
  intro h
  have h1 := tvU_smul (herm_v₀_v₀ (n := k)) (u₀ k)
  rw [h, one_smul, herm_v₀_u₀, one_smul] at h1
  exact v₀_ne_zero (by simpa using h1)

theorem card_eq_of_normalized (hk : 2 ≤ k) {N : Subgroup (PG (k + 2))} (hN2 : IsPGroup 2 N)
    (hcent : ∀ x ∈ N, x * tq (v₀ k) = tq (v₀ k) * x)
    (hnorm : ∀ c : PG (k + 2), c * tq (v₀ k) = tq (v₀ k) * c → ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (htN : tq (v₀ k) ∈ N) (hne : ∃ x ∈ N, x ≠ 1 ∧ x ≠ tq (v₀ k)) :
    Nat.card N = 2 ^ (2 * k + 1) := by
  have hm : 3 ≤ k + 2 := by omega
  obtain ⟨Nh, hmap, hinj⟩ := AS35U.exists_lift hm N hN2
  have hmk : ∀ x ∈ Nh, (QuotientGroup.mk x : PG (k + 2)) ∈ N := fun x hx =>
    hmap ▸ Subgroup.mem_map_of_mem _ hx
  have hpow : ∀ x ∈ Nh, ∃ j : ℕ, x ^ 2 ^ j = 1 := by
    intro x hx
    obtain ⟨j, hj⟩ := hN2 ⟨_, hmk x hx⟩
    refine ⟨j, hinj _ (Nh.pow_mem hx _) ?_⟩
    rw [map_pow]
    exact congrArg Subtype.val hj
  have hfix : ∀ x ∈ Nh, x • v₀ k = v₀ k := fun x hx =>
    smul_v₀_of_commute hk (hpow x hx) (hcent _ (hmk x hx))
  have hconj : ∀ c : SUid frob (k + 2), (QuotientGroup.mk c : PG (k + 2)) * tq (v₀ k) =
      tq (v₀ k) * QuotientGroup.mk c → ∀ x ∈ Nh, c * x * c⁻¹ ∈ Nh := by
    intro c hc x hx
    have h1 : (QuotientGroup.mk' (Subgroup.center (SUid frob (k + 2)))) (c * x * c⁻¹) ∈ N := by
      rw [map_mul, map_mul, map_inv]
      exact hnorm _ hc _ (hmk x hx)
    rw [← hmap] at h1
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 h1
    have hw2 : ∃ j : ℕ, (c * x * c⁻¹) ^ 2 ^ j = 1 := by
      obtain ⟨j, hj⟩ := hpow x hx
      exact ⟨j, by rw [conj_pow, hj, mul_one, mul_inv_cancel]⟩
    rw [← eq_of_mk_eq hm (hpow y hy) hw2 hyw]
    exact hy
  have hnormv : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ Nh,
      tvU (ι k z) * x * tvU (ι k z) ∈ Nh := by
    intro z hz0 hz x hx
    have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
    have := hconj (tvU (ι k z)) (AS35L.tq_ι_mul_tq_v₀ hz) x hx
    rwa [tvU_inv hz'] at this
  have hρ := rho_trivial hk hfix hpow hnormv
  have htv : tvU (v₀ k) ∈ Nh := by
    rw [← hmap] at htN
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.1 htN
    have h2 : ∃ j : ℕ, tvU (v₀ k) ^ 2 ^ j = 1 :=
      ⟨1, by rw [pow_one, sq]; exact tvU_mul_self herm_v₀_v₀⟩
    rw [← eq_of_mk_eq hm (hpow y hy) h2 hyt]
    exact hy
  set d := coordHom hfix hρ with hd
  have hker : ∀ x : Nh, d x = 1 → (x : SUid frob (k + 2)) = 1 ∨
      (x : SUid frob (k + 2)) = tvU (v₀ k) := by
    intro x hx
    have h0 : π k ((x : SUid frob (k + 2)) • u₀ k) = 0 := by
      rw [← coordHom_apply hfix hρ x, ← hd, hx, toAdd_one]
    refine S12InspPSU.eq_one_or_eq_tvU_of_fix (hfix x x.2) fun y => ?_
    rw [S12InspPSU.smul_ι_eq_of_rho (hfix x x.2) (hρ x x.2), h0, herm_zero_left, zero_smul,
      add_zero]
  set t : Nh := ⟨tvU (v₀ k), htv⟩ with ht
  have hdt : d t = 1 := by
    apply Multiplicative.toAdd.injective
    rw [hd, coordHom_apply, toAdd_one, ht, tvU_smul herm_v₀_v₀, herm_v₀_u₀, one_smul, map_add,
      π_u₀, π_v₀, add_zero]
  have hkerz : d.ker = Subgroup.zpowers t := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      rcases hker x hx with h | h
      · rw [show x = 1 from Subtype.ext h]
        exact one_mem _
      · rw [show x = t from Subtype.ext h]
        exact Subgroup.mem_zpowers t
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [map_zpow, hdt, _root_.one_zpow]
  have hcardker : Nat.card d.ker = 2 := by
    rw [hkerz, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact tvU_mul_self herm_v₀_v₀)
    · intro h
      exact tvU_v₀_ne_one (congrArg Subtype.val h)
  set U : AddSubgroup (Fin k → K) := Subgroup.toAddSubgroup' d.range with hU
  have hmemU : ∀ x ∈ Nh, π k (x • u₀ k) ∈ U := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hUmem : ∀ a ∈ U, ∃ x ∈ Nh, π k (x • u₀ k) = a := by
    rintro a ⟨x, hx⟩
    exact ⟨x, x.2, congrArg Multiplicative.toAdd hx⟩
  have hUtv : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ a ∈ U, tvU z • a ∈ U := by
    intro z hz0 hz a ha
    obtain ⟨x, hx, rfl⟩ := hUmem a ha
    rw [← S12InspPSU.pi_conj_smul_u₀ hz x (hfix x hx)]
    exact hmemU _ (hnormv z hz0 hz x hx)
  obtain ⟨a, haU, ha0⟩ : ∃ a ∈ U, a ≠ 0 := by
    obtain ⟨x, hx, hx1, hxt⟩ := hne
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨_, hmemU y hy, fun h0 => ?_⟩
    have hdy : d ⟨y, hy⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hd, coordHom_apply, toAdd_one]
      exact h0
    rcases hker _ hdy with h | h
    · exact hx1 (by rw [show y = 1 from h, map_one])
    · exact hxt (by rw [show y = tvU (v₀ k) from h]; rfl)
  have hUtop : ∀ v : Fin k → K, v ∈ U := by
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · obtain rfl : k = 2 := by omega
      have hω : ∀ b ∈ U, ω • b ∈ U := by
        intro b hb
        obtain ⟨x, hx, rfl⟩ := hUmem b hb
        rw [← AS35L.pi_conj_sω_smul_u₀ (hfix x hx)]
        exact hmemU _ (hconj AS35L.sω AS35L.sω_mem_centralizer x hx)
      exact mem_of_iso_two hω hUtv haU ha0
    ·
      obtain ⟨z, hz, hza⟩ : ∃ z : Fin k → K, herm frob z z = 0 ∧ herm frob z a ≠ 0 := by
        by_contra h
        push Not at h
        exact ha0 (eq_zero_of_forall_isotropic hk h)
      have hz0 : z ≠ 0 := by
        rintro rfl
        exact hza (herm_zero_left frob _)
      have hy₀U : herm frob z a • z ∈ U := by
        have h1 := add_mem (hUtv z hz0 hz a haU) haU
        have e : tvU z • a + a = herm frob z a • z := by
          rw [tvU_smul hz, add_comm, ← add_assoc, ← two_smul K a, two_eq_zero, zero_smul,
            zero_add]
        rwa [e] at h1
      have hy₀0 : herm frob z a • z ≠ 0 := smul_ne_zero hza hz0
      have hy₀iso : herm frob (herm frob z a • z) (herm frob z a • z) = 0 :=
        herm_smul_smul_self hz _
      have hUT : ∀ g ∈ T frob k, ∀ b ∈ U, g • b ∈ U := by
        intro g hg
        rw [T_eq_closure_tvU] at hg
        refine (Subgroup.closure_induction
          (p := fun g _ => (∀ b ∈ U, g • b ∈ U) ∧ ∀ b ∈ U, g⁻¹ • b ∈ U) ?_ ?_ ?_ ?_ hg).1
        · rintro _ ⟨v, hv0, hv, rfl⟩
          refine ⟨hUtv v hv0 hv, ?_⟩
          rw [tvU_inv hv]
          exact hUtv v hv0 hv
        · exact ⟨fun b hb => by rwa [one_smul], fun b hb => by rwa [inv_one, one_smul]⟩
        · intro x y _ _ hx hy
          refine ⟨fun b hb => ?_, fun b hb => ?_⟩
          · rw [mul_smul]
            exact hx.1 _ (hy.1 b hb)
          · rw [_root_.mul_inv_rev, mul_smul]
            exact hy.2 _ (hx.2 b hb)
        · intro x _ hx
          exact ⟨hx.2, fun b hb => by rw [inv_inv]; exact hx.1 b hb⟩
      refine mem_of_forall_isotropic hk fun y hy => ?_
      by_cases hy0 : y = 0
      · rw [hy0]
        exact zero_mem _
      obtain ⟨g, hg, hgy⟩ :=
        exists_mem_T_smul_eq_of_iso isUnitaryInvolution_frob hk3 hy₀0 hy₀iso hy0 hy
      rw [← hgy]
      exact hUT g hg _ hy₀U
  have hrange : d.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact hUtop (Multiplicative.toAdd x)
  have h1 : Nat.card d.ker * Nat.card d.range = Nat.card Nh := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hcardK : Nat.card (Multiplicative (Fin k → K)) = 4 ^ k := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, card_K, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num
  rw [hrange, Subgroup.card_top, hcardK, hcardker] at h1
  have h2 : Nat.card N = Nat.card Nh := by
    rw [← hmap]
    exact card_map_of_injOn _ Nh hinj
  rw [h2, ← h1, pow_succ, pow_mul]
  norm_num
  ring

end CFSG.LargeExtraspecial.AS35YF
