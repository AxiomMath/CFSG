module

public import CFSG.LargeExtraspecial.S12InspPSULoc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35L

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary CFSG.LargeExtraspecial.S12InspPSU
open CFSG.Blueprint.Fischer (K)

variable {k : ℕ}

theorem eq_one_or_eq_of_normalized_omega (hk : 2 ≤ k) {N : Subgroup (SUid frob (k + 2))}
    (hfix : ∀ x ∈ N, x • v₀ k = v₀ k) (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hsq : ∀ x ∈ N, x * x = 1)
    (hnorm : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ N,
      tvU (ι k z) * x * tvU (ι k z) ∈ N)
    (hω : ∀ x ∈ N, ∃ x' ∈ N, π k (x' • u₀ k) = ω • π k (x • u₀ k)) :
    ∀ x ∈ N, x = 1 ∨ x = tvU (v₀ k) := by
  have hNS : N ≤ Stab k := fun x hx => MulAction.mem_stabilizer_iff.2 (hfix x hx)
  set P : Subgroup (GL (Fin k) K) := (N.subgroupOf (Stab k)).map (rho k) with hP
  have hP2 : IsPGroup 2 P := by
    rintro ⟨p, hp⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    refine ⟨1, Subtype.ext ?_⟩
    have hx2 : x * x = 1 := Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.1 hx))
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [sq, ← map_mul, hx2, map_one]
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
  have hρ : ∀ x ∈ N, ∀ z, π k (x • ι k z) = z := by
    intro x hx
    have hmem : rho k ⟨x, hNS hx⟩ ∈ P :=
      Subgroup.mem_map.2 ⟨⟨x, hNS hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [hPbot, Subgroup.mem_bot] at hmem
    exact (rho_eq_one_iff _).1 hmem
  set U : Set (Fin k → K) := {d | ∃ x ∈ N, π k (x • u₀ k) = d} with hU
  have hUadd : ∀ a ∈ U, ∀ b ∈ U, a + b ∈ U := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, N.mul_mem hx hy, pi_mul_smul_u₀ (hfix x hx) (hρ x hx) (hfix y hy)⟩
  have hUtv : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ a ∈ U, tvU z • a ∈ U := by
    rintro z hz0 hz _ ⟨x, hx, rfl⟩
    exact ⟨_, hnorm z hz0 hz x hx, pi_conj_smul_u₀ hz x (hfix x hx)⟩
  have hUherm : ∀ a ∈ U, ∀ b ∈ U, herm frob a b = herm frob b a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact herm_comm_of_commute (hfix x hx) (hρ x hx) (hfix y hy) (hρ y hy) (hcomm x hx y hy)
  have hUω : ∀ a ∈ U, ω • a ∈ U := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', he⟩ := hω x hx
    exact ⟨x', hx', he⟩
  have hiso : ∀ a ∈ U, a ≠ 0 → ∃ y ∈ U, y ≠ 0 ∧ herm frob y y = 0 ∧
      ∃ z : Fin k → K, herm frob z z = 0 ∧ y = herm frob z a • z ∧ herm frob z a ≠ 0 := by
    intro a ha ha0
    obtain ⟨z, hz, hza⟩ : ∃ z : Fin k → K, herm frob z z = 0 ∧ herm frob z a ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (eq_zero_of_forall_isotropic hk h)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hza (herm_zero_left frob _)
    refine ⟨herm frob z a • z, ?_, smul_ne_zero hza hz0, herm_smul_smul_self hz _, z, hz, rfl,
      hza⟩
    have h1 := hUadd _ (hUtv z hz0 hz a ha) a ha
    have e : tvU z • a + a = herm frob z a • z := by
      rw [tvU_smul hz, add_comm, ← add_assoc, ← two_smul K a, two_eq_zero, zero_smul, zero_add]
    rwa [e] at h1
  have hU0 : ∀ x ∈ N, π k (x • u₀ k) = 0 := by
    intro x hx
    by_contra hd
    obtain ⟨y₀, hy₀U, hy₀0, hy₀, -⟩ := hiso _ ⟨x, hx, rfl⟩ hd
    obtain ⟨y₁, hy₁U, -, -, z', hz', rfl, hz'y⟩ := hiso y₀ hy₀U hy₀0
    have h1 : herm frob y₀ (herm frob z' y₀ • z') = 1 := by
      rw [herm_smul_right, herm_conj frob frob_frob z' y₀, mul_comm]
      exact frob_mul_self hz'y
    have h2 := hUherm _ hy₀U _ (hUω _ hy₁U)
    rw [herm_smul_right, h1, herm_smul_left, herm_conj frob frob_frob y₀, h1, map_one, mul_one,
      mul_one, frob_omega] at h2
    exact one_ne_zero (by linear_combination -h2 : (1 : K) = 0)
  intro x hx
  refine eq_one_or_eq_tvU_of_fix (hfix x hx) fun y => ?_
  rw [smul_ι_eq_of_rho (hfix x hx) (hρ x hx), hU0 x hx, herm_zero_left, zero_smul, add_zero]

@[expose] noncomputable def sDiag : Fin (2 + 2) → K :=
  Fin.cons ω (Fin.cons ω (fun _ => frob ω : Fin 2 → K) : Fin (2 + 1) → K)

theorem frob_sDiag_mul (i : Fin (2 + 2)) : frob (sDiag i) * sDiag i = 1 := by
  have h1 : frob ω * ω = 1 := frob_mul_self omega_ne_zero
  have h2 : frob (frob ω) * frob ω = 1 := frob_mul_self (frob_ne_zero omega_ne_zero)
  cases i using Fin.cases with
  | zero => exact h1
  | succ j =>
    cases j using Fin.cases with
    | zero => exact h1
    | succ j => exact h2

theorem det_diagonal_sDiag : (diagonal sDiag).det = 1 := by
  rw [det_diagonal, Fin.prod_univ_four]
  change ω * ω * frob ω * frob ω = 1
  have h1 : frob ω * ω = 1 := frob_mul_self omega_ne_zero
  linear_combination (ω * frob ω + 1) * h1

theorem herm_diagonal_sDiag (x y : Fin (2 + 2) → K) :
    herm frob (diagonal sDiag *ᵥ x) (diagonal sDiag *ᵥ y) = herm frob x y := by
  simp only [herm_def, mulVec_diagonal, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show frob (sDiag i) * frob (x i) * (sDiag i * y i) =
    (frob (sDiag i) * sDiag i) * (frob (x i) * y i) by ring, frob_sDiag_mul, one_mul]

@[expose] noncomputable def sω : SUid frob (2 + 2) :=
  mkSU frob (diagonal sDiag) det_diagonal_sDiag herm_diagonal_sDiag

theorem sω_smul_of_pi {v : Fin (2 + 2) → K} (hv : π 2 v = 0) : sω • v = ω • v := by
  rw [sω, mkSU_smul]
  funext i
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      have h : v j.succ.succ = 0 := congrFun hv j
      rw [h, mul_zero, mul_zero]

theorem sω_smul_v₀ : sω • v₀ 2 = ω • v₀ 2 := sω_smul_of_pi π_v₀

theorem sω_smul_u₀ : sω • u₀ 2 = ω • u₀ 2 := sω_smul_of_pi π_u₀

theorem sω_smul_ι (z : Fin 2 → K) : sω • ι 2 z = frob ω • ι 2 z := by
  rw [sω, mkSU_smul]
  funext i
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  cases i using Fin.cases with
  | zero => rw [ι_apply_zero, mul_zero, mul_zero]
  | succ j =>
    cases j using Fin.cases with
    | zero => rw [show ι 2 z (Fin.succ 0) = 0 from rfl, mul_zero, mul_zero]
    | succ j => rfl

theorem sω_inv_smul_u₀ : sω⁻¹ • u₀ 2 = ω⁻¹ • u₀ 2 := by
  rw [inv_smul_eq_iff, smul_comm, sω_smul_u₀, smul_smul, inv_mul_cancel₀ omega_ne_zero, one_smul]

theorem pi_conj_sω_smul_u₀ {x : SUid frob (2 + 2)} (hx : x • v₀ 2 = v₀ 2) :
    π 2 ((sω * x * sω⁻¹) • u₀ 2) = ω • π 2 (x • u₀ 2) := by
  set α := herm frob (u₀ 2) (x • u₀ 2)
  set d := π 2 (x • u₀ 2)
  have h1 : sω • (x • u₀ 2) = (α * ω) • v₀ 2 + ω • u₀ 2 + frob ω • ι 2 d := by
    rw [smul_u₀_eq hx, smul_add, smul_add, smul_comm sω α (v₀ 2), sω_smul_v₀, sω_smul_u₀,
      sω_smul_ι, smul_smul]
  have h2 : (sω * x * sω⁻¹) • u₀ 2 = ω⁻¹ • (sω • (x • u₀ 2)) := by
    rw [mul_smul, mul_smul, sω_inv_smul_u₀, smul_comm x ω⁻¹, smul_comm sω ω⁻¹]
  rw [h2, h1]
  simp only [map_smul, map_add, π_v₀, π_u₀, π_ι, smul_zero, zero_add, smul_smul]
  congr 1
  rw [inv_mul_eq_iff_eq_mul₀ omega_ne_zero, frob_apply, sq]

theorem sω_mem_centralizer :
    (QuotientGroup.mk sω : PG (2 + 2)) * tq (v₀ 2) = tq (v₀ 2) * QuotientGroup.mk sω := by
  have h := conj_tq sω (herm_v₀_v₀ (n := 2))
  rw [sω_smul_v₀, show tq (ω • v₀ 2) = tq (v₀ 2) from
    congrArg QuotientGroup.mk (tvU_smul_vec herm_v₀_v₀ omega_ne_zero)] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem exists_lift_facts {N : Subgroup (PG (k + 2))} (hk : 1 ≤ k)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hsq : ∀ x ∈ N, x * x = 1)
    (hcent : ∀ x ∈ N, x * tq (v₀ k) = tq (v₀ k) * x) :
    ∃ Nh : Subgroup (SUid frob (k + 2)),
      Nh.map (QuotientGroup.mk' (Subgroup.center (SUid frob (k + 2)))) = N ∧
      (∀ x ∈ Nh, x * x = 1) ∧ (∀ x ∈ Nh, ∀ y ∈ Nh, x * y = y * x) ∧
      (∀ x ∈ Nh, x • v₀ k = v₀ k) ∧
      ∀ c : SUid frob (k + 2), (∀ x ∈ N, (QuotientGroup.mk c : PG (k + 2)) * x *
        (QuotientGroup.mk c)⁻¹ ∈ N) → ∀ x ∈ Nh, c * x * c⁻¹ ∈ Nh := by
  have hm : 3 ≤ k + 2 := by omega
  have hN2 : IsPGroup 2 N := fun x => ⟨1, Subtype.ext (by
    simp only [pow_one, Subgroup.coe_one, sq]
    exact hsq _ x.2)⟩
  obtain ⟨Nh, hmap, hinj⟩ := AS35U.exists_lift hm N hN2
  set f := QuotientGroup.mk' (Subgroup.center (SUid frob (k + 2))) with hf
  have hmk : ∀ x ∈ Nh, f x ∈ N := fun x hx => hmap ▸ Subgroup.mem_map_of_mem f hx
  have hsq' : ∀ x ∈ Nh, x * x = 1 := fun x hx =>
    hinj _ (Nh.mul_mem hx hx) (by rw [map_mul]; exact hsq _ (hmk x hx))
  have hcomm' : ∀ x ∈ Nh, ∀ y ∈ Nh, x * y = y * x := by
    intro x hx y hy
    have h := hinj (x * y * (y * x)⁻¹)
      (Nh.mul_mem (Nh.mul_mem hx hy) (Nh.inv_mem (Nh.mul_mem hy hx)))
      (by rw [map_mul, map_inv, map_mul, map_mul, hcomm _ (hmk x hx) _ (hmk y hy),
        mul_inv_cancel])
    exact mul_inv_eq_one.mp h
  refine ⟨Nh, hmap, hsq', hcomm', ?_, ?_⟩
  · intro x hx
    have h1 : tq (x • v₀ k) = tq (v₀ k) := by
      rw [← conj_tq x herm_v₀_v₀, show (QuotientGroup.mk x : PG (k + 2)) = f x from rfl,
        hcent _ (hmk x hx), mul_inv_cancel_right]
    have hx0 : x • v₀ k ≠ 0 := (smul_ne_zero_iff_ne x).2 v₀_ne_zero
    obtain ⟨c, hc⟩ := (tq_eq_tq_iff hm hx0 (by rw [herm_smul_smul, herm_v₀_v₀]) v₀_ne_zero
      herm_v₀_v₀).1 h1
    have h2 : x • v₀ k = c • v₀ k := by
      have : x • v₀ k = x • (c • (x • v₀ k)) := congrArg (x • ·) hc
      rw [smul_comm x c (x • v₀ k), ← mul_smul, hsq' x hx, one_smul] at this
      exact this
    have h3 : v₀ k = (c * c) • v₀ k := by
      rw [mul_smul, ← h2]
      exact hc
    have hc1 : c * c = 1 := by
      have h4 : (c * c - 1) • v₀ k = 0 := by rw [sub_smul, ← h3, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_right v₀_ne_zero)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hc1
      exact zero_ne_one hc1
    have hc3 : c = 1 := by
      have h5 := frob_mul_self hc0
      rw [frob_apply] at h5
      linear_combination h5 - c * hc1
    rw [h2, hc3, one_smul]
  · intro c hc x hx
    set w := c * x * c⁻¹ with hw
    have hfw : f w ∈ N := by
      rw [hw, map_mul, map_mul, map_inv]
      exact hc _ (hmk x hx)
    rw [← hmap] at hfw
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 hfw
    have hζ : y⁻¹ * w ∈ Subgroup.center (SUid frob (k + 2)) := QuotientGroup.eq.1 hyw
    have hww : w * w = 1 := by
      rw [hw, show c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ by group, hsq' x hx,
        mul_one, mul_inv_cancel]
    have hyy := hsq' y hy
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    have hζc : ∀ g, (y⁻¹ * w) * g = g * (y⁻¹ * w) := fun g =>
      ((Subgroup.mem_center_iff.1 hζ) g).symm
    have hζ2 : (y⁻¹ * w) ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq]
      calc (y⁻¹ * w) * (y⁻¹ * w) = ((y⁻¹ * w) * y⁻¹) * w := by group
        _ = (y⁻¹ * (y⁻¹ * w)) * w := by rw [hζc y⁻¹]
        _ = (y⁻¹ * y⁻¹) * (w * w) := by group
        _ = 1 := by rw [hww, hyinv, hyy, mul_one]
    have hζ1 := AS35U.eq_one_of_mem_center hm hζ hζ2
    have hwy : w = y := by rw [← mul_inv_cancel_left y w, hζ1, mul_one]
    rw [hwy]
    exact hy

theorem tq_ι_mul_tq_v₀ {z : Fin k → K} (hz : herm frob z z = 0) :
    tq (ι k z) * tq (v₀ k) = tq (v₀ k) * tq (ι k z) := by
  have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
  rw [← QuotientGroup.mk_mul, tvU_commute hz' herm_v₀_v₀ (herm_ι_v₀ z), QuotientGroup.mk_mul]

theorem eq_one_or_eq_tq_of_normalized_cent (hk : 2 ≤ k) {N : Subgroup (PG (k + 2))}
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hsq : ∀ x ∈ N, x * x = 1)
    (hcent : ∀ x ∈ N, x * tq (v₀ k) = tq (v₀ k) * x)
    (hnorm : ∀ c : PG (k + 2), c * tq (v₀ k) = tq (v₀ k) * c → ∀ x ∈ N, c * x * c⁻¹ ∈ N) :
    ∀ x ∈ N, x = 1 ∨ x = tq (v₀ k) := by
  have hτ : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ N,
      tq (ι k z) * x * tq (ι k z) ∈ N := by
    intro z _ hz x hx
    have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
    have h := hnorm _ (tq_ι_mul_tq_v₀ hz) x hx
    rwa [inv_eq_of_mul_eq_one_right (tq_mul_self hz')] at h
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · obtain rfl : k = 2 := by omega
    obtain ⟨Nh, hmap, hsq', hcomm', hfix', hconj⟩ :=
      exists_lift_facts (by norm_num) hcomm hsq hcent
    have hnorm' : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ Nh,
        tvU (ι 2 z) * x * tvU (ι 2 z) ∈ Nh := by
      intro z hz0 hz
      have hz' : herm frob (ι 2 z) (ι 2 z) = 0 := by rw [herm_ι_ι, hz]
      have e : (QuotientGroup.mk (tvU (ι 2 z)) : PG (2 + 2))⁻¹ = tq (ι 2 z) :=
        inv_eq_of_mul_eq_one_right (tq_mul_self hz')
      have h := hconj (tvU (ι 2 z)) (fun x hx => by
        rw [e]
        exact hτ z hz0 hz x hx)
      intro x hx
      have := h x hx
      rwa [tvU_inv hz'] at this
    have hω : ∀ x ∈ Nh, ∃ x' ∈ Nh, π 2 (x' • u₀ 2) = ω • π 2 (x • u₀ 2) := by
      intro x hx
      exact ⟨_, hconj sω (hnorm _ sω_mem_centralizer) x hx, pi_conj_sω_smul_u₀ (hfix' x hx)⟩
    have key := eq_one_or_eq_of_normalized_omega le_rfl hfix' hcomm' hsq' hnorm' hω
    intro x hx
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rcases key y hy with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
      rfl
  · exact S12InspPSU.eq_one_or_eq_tq_of_normalized hk3 hcomm hsq hcent hτ

theorem mul_comm_of_mul_self {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y * (x * y) = 1) : x * y = y * x := by
  have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [← h1, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]

theorem eq_one_or_eq_of_normalized_DG (hk : 2 ≤ k) {d : PG (k + 2)} (hd : d ∈ DG (k + 2))
    {W : Subgroup (PG (k + 2))} (hW2 : ∀ w ∈ W, w * w = 1) (hdW : d ∈ W)
    (hWn : ∀ c : PG (k + 2), c * d = d * c → ∀ w ∈ W, c * w * c⁻¹ ∈ W) :
    ∀ w ∈ W, w = 1 ∨ w = d := by
  have hcls := DG_eq_isConj (by omega : 3 ≤ k + 2) (v₀_ne_zero (n := k)) herm_v₀_v₀
  rw [hcls] at hd
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 (show IsConj (tq (v₀ k)) d from hd)
  set N := W.map (MulAut.conj c₀⁻¹).toMonoidHom with hN
  have hmemN : ∀ x, x ∈ N ↔ c₀ * x * c₀⁻¹ ∈ W := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hw
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    mul_comm_of_mul_self (hW2 a ha) (hW2 b hb) (hW2 _ (W.mul_mem ha hb))
  have hsq : ∀ x ∈ N, x * x = 1 := by
    intro x hx
    have h := hW2 _ ((hmemN x).1 hx)
    have e : c₀ * x * c₀⁻¹ * (c₀ * x * c₀⁻¹) = c₀ * (x * x) * c₀⁻¹ := by group
    rw [e] at h
    calc x * x = c₀⁻¹ * (c₀ * (x * x) * c₀⁻¹) * c₀ := by group
      _ = 1 := by rw [h]; group
  have hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mul_self (hsq x hx) (hsq y hy) (hsq _ (N.mul_mem hx hy))
  have hτ : tq (v₀ k) = c₀⁻¹ * d * c₀ := by rw [← hc₀]; group
  have hcent : ∀ x ∈ N, x * tq (v₀ k) = tq (v₀ k) * x := by
    intro x hx
    have h := hWcomm _ ((hmemN x).1 hx) d hdW
    rw [hτ]
    calc x * (c₀⁻¹ * d * c₀) = c₀⁻¹ * ((c₀ * x * c₀⁻¹) * d) * c₀ := by group
      _ = c₀⁻¹ * (d * (c₀ * x * c₀⁻¹)) * c₀ := by rw [h]
      _ = c₀⁻¹ * d * c₀ * x := by group
  have hnorm : ∀ c : PG (k + 2), c * tq (v₀ k) = tq (v₀ k) * c → ∀ x ∈ N, c * x * c⁻¹ ∈ N := by
    intro c hc x hx
    have hc' : (c₀ * c * c₀⁻¹) * d = d * (c₀ * c * c₀⁻¹) := by
      rw [hτ] at hc
      calc c₀ * c * c₀⁻¹ * d = c₀ * (c * (c₀⁻¹ * d * c₀)) * c₀⁻¹ := by group
        _ = c₀ * ((c₀⁻¹ * d * c₀) * c) * c₀⁻¹ := by rw [hc]
        _ = d * (c₀ * c * c₀⁻¹) := by group
    have h := hWn _ hc' _ ((hmemN x).1 hx)
    rw [hmemN]
    rw [show c₀ * (c * x * c⁻¹) * c₀⁻¹ =
      c₀ * c * c₀⁻¹ * (c₀ * x * c₀⁻¹) * (c₀ * c * c₀⁻¹)⁻¹ by group]
    exact h
  have key := eq_one_or_eq_tq_of_normalized_cent hk hcomm hsq hcent hnorm
  intro w hw
  have hwN : c₀⁻¹ * w * c₀ ∈ N := by
    rw [hmemN]
    simpa [mul_assoc] using hw
  rcases key _ hwN with h | h
  · left
    calc w = c₀ * (c₀⁻¹ * w * c₀) * c₀⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc w = c₀ * (c₀⁻¹ * w * c₀) * c₀⁻¹ := by group
      _ = d := by rw [h, ← hc₀]

end CFSG.LargeExtraspecial.AS35L
