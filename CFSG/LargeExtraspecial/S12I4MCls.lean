module

public import CFSG.LargeExtraspecial.S12InspPSULoc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12I4M

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary CFSG.LargeExtraspecial.S12InspPSU
open CFSG.Blueprint.Fischer (K)

theorem herm_lin (c c' : K) (d d' : Fin 2 → K) :
    herm frob (c • v₀ 2 + ι 2 d) (c' • v₀ 2 + ι 2 d') = herm frob d d' := by
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_v₀_v₀,
    herm_v₀_ι, herm_ι_v₀, herm_ι_ι, mul_zero, zero_add, add_zero]

theorem herm_lin_v₀ (c : K) (d : Fin 2 → K) : herm frob (c • v₀ 2 + ι 2 d) (v₀ 2) = 0 := by
  simp only [herm_add_left, herm_smul_left, herm_v₀_v₀, herm_ι_v₀, mul_zero, add_zero]

theorem herm_v₀_lin (c : K) (d : Fin 2 → K) : herm frob (v₀ 2) (c • v₀ 2 + ι 2 d) = 0 := by
  simp only [herm_add_right, herm_smul_right, herm_v₀_v₀, herm_v₀_ι, mul_zero, add_zero]

theorem herm_lin_ι (c : K) (d z : Fin 2 → K) :
    herm frob (c • v₀ 2 + ι 2 d) (ι 2 z) = herm frob d z := by
  simp only [herm_add_left, herm_smul_left, herm_v₀_ι, herm_ι_ι, mul_zero, zero_add]

theorem herm_lin_u₀ (c : K) (d : Fin 2 → K) : herm frob (c • v₀ 2 + ι 2 d) (u₀ 2) = frob c := by
  simp only [herm_add_left, herm_smul_left, herm_v₀_u₀, herm_ι_u₀, mul_one, add_zero]

theorem isotropic_lin {d : Fin 2 → K} (hd : herm frob d d = 0) (c : K) :
    herm frob (c • v₀ 2 + ι 2 d) (c • v₀ 2 + ι 2 d) = 0 := by
  rw [herm_lin, hd]

@[expose] noncomputable def sU (d : Fin 2 → K) : SUid frob 4 :=
  tvU (ω • v₀ 2 + ι 2 d) * tvU (frob ω • v₀ 2 + ι 2 d)

variable {d : Fin 2 → K}

theorem sU_smul_v₀ (hd : herm frob d d = 0) : sU d • v₀ 2 = v₀ 2 := by
  rw [sU, mul_smul, tvU_smul_of_herm_eq_zero (isotropic_lin hd _) (herm_lin_v₀ _ _),
    tvU_smul_of_herm_eq_zero (isotropic_lin hd _) (herm_lin_v₀ _ _)]

theorem sU_smul_ι (hd : herm frob d d = 0) (z : Fin 2 → K) :
    sU d • ι 2 z = ι 2 z + herm frob d z • v₀ 2 := by
  rw [sU, mul_smul, tvU_smul (isotropic_lin hd (frob ω)) (ι 2 z), herm_lin_ι,
    tvU_smul (isotropic_lin hd ω), herm_add_right, herm_lin_ι, herm_smul_right, herm_lin, hd,
    mul_zero, add_zero]
  have hab : herm frob d z • (frob ω • v₀ 2 + ι 2 d) + herm frob d z • (ω • v₀ 2 + ι 2 d) =
      herm frob d z • v₀ 2 := by
    calc herm frob d z • (frob ω • v₀ 2 + ι 2 d) + herm frob d z • (ω • v₀ 2 + ι 2 d) =
        (herm frob d z * (ω + frob ω)) • v₀ 2 + (herm frob d z + herm frob d z) • ι 2 d := by
          module
      _ = herm frob d z • v₀ 2 := by rw [omega_add_frob, mul_one, add_self_K, zero_smul, add_zero]
  rw [add_assoc, hab]

theorem sU_smul_u₀ (hd : herm frob d d = 0) : sU d • u₀ 2 = u₀ 2 + ι 2 d := by
  rw [sU, mul_smul, tvU_smul (isotropic_lin hd (frob ω)) (u₀ 2), herm_lin_u₀, frob_frob,
    tvU_smul (isotropic_lin hd ω), herm_add_right, herm_lin_u₀, herm_smul_right, herm_lin, hd,
    mul_zero, add_zero]
  have hab : ω • (frob ω • v₀ 2 + ι 2 d) + frob ω • (ω • v₀ 2 + ι 2 d) = ι 2 d := by
    calc ω • (frob ω • v₀ 2 + ι 2 d) + frob ω • (ω • v₀ 2 + ι 2 d) =
        (ω * frob ω + ω * frob ω) • v₀ 2 + (ω + frob ω) • ι 2 d := by module
      _ = ι 2 d := by rw [add_self_K, zero_smul, zero_add, omega_add_frob, one_smul]
  rw [add_assoc, hab]

theorem sU_mul_self (hd : herm frob d d = 0) : sU d * sU d = 1 := by
  have hc := tvU_commute (isotropic_lin hd ω) (isotropic_lin hd (frob ω))
    (by rw [herm_lin, hd])
  rw [sU, show tvU (ω • v₀ 2 + ι 2 d) * tvU (frob ω • v₀ 2 + ι 2 d) *
      (tvU (ω • v₀ 2 + ι 2 d) * tvU (frob ω • v₀ 2 + ι 2 d)) =
      tvU (ω • v₀ 2 + ι 2 d) * (tvU (frob ω • v₀ 2 + ι 2 d) * tvU (ω • v₀ 2 + ι 2 d)) *
        tvU (frob ω • v₀ 2 + ι 2 d) by group, ← hc,
    show tvU (ω • v₀ 2 + ι 2 d) * (tvU (ω • v₀ 2 + ι 2 d) * tvU (frob ω • v₀ 2 + ι 2 d)) *
      tvU (frob ω • v₀ 2 + ι 2 d) = tvU (ω • v₀ 2 + ι 2 d) * tvU (ω • v₀ 2 + ι 2 d) *
        (tvU (frob ω • v₀ 2 + ι 2 d) * tvU (frob ω • v₀ 2 + ι 2 d)) by group,
    tvU_mul_self (isotropic_lin hd _), tvU_mul_self (isotropic_lin hd _), one_mul]

theorem eq_of_normalized_SU {N : Subgroup (SUid frob 4)}
    (hfix : ∀ x ∈ N, x • v₀ 2 = v₀ 2) (hsq : ∀ x ∈ N, x * x = 1)
    (hnorm : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ N,
      tvU (ι 2 z) * x * tvU (ι 2 z) ∈ N) :
    ∀ x ∈ N, x = 1 ∨ x = tvU (v₀ 2) ∨ ∃ d : Fin 2 → K, d ≠ 0 ∧ herm frob d d = 0 ∧
      (x = sU d ∨ x = sU d * tvU (v₀ 2)) := by
  have hNS : N ≤ Stab 2 := fun x hx => MulAction.mem_stabilizer_iff.2 (hfix x hx)
  set P : Subgroup (GL (Fin 2) K) := (N.subgroupOf (Stab 2)).map (rho 2) with hP
  have hP2 : IsPGroup 2 P := by
    rintro ⟨p, hp⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    refine ⟨1, Subtype.ext ?_⟩
    have hx2 : x * x = 1 := Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.1 hx))
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [sq, ← map_mul, hx2, map_one]
  have hPn : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 → ∀ p ∈ P,
      ((tvU z : SUid frob 2) : GL (Fin 2) K)⁻¹ * p * (tvU z : SUid frob 2) ∈ P := by
    intro z hz0 hz p hp
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    have hz' : herm frob (ι 2 z) (ι 2 z) = 0 := by rw [herm_ι_ι, hz]
    have hvz : herm frob (v₀ 2) (ι 2 z) = 0 := herm_v₀_ι z
    have hρt : rho 2 ⟨tvU (ι 2 z), tvU_mem_Stab hz' hvz⟩ =
        ((tvU z : SUid frob 2) : GL (Fin 2) K) := by
      have := rho_tvU hz' hvz
      rwa [π_ι] at this
    rw [← hρt, ← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, tvU_inv hz']
    exact hnorm z hz0 hz _ (Subgroup.mem_subgroupOf.1 hx)
  have hPbot := eq_bot_of_isPGroup_of_normalized (le_refl 2) hP2 hPn
  have hρ : ∀ x ∈ N, ∀ z, π 2 (x • ι 2 z) = z := by
    intro x hx
    have hmem : rho 2 ⟨x, hNS hx⟩ ∈ P :=
      Subgroup.mem_map.2 ⟨⟨x, hNS hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [hPbot, Subgroup.mem_bot] at hmem
    exact (rho_eq_one_iff _).1 hmem
  intro x hx
  have hxv := hfix x hx
  have hxρ := hρ x hx
  set d := π 2 (x • u₀ 2) with hd
  have hdd : herm frob d d = 0 := by
    have h := herm_u₀_mul_smul_u₀ hxv hxρ hxv
    rw [hsq x hx, one_smul, herm_u₀_u₀, add_self_K, zero_add] at h
    exact h.symm
  by_cases hd0 : d = 0
  · have hι : ∀ y, x • ι 2 y = ι 2 y := fun y => by
      rw [smul_ι_eq_of_rho hxv hxρ, ← hd, hd0, herm_zero_left, zero_smul, add_zero]
    rcases eq_one_or_eq_tvU_of_fix hxv hι with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ⟨d, hd0, hdd, ?_⟩)
  set y := sU d * x with hy
  have hyv : y • v₀ 2 = v₀ 2 := by rw [hy, mul_smul, hxv, sU_smul_v₀ hdd]
  have hyρ : ∀ z, π 2 (y • ι 2 z) = z := by
    intro z
    rw [hy, mul_smul, smul_ι_eq_of_rho hxv hxρ, ← hd, smul_add, smul_comm, sU_smul_ι hdd,
      sU_smul_v₀ hdd]
    simp only [map_add, map_smul, π_ι, π_v₀, smul_zero, add_zero]
  have hyu : π 2 (y • u₀ 2) = 0 := by
    rw [hy, mul_smul, smul_u₀_eq hxv, ← hd, smul_add, smul_add, smul_comm, sU_smul_v₀ hdd,
      sU_smul_u₀ hdd, sU_smul_ι hdd, hdd, zero_smul, add_zero]
    simp only [map_add, map_smul, π_ι, π_v₀, π_u₀, smul_zero, zero_add]
    rw [← two_smul K d, two_eq_zero, zero_smul]
  have hyι : ∀ z, y • ι 2 z = ι 2 z := fun z => by
    rw [smul_ι_eq_of_rho hyv hyρ, hyu, herm_zero_left, zero_smul, add_zero]
  have hx' : x = sU d * y := by rw [hy, ← mul_assoc, sU_mul_self hdd, one_mul]
  rcases eq_one_or_eq_tvU_of_fix hyv hyι with h | h
  · left
    rw [hx', h, mul_one]
  · right
    rw [hx', h]

theorem eq_of_normalized {N : Subgroup (PG 4)} (hsq : ∀ x ∈ N, x * x = 1)
    (hcent : ∀ x ∈ N, x * tq (v₀ 2) = tq (v₀ 2) * x)
    (hnorm : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ N,
      tq (ι 2 z) * x * tq (ι 2 z) ∈ N) :
    ∀ x ∈ N, x = 1 ∨ x = tq (v₀ 2) ∨ ∃ d : Fin 2 → K, d ≠ 0 ∧ herm frob d d = 0 ∧
      (x = tq (ω • v₀ 2 + ι 2 d) * tq (frob ω • v₀ 2 + ι 2 d) ∨
        x = tq (ω • v₀ 2 + ι 2 d) * tq (frob ω • v₀ 2 + ι 2 d) * tq (v₀ 2)) := by
  have hm : 3 ≤ 4 := by norm_num
  have hN2 : IsPGroup 2 N := fun x => ⟨1, Subtype.ext (by
    simp only [pow_one, Subgroup.coe_one, sq]
    exact hsq _ x.2)⟩
  obtain ⟨Nh, hmap, hinj⟩ := AS35U.exists_lift hm N hN2
  set f := QuotientGroup.mk' (Subgroup.center (SUid frob 4)) with hf
  have hmk : ∀ x ∈ Nh, f x ∈ N := fun x hx => hmap ▸ Subgroup.mem_map_of_mem f hx
  have hsq' : ∀ x ∈ Nh, x * x = 1 := fun x hx =>
    hinj _ (Nh.mul_mem hx hx) (by rw [map_mul]; exact hsq _ (hmk x hx))
  have hfix' : ∀ x ∈ Nh, x • v₀ 2 = v₀ 2 := by
    intro x hx
    have h1 : tq (x • v₀ 2) = tq (v₀ 2) := by
      rw [← conj_tq x herm_v₀_v₀, show (QuotientGroup.mk x : PG 4) = f x from rfl,
        hcent _ (hmk x hx), mul_inv_cancel_right]
    have hx0 : x • v₀ 2 ≠ 0 := (smul_ne_zero_iff_ne x).2 v₀_ne_zero
    obtain ⟨c, hc⟩ := (tq_eq_tq_iff hm hx0 (by rw [herm_smul_smul, herm_v₀_v₀]) v₀_ne_zero
      herm_v₀_v₀).1 h1
    have h2 : x • v₀ 2 = c • v₀ 2 := by
      have : x • v₀ 2 = x • (c • (x • v₀ 2)) := congrArg (x • ·) hc
      rw [smul_comm x c (x • v₀ 2), ← mul_smul, hsq' x hx, one_smul] at this
      exact this
    have h3 : v₀ 2 = (c * c) • v₀ 2 := by
      rw [mul_smul, ← h2]
      exact hc
    have hc1 : c * c = 1 := by
      have h4 : (c * c - 1) • v₀ 2 = 0 := by rw [sub_smul, ← h3, one_smul, sub_self]
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
  have hnorm' : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ Nh,
      tvU (ι 2 z) * x * tvU (ι 2 z) ∈ Nh := by
    intro z hz0 hz x hx
    have hz' : herm frob (ι 2 z) (ι 2 z) = 0 := by rw [herm_ι_ι, hz]
    set w := tvU (ι 2 z) * x * tvU (ι 2 z) with hw
    have hfw : f w ∈ N := by
      rw [hw, map_mul, map_mul]
      exact hnorm z hz0 hz _ (hmk x hx)
    rw [← hmap] at hfw
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 hfw
    have hζ : y⁻¹ * w ∈ Subgroup.center (SUid frob 4) := QuotientGroup.eq.1 hyw
    have hww : w * w = 1 := by
      rw [hw]
      calc tvU (ι 2 z) * x * tvU (ι 2 z) * (tvU (ι 2 z) * x * tvU (ι 2 z))
          = tvU (ι 2 z) * (x * (tvU (ι 2 z) * tvU (ι 2 z)) * x) * tvU (ι 2 z) := by group
        _ = 1 := by rw [tvU_mul_self hz', mul_one, hsq' x hx, mul_one, tvU_mul_self hz']
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
  have key := eq_of_normalized_SU hfix' hsq' hnorm'
  intro x hx
  rw [← hmap] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hs : ∀ d : Fin 2 → K, f (sU d) = tq (ω • v₀ 2 + ι 2 d) * tq (frob ω • v₀ 2 + ι 2 d) :=
    fun d => by rw [sU, map_mul]; rfl
  rcases key y hy with h | h | ⟨d, hd0, hdd, h | h⟩
  · left
    rw [h, map_one]
  · right; left
    rw [h]
    rfl
  · right; right
    exact ⟨d, hd0, hdd, Or.inl (by rw [h, hs])⟩
  · right; right
    refine ⟨d, hd0, hdd, Or.inr ?_⟩
    rw [h, map_mul, hs]
    rfl

end CFSG.LargeExtraspecial.S12I4M
