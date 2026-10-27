module

public import CFSG.Fischer.Classification.Unitary.Local
public import CFSG.LargeExtraspecial.AS35U

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

namespace S12InspPSU

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

variable {k : ℕ}

theorem herm_v₀_smul_u₀ {g : SUid frob (k + 2)} (hg : g • v₀ k = v₀ k) :
    herm frob (v₀ k) (g • u₀ k) = 1 := by
  rw [← hg, herm_smul_smul, herm_v₀_u₀]

theorem smul_u₀_eq {g : SUid frob (k + 2)} (hg : g • v₀ k = v₀ k) :
    g • u₀ k = herm frob (u₀ k) (g • u₀ k) • v₀ k + u₀ k + ι k (π k (g • u₀ k)) := by
  conv_lhs => rw [decomp (g • u₀ k)]
  rw [herm_v₀_smul_u₀ hg, one_smul]

theorem smul_ι_eq_of_rho {g : SUid frob (k + 2)} (hg : g • v₀ k = v₀ k)
    (hρ : ∀ z, π k (g • ι k z) = z) (z : Fin k → K) :
    g • ι k z = ι k z + herm frob (π k (g • u₀ k)) z • v₀ k := by
  have h1 : herm frob (v₀ k) (g • ι k z) = 0 := by rw [← hg, herm_smul_smul, herm_v₀_ι]
  set c := herm frob (u₀ k) (g • ι k z) with hc
  set d := π k (g • u₀ k) with hd
  set α := herm frob (u₀ k) (g • u₀ k) with hα
  have h2 : g • ι k z = c • v₀ k + ι k z := by
    have := decomp_of_perp h1
    rwa [hρ] at this
  have hgu : g • u₀ k = α • v₀ k + u₀ k + ι k d := smul_u₀_eq hg
  have h3 : herm frob (g • u₀ k) (g • ι k z) = 0 := by rw [herm_smul_smul, herm_u₀_ι]
  rw [h2, hgu] at h3
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_v₀_v₀,
    herm_v₀_ι, herm_u₀_v₀, herm_u₀_ι, herm_ι_v₀, herm_ι_ι, mul_zero, add_zero, zero_add,
    mul_one] at h3
  have hc' : c = herm frob d z := by
    rw [← neg_K (herm frob d z)]
    exact eq_neg_of_add_eq_zero_left h3
  rw [h2, hc']
  exact add_comm _ _

theorem mul_smul_u₀_eq {g g' : SUid frob (k + 2)} (hg : g • v₀ k = v₀ k)
    (hρ : ∀ z, π k (g • ι k z) = z) (hg' : g' • v₀ k = v₀ k) :
    (g * g') • u₀ k = herm frob (u₀ k) (g' • u₀ k) • v₀ k + g • u₀ k +
      (ι k (π k (g' • u₀ k)) + herm frob (π k (g • u₀ k)) (π k (g' • u₀ k)) • v₀ k) := by
  conv_lhs => rw [mul_smul, smul_u₀_eq hg', smul_add, smul_add, smul_comm g _ (v₀ k), hg,
    smul_ι_eq_of_rho hg hρ]

theorem pi_mul_smul_u₀ {g g' : SUid frob (k + 2)} (hg : g • v₀ k = v₀ k)
    (hρ : ∀ z, π k (g • ι k z) = z) (hg' : g' • v₀ k = v₀ k) :
    π k ((g * g') • u₀ k) = π k (g • u₀ k) + π k (g' • u₀ k) := by
  rw [mul_smul_u₀_eq hg hρ hg']
  simp only [map_add, map_smul, π_v₀, π_ι, smul_zero, zero_add, add_zero]

theorem herm_u₀_mul_smul_u₀ {g g' : SUid frob (k + 2)} (hg : g • v₀ k = v₀ k)
    (hρ : ∀ z, π k (g • ι k z) = z) (hg' : g' • v₀ k = v₀ k) :
    herm frob (u₀ k) ((g * g') • u₀ k) = herm frob (u₀ k) (g' • u₀ k) +
      herm frob (u₀ k) (g • u₀ k) + herm frob (π k (g • u₀ k)) (π k (g' • u₀ k)) := by
  rw [mul_smul_u₀_eq hg hρ hg']
  simp only [herm_add_right, herm_smul_right, herm_u₀_v₀, herm_u₀_ι, mul_one, zero_add]

theorem herm_comm_of_commute {g g' : SUid frob (k + 2)} (hg : g • v₀ k = v₀ k)
    (hρ : ∀ z, π k (g • ι k z) = z) (hg' : g' • v₀ k = v₀ k)
    (hρ' : ∀ z, π k (g' • ι k z) = z) (hc : g * g' = g' * g) :
    herm frob (π k (g • u₀ k)) (π k (g' • u₀ k)) =
      herm frob (π k (g' • u₀ k)) (π k (g • u₀ k)) := by
  have h1 := herm_u₀_mul_smul_u₀ hg hρ hg'
  have h2 := herm_u₀_mul_smul_u₀ hg' hρ' hg
  rw [hc] at h1
  rw [h1] at h2
  linear_combination h2

theorem pi_conj_smul_u₀ {z : Fin k → K} (hz : herm frob z z = 0) (g : SUid frob (k + 2))
    (hg : g • v₀ k = v₀ k) :
    π k ((tvU (ι k z) * g * tvU (ι k z)) • u₀ k) = tvU z • π k (g • u₀ k) := by
  have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
  rw [mul_smul, mul_smul, tvU_smul_of_herm_eq_zero hz' (herm_ι_u₀ z), smul_u₀_eq hg,
    tvU_smul hz', tvU_smul hz]
  simp only [herm_add_right, herm_smul_right, herm_ι_v₀, herm_ι_u₀, herm_ι_ι, mul_zero,
    zero_add, map_add, map_smul, π_v₀, π_u₀, π_ι, smul_zero]

theorem eq_one_or_eq_tvU_of_fix {g : SUid frob (k + 2)} (hgv : g • v₀ k = v₀ k)
    (hι : ∀ y, g • ι k y = ι k y) : g = 1 ∨ g = tvU (v₀ k) := by
  set r := g • u₀ k - u₀ k with hr
  have hgu : g • u₀ k = u₀ k + r := by rw [hr]; abel
  have hπr : π k r = 0 := by
    refine eq_zero_of_herm frob fun y => ?_
    rw [← herm_ι_right, hr, herm_sub_left, ← hι y, herm_smul_smul, hι, herm_u₀_ι, sub_self]
  have hr2 : herm frob (v₀ k) r = 0 := by
    have h := herm_smul_smul frob g (u₀ k) (v₀ k)
    rw [hgv] at h
    have : herm frob r (v₀ k) = 0 := by rw [hr, herm_sub_left, h, sub_self]
    exact herm_eq_zero_comm frob frob_frob this
  set α := herm frob (u₀ k) r
  have hrα : r = α • v₀ k := by
    conv_lhs => rw [decomp r]
    rw [hr2, hπr, zero_smul, map_zero, add_zero, add_zero]
  have hα : α + frob α = 0 := by
    have h := herm_smul_smul frob g (u₀ k) (u₀ k)
    rw [hgu, hrα, herm_u₀_u₀, herm_add_left, herm_add_right, herm_add_right, herm_smul_left,
      herm_smul_right, herm_smul_right, herm_smul_left, herm_u₀_u₀, herm_u₀_v₀, herm_v₀_u₀,
      herm_v₀_v₀] at h
    linear_combination h
  have hg : ∀ x, g • x = x + (α * herm frob (v₀ k) x) • v₀ k := by
    intro x
    conv_lhs => rw [decomp x]
    rw [smul_add, smul_add, smul_comm g (herm frob (u₀ k) x) (v₀ k),
      smul_comm g (herm frob (v₀ k) x) (u₀ k), hgv, hι, hgu, hrα]
    conv_rhs => lhs; rw [decomp x]
    module
  rcases (add_frob_eq_zero_iff α).1 hα with h0 | h1
  · exact Or.inl (ext_smul _ fun x => by rw [hg, h0, zero_mul, zero_smul, add_zero, one_smul])
  · exact Or.inr (ext_smul _ fun x => by rw [hg, h1, one_mul, tvU_smul herm_v₀_v₀])

theorem eq_one_or_eq_of_normalized (hk : 3 ≤ k) {N : Subgroup (SUid frob (k + 2))}
    (hfix : ∀ x ∈ N, x • v₀ k = v₀ k) (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hsq : ∀ x ∈ N, x * x = 1)
    (hnorm : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ N,
      tvU (ι k z) * x * tvU (ι k z) ∈ N) :
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
  have hPbot := eq_bot_of_isPGroup_of_normalized (by omega : 2 ≤ k) hP2 hPn
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
  have hUT : ∀ g ∈ T frob k, ∀ a ∈ U, g • a ∈ U := by
    intro g hg
    rw [T_eq_closure_tvU] at hg
    refine (Subgroup.closure_induction
      (p := fun g _ => (∀ a ∈ U, g • a ∈ U) ∧ ∀ a ∈ U, g⁻¹ • a ∈ U) ?_ ?_ ?_ ?_ hg).1
    · rintro _ ⟨v, hv0, hv, rfl⟩
      refine ⟨hUtv v hv0 hv, ?_⟩
      rw [tvU_inv hv]
      exact hUtv v hv0 hv
    · exact ⟨fun a ha => by rwa [one_smul], fun a ha => by rwa [inv_one, one_smul]⟩
    · intro x y _ _ hx hy
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · rw [mul_smul]
        exact hx.1 _ (hy.1 a ha)
      · rw [_root_.mul_inv_rev, mul_smul]
        exact hy.2 _ (hx.2 a ha)
    · intro x _ hx
      exact ⟨hx.2, fun a ha => by rw [inv_inv]; exact hx.1 a ha⟩
  have hU0 : ∀ x ∈ N, π k (x • u₀ k) = 0 := by
    intro x hx
    by_contra hd
    obtain ⟨z, hz, hzd⟩ : ∃ z : Fin k → K, herm frob z z = 0 ∧
        herm frob z (π k (x • u₀ k)) ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (eq_zero_of_forall_isotropic (by omega) h)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hzd (herm_zero_left frob _)
    set y₀ := herm frob z (π k (x • u₀ k)) • z with hy₀
    have hy₀U : y₀ ∈ U := by
      have h1 := hUadd _ (hUtv z hz0 hz _ ⟨x, hx, rfl⟩) _ ⟨x, hx, rfl⟩
      have e : tvU z • π k (x • u₀ k) + π k (x • u₀ k) = y₀ := by
        rw [tvU_smul hz, add_comm, ← add_assoc, ← two_smul K (π k (x • u₀ k)), two_eq_zero,
          zero_smul, zero_add]
      rwa [e] at h1
    have hy₀0 : y₀ ≠ 0 := smul_ne_zero hzd hz0
    have hy₀iso : herm frob y₀ y₀ = 0 := herm_smul_smul_self hz _
    have hiso : ∀ y : Fin k → K, y ≠ 0 → herm frob y y = 0 → y ∈ U := by
      intro y hy0 hy
      obtain ⟨g, hg, hgy⟩ :=
        exists_mem_T_smul_eq_of_iso isUnitaryInvolution_frob hk hy₀0 hy₀iso hy0 hy
      rw [← hgy]
      exact hUT g hg _ hy₀U
    have hk2 : 2 ≤ k := by omega
    obtain ⟨y', hy'0, hy', hyy'⟩ :=
      exists_partner_frob (isoVec_ne_zero hk2) (isoVec_isotropic hk2)
    have h1 := hiso _ (isoVec_ne_zero hk2) (isoVec_isotropic hk2)
    have h2 := hiso (ω • y') (smul_ne_zero omega_ne_zero hy'0) (herm_smul_smul_self hy' ω)
    have h3 := hUherm _ h1 _ h2
    rw [herm_smul_right, hyy', herm_smul_left, herm_conj frob frob_frob (isoVec hk2) y', hyy',
      map_one, mul_one, mul_one, frob_omega] at h3
    exact one_ne_zero (by linear_combination -h3 : (1 : K) = 0)
  intro x hx
  refine eq_one_or_eq_tvU_of_fix (hfix x hx) fun y => ?_
  rw [smul_ι_eq_of_rho (hfix x hx) (hρ x hx), hU0 x hx, herm_zero_left, zero_smul, add_zero]

theorem eq_one_or_eq_tq_of_normalized (hk : 3 ≤ k) {N : Subgroup (PG (k + 2))}
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hsq : ∀ x ∈ N, x * x = 1)
    (hcent : ∀ x ∈ N, x * tq (v₀ k) = tq (v₀ k) * x)
    (hnorm : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ N,
      tq (ι k z) * x * tq (ι k z) ∈ N) :
    ∀ x ∈ N, x = 1 ∨ x = tq (v₀ k) := by
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
  have hfix' : ∀ x ∈ Nh, x • v₀ k = v₀ k := by
    intro x hx
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
  have hnorm' : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ Nh,
      tvU (ι k z) * x * tvU (ι k z) ∈ Nh := by
    intro z hz0 hz x hx
    have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
    set w := tvU (ι k z) * x * tvU (ι k z) with hw
    have hfw : f w ∈ N := by
      rw [hw, map_mul, map_mul]
      exact hnorm z hz0 hz _ (hmk x hx)
    rw [← hmap] at hfw
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 hfw
    have hζ : y⁻¹ * w ∈ Subgroup.center (SUid frob (k + 2)) := QuotientGroup.eq.1 hyw
    have hww : w * w = 1 := by
      rw [hw]
      calc tvU (ι k z) * x * tvU (ι k z) * (tvU (ι k z) * x * tvU (ι k z))
          = tvU (ι k z) * (x * (tvU (ι k z) * tvU (ι k z)) * x) * tvU (ι k z) := by group
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
  have key := eq_one_or_eq_of_normalized hk hfix' hcomm' hsq' hnorm'
  intro x hx
  rw [← hmap] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  rcases key y hy with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]
    rfl

theorem exists_sq_eq_tvU (hk : 3 ≤ k) {z : Fin k → K} (hz0 : z ≠ 0) (hz : herm frob z z = 0) :
    ∃ c : SUid frob (k + 2), c • v₀ k = v₀ k ∧ c * c = tvU (ι k z) := by
  obtain ⟨z', -, hz', hzz'⟩ := exists_partner_frob hz0 hz
  obtain ⟨u, hu, hzu, -⟩ := exists_norm_one_perp_pair isUnitaryInvolution_frob hk hz hz' hzz'
  have he : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
  have hey : herm frob (ι k z) (ι k u) = 0 := by rw [herm_ι_ι, hzu]
  have huu : herm frob (ι k u) (ι k u) = 1 := by rw [herm_ι_ι, hu]
  have hc : ω + frob ω = -herm frob (ι k u) (ι k u) := by rw [huu, neg_K, omega_add_frob]
  refine ⟨eichler frob_frob he hey hc, ?_, ?_⟩
  · rw [eichler_smul, herm_ι_v₀, herm_ι_v₀, zero_smul, zero_smul, add_zero, sub_zero]
  · refine ext_smul _ fun x => ?_
    have hye : herm frob (ι k u) (ι k z) = 0 := herm_eq_zero_comm frob frob_frob hey
    rw [mul_smul, eichler_smul, eichler_smul, tvU_smul he]
    simp only [herm_add_right, herm_sub_right, herm_smul_right, he, hey, hye, huu, mul_zero,
      add_zero, sub_zero, mul_one]
    match_scalars
    · ring
    · linear_combination herm frob (ι k z) x * two_eq_zero
    · linear_combination (herm frob (ι k z) x * ω - herm frob (ι k u) x -
        herm frob (ι k z) x) * two_eq_zero

end S12InspPSU

end CFSG.LargeExtraspecial
