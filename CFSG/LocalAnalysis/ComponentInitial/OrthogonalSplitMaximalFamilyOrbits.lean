module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitMaximalFamilyCharacter
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitUnipotentInvariant

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open scoped Pointwise

variable {r : ℕ} {K : Type*} [Field K]

theorem flag_le_flag_of_le {i j : ℕ} (h : i ≤ j) : flag r K i ≤ flag r K j := fun _ hv =>
  mem_flag.2 ⟨(mem_flag.1 hv).1, fun k hk => (mem_flag.1 hv).2 k (h.trans hk)⟩

theorem map_swapPair_flag (hr : 0 < r) :
    (flag r K r).map (swapPair K (⟨r - 1, by omega⟩ : Fin r) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = Xstar r K hr := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_flag_top] at hv
    rw [mem_Xstar, LinearEquiv.coe_coe, swapPair_apply, Equiv.swap_apply_left]
    refine ⟨hv _, fun k hk => ?_⟩
    rw [swapPair_apply, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (by simpa using hk)]
    exact hv k
  · intro v hv
    rw [mem_Xstar] at hv
    refine ⟨swapPair K (⟨r - 1, by omega⟩ : Fin r) v, mem_flag_top.2 fun k => ?_, ?_⟩
    · rw [swapPair_apply]
      by_cases hk : k = ⟨r - 1, by omega⟩
      · rw [hk, Equiv.swap_apply_right]
        exact hv.1
      · rw [Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (by simpa using hk)]
        exact hv.2 k hk
    · rw [LinearEquiv.coe_coe, ← LinearEquiv.mul_apply, swapPair_mul_self]
      rfl

theorem map_swapPair_Xstar (hr : 0 < r) :
    (Xstar r K hr).map (swapPair K (⟨r - 1, by omega⟩ : Fin r) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = flag r K r := by
  rw [← map_swapPair_flag hr, ← map_mul_linearEquiv, swapPair_mul_self]
  exact map_one_linearEquiv _

theorem Xstar_mem_singularSubspaces (hr : 0 < r) :
    Xstar r K hr ∈ singularSubspaces (quadPlus r K) r := by
  rw [← map_swapPair_flag hr]
  exact map_mem_singularSubspaces (swapIso K _).2 (flag_mem_singularSubspaces le_rfl)

theorem eq_flag_or_eq_Xstar (hr : 0 < r) {L : Submodule K (Fin r ⊕ Fin r → K)}
    (hL : L ∈ singularSubspaces (quadPlus r K) r) (hF : flag r K (r - 1) ≤ L) :
    L = flag r K r ∨ L = Xstar r K hr := by
  have hy : ∀ w ∈ L, ∀ k : Fin r, k ≠ ⟨r - 1, by omega⟩ → w (Sum.inr k) = 0 := by
    intro w hw k hk
    have hk' : (k : ℕ) < r - 1 := by
      have h1 := k.2
      have h2 : (k : ℕ) ≠ r - 1 := fun h => hk (Fin.ext h)
      omega
    exact polar_flag_eq_zero_iff.1 (fun x hx => polar_eq_zero_of_singular hL.2 hw (hF hx)) k hk'
  have hxy : ∀ w ∈ L, w (Sum.inl ⟨r - 1, by omega⟩) * w (Sum.inr ⟨r - 1, by omega⟩) = 0 := by
    intro w hw
    have hQ := hL.2 w hw
    rwa [quadPlus_apply, Finset.sum_eq_single (⟨r - 1, by omega⟩ : Fin r)
      (fun k _ hk => by rw [hy w hw k hk, mul_zero]) (by simp)] at hQ
  by_cases h : ∃ w₀ ∈ L, w₀ (Sum.inr ⟨r - 1, by omega⟩) ≠ 0
  · right
    obtain ⟨w₀, hw₀, hw₀0⟩ := h
    have hx0 : w₀ (Sum.inl ⟨r - 1, by omega⟩) = 0 :=
      (mul_eq_zero.1 (hxy w₀ hw₀)).resolve_right hw₀0
    refine eq_of_le_of_finrank_eq (fun w hw => (mem_Xstar hr).2 ⟨?_, hy w hw⟩) ?_
    · by_contra hwx
      have hwy : w (Sum.inr ⟨r - 1, by omega⟩) = 0 :=
        (mul_eq_zero.1 (hxy w hw)).resolve_left hwx
      have h := hxy (w + w₀) (L.add_mem hw hw₀)
      rw [Pi.add_apply, Pi.add_apply, hx0, hwy, add_zero, zero_add] at h
      exact mul_ne_zero hwx hw₀0 h
    · rw [hL.1, (Xstar_mem_singularSubspaces hr).1]
  · left
    simp only [not_exists, not_and, not_not] at h
    refine eq_of_le_of_finrank_eq (fun w hw => mem_flag_top.2 fun k => ?_) ?_
    · by_cases hk : k = ⟨r - 1, by omega⟩
      · rw [hk]
        exact h w hw
      · exact hy w hw k hk
    · rw [hL.1, finrank_flag le_rfl]

theorem mem_orbit_elementary {X L : Submodule K (Fin r ⊕ Fin r → K)} :
    L ∈ MulAction.orbit (orthElementaryGroup (quadPlus r K)) X ↔
      ∃ a ∈ orthElementaryGroup (quadPlus r K), a • X = L := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem image_map_orbit {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))
    (Y : Submodule K (Fin r ⊕ Fin r → K)) :
    (fun L => L.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) ''
        MulAction.orbit (orthElementaryGroup (quadPlus r K)) Y =
      MulAction.orbit (orthElementaryGroup (quadPlus r K))
        (Y.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) := by
  ext L
  rw [Set.mem_image, mem_orbit_elementary]
  constructor
  · rintro ⟨_, hx, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hx
    refine ⟨g * a * g⁻¹, conj_mem_elementaryGroup hg ha, ?_⟩
    change (g * a * g⁻¹) • g • Y = g • a • Y
    rw [smul_smul, inv_mul_cancel_right, mul_smul]
  · rintro ⟨b, hb, rfl⟩
    have hb' : g⁻¹ * b * g ∈ orthElementaryGroup (quadPlus r K) := by
      have h := conj_mem_elementaryGroup (inv_mem hg) hb
      rw [inv_inv] at h
      exact h
    refine ⟨(g⁻¹ * b * g) • Y, mem_orbit_elementary.2 ⟨_, hb', rfl⟩, ?_⟩
    change g • (g⁻¹ * b * g) • Y = b • g • Y
    rw [smul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]

theorem orthogonal_geometry_split_maximal_family_orbits {K : Type*} [Field K] [Finite K]
    {r : ℕ} (hr : 3 ≤ r) :
    flag r K r ∈ singularSubspaces (quadPlus r K) r ∧
      Xstar r K (by omega) ∈ singularSubspaces (quadPlus r K) r ∧
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) ⊆
        singularSubspaces (quadPlus r K) r ∧
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K (by omega)) ⊆
        singularSubspaces (quadPlus r K) r ∧
      (∀ L ∈ singularSubspaces (quadPlus r K) r,
        L ∈ MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) ∨
          L ∈ MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K (by omega))) ∧
      Disjoint (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r))
        (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K (by omega))) ∧
      Nat.card (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r)) =
        ∏ i ∈ Finset.Icc 1 (r - 1), (Nat.card K ^ i + 1) ∧
      Nat.card (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K (by omega))) =
        ∏ i ∈ Finset.Icc 1 (r - 1), (Nat.card K ^ i + 1) ∧
      swapPair K (⟨r - 1, by omega⟩ : Fin r) ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) ∧
      (fun L => L.map (swapPair K (⟨r - 1, by omega⟩ : Fin r) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) ''
          MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) =
        MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K (by omega)) ∧
      (fun L => L.map (swapPair K (⟨r - 1, by omega⟩ : Fin r) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) ''
          MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K (by omega)) =
        MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) := by
  have hr0 : 0 < r := by omega
  have hX : flag r K r ∈ singularSubspaces (quadPlus r K) r := flag_mem_singularSubspaces le_rfl
  have hXs := Xstar_mem_singularSubspaces (K := K) hr0
  have hs : swapPair K (⟨r - 1, by omega⟩ : Fin r) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := (swapIso K _).2
  have hsub : ∀ Y ∈ singularSubspaces (quadPlus r K) r,
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) Y ⊆
        singularSubspaces (quadPlus r K) r := by
    intro Y hY L hL
    obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hL
    exact map_mem_singularSubspaces (orthElementaryGroup_le _ ha) hY
  have hcover : ∀ L ∈ singularSubspaces (quadPlus r K) r,
      L ∈ MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) ∨
        L ∈ MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K hr0) := by
    intro L hL
    obtain ⟨g, hg, hgL⟩ := exists_isometry_map_eq le_rfl hL
    obtain ⟨a, ha, hag⟩ := exists_elementary_map_flag_eq (by omega) hg
    have hL' : a⁻¹ • L ∈ singularSubspaces (quadPlus r K) r :=
      map_mem_singularSubspaces (orthElementaryGroup_le _ (inv_mem ha)) hL
    have hF : flag r K (r - 1) ≤ a⁻¹ • L := by
      have h1 : a • flag r K (r - 1) = g • flag r K (r - 1) := hag (r - 1) le_rfl
      have h2 : g • flag r K (r - 1) ≤ L := by
        rw [← hgL]
        exact Submodule.map_mono (flag_le_flag_of_le (Nat.sub_le r 1))
      rw [← inv_smul_smul a (flag r K (r - 1)), h1]
      exact Submodule.map_mono h2
    rcases eq_flag_or_eq_Xstar hr0 hL' hF with h | h
    · exact Or.inl (mem_orbit_elementary.2 ⟨a, ha, by rw [← h, smul_inv_smul]⟩)
    · exact Or.inr (mem_orbit_elementary.2 ⟨a, ha, by rw [← h, smul_inv_smul]⟩)
  obtain ⟨-, -, -, ⟨χ, hEχ, hSχ, hsχ⟩, -, -⟩ :=
    orthogonal_geometry_split_maximal_family_character (K := K) hr
  have hdisj : Disjoint (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r))
      (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K hr0)) := by
    rw [Set.disjoint_left]
    intro L hLX hLXs
    obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hLX
    obtain ⟨b, hb, hbL⟩ := mem_orbit_elementary.1 hLXs
    have haO := orthElementaryGroup_le _ ha
    have hbO := orthElementaryGroup_le _ hb
    have hχa : χ ⟨a, haO⟩ = 1 := hEχ (show (⟨a, haO⟩ : TauCeti.QuadraticMap.orthogonalGroup
      (quadPlus r K)) ∈ _ from Subgroup.mem_subgroupOf.2 ha)
    have hχb : χ ⟨b, hbO⟩ = 1 := hEχ (show (⟨b, hbO⟩ : TauCeti.QuadraticMap.orthogonalGroup
      (quadPlus r K)) ∈ _ from Subgroup.mem_subgroupOf.2 hb)
    have hsX : swapPair K (⟨r - 1, by omega⟩ : Fin r) • flag r K r = Xstar r K hr0 :=
      map_swapPair_flag hr0
    have hmem : (swapIso K ⟨r - 1, by omega⟩)⁻¹ * (⟨b, hbO⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))⁻¹ * ⟨a, haO⟩ ∈
          (maxStab r K).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) := by
      rw [Subgroup.mem_subgroupOf]
      refine mem_maxStab.2 ⟨Subtype.prop _, ?_⟩
      change ((swapPair K (⟨r - 1, by omega⟩ : Fin r))⁻¹ * b⁻¹ * a) • flag r K r = flag r K r
      rw [mul_smul, mul_smul, ← hbL, inv_smul_smul, ← hsX, inv_smul_smul]
    have h1 : χ ((swapIso K ⟨r - 1, by omega⟩)⁻¹ * (⟨b, hbO⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))⁻¹ * ⟨a, haO⟩) = 1 := hSχ hmem
    rw [map_mul, map_mul, map_inv, map_inv, hsχ, hχa, hχb] at h1
    exact absurd h1 (by decide)
  have hexch1 : (fun L => L.map (swapPair K (⟨r - 1, by omega⟩ : Fin r) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) ''
        MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) =
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K hr0) := by
    rw [image_map_orbit hs, map_swapPair_flag hr0]
  have hexch2 : (fun L => L.map (swapPair K (⟨r - 1, by omega⟩ : Fin r) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) ''
        MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K hr0) =
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) := by
    rw [image_map_orbit hs, map_swapPair_Xstar hr0]
  have hunion : singularSubspaces (quadPlus r K) r =
      MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r) ∪
        MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K hr0) := by
    ext L
    exact ⟨fun hL => hcover L hL, fun h => h.elim (fun h => hsub _ hX h) (fun h => hsub _ hXs h)⟩
  have hncard : (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K hr0)).ncard =
      (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r)).ncard := by
    rw [← hexch1]
    exact Set.ncard_image_of_injective _
      (Submodule.map_injective_of_injective (swapPair K _).injective)
  have hsum : (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (flag r K r)).ncard +
      (MulAction.orbit (orthElementaryGroup (quadPlus r K)) (Xstar r K hr0)).ncard =
        2 * ∏ i ∈ Finset.Icc 1 (r - 1), (Nat.card K ^ i + 1) := by
    rw [← Set.ncard_union_eq hdisj, ← hunion, ← Nat.card_coe_set_eq, card_maximal (by omega)]
  refine ⟨hX, hXs, hsub _ hX, hsub _ hXs, hcover, hdisj, ?_, ?_, hs, hexch1, hexch2⟩
  · rw [Nat.card_coe_set_eq]
    omega
  · rw [Nat.card_coe_set_eq]
    omega

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
