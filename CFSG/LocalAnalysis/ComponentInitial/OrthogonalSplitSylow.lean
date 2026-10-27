module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitUnipotentInvariant
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitMaximalFamilyCharacter

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Matrix CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type*} [Field K]

theorem flag_eq_flag_top {i : ℕ} (hi : r ≤ i) : flag r K i = flag r K r := by
  rw [flag, flag]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  exact ⟨fun ⟨j, _, hj⟩ => ⟨j, j.2, hj⟩, fun ⟨j, _, hj⟩ => ⟨j, by omega, hj⟩⟩

theorem flag_lt_Xstar (hr : 0 < r) : flag r K (r - 1) < Xstar r K hr := by
  refine lt_of_le_of_ne le_sup_left fun heq => ?_
  have hf : (Pi.single (Sum.inr (⟨r - 1, by omega⟩ : Fin r)) (1 : K) :
      Fin r ⊕ Fin r → K) ∈ flag r K (r - 1) := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have := (mem_flag_iff_coord.1 hf).1 ⟨r - 1, by omega⟩
  simp at this

theorem eq_flag_top_or_Xstar (hr : 0 < r) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hWs : ∀ x ∈ W, quadPlus r K x = 0) (hWd : finrank K W = r) (hF : flag r K (r - 1) ≤ W) :
    W = flag r K r ∨ W = Xstar r K hr := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : Fin r, (z : ℕ) = r - 1 := ⟨⟨r - 1, by omega⟩, rfl⟩
  have hz' : z = ⟨r - 1, by omega⟩ := Fin.ext hz
  have hzlt : ∀ c : Fin r, c ≠ z → (c : ℕ) < r - 1 := fun c hc => by
    have h1 := c.2
    have h2 : (c : ℕ) ≠ r - 1 := fun h => hc (Fin.ext (h.trans hz.symm))
    omega
  have horth : ∀ v ∈ W, ∀ c : Fin r ⊕ Fin r, (Pi.single c (1 : K) : Fin r ⊕ Fin r → K) ∈ W →
      v c.swap = 0 := fun v hv c hc => by
    rw [← polar_single v c]
    exact polar_eq_zero_of_singular hWs hv hc
  have hFk : ∀ k : Fin r, k ≠ z → (Pi.single (Sum.inl k) (1 : K) : Fin r ⊕ Fin r → K) ∈ W :=
    fun k hk => hF (Submodule.subset_span ⟨k, hzlt k hk, rfl⟩)
  have hne : ¬W ≤ flag r K (r - 1) := fun h => by
    have := Submodule.finrank_mono h
    rw [hWd, finrank_flag_of_le (by omega)] at this
    omega
  obtain ⟨w₀, hw₀W, hw₀⟩ := Set.not_subset.1 hne
  obtain ⟨w, hw⟩ : ∃ w : Fin r ⊕ Fin r → K, w = w₀ - ∑ k : Fin r, if k = z then 0 else
      w₀ (Sum.inl k) • (Pi.single (Sum.inl k) (1 : K) : Fin r ⊕ Fin r → K) := ⟨_, rfl⟩
  have hSF : (∑ k : Fin r, if k = z then 0 else
      w₀ (Sum.inl k) • (Pi.single (Sum.inl k) (1 : K) : Fin r ⊕ Fin r → K)) ∈
        flag r K (r - 1) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    split_ifs with hk
    · exact zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hzlt k hk, rfl⟩)
  have hwW : w ∈ W := by rw [hw]; exact W.sub_mem hw₀W (hF hSF)
  have hwF : w ∉ flag r K (r - 1) := fun h => hw₀ (by
    have := (flag r K (r - 1)).add_mem h hSF
    rwa [hw, sub_add_cancel] at this)
  have hwl : ∀ k : Fin r, k ≠ z → w (Sum.inl k) = 0 := fun k hk => by
    rw [hw, Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hjk
      split_ifs <;> simp [Ne.symm hjk]
    · simp
  have hwr : ∀ k : Fin r, k ≠ z → w (Sum.inr k) = 0 := fun k hk => by
    have := horth w hwW (Sum.inl k) (hFk k hk)
    simpa using this
  have hQ := hWs w hwW
  rw [quadPlus_apply, Finset.sum_eq_single z (fun j _ hj => by rw [hwr j hj, mul_zero])
    (by simp)] at hQ
  by_cases hl : w (Sum.inl z) = 0
  ·
    have hr0 : w (Sum.inr z) ≠ 0 := fun h0 => hwF (by
      rw [mem_flag_iff_coord]
      refine ⟨fun k => ?_, fun k hk => ?_⟩
      · by_cases hk : k = z
        · rw [hk]; exact h0
        · exact hwr k hk
      · have hkz : k = z := Fin.ext (by have := k.2; omega)
        rw [hkz]
        exact hl)
    have hweq : w = w (Sum.inr z) • Pi.single (Sum.inr z) 1 := by
      ext c
      rcases c with c | c
      · by_cases hc : c = z
        · rw [hc]; simp [hl]
        · simp [hwl c hc]
      · by_cases hc : c = z
        · rw [hc]; simp
        · simp [hc, hwr c hc]
    have hf : (Pi.single (Sum.inr z) (1 : K) : Fin r ⊕ Fin r → K) ∈ W :=
      mem_of_smul_mem hr0 (hweq ▸ hwW)
    have hle : Xstar r K hr ≤ W :=
      sup_le hF ((Submodule.span_singleton_le_iff_mem _ _).2 (by rw [← hz']; exact hf))
    refine Or.inr (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    have := Submodule.finrank_lt_finrank_of_lt (flag_lt_Xstar (K := K) hr)
    rw [finrank_flag_of_le (by omega)] at this
    omega
  ·
    have hr0 : w (Sum.inr z) = 0 := (mul_eq_zero.1 hQ).resolve_left hl
    have hweq : w = w (Sum.inl z) • Pi.single (Sum.inl z) 1 := by
      ext c
      rcases c with c | c
      · by_cases hc : c = z
        · rw [hc]; simp
        · simp [hc, hwl c hc]
      · by_cases hc : c = z
        · rw [hc]; simp [hr0]
        · simp [hwr c hc]
    have he : (Pi.single (Sum.inl z) (1 : K) : Fin r ⊕ Fin r → K) ∈ W :=
      mem_of_smul_mem hl (hweq ▸ hwW)
    have hle : flag r K r ≤ W := by
      have := flag_succ_le (m := r - 1) hz hF he
      rwa [show r - 1 + 1 = r by omega] at this
    refine Or.inl (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    rw [hWd, finrank_flag_of_le le_rfl]

variable (r K) in
@[expose] noncomputable def flagStab :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  orthElementaryGroup (quadPlus r K) ⊓ ⨅ i : Fin (r - 1),
    MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K (i + 1))

theorem mem_flagStab {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ flagStab r K ↔ g ∈ orthElementaryGroup (quadPlus r K) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ r - 1 →
        (flag r K i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = flag r K i := by
  simp only [flagStab, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine and_congr_right fun _ => ⟨fun h i hi hir => ?_, fun h i => h (i + 1) (by omega)
    (by omega)⟩
  have := h ⟨i - 1, by omega⟩
  rwa [show i - 1 + 1 = i by omega] at this

theorem flagStab_le : flagStab r K ≤ orthElementaryGroup (quadPlus r K) := inf_le_left

theorem posUnip_le_flagStab : posUnip r K ≤ flagStab r K := fun _ hg =>
  mem_flagStab.2 ⟨posUnip_le_orthElementaryGroup hg, fun i _ _ =>
    (mem_posBorel.1 (posUnip_le_posBorel hg)).2 i⟩

theorem flagStab_le_posBorel (hr : 0 < r)
    (hXX : ∀ a ∈ orthElementaryGroup (quadPlus r K),
      (flag r K r).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ≠ Xstar r K hr) :
    flagStab r K ≤ posBorel r K := by
  intro b hb
  obtain ⟨hbE, hbF⟩ := mem_flagStab.1 hb
  have hbO := orthElementaryGroup_le (quadPlus r K) hbE
  have hbX : (flag r K r).map (b : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
      flag r K r := by
    rcases eq_flag_top_or_Xstar hr (W := (flag r K r).map (b : _ →ₗ[K] _))
        (by
          rintro _ ⟨v, hv, rfl⟩
          rw [LinearEquiv.coe_coe, map_of_mem hbO]
          exact flag_singular r v hv)
        (by rw [LinearEquiv.finrank_map_eq, finrank_flag_of_le le_rfl])
        (by
          rcases Nat.eq_zero_or_pos (r - 1) with h0 | h0
          · rw [h0, flag_zero]
            exact bot_le
          · rw [← hbF (r - 1) h0 le_rfl]
            exact Submodule.map_mono (Submodule.span_mono
              (Set.image_mono fun j (hj : (j : ℕ) < r - 1) => show (j : ℕ) < r by omega)))
      with h | h
    · exact h
    · exact absurd h (hXX b hbE)
  refine mem_posBorel.2 ⟨⟨hbO, hbX⟩, fun i => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [flag_zero, Submodule.map_bot]
  · rcases Nat.lt_or_ge i r with hir | hir
    · exact hbF i hi0 (by omega)
    · rw [flag_eq_flag_top hir]
      exact hbX

theorem finrank_Xstar_le (hr : 0 < r) : finrank K (Xstar r K hr) ≤ r := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (flag r K (r - 1))
    (K ∙ (Pi.single (Sum.inr (⟨r - 1, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K))
  have h1 : finrank K (K ∙ (Pi.single (Sum.inr (⟨r - 1, by omega⟩ : Fin r)) (1 : K) :
      Fin r ⊕ Fin r → K)) = 1 := finrank_span_singleton (by simp)
  rw [finrank_flag_of_le (by omega), h1] at h
  rw [Xstar]
  omega

theorem map_swapIso_flag_top [Finite K] (hr : 3 ≤ r) :
    (flag r K r).map ((swapIso K (⟨r - 1, by omega⟩ : Fin r) :
      (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = Xstar r K (by omega) := by
  obtain ⟨h1, -, h3, -⟩ := orthogonal_geometry_split_maximal_family_character (K := K) hr
  have hle : (flag r K r).map ((swapIso K (⟨r - 1, by omega⟩ : Fin r) :
      (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ≤ Xstar r K (by omega) := by
    rw [flag, Submodule.map_span_le]
    rintro _ ⟨j, -, rfl⟩
    rw [LinearEquiv.coe_coe]
    by_cases hj : j = ⟨r - 1, by omega⟩
    · rw [hj, h1]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [h3 _ (by simpa using hj) (by simp)]
      refine Submodule.mem_sup_left (Submodule.subset_span ⟨j, ?_, rfl⟩)
      have := j.2
      have : (j : ℕ) ≠ r - 1 := fun h => hj (Fin.ext h)
      show (j : ℕ) < r - 1
      omega
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [LinearEquiv.finrank_map_eq, finrank_flag_of_le le_rfl]
  exact finrank_Xstar_le _

theorem map_flag_top_ne_Xstar [Finite K] (hr : 3 ≤ r)
    {a : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (ha : a ∈ orthElementaryGroup (quadPlus r K)) :
    (flag r K r).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ≠
      Xstar r K (by omega) := by
  intro h
  obtain ⟨-, -, -, ⟨χ, hE, hS, hs⟩, -⟩ := orthogonal_geometry_split_maximal_family_character
    (K := K) hr
  have haO := orthElementaryGroup_le (quadPlus r K) ha
  set s := swapIso K (⟨r - 1, by omega⟩ : Fin r) with hsdef
  have hsX := map_swapIso_flag_top (K := K) hr
  have hmem : s⁻¹ * ⟨a, haO⟩ ∈ (maxStab r K).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) := by
    rw [Subgroup.mem_subgroupOf]
    refine mem_maxStab.2 ⟨(s⁻¹ * ⟨a, haO⟩).2, ?_⟩
    rw [Subgroup.coe_mul, map_mul_linearEquiv, h, ← hsX, ← map_mul_linearEquiv,
      Subgroup.coe_inv, inv_mul_cancel]
    exact Submodule.map_id _
  have h1 := hS hmem
  have h2 := hE (Subgroup.mem_subgroupOf.2 ha : (⟨a, haO⟩ : TauCeti.QuadraticMap.orthogonalGroup
    (quadPlus r K)) ∈ _)
  rw [MonoidHom.mem_ker, map_mul, map_inv, hs, MonoidHom.mem_ker.1 h2, mul_one] at h1
  exact absurd h1 (by decide)

variable (r K) in
@[expose] def stdFlag : Fin (r - 1) → Submodule K (Fin r ⊕ Fin r → K) :=
  fun i => flag r K (i + 1)

theorem stdFlag_mem : stdFlag r K ∈ singularFlags (quadPlus r K) (r - 1) :=
  ⟨fun i => finrank_flag_of_le (by omega),
    fun i j hij => Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < i + 1) =>
      show (l : ℕ) < j + 1 by have : (i : ℕ) ≤ j := hij; omega),
    fun _ x hx => flag_singular _ x hx⟩

theorem map_mem_singularFlags {k : ℕ} {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))
    {W : Fin k → Submodule K (Fin r ⊕ Fin r → K)} (hW : W ∈ singularFlags (quadPlus r K) k) :
    (fun i => (W i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) ∈
      singularFlags (quadPlus r K) k := by
  obtain ⟨hd, hm, hs⟩ := hW
  refine ⟨fun i => by rw [LinearEquiv.finrank_map_eq, hd],
    fun i j hij => Submodule.map_mono (hm hij), fun i x hx => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hx
  rw [LinearEquiv.coe_coe, map_of_mem hg]
  exact hs i v hv

theorem stabilizer_stdFlag :
    MulAction.stabilizer (orthElementaryGroup (quadPlus r K)) (stdFlag r K) =
      (flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K)) := by
  ext x
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, flagStab, Subgroup.mem_inf,
    Subgroup.mem_iInf]
  exact ⟨fun h => ⟨x.2, fun i => congrFun h i⟩, fun h => funext fun i => h.2 i⟩

theorem orbit_stdFlag (hr : 1 ≤ r) :
    MulAction.orbit (orthElementaryGroup (quadPlus r K)) (stdFlag r K) =
      singularFlags (quadPlus r K) (r - 1) := by
  ext W
  constructor
  · rintro ⟨x, rfl⟩
    exact map_mem_singularFlags (orthElementaryGroup_le (quadPlus r K) x.2) stdFlag_mem
  · intro hW
    obtain ⟨g, hg, hgW⟩ := (orthogonal_geometry_split_partial_flag_transitivity (K := K) hr
      le_rfl).1 _ stdFlag_mem W hW
    exact ⟨⟨g, hg⟩, funext fun i => hgW i⟩

theorem relIndex_flagStab (hr : 1 ≤ r) :
    (flagStab r K).relIndex (orthElementaryGroup (quadPlus r K)) =
      Nat.card (singularFlags (quadPlus r K) (r - 1)) := by
  rw [Subgroup.relIndex, ← stabilizer_stdFlag, MulAction.index_stabilizer, orbit_stdFlag hr,
    Nat.card_coe_set_eq]

theorem card_singularLines_eq_div {s : ℕ} [Finite K] :
    (Nat.card (singularLinesIn (quadPlus s K) ⊤) : ℚ) =
      ((Nat.card K : ℚ) ^ s - 1) * ((Nat.card K : ℚ) ^ (s - 1) + 1) / ((Nat.card K : ℚ) - 1) := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h := (orthogonal_geometry_split_point_count K s).1
  have hpos : 1 ≤ Nat.card K ^ s := Nat.one_le_pow _ _ (by omega)
  have hcast := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast [Nat.cast_sub hq.le, Nat.cast_sub hpos] at hcast
  have hq1 : (Nat.card K : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < Nat.card K := by exact_mod_cast hq
    linarith
  rw [eq_div_iff hq1, mul_comm, hcast]

theorem card_singularFlags_eq_prod [Finite K] (hr : 1 ≤ r) :
    Nat.card (singularFlags (quadPlus r K) (r - 1)) =
      ∏ j ∈ Finset.range (r - 1), Nat.card (singularLinesIn (quadPlus (r - j) K) ⊤) := by
  have h := (orthogonal_geometry_split_singular_subspace_count (K := K) hr
    (show r - 1 ≤ r by omega)).2.1
  apply Nat.cast_injective (R := ℚ)
  rw [h, Nat.cast_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [card_singularLines_eq_div, show r - j - 1 = r - j - 1 from rfl]

theorem relIndex_flagStab_modEq [Finite K] (hr : 1 ≤ r) :
    (flagStab r K).relIndex (orthElementaryGroup (quadPlus r K)) ≡ 1 [MOD Nat.card K] := by
  rw [relIndex_flagStab hr, card_singularFlags_eq_prod hr, ← ZMod.natCast_eq_natCast_iff,
    Nat.cast_prod, Nat.cast_one]
  refine Finset.prod_eq_one fun j hj => ?_
  have hj' : j < r - 1 := Finset.mem_range.1 hj
  have := (orthogonal_geometry_split_point_count K (r - j)).2 (by omega)
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one] at this
  exact this

theorem conj_mem_posUnip {g u : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ posBorel r K) (hu : u ∈ posUnip r K) : g * u * g⁻¹ ∈ posUnip r K := by
  have := posUnip_normal.conj_mem ⟨u, posUnip_le_posBorel hu⟩ (Subgroup.mem_subgroupOf.2 hu)
    ⟨g, hg⟩
  rwa [Subgroup.mem_subgroupOf] at this

section Sylow

variable [Finite K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

omit hp in
theorem prime_dvd_card : p ∣ Nat.card K := by
  let _ := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self p n.ne_zero

include hp in
theorem not_dvd_of_modEq_one {m : ℕ} (hm : m ≡ 1 [MOD Nat.card K]) : ¬p ∣ m := by
  intro hpm
  have h := hm.of_dvd (prime_dvd_card (K := K) p)
  have h1 : m % p = 0 := Nat.mod_eq_zero_of_dvd hpm
  rw [Nat.ModEq, h1, Nat.mod_eq_of_lt hp.out.one_lt] at h
  exact one_ne_zero h.symm

include hp in
theorem not_dvd_card_sub_one_pow : ¬p ∣ (Nat.card K - 1) ^ r := by
  intro h
  have h1 := hp.out.dvd_of_dvd_pow h
  have h2 := prime_dvd_card (K := K) p
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 (Nat.card_pos (α := K)).ne'
  have := Nat.dvd_sub h2 h1
  rw [Nat.sub_sub_self hq] at this
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)

theorem posUnip_isSylow (hr : 2 ≤ r)
    (hXX : ∀ a ∈ orthElementaryGroup (quadPlus r K),
      (flag r K r).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ≠
        Xstar r K (by omega)) :
    ∃ S : Sylow p (orthElementaryGroup (quadPlus r K)),
      (S : Subgroup (orthElementaryGroup (quadPlus r K))) =
        (posUnip r K).subgroupOf (orthElementaryGroup (quadPlus r K)) := by
  set E := orthElementaryGroup (quadPlus r K)
  have hUE : posUnip r K ≤ E := posUnip_le_orthElementaryGroup
  have hP : IsPGroup p ((posUnip r K).subgroupOf E) :=
    (((orthogonal_geometry_split_positive_unipotent_matrices (r := r) (K := K)).2.2.2.2.2.2.2.2.2.2
      p ‹_› ‹_›).2.1).of_equiv (Subgroup.subgroupOfEquivOfLe hUE).symm
  have hidx : ¬p ∣ ((posUnip r K).subgroupOf E).index := by
    change ¬p ∣ (posUnip r K).relIndex E
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ posUnip_le_flagStab flagStab_le]
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
    ·
      have hdvd : (posUnip r K).relIndex (flagStab r K) ∣
          (posUnip r K).relIndex (posBorel r K) := by
        rw [← Subgroup.relIndex_mul_relIndex _ _ _ posUnip_le_flagStab
          (flagStab_le_posBorel (by omega) hXX)]
        exact dvd_mul_right _ _
      have hidx : (posUnip r K).relIndex (posBorel r K) = (Nat.card K - 1) ^ r := index_posUnip
      exact not_dvd_card_sub_one_pow (r := r) (K := K) p (hidx ▸ h.trans hdvd)
    · exact not_dvd_of_modEq_one (K := K) p (relIndex_flagStab_modEq (by omega)) h
  exact ⟨IsPGroup.toSylow hP hidx, rfl⟩

omit [Finite K] in
theorem normalizer_posUnip (hr : 2 ≤ r)
    (hXX : ∀ a ∈ orthElementaryGroup (quadPlus r K),
      (flag r K r).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ≠
        Xstar r K (by omega)) :
    Subgroup.normalizer (((posUnip r K).subgroupOf (orthElementaryGroup (quadPlus r K)) :
        Subgroup (orthElementaryGroup (quadPlus r K))) :
          Set (orthElementaryGroup (quadPlus r K))) =
      (flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K)) := by
  set E := orthElementaryGroup (quadPlus r K)
  ext ⟨y, hyE⟩
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hconj : ∀ g ∈ posUnip r K, y⁻¹ * g * y ∈ posUnip r K := by
      intro g hg
      have := (h ((⟨y, hyE⟩ : E)⁻¹ * ⟨g, posUnip_le_orthElementaryGroup hg⟩ * ⟨y, hyE⟩)).2 (by
        rw [Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using hg)
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hO := orthElementaryGroup_le (quadPlus r K) hyE
    refine mem_flagStab.2 ⟨hyE, fun i hi hir => ?_⟩
    refine (orthogonal_geometry_split_unipotent_invariant_singular_subspaces (K := K) hr).2.2.2.2
      (fun i => (flag r K i).map (y : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)))
      (fun j hj hjr => ⟨?_, ?_, ?_⟩) i hi hir
    · rw [LinearEquiv.finrank_map_eq, finrank_flag_of_le (by omega)]
    · rintro _ ⟨v, hv, rfl⟩
      rw [LinearEquiv.coe_coe, map_of_mem hO]
      exact flag_singular j v hv
    · intro g hg
      have hk := (mem_posBorel.1 (posUnip_le_posBorel (hconj g hg))).2 j
      rw [← map_mul_linearEquiv, show g * y = y * (y⁻¹ * g * y) by group, map_mul_linearEquiv,
        hk]
  · intro hx h
    have hxB := flagStab_le_posBorel (by omega) hXX hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hh
      simpa using conj_mem_posUnip hxB hh
    · intro hh
      have := conj_mem_posUnip (inv_mem hxB) (by simpa using hh)
      simpa [mul_assoc] using this

end Sylow

section Projective

variable (r K) in
@[expose] noncomputable def elemScalars : Subgroup (orthElementaryGroup (quadPlus r K)) :=
  (scalars K (Fin r ⊕ Fin r → K)).subgroupOf (orthElementaryGroup (quadPlus r K))

instance elemScalars_normal : (elemScalars r K).Normal :=
  (scalars_normal (K := K) (V := Fin r ⊕ Fin r → K)).subgroupOf _

theorem eq_one_of_mem_posUnip_scalars (hr : 1 ≤ r)
    {z : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (hzU : z ∈ posUnip r K)
    (hzZ : z ∈ scalars K (Fin r ⊕ Fin r → K)) : z = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.1 hzZ
  have h1 := (mem_posUnip.1 hzU).2 ⟨0, by omega⟩
  rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, hc] at h1
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
  refine LinearEquiv.ext fun v => ?_
  rw [hc, h1, one_smul]
  rfl

theorem pow_card_sub_one_of_mem_scalars [Finite K] (hr : 1 ≤ r)
    {z : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hz : z ∈ scalars K (Fin r ⊕ Fin r → K)) : z ^ (Nat.card K - 1) = 1 := by
  let _ := Fintype.ofFinite K
  obtain ⟨c, hc⟩ := mem_scalars.1 hz
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := hc (Pi.single (Sum.inl ⟨0, by omega⟩) 1)
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at h
    exact one_ne_zero (congrFun h (Sum.inl ⟨0, by omega⟩) |>.symm.trans (by simp) |>.symm)
  have hpow : ∀ n : ℕ, ∀ v, (z ^ n) v = c ^ n • v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih => intro v; rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hc, smul_smul,
        pow_succ, mul_comm]
  refine LinearEquiv.ext fun v => ?_
  rw [hpow, Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one c hc0, one_smul]
  rfl

variable [Finite K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

include hp in
theorem eq_one_of_mul_scalar_pow (hr : 1 ≤ r)
    {u z : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (hu : u ∈ posUnip r K)
    (hz : z ∈ scalars K (Fin r ⊕ Fin r → K)) {k : ℕ} (hk : (u * z) ^ p ^ k = 1) : z = 1 := by
  have hcomm : Commute u z := (commute_of_mem_scalars hz u).symm
  rw [hcomm.mul_pow] at hk
  have hzk : z ^ p ^ k = 1 := by
    have hmem : z ^ p ^ k ∈ posUnip r K := by
      rw [show z ^ p ^ k = (u ^ p ^ k)⁻¹ from eq_inv_of_mul_eq_one_right hk]
      exact inv_mem (pow_mem hu _)
    exact eq_one_of_mem_posUnip_scalars hr hmem (pow_mem hz _)
  have hcop : Nat.Coprime (p ^ k) (Nat.card K - 1) := Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun h => not_dvd_card_sub_one_pow (r := 1) p
      (by rwa [pow_one]))
  have := pow_gcd_eq_one.2 ⟨hzk, pow_card_sub_one_of_mem_scalars hr hz⟩
  rwa [hcop, pow_one] at this

theorem finite_orthElementaryGroup : Finite (orthElementaryGroup (quadPlus r K)) := by
  have : Finite (Fin r ⊕ Fin r → K) := inferInstance
  have : Finite ((Fin r ⊕ Fin r → K) → (Fin r ⊕ Fin r → K)) := inferInstance
  have : Finite ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
    Finite.of_injective (β := (Fin r ⊕ Fin r → K) → (Fin r ⊕ Fin r → K))
      (fun e => ⇑e) fun a b h => LinearEquiv.ext (congrFun h)
  infer_instance

theorem projUnip_isSylow (hr : 3 ≤ r) :
    ∃ S : Sylow p (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K),
      (S : Subgroup (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K)) =
        ((posUnip r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
          (QuotientGroup.mk' (elemScalars r K)) := by
  have := finite_orthElementaryGroup (r := r) (K := K)
  obtain ⟨S, hS⟩ := posUnip_isSylow p (by omega) fun a ha =>
    map_flag_top_ne_Xstar (K := K) hr ha
  exact ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective _) S,
    by rw [Sylow.coe_mapSurjective, hS]⟩

theorem normalizer_projUnip (hr : 3 ≤ r) :
    Subgroup.normalizer ((((posUnip r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
        (QuotientGroup.mk' (elemScalars r K)) :
          Subgroup (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K)) :
        Set (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K)) =
      ((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
        (QuotientGroup.mk' (elemScalars r K)) := by
  set E := orthElementaryGroup (quadPlus r K)
  let p := ringChar K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have : CharP K p := ringChar.charP K
  have hXX : ∀ a ∈ E, (flag r K r).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] _) ≠
      Xstar r K (by omega) := fun a ha => map_flag_top_ne_Xstar hr ha
  have hN := normalizer_posUnip (K := K) (by omega) hXX
  refine le_antisymm ?_ (hN ▸ Subgroup.le_normalizer_map _)
  have key : ∀ y : E, QuotientGroup.mk' (elemScalars r K) y ∈ Subgroup.normalizer
      ((((posUnip r K).subgroupOf E).map (QuotientGroup.mk' (elemScalars r K)) :
        Subgroup (E ⧸ elemScalars r K)) : Set (E ⧸ elemScalars r K)) →
      ∀ u ∈ (posUnip r K).subgroupOf E, y * u * y⁻¹ ∈ (posUnip r K).subgroupOf E := by
    intro y hy u hu
    have hmem := (Subgroup.mem_normalizer_iff.1 hy (QuotientGroup.mk' _ u)).1 ⟨u, hu, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at hmem
    obtain ⟨u', hu', hu'eq⟩ := hmem
    obtain ⟨w, hw⟩ : ∃ w : E, w = y * u * y⁻¹ := ⟨_, rfl⟩
    rw [← hw] at hu'eq ⊢
    have hz : u'⁻¹ * w ∈ elemScalars r K := QuotientGroup.eq.1 hu'eq
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu'
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    obtain ⟨k, hk⟩ := ((orthogonal_geometry_split_positive_unipotent_matrices (r := r)
      (K := K)).2.2.2.2.2.2.2.2.2.2 p ‹_› ‹_›).2.1 ⟨(u : (Fin r ⊕ Fin r → K) ≃ₗ[K] _), hu⟩
    have huk : (u : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hwk : (w : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ^ p ^ k = 1 := by
      rw [hw, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, conj_pow, huk, mul_one,
        mul_inv_cancel]
    have hk' : ((u' : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) *
        ((u'⁻¹ * w : E) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) ^ p ^ k = 1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      exact hwk
    have hz1 := eq_one_of_mul_scalar_pow p (by omega) hu' (Subgroup.mem_subgroupOf.1 hz) hk'
    have hwu : w = u' := by
      have h2 : u'⁻¹ * w = 1 := Subtype.ext hz1
      rw [inv_mul_eq_one] at h2
      exact h2.symm
    rw [hwu]
    exact hu'
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (elemScalars r K) x
  have hy1 := key y hx
  have hy2 := key y⁻¹ (by rw [map_inv]; exact inv_mem hx)
  have hyN : y ∈ Subgroup.normalizer (((posUnip r K).subgroupOf E : Subgroup E) : Set E) :=
    Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hy1 h hh, fun hh => by
      have := hy2 _ hh
      simpa [mul_assoc] using this⟩
  rw [hN] at hyN
  exact ⟨y, hyN, rfl⟩

theorem aut_map_conj_projFlagStab (hr : 3 ≤ r)
    (φ : (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K) ≃*
      (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K))
    (g : orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K) :
    ∃ h : orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K,
      ((((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
          (QuotientGroup.mk' (elemScalars r K))).map (MulAut.conj g).toMonoidHom).map
          φ.toMonoidHom =
        (((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
          (QuotientGroup.mk' (elemScalars r K))).map (MulAut.conj h).toMonoidHom := by
  have := finite_orthElementaryGroup (r := r) (K := K)
  let p := ringChar K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨S, hS⟩ := projUnip_isSylow (K := K) p hr
  rw [← normalizer_projUnip hr, ← hS]
  let f : (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K) ≃*
      (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K) := (MulAut.conj g).trans φ
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq
    (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K) S
    (Sylow.mapSurjective (f := f.toMonoidHom) f.surjective S)
  refine ⟨h, ?_⟩
  have h1 := congrArg (fun T : Sylow p (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K) =>
    (T : Subgroup (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K))) hh
  simp only [Sylow.coe_subgroup_smul] at h1
  rw [Subgroup.pointwise_smul_def] at h1
  rw [Subgroup.map_equiv_normalizer_eq, Subgroup.map_equiv_normalizer_eq,
    Subgroup.map_equiv_normalizer_eq, Subgroup.map_map]
  congr 2
  exact h1.symm

omit [Finite K] in
theorem conj_projFlagStab_eq_stabilizer (hr : 1 ≤ r) :
    (∀ W ∈ singularFlags (quadPlus r K) (r - 1),
      ∃ h : orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K,
        (((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
            (QuotientGroup.mk' (elemScalars r K))).map (MulAut.conj h).toMonoidHom =
          (MulAction.stabilizer (orthElementaryGroup (quadPlus r K)) W).map
            (QuotientGroup.mk' (elemScalars r K))) ∧
    ∀ h : orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K,
      ∃ W ∈ singularFlags (quadPlus r K) (r - 1),
        (((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
            (QuotientGroup.mk' (elemScalars r K))).map (MulAut.conj h).toMonoidHom =
          (MulAction.stabilizer (orthElementaryGroup (quadPlus r K)) W).map
            (QuotientGroup.mk' (elemScalars r K)) := by
  set E := orthElementaryGroup (quadPlus r K)
  have hconj : ∀ g : E, ((MulAction.stabilizer E (stdFlag r K)).map
      (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' (elemScalars r K)) =
        ((MulAction.stabilizer E (stdFlag r K)).map (QuotientGroup.mk' (elemScalars r K))).map
          (MulAut.conj (QuotientGroup.mk' (elemScalars r K) g)).toMonoidHom := by
    intro g
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  refine ⟨fun W hW => ?_, fun h => ?_⟩
  · rw [← orbit_stdFlag hr] at hW
    obtain ⟨g, rfl⟩ := hW
    refine ⟨QuotientGroup.mk' (elemScalars r K) g, ?_⟩
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, hconj, stabilizer_stdFlag]
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elemScalars r K) h
    refine ⟨g • stdFlag r K, by rw [← orbit_stdFlag hr]; exact ⟨g, rfl⟩, ?_⟩
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, hconj, stabilizer_stdFlag]

end Projective

theorem orthogonal_geometry_split_Sylow_flag_normalizer [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hr : 3 ≤ r) :
    (∃ S : Sylow p (orthElementaryGroup (quadPlus r K)),
      (S : Subgroup (orthElementaryGroup (quadPlus r K))) =
        (posUnip r K).subgroupOf (orthElementaryGroup (quadPlus r K))) ∧
    Subgroup.normalizer (((posUnip r K).subgroupOf (orthElementaryGroup (quadPlus r K)) :
        Subgroup (orthElementaryGroup (quadPlus r K))) :
          Set (orthElementaryGroup (quadPlus r K))) =
      (flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K)) ∧
    (∃ S : Sylow p (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K),
      (S : Subgroup (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K)) =
        ((posUnip r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
          (QuotientGroup.mk' (elemScalars r K))) ∧
    Subgroup.normalizer ((((posUnip r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
        (QuotientGroup.mk' (elemScalars r K)) :
          Subgroup (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K)) :
        Set (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K)) =
      ((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
        (QuotientGroup.mk' (elemScalars r K)) ∧
    (∀ (φ : (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K) ≃*
        (orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K))
      (g : orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K),
      ∃ h : orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K,
        ((((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
            (QuotientGroup.mk' (elemScalars r K))).map (MulAut.conj g).toMonoidHom).map
            φ.toMonoidHom =
          (((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
            (QuotientGroup.mk' (elemScalars r K))).map (MulAut.conj h).toMonoidHom) ∧
    (∀ W ∈ singularFlags (quadPlus r K) (r - 1),
      ∃ h : orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K,
        (((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
            (QuotientGroup.mk' (elemScalars r K))).map (MulAut.conj h).toMonoidHom =
          (MulAction.stabilizer (orthElementaryGroup (quadPlus r K)) W).map
            (QuotientGroup.mk' (elemScalars r K))) ∧
    ∀ h : orthElementaryGroup (quadPlus r K) ⧸ elemScalars r K,
      ∃ W ∈ singularFlags (quadPlus r K) (r - 1),
        (((flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K))).map
            (QuotientGroup.mk' (elemScalars r K))).map (MulAut.conj h).toMonoidHom =
          (MulAction.stabilizer (orthElementaryGroup (quadPlus r K)) W).map
            (QuotientGroup.mk' (elemScalars r K)) := by
  have hXX : ∀ a ∈ orthElementaryGroup (quadPlus r K),
      (flag r K r).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ≠
        Xstar r K (by omega) := fun a ha => map_flag_top_ne_Xstar hr ha
  exact ⟨posUnip_isSylow p (by omega) hXX, normalizer_posUnip (by omega) hXX,
    projUnip_isSylow p hr, normalizer_projUnip hr, aut_map_conj_projFlagStab hr,
    (conj_projFlagStab_eq_stabilizer (by omega)).1, (conj_projFlagStab_eq_stabilizer (by omega)).2⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
