module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Matrix CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type*} [Field K]

theorem eichler_inl_inr_apply {i j : Fin r} (hij : i ≠ j) (t : K) (v : Fin r ⊕ Fin r → K) :
    eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inr j) 1) v =
      v + (t * v (Sum.inl j)) • Pi.single (Sum.inl i) 1 -
        (t * v (Sum.inr i)) • Pi.single (Sum.inr j) 1 := by
  have hv : polar (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inr j) 1) = 0 :=
    polar_single_smul_single (by simpa using Ne.symm hij) _
  rw [eichler_apply (quadPlus_single (Sum.inl i)) hv, polar_single, polar_smul_right_eq,
    polar_single, map_smul_eq_sq, quadPlus_single]
  simp only [Sum.swap_inl, Sum.swap_inr, mul_zero, zero_mul, add_zero, neg_mul, neg_smul,
    smul_neg, smul_smul, sub_neg_eq_add]
  rw [mul_comm (v (Sum.inr i)) t]
  abel

theorem eichler_inl_inl_apply {i j : Fin r} (t : K) (v : Fin r ⊕ Fin r → K) :
    eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inl j) 1) v =
      v + (t * v (Sum.inr j)) • Pi.single (Sum.inl i) 1 -
        (t * v (Sum.inr i)) • Pi.single (Sum.inl j) 1 := by
  have hv : polar (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inl j) 1) = 0 :=
    polar_single_smul_single (by simp) _
  rw [eichler_apply (quadPlus_single (Sum.inl i)) hv, polar_single, polar_smul_right_eq,
    polar_single, map_smul_eq_sq, quadPlus_single]
  simp only [Sum.swap_inl, mul_zero, zero_mul, add_zero, neg_mul, neg_smul, smul_neg, smul_smul,
    sub_neg_eq_add]
  rw [mul_comm (v (Sum.inr i)) t]
  abel

theorem sub_mem_of_inl_inr {W : Submodule K (Fin r ⊕ Fin r → K)} {i j : Fin r} (hij : i ≠ j)
    (hW : ∀ w ∈ W, eichler (quadPlus r K) (Pi.single (Sum.inl i) 1)
      ((-1 : K) • Pi.single (Sum.inr j) 1) w ∈ W) {w : Fin r ⊕ Fin r → K} (hw : w ∈ W) :
    w (Sum.inl j) • (Pi.single (Sum.inl i) 1 : Fin r ⊕ Fin r → K) -
      w (Sum.inr i) • Pi.single (Sum.inr j) 1 ∈ W := by
  have h := W.sub_mem (hW w hw) hw
  rw [eichler_inl_inr_apply hij, one_mul, one_mul] at h
  convert h using 1
  abel

theorem sub_mem_of_inl_inl {W : Submodule K (Fin r ⊕ Fin r → K)} {i j : Fin r}
    (hW : ∀ w ∈ W, eichler (quadPlus r K) (Pi.single (Sum.inl i) 1)
      ((-1 : K) • Pi.single (Sum.inl j) 1) w ∈ W) {w : Fin r ⊕ Fin r → K} (hw : w ∈ W) :
    w (Sum.inr j) • (Pi.single (Sum.inl i) 1 : Fin r ⊕ Fin r → K) -
      w (Sum.inr i) • Pi.single (Sum.inl j) 1 ∈ W := by
  have h := W.sub_mem (hW w hw) hw
  rw [eichler_inl_inl_apply, one_mul, one_mul] at h
  convert h using 1
  abel

theorem mem_of_smul_mem {W : Submodule K (Fin r ⊕ Fin r → K)} {c : K} (hc : c ≠ 0)
    {v : Fin r ⊕ Fin r → K} (h : c • v ∈ W) : v ∈ W := by
  have := W.smul_mem c⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

variable (r K) in
@[expose] noncomputable def Xstar (hr : 0 < r) : Submodule K (Fin r ⊕ Fin r → K) :=
  flag r K (r - 1) ⊔ K ∙ (Pi.single (Sum.inr (⟨r - 1, by omega⟩ : Fin r)) (1 : K) :
    Fin r ⊕ Fin r → K)

theorem mem_Xstar (hr : 0 < r) {v : Fin r ⊕ Fin r → K} :
    v ∈ Xstar r K hr ↔ v (Sum.inl ⟨r - 1, by omega⟩) = 0 ∧
      ∀ k : Fin r, k ≠ ⟨r - 1, by omega⟩ → v (Sum.inr k) = 0 := by
  constructor
  · intro hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [mem_flag_iff_coord] at ha
    refine ⟨?_, fun k hk => ?_⟩
    · simp [ha.2 ⟨r - 1, by omega⟩ le_rfl]
    · have hk' : (Sum.inr k : Fin r ⊕ Fin r) ≠ Sum.inr ⟨r - 1, by omega⟩ := by simpa using hk
      simp [ha.1 k, Pi.single_eq_of_ne hk']
  · rintro ⟨h1, h2⟩
    have hdec : v = (v - v (Sum.inr ⟨r - 1, by omega⟩) • Pi.single (Sum.inr ⟨r - 1, by omega⟩) 1) +
        v (Sum.inr ⟨r - 1, by omega⟩) • Pi.single (Sum.inr ⟨r - 1, by omega⟩) 1 := by abel
    rw [hdec]
    refine Submodule.add_mem_sup ?_ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    rw [mem_flag_iff_coord]
    refine ⟨fun k => ?_, fun k hk => ?_⟩
    · by_cases hk : k = ⟨r - 1, by omega⟩
      · subst hk
        simp
      · have hk' : (Sum.inr k : Fin r ⊕ Fin r) ≠ Sum.inr ⟨r - 1, by omega⟩ := by simpa using hk
        simp [h2 k hk, Pi.single_eq_of_ne hk']
    · have hkz : k = ⟨r - 1, by omega⟩ := Fin.ext (by have := k.2; simp only; omega)
      rw [hkz]
      simp [h1]

theorem flag_succ_le {W : Submodule K (Fin r ⊕ Fin r → K)} {m : ℕ} {a : Fin r} (ha : (a : ℕ) = m)
    (hF : flag r K m ≤ W) (he : (Pi.single (Sum.inl a) (1 : K) : Fin r ⊕ Fin r → K) ∈ W) :
    flag r K (m + 1) ≤ W := by
  rw [flag, Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
  · exact hF (Submodule.subset_span ⟨j, h, rfl⟩)
  · rwa [show j = a from Fin.ext (h.trans ha.symm)]

theorem classify_invariant_singular (hr : 0 < r) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW0 : W ≠ ⊥) (hWs : ∀ x ∈ W, quadPlus r K x = 0)
    (hx : ∀ i j : Fin r, i < j → ∀ w ∈ W, eichler (quadPlus r K) (Pi.single (Sum.inl i) 1)
      ((-1 : K) • Pi.single (Sum.inr j) 1) w ∈ W)
    (hy : ∀ i j : Fin r, i < j → ∀ w ∈ W, eichler (quadPlus r K) (Pi.single (Sum.inl i) 1)
      ((-1 : K) • Pi.single (Sum.inl j) 1) w ∈ W) :
    (∃ m, 1 ≤ m ∧ m ≤ r ∧ W = flag r K m) ∨ W = Xstar r K hr := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : Fin r, (z : ℕ) = r - 1 := ⟨⟨r - 1, by omega⟩, rfl⟩
  have hz' : z = ⟨r - 1, by omega⟩ := Fin.ext hz
  have hzlt : ∀ c : Fin r, c ≠ z → (c : ℕ) < r - 1 := fun c hc => by
    have h1 := c.2
    have h2 : (c : ℕ) ≠ r - 1 := fun h => hc (Fin.ext (h.trans hz.symm))
    omega
  obtain ⟨m, hmW, hmr, hgreat⟩ : ∃ m, flag r K m ≤ W ∧ m ≤ r ∧
      ∀ k, m < k → k ≤ r → ¬flag r K k ≤ W :=
    ⟨Nat.findGreatest (fun i => flag r K i ≤ W) r,
      Nat.findGreatest_spec (P := fun i => flag r K i ≤ W) (Nat.zero_le r) (by simp [flag]),
      Nat.findGreatest_le r, fun k hk hkr => Nat.findGreatest_is_greatest hk hkr⟩
  have horth : ∀ v ∈ W, ∀ c : Fin r ⊕ Fin r, (Pi.single c (1 : K) : Fin r ⊕ Fin r → K) ∈ W →
      v c.swap = 0 := fun v hv c hc => by
    rw [← polar_single v c]
    exact polar_eq_zero_of_singular hWs hv hc
  by_cases hWm : W ≤ flag r K m
  · refine Or.inl ⟨m, ?_, hmr, le_antisymm hWm hmW⟩
    by_contra h0
    have hm0 : m = 0 := by omega
    apply hW0
    rw [eq_bot_iff]
    refine hWm.trans ?_
    rw [hm0, flag, Set.image_eq_empty.2 (Set.eq_empty_of_forall_notMem fun j hj => ?_)]
    · simp
    · exact Nat.not_lt_zero _ hj
  have hmr' : m < r := by
    refine lt_of_le_of_ne hmr fun hmr' => hWm fun w hw => ?_
    rw [mem_flag_iff_coord]
    refine ⟨fun k => ?_, fun k hk => ?_⟩
    · have := horth w hw (Sum.inl k)
        (hmW (Submodule.subset_span ⟨k, show (k : ℕ) < m by have := k.2; omega, rfl⟩))
      simpa using this
    · exfalso
      have := k.2
      omega
  obtain ⟨a, ha⟩ : ∃ a : Fin r, (a : ℕ) = m := ⟨⟨m, hmr'⟩, rfl⟩
  have hea_not : (Pi.single (Sum.inl a) (1 : K) : Fin r ⊕ Fin r → K) ∉ W := fun he =>
    hgreat (m + 1) (Nat.lt_succ_self m) hmr' (flag_succ_le ha hmW he)
  have hF : ∀ k : Fin r, (k : ℕ) < m → (Pi.single (Sum.inl k) (1 : K) : Fin r ⊕ Fin r → K) ∈ W :=
    fun k hk => hmW (Submodule.subset_span ⟨k, hk, rfl⟩)
  obtain ⟨w₀, hw₀W, hw₀⟩ := Set.not_subset.1 hWm
  obtain ⟨S, hS⟩ : ∃ S : Fin r ⊕ Fin r → K, S = ∑ k : Fin r, if (k : ℕ) < m then
      w₀ (Sum.inl k) • (Pi.single (Sum.inl k) (1 : K) : Fin r ⊕ Fin r → K) else 0 := ⟨_, rfl⟩
  have hSF : S ∈ flag r K m := by
    rw [hS]
    refine Submodule.sum_mem _ fun k _ => ?_
    split_ifs with hk
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · exact zero_mem _
  obtain ⟨w, hw⟩ : ∃ w : Fin r ⊕ Fin r → K, w = w₀ - S := ⟨_, rfl⟩
  have hwW : w ∈ W := by rw [hw]; exact W.sub_mem hw₀W (hmW hSF)
  have hwF : w ∉ flag r K m := fun h => hw₀ (by
    have := (flag r K m).add_mem h hSF
    rwa [hw, sub_add_cancel] at this)
  have hwl : ∀ k : Fin r, (k : ℕ) < m → w (Sum.inl k) = 0 := fun k hk => by
    rw [hw, Pi.sub_apply, hS, Finset.sum_apply, Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hjk
      split_ifs <;> simp [Ne.symm hjk]
    · simp
  have hwr : ∀ k : Fin r, (k : ℕ) < m → w (Sum.inr k) = 0 := fun k hk => by
    have := horth w hwW (Sum.inl k) (hF k hk)
    simpa using this
  suffices hkey : (Pi.single (Sum.inl a) (1 : K) : Fin r ⊕ Fin r → K) ∈ W ∨
      (m = r - 1 ∧ (Pi.single (Sum.inr z) (1 : K) : Fin r ⊕ Fin r → K) ∈ W) by
    rcases hkey with he | ⟨hm1, hf⟩
    · exact absurd he hea_not
    refine Or.inr (le_antisymm (fun v hv => ?_) (sup_le (by rw [← hm1]; exact hmW)
      ((Submodule.span_singleton_le_iff_mem _ _).2 (by rw [← hz']; exact hf))))
    refine (mem_Xstar hr).2 ⟨?_, fun k hk => ?_⟩
    · have := horth v hv (Sum.inr z) hf
      rw [← hz']
      simpa using this
    · have hk' : (k : ℕ) < m := by rw [hm1]; exact hzlt k (by rw [hz']; exact hk)
      have := horth v hv (Sum.inl k) (hF k hk')
      simpa using this
  rw [mem_flag_iff_coord] at hwF
  push Not at hwF
  by_cases hA : ∃ k, w (Sum.inr k) ≠ 0
  · obtain ⟨k, hk⟩ := hA
    by_cases hA1 : ∃ k' : Fin r, (k' : ℕ) < r - 1 ∧ w (Sum.inr k') ≠ 0
    ·
      obtain ⟨k', hk'r, hk'⟩ := hA1
      have hk'z : k' < z := by rw [Fin.lt_def, hz]; exact hk'r
      have hmk' : m ≤ k' := by
        by_contra h
        exact hk' (hwr k' (by omega))
      have hv := sub_mem_of_inl_inr hk'z.ne (hx k' z hk'z) hwW
      obtain ⟨v, hvdef⟩ : ∃ v : Fin r ⊕ Fin r → K, v = w (Sum.inl z) •
          (Pi.single (Sum.inl k') (1 : K) : Fin r ⊕ Fin r → K) -
            w (Sum.inr k') • Pi.single (Sum.inr z) 1 := ⟨_, rfl⟩
      rw [← hvdef] at hv
      have haz : a < z := by rw [Fin.lt_def, ha, hz]; omega
      have hu := sub_mem_of_inl_inl (hy a z haz) hv
      have hvz : v (Sum.inr z) = -w (Sum.inr k') := by simp [hvdef]
      have hva : v (Sum.inr a) = 0 := by simp [hvdef, haz.ne]
      rw [hvz, hva, zero_smul, sub_zero] at hu
      exact Or.inl (mem_of_smul_mem (neg_ne_zero.2 hk') hu)
    · push Not at hA1
      have hkz : k = z := by
        by_contra h
        exact hk (hA1 k (hzlt k h))
      rw [hkz] at hk
      by_cases hmz : m < r - 1
      ·
        have haz : a < z := by rw [Fin.lt_def, ha, hz]; exact hmz
        have hu := sub_mem_of_inl_inl (hy a z haz) hwW
        rw [hA1 a (by rw [ha]; exact hmz), zero_smul, sub_zero] at hu
        exact Or.inl (mem_of_smul_mem hk hu)
      ·
        have hm1 : m = r - 1 := by omega
        refine Or.inr ⟨hm1, mem_of_smul_mem hk ?_⟩
        have hQ := hWs w hwW
        rw [quadPlus_apply, Finset.sum_eq_single z (fun j _ hj => by
          rw [hA1 j (hzlt j hj), mul_zero]) (by simp)] at hQ
        have hlz : w (Sum.inl z) = 0 := (mul_eq_zero.1 hQ).resolve_right hk
        have hweq : w = w (Sum.inr z) • Pi.single (Sum.inr z) 1 := by
          ext c
          rcases c with c | c
          · by_cases hc : c = z
            · rw [hc]
              simp [hlz]
            · have hcm : (c : ℕ) < m := by rw [hm1]; exact hzlt c hc
              simp [hwl c hcm]
          · by_cases hc : c = z
            · rw [hc]
              simp
            · simp [hc, hA1 c (hzlt c hc)]
        rw [← hweq]
        exact hwW
  · push Not at hA
    obtain ⟨k, hmk, hk⟩ := hwF hA
    by_cases hB : ∃ k' : Fin r, a < k' ∧ w (Sum.inl k') ≠ 0
    ·
      obtain ⟨k', hak', hk'⟩ := hB
      have hu := sub_mem_of_inl_inr hak'.ne (hx a k' hak') hwW
      rw [hA a, zero_smul, sub_zero] at hu
      exact Or.inl (mem_of_smul_mem hk' hu)
    ·
      push Not at hB
      have hka : k = a := by
        by_contra h
        have : a < k := by
          rw [Fin.lt_def, ha]
          have : (k : ℕ) ≠ m := fun h' => h (Fin.ext (h'.trans ha.symm))
          omega
        exact hk (hB k this)
      rw [hka] at hk
      have hweq : w = w (Sum.inl a) • Pi.single (Sum.inl a) 1 := by
        ext c
        rcases c with c | c
        · rcases lt_trichotomy c a with h | h | h
          · have hcm : (c : ℕ) < m := by rw [← ha]; exact h
            simp [h.ne, hwl c hcm]
          · rw [h]
            simp
          · simp [h.ne', hB c h]
        · simp [hA c]
      refine Or.inl (mem_of_smul_mem hk ?_)
      rw [← hweq]
      exact hwW

theorem eichler_inl_inr_mem_posUnip {i j : Fin r} (hij : i < j) (t : K) :
    eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inr j) 1) ∈
      posUnip r K := by
  rw [posUnip_eq_closure]
  exact Subgroup.subset_closure (Or.inl ⟨i, j, t, hij, rfl⟩)

theorem eichler_inl_inl_mem_posUnip {i j : Fin r} (hij : i < j) (t : K) :
    eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inl j) 1) ∈
      posUnip r K := by
  rw [posUnip_eq_closure]
  exact Subgroup.subset_closure (Or.inr ⟨i, j, t, hij, rfl⟩)

theorem finrank_flag_of_le {i : ℕ} (hi : i ≤ r) : finrank K (flag r K i) = i := by
  have hli : LinearIndependent K
      (fun j : Fin r => (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K)) := by
    have := (Pi.basisFun K (Fin r ⊕ Fin r)).linearIndependent.comp Sum.inl Sum.inl_injective
    simpa [Function.comp_def] using this
  rw [flag]
  exact SymplecticFlag.finrank_span_image_lt hli hi

theorem flag_singular (i : ℕ) : ∀ x ∈ flag r K i, quadPlus r K x = 0 := fun x hx =>
  map_eq_zero_of_mem_span (by rintro _ ⟨j, -, rfl⟩; exact quadPlus_single _)
    (by rintro _ ⟨j, -, rfl⟩ _ ⟨k, -, rfl⟩; exact polar_single_single (by simp)) hx

theorem map_Xstar_of_mem_posUnip (hr : 0 < r) {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ posUnip r K) :
    (Xstar r K hr).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = Xstar r K hr := by
  have hstab : posUnip r K ≤ MulAction.stabilizer
      ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Xstar r K hr) := by
    rw [posUnip_eq_closure, Subgroup.closure_le]
    intro g hg
    refine mem_stabilizer_iff_map.2 (Submodule.eq_of_le_of_finrank_eq ?_
      (LinearEquiv.finrank_map_eq g _))
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_Xstar] at hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [mem_Xstar]
    rcases hg with ⟨i, j, t, hij, rfl⟩ | ⟨i, j, t, hij, rfl⟩
    · have hiz : i ≠ ⟨r - 1, by omega⟩ := fun h => by
        have := j.2
        rw [Fin.lt_def, h] at hij
        simp only at hij
        omega
      change (eichler _ _ _ v) _ = 0 ∧ ∀ k, k ≠ _ → (eichler _ _ _ v) _ = 0
      rw [eichler_inl_inr_apply hij.ne]
      refine ⟨by simp [hv1, hiz.symm], fun k hk => ?_⟩
      simp [hv2 k hk, hv2 i hiz]
    · have hiz : i ≠ ⟨r - 1, by omega⟩ := fun h => by
        have := j.2
        rw [Fin.lt_def, h] at hij
        simp only at hij
        omega
      change (eichler _ _ _ v) _ = 0 ∧ ∀ k, k ≠ _ → (eichler _ _ _ v) _ = 0
      rw [eichler_inl_inl_apply]
      refine ⟨by simp [hv1, hiz.symm, hv2 i hiz], fun k hk => ?_⟩
      simp [hv2 k hk]
  exact mem_stabilizer_iff_map.1 (hstab hg)

theorem orthogonal_geometry_split_unipotent_invariant_singular_subspaces (hr : 2 ≤ r) :
    {v : Fin r ⊕ Fin r → K | ∀ g ∈ posUnip r K, g v = v} = (flag r K 1 : Set _) ∧
    (∀ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ → (∀ x ∈ W, quadPlus r K x = 0) →
      ((∀ g ∈ posUnip r K,
          W.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = W) ↔
        (∃ i, 1 ≤ i ∧ i ≤ r - 1 ∧ W = flag r K i) ∨ W = flag r K r ∨
          W = Xstar r K (by omega))) ∧
    (∀ i, flag r K i ≤ flag r K (i + 1)) ∧
    (∀ i, 1 ≤ i → i ≤ r - 1 → finrank K (flag r K i) = i ∧
      (∀ x ∈ flag r K i, quadPlus r K x = 0) ∧ ∀ g ∈ posUnip r K,
        (flag r K i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = flag r K i) ∧
    ∀ W : ℕ → Submodule K (Fin r ⊕ Fin r → K), (∀ i, 1 ≤ i → i ≤ r - 1 →
      finrank K (W i) = i ∧ (∀ x ∈ W i, quadPlus r K x = 0) ∧ ∀ g ∈ posUnip r K,
        (W i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = W i) →
      ∀ i, 1 ≤ i → i ≤ r - 1 → W i = flag r K i := by
  have hr0 : 0 < r := by omega
  have hflag : ∀ i, ∀ g ∈ posUnip r K,
      (flag r K i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = flag r K i :=
    fun i g hg => (mem_posBorel.1 (posUnip_le_posBorel hg)).2 i
  have hclass : ∀ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ →
      (∀ x ∈ W, quadPlus r K x = 0) →
      ((∀ g ∈ posUnip r K,
          W.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = W) ↔
        (∃ i, 1 ≤ i ∧ i ≤ r - 1 ∧ W = flag r K i) ∨ W = flag r K r ∨
          W = Xstar r K hr0) := by
    intro W hW0 hWs
    constructor
    · intro hW
      have hmem : ∀ g ∈ posUnip r K, ∀ w ∈ W, g w ∈ W := fun g hg w hw => by
        rw [← hW g hg]
        exact Submodule.mem_map_of_mem hw
      rcases classify_invariant_singular hr0 hW0 hWs
        (fun i j hij => hmem _ (eichler_inl_inr_mem_posUnip hij 1))
        (fun i j hij => hmem _ (eichler_inl_inl_mem_posUnip hij 1)) with ⟨m, hm1, hmr, rfl⟩ | h
      · rcases Nat.lt_or_ge m r with h | h
        · exact Or.inl ⟨m, hm1, by omega, rfl⟩
        · exact Or.inr (Or.inl (by rw [show m = r by omega]))
      · exact Or.inr (Or.inr h)
    · rintro (⟨i, -, -, rfl⟩ | rfl | rfl)
      · exact hflag i
      · exact hflag r
      · exact fun g hg => map_Xstar_of_mem_posUnip hr0 hg
  refine ⟨?_, hclass, fun i => ?_, fun i hi hir => ⟨finrank_flag_of_le (by omega), flag_singular i,
    hflag i⟩, fun W hW i hi hir => ?_⟩
  ·
    ext v
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · intro hv
      obtain ⟨z, hz⟩ : ∃ z : Fin r, (z : ℕ) = r - 1 := ⟨⟨r - 1, by omega⟩, rfl⟩
      let o : Fin r := ⟨0, hr0⟩
      have hoz : o < z := by rw [Fin.lt_def, hz]; simp [o]; omega
      rw [mem_flag_iff_coord]
      have hx : ∀ i j : Fin r, i < j → v (Sum.inl j) = 0 ∧ v (Sum.inr i) = 0 := by
        intro i j hij
        have h := hv _ (eichler_inl_inr_mem_posUnip hij 1)
        rw [eichler_inl_inr_apply hij.ne, one_mul, one_mul, add_sub_assoc, add_eq_left,
          sub_eq_zero] at h
        have h1 := congrFun h (Sum.inl i)
        have h2 := congrFun h (Sum.inr j)
        simp at h1 h2
        exact ⟨h1, h2.symm⟩
      refine ⟨fun k => ?_, fun k hk => (hx o k (by rw [Fin.lt_def]; simp [o]; omega)).1⟩
      by_cases hkz : k = z
      ·
        have h := hv _ (eichler_inl_inl_mem_posUnip hoz 1)
        rw [eichler_inl_inl_apply, one_mul, one_mul, add_sub_assoc, add_eq_left,
          sub_eq_zero] at h
        have h1 := congrFun h (Sum.inl o)
        simp [hoz.ne] at h1
        rw [hkz]
        exact h1
      · exact (hx k z (by
          rw [Fin.lt_def, hz]
          have := k.2
          have : (k : ℕ) ≠ r - 1 := fun h => hkz (Fin.ext (h.trans hz.symm))
          omega)).2
    · intro hv g hg
      obtain ⟨A, C, hA, h1, -, -, hgM⟩ := mem_posUnip_iff.1 hg
      rw [mem_flag_iff_coord] at hv
      have hy : v ∘ Sum.inr = 0 := funext hv.1
      rw [apply_eq_of_toMatrix' hgM, hy, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
      ext c
      rcases c with c | c
      · simp only [Sum.elim_inl, Matrix.mulVec, dotProduct, Function.comp_apply]
        rw [Finset.sum_eq_single (⟨0, hr0⟩ : Fin r)]
        · by_cases hc : c = ⟨0, hr0⟩
          · rw [hc, h1, one_mul]
          · rw [hA (show (⟨0, hr0⟩ : Fin r) < c by
              rw [Fin.lt_def]
              have : (c : ℕ) ≠ 0 := fun h => hc (Fin.ext h)
              simp only
              omega), zero_mul, hv.2 c (by have : (c : ℕ) ≠ 0 := fun h => hc (Fin.ext h); omega)]
        · intro j _ hj
          rw [hv.2 j (by have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h); omega), mul_zero]
        · simp
      · simp [hv.1 c]
  · exact Submodule.span_mono (Set.image_mono fun j (hj : (j : ℕ) < i) => Nat.lt_succ_of_lt hj)
  ·
    obtain ⟨hdim, hs, hinv⟩ := hW i hi hir
    have hne : W i ≠ ⊥ := fun h => by rw [h, finrank_bot] at hdim; omega
    rcases (hclass (W i) hne hs).1 hinv with ⟨j, -, hjr, hj⟩ | h | h
    · rw [hj, finrank_flag_of_le (by omega)] at hdim
      rw [hj, hdim]
    · rw [h, finrank_flag_of_le le_rfl] at hdim
      omega
    ·
      have hlt : flag r K (r - 1) < Xstar r K hr0 := by
        refine lt_of_le_of_ne le_sup_left fun heq => ?_
        have hf : (Pi.single (Sum.inr (⟨r - 1, by omega⟩ : Fin r)) (1 : K) :
            Fin r ⊕ Fin r → K) ∈ flag r K (r - 1) := by
          rw [heq]
          exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        have := (mem_flag_iff_coord.1 hf).1 ⟨r - 1, by omega⟩
        simp at this
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rw [finrank_flag_of_le (by omega), ← h, hdim] at this
      omega

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
