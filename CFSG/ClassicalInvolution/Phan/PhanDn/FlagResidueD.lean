module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagGeom
public import CFSG.LieType.CurtisTits.TitsGeometryRetained
public import CFSG.ClassicalInvolution.Phan.PhanDn.PointResidue

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ : K ≃+* K}

@[expose] noncomputable def shiftN (K : Type) [Field K] (m' : ℕ) :
    (k : ℕ) → (Fin (m' + 1) ⊕ Fin (m' + 1) → K) →ₗ[K]
      (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K)
  | 0 => LinearMap.id
  | k + 1 => (shiftEmb (K := K) (m' + k + 1)).comp (shiftN K m' k)

@[simp] theorem shiftN_zero (m' : ℕ) : shiftN K m' 0 = LinearMap.id := rfl

theorem shiftN_injective (m' : ℕ) : ∀ k, Function.Injective (shiftN K m' k)
  | 0 => by
      intro u v h
      simpa using h
  | k + 1 => by
      intro u v h
      change shiftEmb (K := K) (m' + k + 1) (shiftN K m' k u) =
        shiftEmb (K := K) (m' + k + 1) (shiftN K m' k v) at h
      exact shiftN_injective m' k (shiftEmb_injective (m' + k + 1) h)

theorem shiftN_quadPlus (m' : ℕ) : ∀ (k : ℕ) (v : Fin (m' + 1) ⊕ Fin (m' + 1) → K),
    quadPlus (m' + k + 1) K (shiftN K m' k v) = quadPlus (m' + 1) K v
  | 0, v => rfl
  | k + 1, v => by
      change quadPlus (m' + k + 1 + 1) K
        (shiftEmb (K := K) (m' + k + 1) (shiftN K m' k v)) = quadPlus (m' + 1) K v
      rw [quadPlus_shiftEmb, shiftN_quadPlus m' k v]

theorem shiftN_flipHerm (m' : ℕ) : ∀ (k : ℕ) (u v : Fin (m' + 1) ⊕ Fin (m' + 1) → K),
    flipHerm σ (shiftN K m' k u) (shiftN K m' k v) = flipHerm σ u v
  | 0, u, v => rfl
  | k + 1, u, v => by
      change flipHerm σ (shiftEmb (K := K) (m' + k + 1) (shiftN K m' k u))
        (shiftEmb (K := K) (m' + k + 1) (shiftN K m' k v)) = flipHerm σ u v
      rw [flipHerm_shiftEmb, shiftN_flipHerm m' k u v]

theorem shiftN_inl_eq_zero (m' : ℕ) : ∀ (k : ℕ) (v : Fin (m' + 1) ⊕ Fin (m' + 1) → K)
    (i : Fin (m' + k + 1)), (i : ℕ) < k → shiftN K m' k v (Sum.inl i) = 0
  | 0, v, i, hi => by exfalso; omega
  | k + 1, v, i, hi => by
      change shiftEmb (K := K) (m' + k + 1) (shiftN K m' k v) (Sum.inl i) = 0
      by_cases h0 : i = 0
      · subst h0
        simp
      · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
        rw [shiftEmb_inl_succ]
        exact shiftN_inl_eq_zero m' k v j (by simp only [Fin.val_succ] at hi; omega)

theorem shiftN_inr_eq_zero (m' : ℕ) : ∀ (k : ℕ) (v : Fin (m' + 1) ⊕ Fin (m' + 1) → K)
    (i : Fin (m' + k + 1)), (i : ℕ) < k → shiftN K m' k v (Sum.inr i) = 0
  | 0, v, i, hi => by exfalso; omega
  | k + 1, v, i, hi => by
      change shiftEmb (K := K) (m' + k + 1) (shiftN K m' k v) (Sum.inr i) = 0
      by_cases h0 : i = 0
      · subst h0
        simp
      · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
        rw [shiftEmb_inr_succ]
        exact shiftN_inr_eq_zero m' k v j (by simp only [Fin.val_succ] at hi; omega)

@[expose] noncomputable def initResRestrict (K : Type) [Field K] (m' k : ℕ) :
    (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) →ₗ[K] (Fin k ⊕ Fin k → K) :=
  LinearMap.pi fun x : Fin k ⊕ Fin k =>
    match x with
    | Sum.inl i =>
        LinearMap.proj (Sum.inl (⟨i, by omega⟩ : Fin (m' + k + 1)))
    | Sum.inr i =>
        LinearMap.proj (Sum.inr (⟨i, by omega⟩ : Fin (m' + k + 1)))

@[simp] theorem initResRestrict_inl (m' k : ℕ)
    (v : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) (i : Fin k) :
    initResRestrict K m' k v (Sum.inl i) =
      v (Sum.inl (⟨i, by omega⟩ : Fin (m' + k + 1))) := by
  simp [initResRestrict]

@[simp] theorem initResRestrict_inr (m' k : ℕ)
    (v : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) (i : Fin k) :
    initResRestrict K m' k v (Sum.inr i) =
      v (Sum.inr (⟨i, by omega⟩ : Fin (m' + k + 1))) := by
  simp [initResRestrict]

@[expose] noncomputable def initResLift (K : Type) [Field K] (m' k : ℕ) :
    (Fin k ⊕ Fin k → K) →ₗ[K] (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) :=
  LinearMap.pi fun x =>
    match x with
    | Sum.inl j => if h : (j : ℕ) < k then LinearMap.proj (Sum.inl (⟨j, h⟩ : Fin k)) else 0
    | Sum.inr j => if h : (j : ℕ) < k then LinearMap.proj (Sum.inr (⟨j, h⟩ : Fin k)) else 0

theorem initResRestrict_comp_lift (m' k : ℕ) :
    (initResRestrict K m' k).comp (initResLift K m' k) = LinearMap.id := by
  ext c x
  rcases x with i | i <;> simp [initResRestrict, initResLift]

theorem initResRestrict_surjective (m' k : ℕ) :
    Function.Surjective (initResRestrict K m' k) := by
  intro c
  refine ⟨initResLift K m' k c, ?_⟩
  have h := congrArg (fun f => f c) (initResRestrict_comp_lift (K := K) m' k)
  simpa using h

theorem initResRestrict_range (m' k : ℕ) :
    LinearMap.range (initResRestrict K m' k) = ⊤ :=
  LinearMap.range_eq_top.mpr (initResRestrict_surjective m' k)

theorem shiftN_range_eq_ker (m' k : ℕ) :
    LinearMap.range (shiftN K m' k) = LinearMap.ker (initResRestrict K m' k) := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro v ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    funext x
    rcases x with i | i
    · simpa using shiftN_inl_eq_zero m' k u ⟨i, by omega⟩ i.is_lt
    · simpa using shiftN_inr_eq_zero m' k u ⟨i, by omega⟩ i.is_lt
  · rw [LinearMap.finrank_range_of_inj (shiftN_injective m' k), finrank_flipSpace]
    have h := LinearMap.finrank_range_add_finrank_ker (initResRestrict K m' k)
    rw [initResRestrict_range, finrank_top, finrank_flipSpace (k) K,
      finrank_flipSpace (m' + k + 1) K] at h
    omega

@[expose] noncomputable def initResW (K : Type) [Field K] (m' k : ℕ) :
    Submodule K (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) :=
  LinearMap.range (shiftN K m' k)

theorem initResW_inl_eq_zero {m' k : ℕ} {v : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K}
    (hv : v ∈ initResW K m' k) {i : Fin (m' + k + 1)} (hi : (i : ℕ) < k) :
    v (Sum.inl i) = 0 := by
  rw [initResW, shiftN_range_eq_ker, LinearMap.mem_ker] at hv
  have h := congrFun hv (Sum.inl (⟨i, hi⟩ : Fin k))
  simpa using h

theorem initResW_inr_eq_zero {m' k : ℕ} {v : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K}
    (hv : v ∈ initResW K m' k) {i : Fin (m' + k + 1)} (hi : (i : ℕ) < k) :
    v (Sum.inr i) = 0 := by
  rw [initResW, shiftN_range_eq_ker, LinearMap.mem_ker] at hv
  have h := congrFun hv (Sum.inr (⟨i, hi⟩ : Fin k))
  simpa using h

@[expose] noncomputable def initResT (K : Type) [Field K] (σ : K ≃+* K) (m' k : ℕ) :
    Submodule K (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) :=
  (stdDChamber σ (m' + k + 1)).sub k

theorem initResT_finrank (m' k : ℕ) : Module.finrank K (initResT K σ m' k) = k :=
  (stdDChamber σ (m' + k + 1)).toFlipFrame.finrank_sub (by omega)

theorem initResT_isFlipflopSub (hσ : ∀ x, σ (σ x) = x) (m' k : ℕ) :
    IsFlipflopSub σ (initResT K σ m' k) :=
  (stdDChamber σ (m' + k + 1)).toFlipFrame.isFlipflopSub_sub hσ k

theorem initResT_ne_bot {m' k : ℕ} (hk : 1 ≤ k) : initResT K σ m' k ≠ ⊥ := by
  intro h
  have hfin := initResT_finrank (K := K) (σ := σ) m' k
  rw [h, finrank_bot] at hfin
  omega

theorem initResT_eq_flagChamber (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m') (hk : 1 ≤ k) :
    initResT K σ m' k =
      (flagChamber E (m' + k) (⟨k - 1, by omega⟩ : Fin (m' + k + 1))).1 := by
  rw [initResT, coe_flagChamber]
  rw [FlipFrame.elt_of_add_one_lt _ _ (by simp; omega)]
  congr 1
  change k = (k - 1) + 1
  omega

theorem initRes_flagChamber_le_T (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m')
    {j : Fin (m' + k + 1)} (hj : (j : ℕ) < k) :
    (flagChamber E (m' + k) j).1 ≤ initResT K σ m' k := by
  rw [initResT, coe_flagChamber]
  rw [FlipFrame.elt_of_add_one_lt _ _ (by omega)]
  exact FlipFrame.sub_mono (stdDChamber σ (m' + k + 1)).toFlipFrame (by omega)

theorem initRes_sub_le_ker_inr (m' k : ℕ) {j : ℕ} (hj : j ≤ k) (i : Fin (m' + k + 1)) :
    (stdDChamber σ (m' + k + 1)).sub j ≤ LinearMap.ker
      (LinearMap.proj (Sum.inr i) : (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) →ₗ[K] K) := by
  induction j with
  | zero =>
      rw [FlipFrame.sub_zero]
      exact bot_le
  | succ j ih =>
      rw [FlipFrame.sub_succ _ (by omega)]
      refine sup_le (ih (by omega)) ?_
      rw [stdDChamber_line]
      refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
      rw [LinearMap.mem_ker]
      simp

theorem initRes_sub_le_ker_inl (m' k : ℕ) {j : ℕ} (hj : j ≤ k) {i : Fin (m' + k + 1)}
    (hi : j ≤ (i : ℕ)) :
    (stdDChamber σ (m' + k + 1)).sub j ≤ LinearMap.ker
      (LinearMap.proj (Sum.inl i) : (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) →ₗ[K] K) := by
  induction j with
  | zero =>
      rw [FlipFrame.sub_zero]
      exact bot_le
  | succ j ih =>
      rw [FlipFrame.sub_succ _ (by omega)]
      refine sup_le (ih (by omega) (by omega)) ?_
      rw [stdDChamber_line]
      refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
      rw [LinearMap.mem_ker]
      simp only [LinearMap.proj_apply, stdE_inl]
      have hne : i ≠ (⟨j, by omega⟩ : Fin (m' + k + 1)) := by
        intro h
        have h' : (i : ℕ) = j := by simpa using congrArg Fin.val h
        omega
      simp [hne]

theorem initResT_inr_eq_zero {m' k : ℕ} {v : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K}
    (hv : v ∈ initResT K σ m' k) (i : Fin (m' + k + 1)) : v (Sum.inr i) = 0 := by
  rw [initResT] at hv
  exact initRes_sub_le_ker_inr (σ := σ) m' k le_rfl i hv

theorem initResT_inl_eq_zero {m' k : ℕ} {v : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K}
    (hv : v ∈ initResT K σ m' k) {i : Fin (m' + k + 1)} (hi : k ≤ (i : ℕ)) :
    v (Sum.inl i) = 0 := by
  rw [initResT] at hv
  exact initRes_sub_le_ker_inl (σ := σ) m' k le_rfl hi hv

theorem initRes_sub_le_qPerp_W (m' k : ℕ) {j : ℕ} (hj : j ≤ k) :
    (stdDChamber σ (m' + k + 1)).sub j ≤ qPerp (m' + k + 1) K (initResW K m' k) := by
  induction j with
  | zero =>
      rw [FlipFrame.sub_zero]
      exact bot_le
  | succ j ih =>
      rw [FlipFrame.sub_succ _ (by omega)]
      refine sup_le (ih (by omega)) ?_
      rw [stdDChamber_line]
      refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
      rw [mem_qPerp]
      intro w hw
      have h := polar_quadPlus_single_inl (n := m' + k + 1) (K := K) w
        (⟨j, by omega⟩ : Fin (m' + k + 1))
      rw [show polar (quadPlus (m' + k + 1) K) w
          (stdE (K := K) (n := m' + k + 1) ⟨j, by omega⟩) = w (Sum.inr ⟨j, by omega⟩) by
        simpa [stdE] using h]
      exact initResW_inr_eq_zero hw (by simp; omega)

theorem initRes_sub_le_flipOrth_W (m' k : ℕ) {j : ℕ} (hj : j ≤ k) :
    (stdDChamber σ (m' + k + 1)).sub j ≤ flipOrth σ (initResW K m' k) := by
  induction j with
  | zero =>
      rw [FlipFrame.sub_zero]
      exact bot_le
  | succ j ih =>
      rw [FlipFrame.sub_succ _ (by omega)]
      refine sup_le (ih (by omega)) ?_
      rw [stdDChamber_line]
      refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
      rw [mem_flipOrth]
      intro w hw
      rw [flipHerm, dFlip_stdE]
      have h := polar_quadPlus_single_inr (n := m' + k + 1) (K := K) w
        (⟨j, by omega⟩ : Fin (m' + k + 1))
      rw [show polar (quadPlus (m' + k + 1) K) w
          (stdF (K := K) (n := m' + k + 1) ⟨j, by omega⟩) = w (Sum.inl ⟨j, by omega⟩) by
        simpa [stdF] using h]
      exact initResW_inl_eq_zero hw (by simp; omega)

theorem initResT_le_qPerp_W (m' k : ℕ) :
    initResT K σ m' k ≤ qPerp (m' + k + 1) K (initResW K m' k) := by
  rw [initResT]
  exact initRes_sub_le_qPerp_W m' k le_rfl

theorem initResT_le_flipOrth_W (m' k : ℕ) :
    initResT K σ m' k ≤ flipOrth σ (initResW K m' k) := by
  rw [initResT]
  exact initRes_sub_le_flipOrth_W m' k le_rfl

theorem initResT_inf_W (m' k : ℕ) :
    initResT K σ m' k ⊓ initResW K m' k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨hvT, hvW⟩ := Submodule.mem_inf.mp hv
  funext x
  rcases x with i | i
  · by_cases hi : (i : ℕ) < k
    · exact initResW_inl_eq_zero hvW hi
    · exact initResT_inl_eq_zero hvT (by omega)
  · exact initResT_inr_eq_zero hvT i

@[expose] noncomputable def initResPart (K : Type) [Field K] (m' k : ℕ)
    (x : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) :
    Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K :=
  ∑ i : Fin k, x (Sum.inl (⟨i, by omega⟩ : Fin (m' + k + 1))) •
    stdE (K := K) (n := m' + k + 1) (⟨i, by omega⟩ : Fin (m' + k + 1))

theorem initResPart_inl (m' k : ℕ)
    (x : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) (i : Fin k) :
    initResPart K m' k x (Sum.inl (⟨i, by omega⟩ : Fin (m' + k + 1))) =
      x (Sum.inl (⟨i, by omega⟩ : Fin (m' + k + 1))) := by
  rw [initResPart, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : (⟨i, by omega⟩ : Fin (m' + k + 1)) ≠ ⟨j, by omega⟩ := by
      intro h
      exact hji (Fin.ext (by simpa using congrArg Fin.val h.symm))
    simp [stdE, hne]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem initResPart_inr (m' k : ℕ)
    (x : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) (i : Fin k) :
    initResPart K m' k x (Sum.inr (⟨i, by omega⟩ : Fin (m' + k + 1))) = 0 := by
  rw [initResPart, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp

theorem initResPart_mem_T (m' k : ℕ)
    (x : Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K) :
    initResPart K m' k x ∈ initResT K σ m' k := by
  rw [initResT]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hline : (stdDChamber σ (m' + k + 1)).line (⟨i, by omega⟩ : Fin (m' + k + 1)) ≤
      (stdDChamber σ (m' + k + 1)).sub k :=
    FlipFrame.line_le_sub _ (by simp)
  refine Submodule.smul_mem _ _ (hline ?_)
  rw [stdDChamber_line]
  exact Submodule.mem_span_singleton_self _

theorem initRes_finrank_map_shiftN (m' k : ℕ)
    (Y : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) :
    Module.finrank K (Y.map (shiftN K m' k)) = Module.finrank K Y := by
  have hrange : Y.map (shiftN K m' k) =
      LinearMap.range ((shiftN K m' k).comp Y.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hrange]
  exact LinearMap.finrank_range_of_inj
    ((shiftN_injective m' k).comp (Submodule.subtype_injective Y))

theorem initRes_map_isFlipflopSub (m' k : ℕ) {Y : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)}
    (hY : IsFlipflopSub σ Y) :
    IsFlipflopSub σ (Y.map (shiftN K m' k)) := by
  refine ⟨?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    rw [shiftN_quadPlus m' k v]
    exact hY.total v hv
  · intro u hu hper
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    have hv0 : v = 0 := hY.nondeg v hv fun w hw => by
      have h := hper (shiftN K m' k w) (Submodule.mem_map_of_mem hw)
      rwa [shiftN_flipHerm m' k v w] at h
    rw [hv0, map_zero]

theorem initRes_isFlipflopSub_of_map (m' k : ℕ)
    {Y : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)}
    (hY : IsFlipflopSub σ (Y.map (shiftN K m' k))) : IsFlipflopSub σ Y := by
  refine ⟨?_, ?_⟩
  · intro u hu
    have hu' : shiftN K m' k u ∈ Y.map (shiftN K m' k) := Submodule.mem_map_of_mem hu
    have h0 := hY.total _ hu'
    rwa [shiftN_quadPlus m' k u] at h0
  · intro u hu hper
    have hh := hY.nondeg (shiftN K m' k u) (Submodule.mem_map_of_mem hu) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
      rw [shiftN_flipHerm m' k u v]
      exact hper v hv)
    exact shiftN_injective m' k (by simpa using hh)

theorem initRes_sup_isFlipflopSub (hσ : ∀ x, σ (σ x) = x) (m' k : ℕ)
    {Y : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)} (hY : IsFlipflopSub σ Y) :
    IsFlipflopSub σ (initResT K σ m' k ⊔ Y.map (shiftN K m' k)) := by
  refine (IsFlipflopSub.sup_of_orth hσ (initResT_isFlipflopSub hσ m' k)
    (initRes_map_isFlipflopSub m' k hY) ?_ ?_).1
  · exact le_trans (initResT_le_qPerp_W m' k) (qPerp_antitone (LinearMap.map_le_range))
  · intro v hv
    rw [mem_flipOrth]
    intro w hw
    exact (mem_flipOrth.mp (initResT_le_flipOrth_W m' k hv)) w (LinearMap.map_le_range hw)

theorem initRes_finrank_sup (m' k : ℕ)
    (Y : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) :
    Module.finrank K ↥(initResT K σ m' k ⊔ Y.map (shiftN K m' k)) =
      k + Module.finrank K Y := by
  have hdisj : Disjoint (initResT K σ m' k) (Y.map (shiftN K m' k)) := by
    rw [Submodule.disjoint_def]
    intro x hx hy
    have hxW : x ∈ initResW K m' k := LinearMap.map_le_range hy
    have hbot := initResT_inf_W (K := K) (σ := σ) m' k
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot x (Submodule.mem_inf.mpr ⟨hx, hxW⟩)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (initResT K σ m' k)
    (Y.map (shiftN K m' k))
  rw [hdisj.eq_bot, finrank_bot, add_zero, initResT_finrank,
    initRes_finrank_map_shiftN] at hdim
  exact hdim

theorem initRes_sup_inf_W (m' k : ℕ)
    (Y : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) :
    (initResT K σ m' k ⊔ Y.map (shiftN K m' k)) ⊓ initResW K m' k =
      Y.map (shiftN K m' k) := by
  rw [sup_comm, initResW,
    sup_inf_assoc_of_le (initResT K σ m' k) (LinearMap.map_le_range (f := shiftN K m' k)),
    show initResT K σ m' k ⊓ (shiftN K m' k).range = ⊥ from initResT_inf_W m' k,
    sup_bot_eq]

theorem initRes_decomp (m' k : ℕ)
    {X : Submodule K (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K)}
    (hX : IsFlipflopSub σ X) (hT : initResT K σ m' k ≤ X) :
    X = initResT K σ m' k ⊔ (X ⊓ initResW K m' k) := by
  refine le_antisymm ?_ (sup_le hT inf_le_left)
  intro x hx
  let t := initResPart K m' k x
  have htT : t ∈ initResT K σ m' k := initResPart_mem_T m' k x
  have hwX : x - t ∈ X := X.sub_mem hx (hT htT)
  have hx_inr : ∀ i : Fin k, x (Sum.inr (⟨i, by omega⟩ : Fin (m' + k + 1))) = 0 := by
    intro i
    have hstdT : stdE (K := K) (n := m' + k + 1) (⟨i, by omega⟩ : Fin (m' + k + 1)) ∈
        initResT K σ m' k := by
      rw [initResT]
      have hline : (stdDChamber σ (m' + k + 1)).line
          (⟨i, by omega⟩ : Fin (m' + k + 1)) ≤ (stdDChamber σ (m' + k + 1)).sub k :=
        FlipFrame.line_le_sub _ (by simp)
      exact hline (by rw [stdDChamber_line]; exact Submodule.mem_span_singleton_self _)
    have hzero := hX.total (stdE (K := K) (n := m' + k + 1) (⟨i, by omega⟩ : Fin (m' + k + 1)) + x)
      (X.add_mem (hT hstdT) hx)
    have h1 := hX.total (stdE (K := K) (n := m' + k + 1) (⟨i, by omega⟩ : Fin (m' + k + 1)))
      (hT hstdT)
    have h2 := hX.total x hx
    rw [QuadraticMap.map_add (quadPlus (m' + k + 1) K), h1, h2, zero_add, zero_add] at hzero
    have hp : polar (quadPlus (m' + k + 1) K)
        (stdE (K := K) (n := m' + k + 1) (⟨i, by omega⟩ : Fin (m' + k + 1))) x = 0 := by
      simpa using hzero
    have hcoord := polar_quadPlus_single_inl (n := m' + k + 1) (K := K) x
      (⟨i, by omega⟩ : Fin (m' + k + 1))
    rw [polar_comm, show polar (quadPlus (m' + k + 1) K) x
        (stdE (K := K) (n := m' + k + 1) (⟨i, by omega⟩ : Fin (m' + k + 1))) =
      x (Sum.inr (⟨i, by omega⟩ : Fin (m' + k + 1))) by simpa [stdE] using hcoord] at hp
    exact hp
  have hwW : x - t ∈ initResW K m' k := by
    rw [initResW, shiftN_range_eq_ker, LinearMap.mem_ker]
    funext y
    rcases y with i | i
    · rw [initResRestrict_inl]
      simp only [Pi.sub_apply]
      dsimp only [t]
      rw [initResPart_inl]
      simp
    · rw [initResRestrict_inr]
      simp only [Pi.sub_apply]
      dsimp only [t]
      rw [initResPart_inr]
      simp [hx_inr i]
  exact Submodule.mem_sup.mpr ⟨t, htT, x - t, ⟨hwX, hwW⟩, by abel⟩

theorem initRes_inf_W_isFlipflopSub (m' k : ℕ)
    {X : Submodule K (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K)}
    (hX : IsFlipflopSub σ X) (hT : initResT K σ m' k ≤ X) :
    IsFlipflopSub σ (X ⊓ initResW K m' k) := by
  have hdecomp := initRes_decomp m' k hX hT
  refine ⟨fun u hu => hX.total u hu.1, ?_⟩
  intro u hu hper
  apply hX.nondeg u hu.1
  intro v hv
  rw [hdecomp] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [flipHerm_add_right]
  have hua : flipHerm σ u a = 0 :=
    (mem_flipOrth.mp (initResT_le_flipOrth_W m' k ha)) u hu.2
  have hub : flipHerm σ u b = 0 := hper b hb
  rw [hua, hub, add_zero]

theorem initRes_flagGraph_adj_iff (m : ℕ) (U W : FlagVert σ m) :
    (flagGraph σ m).Adj U W ↔ U.1 < W.1 ∨ W.1 < U.1 ∨
      (Module.finrank K U.1 = m + 1 ∧ Module.finrank K W.1 = m + 1 ∧
        Module.finrank K ↥(U.1 ⊓ W.1) = m) := Iff.rfl

theorem initRes_flagTyp_eq_finrank_sub_one {m : ℕ} {U : FlagVert σ m}
    (hU : Module.finrank K U.1 ≠ m + 1) :
    (flagTyp U : ℕ) = Module.finrank K U.1 - 1 := by
  rw [flagTyp, if_neg hU]
  exact min_eq_left (by
    have hle : Module.finrank K U.1 ≤ m + 1 := U.2.1.finrank_le
    omega)

theorem initRes_flagTyp_ge_iff {m k : ℕ} (hkm : k + 1 ≤ m) {U : FlagVert σ m} :
    k ≤ (flagTyp U : ℕ) ↔ k + 1 ≤ Module.finrank K U.1 := by
  by_cases hU : Module.finrank K U.1 = m + 1
  · rw [flagTyp, if_pos hU]
    have hkm' : k ≤ m - 1 := by omega
    by_cases he : Even ((m + 1) - Module.finrank K ↥(U.1 ⊓ stdLag (m + 1) K))
    · rw [if_pos he]
      simp only [Fin.val_last]
      omega
    · rw [if_neg he]
      simp
      omega
  · have hfin := initRes_flagTyp_eq_finrank_sub_one hU
    rw [hfin]
    have hdpos : 0 < Module.finrank K U.1 := by
      by_contra h0
      have hbot : Module.finrank K U.1 = 0 := by omega
      exact U.2.2.1 (Submodule.finrank_eq_zero.mp hbot)
    omega

theorem initRes_flagTyp_ge_of_finrank {m k : ℕ} (hkm : k + 1 ≤ m) {U : FlagVert σ m}
    (h : k + 1 ≤ Module.finrank K U.1) : k ≤ (flagTyp U : ℕ) :=
  (initRes_flagTyp_ge_iff hkm).mpr h

theorem initRes_sup_ne_bot {m' k : ℕ} (hk : 1 ≤ k) (Y : FlagVert σ m') :
    initResT K σ m' k ⊔ Y.1.map (shiftN K m' k) ≠ ⊥ := by
  intro h
  have hT : initResT K σ m' k ≤ ⊥ := by
    rw [← h]
    exact le_sup_left
  exact initResT_ne_bot hk (le_bot_iff.mp hT)

theorem initRes_sup_finrank_ne (m' k : ℕ) (Y : FlagVert σ m') :
    Module.finrank K ↥(initResT K σ m' k ⊔ Y.1.map (shiftN K m' k)) ≠ m' + k := by
  intro h
  have hfin := initRes_finrank_sup (K := K) (σ := σ) m' k Y.1
  rw [h] at hfin
  exact Y.2.2.2 (by omega)

@[expose] noncomputable def initResVertex (E : QuadExt F K σ) {m' k : ℕ} (hk : 1 ≤ k)
    (Y : FlagVert σ m') : FlagVert σ (m' + k) :=
  ⟨initResT K σ m' k ⊔ Y.1.map (shiftN K m' k),
    initRes_sup_isFlipflopSub E.isUnitary.invol m' k Y.2.1,
    initRes_sup_ne_bot hk Y,
    initRes_sup_finrank_ne m' k Y⟩

theorem initResVertex_finrank (E : QuadExt F K σ) {m' k : ℕ} (hk : 1 ≤ k)
    (Y : FlagVert σ m') :
    Module.finrank K (initResVertex E hk Y).1 = k + Module.finrank K Y.1 := by
  rw [show (initResVertex E hk Y).1 =
      initResT K σ m' k ⊔ Y.1.map (shiftN K m' k) from rfl, initRes_finrank_sup]

theorem initRes_flagTyp_ge (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m') (hk : 1 ≤ k)
    (Y : FlagVert σ m') : k ≤ (flagTyp (initResVertex E hk Y) : ℕ) := by
  exact initRes_flagTyp_ge_of_finrank (K := K) (σ := σ) (m := m' + k) (k := k)
    (U := initResVertex E hk Y) (by omega) (by
      rw [initResVertex_finrank]
      have hYpos : 1 ≤ Module.finrank K Y.1 := by
        by_contra h0
        exact Y.2.2.1 (Submodule.finrank_eq_zero.mp (by omega))
      omega)

theorem initRes_flagChamber_lt (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m') (hk : 1 ≤ k)
    (Y : FlagVert σ m') {j : Fin (m' + k + 1)} (hj : (j : ℕ) < k) :
    (flagChamber E (m' + k) j).1 < (initResVertex E hk Y).1 := by
  refine lt_of_le_of_ne (le_trans (initRes_flagChamber_le_T E hm' hj) le_sup_left) ?_
  intro heq
  have hfinC : Module.finrank K (flagChamber E (m' + k) j).1 = (j : ℕ) + 1 := by
    rw [coe_flagChamber]
    rw [FlipFrame.finrank_elt E.isUnitary.invol]
    rw [if_pos (by omega)]
  have hfinX : Module.finrank K (initResVertex E hk Y).1 = k + Module.finrank K Y.1 :=
    initResVertex_finrank E hk Y
  have hYpos : 1 ≤ Module.finrank K Y.1 := by
    by_contra h0
    exact Y.2.2.1 (Submodule.finrank_eq_zero.mp (by omega))
  have hlt : Module.finrank K (flagChamber E (m' + k) j).1 <
      Module.finrank K (initResVertex E hk Y).1 := by
    rw [hfinC, hfinX]
    omega
  rw [heq] at hlt
  exact lt_irrefl _ hlt

@[expose] noncomputable def initResToResidue (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m')
    (hk : 1 ≤ k) (Y : FlagVert σ m') :
    residueVertex (flagGraph σ (m' + k)) flagTyp (flagChamber E (m' + k))
      {j | (j : ℕ) < k} :=
  ⟨initResVertex E hk Y, by
    simp only [Set.mem_setOf_eq, not_lt]
    exact initRes_flagTyp_ge E hm' hk Y, by
    intro j hj
    simp only [Set.mem_setOf_eq] at hj
    exact Or.inr (Or.inl (initRes_flagChamber_lt E hm' hk Y hj))⟩

theorem initRes_T_lt_of_residue (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m') (hk : 1 ≤ k)
    (X : residueVertex (flagGraph σ (m' + k)) flagTyp (flagChamber E (m' + k))
      {j | (j : ℕ) < k}) : initResT K σ m' k < X.1.1 := by
  have hmem : (⟨k - 1, by omega⟩ : Fin (m' + k + 1)) ∈
      {j : Fin (m' + k + 1) | (j : ℕ) < k} := by
    simp only [Set.mem_setOf_eq]
    omega
  have hadj := X.2.2 _ hmem
  rw [initRes_flagGraph_adj_iff] at hadj
  have htyp : k ≤ (flagTyp X.1 : ℕ) := by
    have h := X.2.1
    simp only [Set.mem_setOf_eq] at h
    omega
  have hfinX : k + 1 ≤ Module.finrank K X.1.1 :=
    (initRes_flagTyp_ge_iff (K := K) (σ := σ) (m := m' + k) (k := k) (by omega)).mp htyp
  have hfinC : Module.finrank K
      (flagChamber E (m' + k) (⟨k - 1, by omega⟩ : Fin (m' + k + 1))).1 = k := by
    rw [coe_flagChamber]
    rw [FlipFrame.finrank_elt E.isUnitary.invol]
    rw [if_pos]
    · simp
      omega
    · simp
      omega
  rcases hadj with h | h | h
  · exfalso
    have hlt := Submodule.finrank_lt_finrank_of_lt h
    rw [hfinC] at hlt
    omega
  · rwa [← initResT_eq_flagChamber E hm' hk] at h
  · exfalso
    rw [hfinC] at h
    omega

@[expose] noncomputable def initResInvSub (m' k : ℕ)
    (X : Submodule K (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K)) :
    Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K) :=
  (X ⊓ initResW K m' k).comap (shiftN K m' k)

theorem initRes_invSub_map (m' k : ℕ)
    (X : Submodule K (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K)) :
    (initResInvSub m' k X).map (shiftN K m' k) = X ⊓ initResW K m' k := by
  rw [initResInvSub]
  exact Submodule.map_comap_eq_of_le (f := shiftN K m' k) (by
    rw [initResW]
    exact inf_le_right)

theorem initRes_inv_map_eq (m' k : ℕ)
    {X : Submodule K (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K)}
    (hX : IsFlipflopSub σ X) (hT : initResT K σ m' k ≤ X) :
    initResT K σ m' k ⊔ (initResInvSub m' k X).map (shiftN K m' k) = X := by
  rw [initRes_invSub_map]
  exact (initRes_decomp m' k hX hT).symm

theorem initRes_invSub_isFlipflopSub (m' k : ℕ)
    {X : Submodule K (Fin (m' + k + 1) ⊕ Fin (m' + k + 1) → K)}
    (hX : IsFlipflopSub σ X) (hT : initResT K σ m' k ≤ X) :
    IsFlipflopSub σ (initResInvSub m' k X) := by
  apply initRes_isFlipflopSub_of_map
  rw [initRes_invSub_map]
  exact initRes_inf_W_isFlipflopSub m' k hX hT

theorem initRes_invSub_ne_bot (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m') (hk : 1 ≤ k)
    (X : residueVertex (flagGraph σ (m' + k)) flagTyp (flagChamber E (m' + k))
      {j | (j : ℕ) < k}) : initResInvSub m' k X.1.1 ≠ ⊥ := by
  intro hbot
  have hTlt := initRes_T_lt_of_residue E hm' hk X
  have hXeq : X.1.1 = initResT K σ m' k := by
    rw [← initRes_inv_map_eq m' k X.1.2.1 (le_of_lt hTlt)]
    rw [hbot, Submodule.map_bot, sup_bot_eq]
  have htyp : k ≤ (flagTyp X.1 : ℕ) := by
    have h := X.2.1
    simp only [Set.mem_setOf_eq] at h
    omega
  have hsol : Module.finrank K X.1.1 ≠ m' + k + 1 := by
    rw [hXeq, initResT_finrank]
    omega
  have hflag := initRes_flagTyp_eq_finrank_sub_one (K := K) (σ := σ) (m := m' + k)
    (U := X.1) hsol
  rw [hXeq, initResT_finrank] at hflag
  omega

theorem initRes_invSub_finrank_ne (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m') (hk : 1 ≤ k)
    (X : residueVertex (flagGraph σ (m' + k)) flagTyp (flagChamber E (m' + k))
      {j | (j : ℕ) < k}) : Module.finrank K (initResInvSub m' k X.1.1) ≠ m' := by
  intro hfin
  have hTlt := initRes_T_lt_of_residue E hm' hk X
  have hXfin : Module.finrank K X.1.1 = m' + k := by
    rw [← initRes_inv_map_eq m' k X.1.2.1 (le_of_lt hTlt),
      initRes_finrank_sup (K := K) (σ := σ) m' k (initResInvSub m' k X.1.1), hfin]
    omega
  exact X.1.2.2.2 hXfin

@[expose] noncomputable def initResInv (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m')
    (hk : 1 ≤ k) (X : residueVertex (flagGraph σ (m' + k)) flagTyp
      (flagChamber E (m' + k)) {j | (j : ℕ) < k}) : FlagVert σ m' :=
  ⟨initResInvSub m' k X.1.1,
    initRes_invSub_isFlipflopSub m' k X.1.2.1
      (le_of_lt (initRes_T_lt_of_residue E hm' hk X)),
    initRes_invSub_ne_bot E hm' hk X,
    initRes_invSub_finrank_ne E hm' hk X⟩

theorem initRes_inv_toResidue (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m') (hk : 1 ≤ k)
    (Y : FlagVert σ m') : initResInv E hm' hk (initResToResidue E hm' hk Y) = Y := by
  apply Subtype.ext
  change ((initResToResidue E hm' hk Y).1.1 ⊓ initResW K m' k).comap (shiftN K m' k) = Y.1
  rw [show (initResToResidue E hm' hk Y).1.1 =
      initResT K σ m' k ⊔ Y.1.map (shiftN K m' k) from rfl, initRes_sup_inf_W]
  exact Submodule.comap_map_eq_self (by
    rw [LinearMap.ker_eq_bot.mpr (shiftN_injective m' k)]
    exact bot_le)

theorem initRes_toResidue_inv (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m') (hk : 1 ≤ k)
    (X : residueVertex (flagGraph σ (m' + k)) flagTyp (flagChamber E (m' + k))
      {j | (j : ℕ) < k}) : initResToResidue E hm' hk (initResInv E hm' hk X) = X := by
  apply Subtype.ext
  apply Subtype.ext
  exact initRes_inv_map_eq m' k X.1.2.1
    (le_of_lt (initRes_T_lt_of_residue E hm' hk X))

theorem initRes_lt_iff (m' k : ℕ)
    {Y Y' : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)} :
    (initResT K σ m' k ⊔ Y.map (shiftN K m' k)) <
        (initResT K σ m' k ⊔ Y'.map (shiftN K m' k)) ↔ Y < Y' := by
  constructor
  · intro h
    have hleW : Y.map (shiftN K m' k) ≤ Y'.map (shiftN K m' k) := by
      have hle := inf_le_inf (le_of_lt h) (le_refl (initResW K m' k))
      rwa [initRes_sup_inf_W, initRes_sup_inf_W] at hle
    have hne : Y ≠ Y' := by
      intro heq
      exact h.ne (by rw [heq])
    have hle : Y ≤ Y' := (LinearMap.map_le_map_iff'
      (LinearMap.ker_eq_bot.mpr (shiftN_injective m' k))).mp hleW
    exact lt_of_le_of_ne hle hne
  · intro h
    have hle : (initResT K σ m' k ⊔ Y.map (shiftN K m' k)) ≤
        (initResT K σ m' k ⊔ Y'.map (shiftN K m' k)) := by
      refine sup_le le_sup_left ?_
      exact le_trans (Submodule.map_mono (le_of_lt h)) le_sup_right
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hinf := congrArg (fun Z => Z ⊓ initResW K m' k) heq
    rw [initRes_sup_inf_W, initRes_sup_inf_W] at hinf
    exact h.ne (Submodule.map_injective_of_injective (shiftN_injective m' k) hinf)

theorem initRes_inf_sup (m' k : ℕ)
    (Y Y' : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) :
    (initResT K σ m' k ⊔ Y.map (shiftN K m' k)) ⊓
        (initResT K σ m' k ⊔ Y'.map (shiftN K m' k)) =
      initResT K σ m' k ⊔ (Y ⊓ Y').map (shiftN K m' k) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
    obtain ⟨t1, ht1, a, ha, rfl⟩ := Submodule.mem_sup.mp hz1
    obtain ⟨t2, ht2, b, hb, hEq⟩ := Submodule.mem_sup.mp hz2
    have hdiff : a - b = t2 - t1 := by
      have h : t1 + a = t2 + b := hEq.symm
      calc a - b = (t1 + a) - (t1 + b) := by abel
        _ = (t2 + b) - (t1 + b) := by rw [h]
        _ = t2 - t1 := by abel
    have hmemW : a - b ∈ initResW K m' k :=
      Submodule.sub_mem (initResW K m' k)
        (show a ∈ initResW K m' k from LinearMap.map_le_range ha)
        (show b ∈ initResW K m' k from LinearMap.map_le_range hb)
    have hmemT : a - b ∈ initResT K σ m' k := by
      rw [hdiff]
      exact Submodule.sub_mem (initResT K σ m' k) ht2 ht1
    have hzero : a - b = 0 := by
      have hmem : a - b ∈ initResT K σ m' k ⊓ initResW K m' k := ⟨hmemT, hmemW⟩
      rw [initResT_inf_W] at hmem
      simpa using hmem
    have hab : a = b := sub_eq_zero.mp hzero
    have hbY : b ∈ Y.map (shiftN K m' k) := by rw [← hab]; exact ha
    have hbYY : b ∈ (Y ⊓ Y').map (shiftN K m' k) := by
      rw [Submodule.map_inf _ (shiftN_injective m' k)]
      exact ⟨hbY, hb⟩
    exact Submodule.mem_sup.mpr ⟨t1, ht1, b, hbYY, by rw [hab]⟩
  · refine sup_le (le_inf le_sup_left le_sup_left) ?_
    refine le_inf ?_ ?_
    · exact le_trans (Submodule.map_mono inf_le_left) le_sup_right
    · exact le_trans (Submodule.map_mono inf_le_right) le_sup_right

theorem initRes_inf_finrank (m' k : ℕ)
    (Y Y' : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) :
    Module.finrank K ↥((initResT K σ m' k ⊔ Y.map (shiftN K m' k)) ⊓
        (initResT K σ m' k ⊔ Y'.map (shiftN K m' k))) =
      k + Module.finrank K ↥(Y ⊓ Y') := by
  rw [initRes_inf_sup, initRes_finrank_sup]

theorem initResVertex_inf_finrank (E : QuadExt F K σ) {m' k : ℕ} (hk : 1 ≤ k)
    (Y Y' : FlagVert σ m') :
    Module.finrank K ↥((initResVertex E hk Y).1 ⊓ (initResVertex E hk Y').1) =
      k + Module.finrank K ↥(Y.1 ⊓ Y'.1) := by
  rw [show (initResVertex E hk Y).1 ⊓ (initResVertex E hk Y').1 =
      (initResT K σ m' k ⊔ Y.1.map (shiftN K m' k)) ⊓
        (initResT K σ m' k ⊔ Y'.1.map (shiftN K m' k)) from rfl,
    initRes_inf_finrank]

theorem initRes_adj_iff (E : QuadExt F K σ) {m' k : ℕ} (hk : 1 ≤ k)
    (Y Y' : FlagVert σ m') :
    (flagGraph σ (m' + k)).Adj (initResVertex E hk Y) (initResVertex E hk Y') ↔
      (flagGraph σ m').Adj Y Y' := by
  rw [initRes_flagGraph_adj_iff, initRes_flagGraph_adj_iff]
  constructor
  · rintro (h | h | ⟨h1, h2, h3⟩)
    · exact Or.inl ((initRes_lt_iff (K := K) (σ := σ) m' k).mp h)
    · exact Or.inr (Or.inl ((initRes_lt_iff (K := K) (σ := σ) m' k).mp h))
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · rw [initResVertex_finrank E hk Y] at h1
        omega
      · rw [initResVertex_finrank E hk Y'] at h2
        omega
      · rw [initResVertex_inf_finrank E hk Y Y'] at h3
        omega
  · rintro (h | h | ⟨h1, h2, h3⟩)
    · exact Or.inl ((initRes_lt_iff (K := K) (σ := σ) m' k).mpr h)
    · exact Or.inr (Or.inl ((initRes_lt_iff (K := K) (σ := σ) m' k).mpr h))
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · rw [initResVertex_finrank E hk Y]
        omega
      · rw [initResVertex_finrank E hk Y']
        omega
      · rw [initResVertex_inf_finrank E hk Y Y']
        omega

@[expose] noncomputable def initResEquiv (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m')
    (hk : 1 ≤ k) :
    residueVertex (flagGraph σ (m' + k)) flagTyp (flagChamber E (m' + k))
      {j | (j : ℕ) < k} ≃ FlagVert σ m' where
  toFun := initResInv E hm' hk
  invFun := initResToResidue E hm' hk
  left_inv := initRes_toResidue_inv E hm' hk
  right_inv := initRes_inv_toResidue E hm' hk

theorem nonempty_residueGraph_init_iso (E : QuadExt F K σ) {m' k : ℕ} (hm' : 1 ≤ m')
    (hk : 1 ≤ k) :
    Nonempty (residueGraph (flagGraph σ (m' + k)) flagTyp (flagChamber E (m' + k))
      {j | (j : ℕ) < k} ≃g flagGraph σ m') := by
  refine ⟨{ toEquiv := initResEquiv E hm' hk, map_rel_iff' := ?_ }⟩
  intro x y
  change (flagGraph σ m').Adj (initResInv E hm' hk x) (initResInv E hm' hk y) ↔
    (flagGraph σ (m' + k)).Adj x.1 y.1
  have hx : x.1 = initResVertex E hk (initResInv E hm' hk x) := by
    have h := congrArg (fun z : residueVertex (flagGraph σ (m' + k)) flagTyp
      (flagChamber E (m' + k)) {j | (j : ℕ) < k} => z.1)
      (initRes_toResidue_inv E hm' hk x)
    exact h.symm
  have hy : y.1 = initResVertex E hk (initResInv E hm' hk y) := by
    have h := congrArg (fun z : residueVertex (flagGraph σ (m' + k)) flagTyp
      (flagChamber E (m' + k)) {j | (j : ℕ) < k} => z.1)
      (initRes_toResidue_inv E hm' hk y)
    exact h.symm
  rw [hx, hy]
  exact (initRes_adj_iff E hk (initResInv E hm' hk x) (initResInv E hm' hk y)).symm

end CFSG.ClassicalInvolution.PhanDn
