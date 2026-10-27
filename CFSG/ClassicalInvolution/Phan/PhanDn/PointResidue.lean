module

public import CFSG.ClassicalInvolution.Phan.PhanDn.ChamberMoves
public import CFSG.ClassicalInvolution.Phan.PanelLift
public import CFSG.ClassicalInvolution.Phan.GalleryWalk
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.PhanG

variable {K : Type} [Field K] {σ : K ≃+* K} {r : ℕ}

@[expose] noncomputable def shiftEmb (r : ℕ) :
    (Fin r ⊕ Fin r → K) →ₗ[K] (Fin (r + 1) ⊕ Fin (r + 1) → K) :=
  LinearMap.pi fun x =>
    match x with
    | Sum.inl i => Fin.cases 0 (fun j => LinearMap.proj (Sum.inl j)) i
    | Sum.inr i => Fin.cases 0 (fun j => LinearMap.proj (Sum.inr j)) i

theorem shiftEmb_apply_inl (r : ℕ) (v : Fin r ⊕ Fin r → K) (i : Fin (r + 1)) :
    shiftEmb r v (Sum.inl i) = Fin.cases 0 (fun j => v (Sum.inl j)) i := by
  refine Fin.cases ?_ ?_ i <;> simp [shiftEmb]

theorem shiftEmb_apply_inr (r : ℕ) (v : Fin r ⊕ Fin r → K) (i : Fin (r + 1)) :
    shiftEmb r v (Sum.inr i) = Fin.cases 0 (fun j => v (Sum.inr j)) i := by
  refine Fin.cases ?_ ?_ i <;> simp [shiftEmb]

@[simp] theorem shiftEmb_inl_zero (r : ℕ) (v : Fin r ⊕ Fin r → K) :
    shiftEmb r v (Sum.inl 0) = 0 := by
  rw [shiftEmb_apply_inl]; simp

@[simp] theorem shiftEmb_inr_zero (r : ℕ) (v : Fin r ⊕ Fin r → K) :
    shiftEmb r v (Sum.inr 0) = 0 := by
  rw [shiftEmb_apply_inr]; simp

@[simp] theorem shiftEmb_inl_succ (r : ℕ) (v : Fin r ⊕ Fin r → K) (j : Fin r) :
    shiftEmb r v (Sum.inl (Fin.succ j)) = v (Sum.inl j) := by
  rw [shiftEmb_apply_inl]; simp

@[simp] theorem shiftEmb_inr_succ (r : ℕ) (v : Fin r ⊕ Fin r → K) (j : Fin r) :
    shiftEmb r v (Sum.inr (Fin.succ j)) = v (Sum.inr j) := by
  rw [shiftEmb_apply_inr]; simp

theorem shiftEmb_injective (r : ℕ) : Function.Injective (shiftEmb (K := K) r) := by
  intro v w h
  funext x
  rcases x with i | i
  · have := congrFun h (Sum.inl (Fin.succ i))
    simpa using this
  · have := congrFun h (Sum.inr (Fin.succ i))
    simpa using this

theorem quadPlus_shiftEmb (v : Fin r ⊕ Fin r → K) :
    quadPlus (r + 1) K (shiftEmb r v) = quadPlus r K v := by
  rw [quadPlus_apply (n := r + 1), quadPlus_apply (n := r), Fin.sum_univ_succ]
  simp

theorem dFlip_shiftEmb (v : Fin r ⊕ Fin r → K) :
    dFlip σ (shiftEmb r v) = shiftEmb r (dFlip σ v) := by
  funext x
  rcases x with i | i <;> refine Fin.cases ?_ ?_ i <;> simp [dFlip]

theorem flipHerm_shiftEmb (u v : Fin r ⊕ Fin r → K) :
    flipHerm σ (shiftEmb r u) (shiftEmb r v) = flipHerm σ u v := by
  rw [flipHerm_apply (n := r + 1), flipHerm_apply (n := r), Fin.sum_univ_succ]
  simp

theorem polar_shiftEmb (u v : Fin r ⊕ Fin r → K) :
    polar (quadPlus (r + 1) K) (shiftEmb r u) (shiftEmb r v) =
      polar (quadPlus r K) u v := by
  rw [polar_quadPlus (n := r + 1), polar_quadPlus (n := r), Fin.sum_univ_succ]
  simp

theorem range_shiftEmb (r : ℕ) :
    LinearMap.range (shiftEmb (K := K) r) =
      qPerp (r + 1) K (K ∙ stdE (K := K) (n := r + 1) 0 ⊔
        K ∙ stdF (K := K) (n := r + 1) 0) := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    rw [mem_qPerp]
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left]
    have h1 : polar (quadPlus (r + 1) K) (stdE (K := K) (n := r + 1) 0)
        (shiftEmb r u) = 0 := by
      have := polar_quadPlus_single_inl (n := r + 1) (v := shiftEmb r u) (j := 0)
      rw [polar_comm]
      simpa [stdE] using this
    have h2 : polar (quadPlus (r + 1) K) (stdF (K := K) (n := r + 1) 0)
        (shiftEmb r u) = 0 := by
      have := polar_quadPlus_single_inr (n := r + 1) (v := shiftEmb r u) (j := 0)
      rw [polar_comm]
      simpa [stdF] using this
    rw [h1, h2, smul_zero, smul_zero, zero_add]
  · intro hv
    have h1 : v (Sum.inl (0 : Fin (r + 1))) = 0 := by
      have h := (mem_qPerp.mp hv) (stdF (K := K) (n := r + 1) 0)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      rw [polar_comm] at h
      rw [← polar_quadPlus_single_inr (n := r + 1) (v := v) (j := 0)]
      simpa [stdF] using h
    have h2 : v (Sum.inr (0 : Fin (r + 1))) = 0 := by
      have h := (mem_qPerp.mp hv) (stdE (K := K) (n := r + 1) 0)
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
      rw [polar_comm] at h
      rw [← polar_quadPlus_single_inl (n := r + 1) (v := v) (j := 0)]
      simpa [stdE] using h
    let u : Fin r ⊕ Fin r → K :=
      Sum.elim (fun j => v (Sum.inl (Fin.succ j))) (fun j => v (Sum.inr (Fin.succ j)))
    refine ⟨u, ?_⟩
    funext x
    rcases x with i | i <;> refine Fin.cases ?_ ?_ i <;> simp [u, h1, h2]

theorem stdLag_succ (r : ℕ) :
    stdLag (r + 1) K = K ∙ stdE (K := K) (n := r + 1) 0 ⊔
      (stdLag r K).map (shiftEmb (K := K) r) := by
  apply le_antisymm
  · intro v hv
    rw [mem_stdLag] at hv
    let u : Fin r ⊕ Fin r → K :=
      Sum.elim (fun j => v (Sum.inl (Fin.succ j))) (fun _ => 0)
    have hu : u ∈ stdLag r K := by
      rw [mem_stdLag]
      intro j
      rfl
    refine Submodule.mem_sup.mpr ⟨v (Sum.inl (0 : Fin (r + 1))) •
        stdE (K := K) (n := r + 1) 0,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), shiftEmb r u,
      Submodule.mem_map_of_mem hu, ?_⟩
    funext x
    rcases x with i | i <;> refine Fin.cases ?_ ?_ i <;> simp [u, stdE, hv]
  · refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, mem_stdLag]
      intro i
      simp
    · refine Submodule.map_le_iff_le_comap.mpr ?_
      intro w hw
      rw [Submodule.mem_comap, mem_stdLag]
      intro i
      rw [mem_stdLag] at hw
      cases i using Fin.cases with
      | zero => simp
      | succ j => simpa using hw j

private theorem exists_pointIso (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1)) :
    ∃ L : (Fin (r + 1) ⊕ Fin (r + 1) → K) ≃ₗ[K] (Fin (r + 1) ⊕ Fin (r + 1) → K),
      (∀ y, quadPlus (r + 1) K (L y) = quadPlus (r + 1) K y) ∧
        (∀ y, L (dFlip σ y) = dFlip σ (L y)) ∧
          ∀ i, (K ∙ stdE (K := K) (n := r + 1) i).map L.toLinearMap = e.line i :=
  e.toFlipFrame.exists_isometry hσ.invol (fun a ha ha0 => by
    obtain ⟨x, hx⟩ := hσ.norm_surj a ha ha0
    exact ⟨x, by rw [mul_comm]; exact hx⟩)

noncomputable def DChamber.pointIso (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1)) :
    (Fin (r + 1) ⊕ Fin (r + 1) → K) ≃ₗ[K] (Fin (r + 1) ⊕ Fin (r + 1) → K) :=
  Classical.choose (exists_pointIso hσ e)

private theorem DChamber.pointIso_spec (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1)) :
    (∀ y, quadPlus (r + 1) K (e.pointIso hσ y) = quadPlus (r + 1) K y) ∧
      (∀ y, e.pointIso hσ (dFlip σ y) = dFlip σ (e.pointIso hσ y)) ∧
        ∀ i, (K ∙ stdE (K := K) (n := r + 1) i).map (e.pointIso hσ).toLinearMap = e.line i :=
  Classical.choose_spec (exists_pointIso hσ e)

private theorem DChamber.pointIso_quadPlus (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) (y : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    quadPlus (r + 1) K (e.pointIso hσ y) = quadPlus (r + 1) K y :=
  (e.pointIso_spec hσ).1 y

private theorem DChamber.pointIso_dFlip (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) (y : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    e.pointIso hσ (dFlip σ y) = dFlip σ (e.pointIso hσ y) :=
  (e.pointIso_spec hσ).2.1 y

private theorem DChamber.pointIso_line (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) (i : Fin (r + 1)) :
    (K ∙ stdE (K := K) (n := r + 1) i).map (e.pointIso hσ).toLinearMap = e.line i :=
  (e.pointIso_spec hσ).2.2 i

private theorem DChamber.pointIso_polar (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) (a b : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    polar (quadPlus (r + 1) K) (e.pointIso hσ a) (e.pointIso hσ b) =
      polar (quadPlus (r + 1) K) a b := by
  rw [← quadPlusForm_polar (n := r + 1), ← quadPlusForm_polar (n := r + 1)]
  refine QuadForm.polar_map_of_Q (Φ := quadPlusForm (r + 1) K) ?_ a b
  intro y
  rw [quadPlusForm_Q, quadPlusForm_Q]
  exact e.pointIso_quadPlus hσ y

@[expose] noncomputable def DChamber.pointMap (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) :
    (Fin r ⊕ Fin r → K) →ₗ[K] (Fin (r + 1) ⊕ Fin (r + 1) → K) :=
  (e.pointIso hσ).toLinearMap.comp (shiftEmb r)

theorem DChamber.pointMap_apply (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1))
    (v : Fin r ⊕ Fin r → K) :
    e.pointMap hσ v = e.pointIso hσ (shiftEmb r v) := rfl

theorem DChamber.pointMap_injective (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1)) :
    Function.Injective (e.pointMap hσ) :=
  (e.pointIso hσ).injective.comp (shiftEmb_injective r)

theorem DChamber.quadPlus_pointMap (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1))
    (v : Fin r ⊕ Fin r → K) :
    quadPlus (r + 1) K (e.pointMap hσ v) = quadPlus r K v := by
  rw [e.pointMap_apply hσ, e.pointIso_quadPlus hσ, quadPlus_shiftEmb]

theorem DChamber.polar_pointMap (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1))
    (u v : Fin r ⊕ Fin r → K) :
    polar (quadPlus (r + 1) K) (e.pointMap hσ u) (e.pointMap hσ v) =
      polar (quadPlus r K) u v := by
  rw [e.pointMap_apply hσ, e.pointMap_apply hσ, e.pointIso_polar hσ, polar_shiftEmb]

theorem DChamber.flipHerm_pointMap (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1))
    (u v : Fin r ⊕ Fin r → K) :
    flipHerm σ (e.pointMap hσ u) (e.pointMap hσ v) = flipHerm σ u v := by
  rw [flipHerm, flipHerm]
  rw [e.pointMap_apply hσ, e.pointMap_apply hσ, ← e.pointIso_dFlip hσ]
  rw [e.pointIso_polar hσ, dFlip_shiftEmb, polar_shiftEmb]

theorem dFlipSub_map_of_comm {m n : ℕ}
    {L : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin n ⊕ Fin n → K)}
    (hL : ∀ y, L (dFlip σ y) = dFlip σ (L y)) (W : Submodule K (Fin m ⊕ Fin m → K)) :
    (dFlipSub σ W).map L = dFlipSub σ (W.map L) := by
  rw [dFlipSub, Submodule.map_span, dFlipSub]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨L w, ⟨w, hw, rfl⟩, (hL w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨w₀, hw₀, rfl⟩ := Submodule.mem_map.mp hw
    exact ⟨dFlip σ w₀, ⟨w₀, hw₀, rfl⟩, hL w₀⟩

private theorem DChamber.qPerp_map_pointIso (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) (W : Submodule K (Fin (r + 1) ⊕ Fin (r + 1) → K)) :
    (qPerp (r + 1) K W).map (e.pointIso hσ).toLinearMap =
      qPerp (r + 1) K (W.map (e.pointIso hσ).toLinearMap) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : ∀ u ∈ W, polar (quadPlus (r + 1) K) u w = 0 := mem_qPerp.mp hw
    rw [mem_qPerp]
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    exact (e.pointIso_polar hσ u₀ w).trans (hw' u₀ hu₀)
  · intro hv
    obtain ⟨w, rfl⟩ := (e.pointIso hσ).surjective v
    have hv' : ∀ u ∈ W.map (e.pointIso hσ).toLinearMap,
        polar (quadPlus (r + 1) K) u (e.pointIso hσ w) = 0 := mem_qPerp.mp hv
    refine Submodule.mem_map_of_mem ?_
    rw [mem_qPerp]
    intro u hu
    have h := hv' (e.pointIso hσ u) (Submodule.mem_map_of_mem hu)
    exact (e.pointIso_polar hσ u w).symm.trans h

theorem DChamber.range_pointMap (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1)) :
    LinearMap.range (e.pointMap hσ) =
      qPerp (r + 1) K (e.line 0 ⊔ dFlipSub σ (e.line 0)) := by
  have hmap : (K ∙ stdE (K := K) (n := r + 1) 0 ⊔ K ∙ stdF (K := K) (n := r + 1) 0).map
      (e.pointIso hσ).toLinearMap = e.line 0 ⊔ dFlipSub σ (e.line 0) := by
    have hB : K ∙ stdF (K := K) (n := r + 1) 0 =
        dFlipSub σ (K ∙ stdE (K := K) (n := r + 1) 0) := by
      rw [dFlipSub_span_singleton, dFlip_stdE]
    rw [hB, Submodule.map_sup, e.pointIso_line hσ,
      dFlipSub_map_of_comm (e.pointIso_dFlip hσ), e.pointIso_line hσ]
  change LinearMap.range ((e.pointIso hσ).toLinearMap.comp (shiftEmb (K := K) r)) =
    qPerp (r + 1) K (e.line 0 ⊔ dFlipSub σ (e.line 0))
  rw [LinearMap.range_comp, range_shiftEmb, e.qPerp_map_pointIso hσ, hmap]

theorem DChamber.le_range_pointMap (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1))
    {x : Submodule K (Fin (r + 1) ⊕ Fin (r + 1) → K)}
    (hp : ∀ u ∈ e.line 0, ∀ v ∈ x, polar (quadPlus (r + 1) K) u v = 0)
    (hh : ∀ u ∈ e.line 0, ∀ v ∈ x, flipHerm σ u v = 0) :
    x ≤ LinearMap.range (e.pointMap hσ) := by
  rw [e.range_pointMap hσ]
  intro v hv
  rw [mem_qPerp]
  intro w hw
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  have hz0 : polar (quadPlus (r + 1) K) z v = 0 := by
    have hz' : dFlip σ z ∈ e.line 0 := (mem_dFlipSub hσ.invol).mp hz
    calc
      polar (quadPlus (r + 1) K) z v =
          polar (quadPlus (r + 1) K) (dFlip σ (dFlip σ z)) (dFlip σ (dFlip σ v)) := by
            rw [dFlip_dFlip hσ.invol, dFlip_dFlip hσ.invol]
      _ = σ (polar (quadPlus (r + 1) K) (dFlip σ z) (dFlip σ v)) := polar_dFlip _ _
      _ = σ (flipHerm σ (dFlip σ z) v) := rfl
      _ = σ 0 := by rw [hh (dFlip σ z) hz' v hv]
      _ = 0 := map_zero σ
  rw [QuadraticMap.polar_add_left, hp u hu v hv, hz0, add_zero]

private theorem DChamber.disjoint_line_range_pointMap (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) :
    Disjoint (e.line 0) (LinearMap.range (e.pointMap hσ)) := by
  rw [e.range_pointMap hσ, Submodule.disjoint_def]
  intro x hx hxr
  have hp := e.isFlipflopPt_line 0
  have hne : e.line 0 ≠ ⊥ := by
    intro hbot
    have h := hp.2
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hline : e.line 0 = K ∙ u := eq_span_singleton_of_mem_of_finrank_eq_one hp.2 hu hu0
  have huu : flipHerm σ u u ≠ 0 := by
    have hsub : IsFlipflopSub σ (K ∙ u) := by rw [← hline]; exact hp.1
    exact ((isFlipflopSub_span_singleton_iff hu0).mp hsub).2
  rw [hline] at hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have hd : dFlip σ u ∈ e.line 0 ⊔ dFlipSub σ (e.line 0) := by
    refine Submodule.mem_sup_right ?_
    rw [hline, dFlipSub_span_singleton]
    exact Submodule.mem_span_singleton_self _
  have h := (mem_qPerp.mp hxr) (dFlip σ u) hd
  rw [QuadraticMap.polar_smul_right, smul_eq_mul] at h
  have hnon : polar (quadPlus (r + 1) K) (dFlip σ u) u ≠ 0 := by
    have hpold : polar (quadPlus (r + 1) K) (dFlip σ u) u = σ (flipHerm σ u u) := by
      have h' := polar_dFlip (σ := σ) (n := r + 1) u (dFlip σ u)
      rw [dFlip_dFlip hσ.invol] at h'
      simpa [flipHerm] using h'
    rw [hpold]
    exact fun h0 => huu ((map_eq_zero_iff σ σ.injective).mp h0)
  have hc : c = 0 := (mul_eq_zero.mp h).resolve_right hnon
  rw [hc, zero_smul]

theorem DChamber.sup_map_pointMap_inj (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 1))
    {A B : Submodule K (Fin r ⊕ Fin r → K)}
    (h : e.line 0 ⊔ A.map (e.pointMap hσ) = e.line 0 ⊔ B.map (e.pointMap hσ)) : A = B := by
  have hinj : Function.Injective (e.pointMap hσ) := e.pointMap_injective hσ
  have hdisj := e.disjoint_line_range_pointMap hσ
  have hA : (e.line 0 ⊔ A.map (e.pointMap hσ)) ⊓ LinearMap.range (e.pointMap hσ) =
      A.map (e.pointMap hσ) := by
    rw [sup_comm, sup_inf_assoc_of_le (e.line 0) (LinearMap.map_le_range (f := e.pointMap hσ)),
      hdisj.eq_bot, sup_bot_eq]
  have hB : (e.line 0 ⊔ B.map (e.pointMap hσ)) ⊓ LinearMap.range (e.pointMap hσ) =
      B.map (e.pointMap hσ) := by
    rw [sup_comm, sup_inf_assoc_of_le (e.line 0) (LinearMap.map_le_range (f := e.pointMap hσ)),
      hdisj.eq_bot, sup_bot_eq]
  have hEq : A.map (e.pointMap hσ) = B.map (e.pointMap hσ) := by
    rw [← hA, ← hB, h]
  exact Submodule.map_injective_of_injective hinj hEq

private theorem finrank_map_shiftEmb (W : Submodule K (Fin r ⊕ Fin r → K)) :
    Module.finrank K (W.map (shiftEmb (K := K) r)) = Module.finrank K W := by
  have h := rank_map_eq (shiftEmb_injective (K := K) r) W
  simpa [Module.finrank] using congrArg Cardinal.toNat h

private theorem line_stdE_inf_range_shift (r : ℕ) :
    K ∙ stdE (K := K) (n := r + 1) 0 ⊓ LinearMap.range (shiftEmb (K := K) r) = ⊥ := by
  rw [range_shiftEmb (K := K) (r := r)]
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hx, hxr⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have hd : stdF (K := K) (n := r + 1) 0 ∈
      K ∙ stdE (K := K) (n := r + 1) 0 ⊔ K ∙ stdF (K := K) (n := r + 1) 0 :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hp : polar (quadPlus (r + 1) K) (stdF (K := K) (n := r + 1) 0)
      (stdE (K := K) (n := r + 1) 0) = 1 := by
    have h := polar_quadPlus_single_inl (n := r + 1)
      (v := stdF (K := K) (n := r + 1) 0) (j := 0)
    simpa [stdE, stdF, Pi.single_apply] using h
  have h := (mem_qPerp.mp hxr) (stdF (K := K) (n := r + 1) 0) hd
  rw [QuadraticMap.polar_smul_right, smul_eq_mul, hp, mul_one] at h
  rw [h, zero_smul]

private theorem isFlipflopPt_map_pointMap (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) {p : Submodule K (Fin r ⊕ Fin r → K)}
    (hp : IsFlipflopPt σ p) :
    IsFlipflopPt σ (p.map (e.pointMap hσ)) := by
  have hpne : p ≠ ⊥ := by
    intro hbot
    have h := hp.2
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  have hline : p = K ∙ u := eq_span_singleton_of_mem_of_finrank_eq_one hp.2 hu hu0
  have hsub : IsFlipflopSub σ (K ∙ u) := by rw [← hline]; exact hp.1
  obtain ⟨hQu, huu⟩ := (isFlipflopSub_span_singleton_iff hu0).mp hsub
  have hmap : p.map (e.pointMap hσ) = K ∙ (e.pointMap hσ u) := by
    rw [hline, Submodule.map_span, Set.image_singleton]
  have hlu0 : e.pointMap hσ u ≠ 0 := by
    intro h0
    exact hu0 (e.pointMap_injective hσ (by rw [h0, map_zero]))
  rw [hmap]
  refine (isFlipflopPt_span_singleton_iff hlu0).mpr ⟨?_, ?_⟩
  · rw [e.quadPlus_pointMap hσ, hQu]
  · rw [e.flipHerm_pointMap hσ]
    exact huu

private theorem flipHerm_eq_zero_of_mem_range (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) {u v : Fin (r + 1) ⊕ Fin (r + 1) → K}
    (hu : u ∈ e.line 0) (hv : v ∈ LinearMap.range (e.pointMap hσ)) :
    flipHerm σ u v = 0 := by
  rw [e.range_pointMap hσ] at hv
  have hd : dFlip σ u ∈ e.line 0 ⊔ dFlipSub σ (e.line 0) :=
    Submodule.mem_sup_right (Submodule.subset_span ⟨u, hu, rfl⟩)
  have h := (mem_qPerp.mp hv) (dFlip σ u) hd
  have hpold : polar (quadPlus (r + 1) K) (dFlip σ u) v = σ (flipHerm σ u v) := by
    calc
      polar (quadPlus (r + 1) K) (dFlip σ u) v =
          polar (quadPlus (r + 1) K) (dFlip σ u) (dFlip σ (dFlip σ v)) := by
            rw [dFlip_dFlip hσ.invol]
      _ = σ (polar (quadPlus (r + 1) K) u (dFlip σ v)) := polar_dFlip _ _
      _ = σ (flipHerm σ u v) := rfl
  rw [hpold] at h
  exact (map_eq_zero_iff σ σ.injective).mp h

@[expose] noncomputable def pointFrame (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 2))
    (d : FlipFrame σ (r + 1)) : FlipFrame σ (r + 2) where
  line := Fin.cases (e.line 0) fun j => (d.line j).map (e.pointMap hσ)
  isFlipflopPt_line := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact e.isFlipflopPt_line 0
    · intro j
      exact isFlipflopPt_map_pointMap hσ e (d.isFlipflopPt_line j)
  polar_eq_zero := by
    intro i j hij u hu v hv
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ k =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hu hv
        obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hv
        have hmem : e.pointMap hσ w ∈
            qPerp (r + 2) K (e.line 0 ⊔ dFlipSub σ (e.line 0)) := by
          rw [← e.range_pointMap hσ]
          exact ⟨w, rfl⟩
        exact (mem_qPerp.mp hmem) u (Submodule.mem_sup_left hu)
    | succ k =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hu hv
        obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hu
        have hmem : e.pointMap hσ w ∈
            qPerp (r + 2) K (e.line 0 ⊔ dFlipSub σ (e.line 0)) := by
          rw [← e.range_pointMap hσ]
          exact ⟨w, rfl⟩
        rw [QuadraticMap.polar_comm]
        exact (mem_qPerp.mp hmem) v (Submodule.mem_sup_left hv)
      | succ l =>
        simp only [Fin.cases_succ] at hu hv
        obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hu
        obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hv
        rw [e.polar_pointMap hσ]
        exact d.polar_eq_zero k l (fun h => hij (by rw [h])) a ha b hb
  flipHerm_eq_zero := by
    intro i j hij u hu v hv
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ k =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hu hv
        obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hv
        exact flipHerm_eq_zero_of_mem_range hσ e hu ⟨w, rfl⟩
    | succ k =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hu hv
        obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hu
        rw [flipHerm_eq_zero_iff hσ.invol]
        exact flipHerm_eq_zero_of_mem_range hσ e hv ⟨w, rfl⟩
      | succ l =>
        simp only [Fin.cases_succ] at hu hv
        obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hu
        obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hv
        rw [e.flipHerm_pointMap hσ]
        exact d.flipHerm_eq_zero k l (fun h => hij (by rw [h])) a ha b hb

@[simp] private theorem pointFrame_line_zero (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 2)) (d : FlipFrame σ (r + 1)) :
    (pointFrame hσ e d).line 0 = e.line 0 := rfl

@[simp] private theorem pointFrame_line_succ (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 2)) (d : FlipFrame σ (r + 1)) (j : Fin (r + 1)) :
    (pointFrame hσ e d).line j.succ = (d.line j).map (e.pointMap hσ) := rfl

private theorem DChamber.map_stdLag_pointIso (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) :
    (stdLag (r + 1) K).map (e.pointIso hσ).toLinearMap = e.spanAt Finset.univ := by
  rw [stdLag_eq_span_stdE, Submodule.map_span]
  have hspan : e.spanAt Finset.univ =
      Submodule.span K (Set.range fun i =>
        e.pointIso hσ (stdE (K := K) (n := r + 1) i)) := by
    rw [FlipFrame.spanAt]
    apply le_antisymm
    · refine Finset.sup_le fun i _ => ?_
      rw [← e.pointIso_line hσ i, Submodule.map_span, Set.image_singleton]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨i, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      have hmem : e.pointIso hσ (stdE (K := K) (n := r + 1) i) ∈ e.line i := by
        rw [← e.pointIso_line hσ i]
        exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
      exact mem_of_le_of_mem (Finset.le_sup (Finset.mem_univ i)) hmem
  rw [hspan]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨stdE (K := K) (n := r + 1) i, ⟨i, rfl⟩, rfl⟩

private theorem pointFrame_spanAt (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 2))
    (d : FlipFrame σ (r + 1)) :
    (pointFrame hσ e d).spanAt Finset.univ =
      (K ∙ stdE (K := K) (n := r + 2) 0 ⊔
        (d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1))).map
        (e.pointIso hσ).toLinearMap := by
  rw [FlipFrame.spanAt, Fin.univ_succ, Finset.sup_cons, Finset.sup_map]
  change (pointFrame hσ e d).line 0 ⊔
    (Finset.univ.sup fun j : Fin (r + 1) =>
      (pointFrame hσ e d).line (Fin.succ j)) = _
  simp only [pointFrame_line_zero, pointFrame_line_succ]
  have hsup : (Finset.univ.sup fun j : Fin (r + 1) =>
      (d.line j).map (e.pointMap hσ)) =
      (d.spanAt Finset.univ).map (e.pointMap hσ) := by
    rw [FlipFrame.spanAt, Finset.sup_eq_iSup]
    rw [Finset.sup_eq_iSup]
    simp only [Finset.mem_univ, iSup_true]
    rw [Submodule.map_iSup]
  rw [hsup]
  have hAe : e.line 0 =
      (K ∙ stdE (K := K) (n := r + 2) 0).map (e.pointIso hσ).toLinearMap :=
    (e.pointIso_line hσ 0).symm
  have hBe : (d.spanAt Finset.univ).map (e.pointMap hσ) =
      ((d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1))).map
        (e.pointIso hσ).toLinearMap := by
    change (d.spanAt Finset.univ).map
      ((e.pointIso hσ).toLinearMap.comp (shiftEmb (K := K) (r + 1))) = _
    rw [Submodule.map_comp]
  rw [hAe, hBe, Submodule.map_sup]

private theorem isLagrangian_pointFrame_span (hσ : IsUnitaryInvolution σ)
    (d : FlipFrame σ (r + 1)) :
    (quadPlusForm (r + 2) K).IsLagrangian
      (K ∙ stdE (K := K) (n := r + 2) 0 ⊔
        (d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1))) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [quadPlusForm_Q]
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hb
    have hQa : quadPlus (r + 2) K (stdE (K := K) (n := r + 2) 0) = 0 :=
      quadPlus_stdE 0
    have hQb : quadPlus (r + 2) K (shiftEmb (K := K) (r + 1) x) = 0 := by
      rw [quadPlus_shiftEmb]
      exact (d.isFlipflopSub_spanAt hσ.invol Finset.univ).total x hx
    have hp : polar (quadPlus (r + 2) K) (shiftEmb (K := K) (r + 1) x)
        (stdE (K := K) (n := r + 2) 0) = 0 := by
      simpa [stdE] using polar_quadPlus_single_inl (n := r + 2)
        (v := shiftEmb (K := K) (r + 1) x) (j := 0)
    have hpab : polar (quadPlus (r + 2) K) (c • stdE (K := K) (n := r + 2) 0)
        (shiftEmb (K := K) (r + 1) x) = 0 := by
      rw [QuadraticMap.polar_smul_left, polar_comm, hp, smul_zero]
    rw [QuadraticMap.map_add (quadPlus (r + 2) K), QuadraticMap.map_smul (quadPlus (r + 2) K),
      hQa, hQb, hpab]
    simp
  · have hA : Module.finrank K (K ∙ stdE (K := K) (n := r + 2) 0) = 1 := by
      rw [finrank_span_singleton]
      intro h
      have := congrFun h (Sum.inl (0 : Fin (r + 2)))
      simp [stdE] at this
    have hB : Module.finrank K
        ((d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1))) = r + 1 := by
      rw [finrank_map_shiftEmb, d.finrank_spanAt]
      simp
    have hdisj : K ∙ stdE (K := K) (n := r + 2) 0 ⊓
        (d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1)) = ⊥ := by
      refine le_bot_iff.mp ?_
      calc K ∙ stdE (K := K) (n := r + 2) 0 ⊓
            (d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1)) ≤
            K ∙ stdE (K := K) (n := r + 2) 0 ⊓
              LinearMap.range (shiftEmb (K := K) (r + 1)) :=
            inf_le_inf_left _ LinearMap.map_le_range
        _ = ⊥ := line_stdE_inf_range_shift (r + 1)
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (K ∙ stdE (K := K) (n := r + 2) 0)
      ((d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1)))
    rw [hdisj, finrank_bot, add_zero, hA, hB] at h
    rw [h, finrank_flipSpace]
    ring

private theorem inf_stdLag_pointFrame (d : FlipFrame σ (r + 1)) :
    (K ∙ stdE (K := K) (n := r + 2) 0 ⊔
        (d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1))) ⊓ stdLag (r + 2) K =
      K ∙ stdE (K := K) (n := r + 2) 0 ⊔
        ((d.spanAt Finset.univ ⊓ stdLag (r + 1) K).map
          (shiftEmb (K := K) (r + 1))) := by
  set A : Submodule K (Fin (r + 2) ⊕ Fin (r + 2) → K) :=
    K ∙ stdE (K := K) (n := r + 2) 0 with hA
  set B : Submodule K (Fin (r + 2) ⊕ Fin (r + 2) → K) :=
    (d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1)) with hB
  set C : Submodule K (Fin (r + 2) ⊕ Fin (r + 2) → K) :=
    (stdLag (r + 1) K).map (shiftEmb (K := K) (r + 1)) with hC
  have hstd : stdLag (r + 2) K = A ⊔ C := by
    rw [hA, hC, stdLag_succ]
  have hBrange : B ≤ LinearMap.range (shiftEmb (K := K) (r + 1)) := by
    rw [hB]; exact LinearMap.map_le_range
  have hCrange : C ≤ LinearMap.range (shiftEmb (K := K) (r + 1)) := by
    rw [hC]; exact LinearMap.map_le_range
  have hArange : A ⊓ LinearMap.range (shiftEmb (K := K) (r + 1)) = ⊥ := by
    rw [hA]; exact line_stdE_inf_range_shift (r + 1)
  have hmod : (A ⊔ B) ⊓ (A ⊔ C) = A ⊔ (B ⊓ C) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx1
      obtain ⟨a', ha', c, hc, hx2'⟩ := Submodule.mem_sup.mp hx2
      have hdiff : a - a' = c - b := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm c a']
        exact hx2'.symm
      have hmemA : a - a' ∈ A := A.sub_mem ha ha'
      have hmemR : c - b ∈ LinearMap.range (shiftEmb (K := K) (r + 1)) := by
        refine (LinearMap.range (shiftEmb (K := K) (r + 1))).sub_mem ?_ ?_
        · exact hCrange hc
        · exact hBrange hb
      have hzero : a - a' = 0 := by
        have hmem : a - a' ∈ A ⊓ LinearMap.range (shiftEmb (K := K) (r + 1)) :=
          ⟨hmemA, by rw [hdiff]; exact hmemR⟩
        rwa [hArange] at hmem
      have hbc : b = c := by
        have hzero' : c - b = 0 := by rw [← hdiff, hzero]
        exact (sub_eq_zero.mp hzero').symm
      refine Submodule.mem_sup.mpr ⟨a, ha, b, ⟨hb, ?_⟩, ?_⟩
      · rw [hbc]; exact hc
      · rfl
    · refine sup_le ?_ ?_
      · exact le_inf le_sup_left le_sup_left
      · exact le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right)
  rw [hstd, hmod]
  congr 1
  rw [hB, hC, ← Submodule.map_inf (shiftEmb (K := K) (r + 1))
    (shiftEmb_injective (K := K) (r + 1))]

theorem even_pointFrame_iff (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 2))
    (d : FlipFrame σ (r + 1)) :
    Even ((r + 2) - Module.finrank K
        ↥((pointFrame hσ e d).spanAt Finset.univ ⊓ stdLag (r + 2) K)) ↔
      Even ((r + 1) - Module.finrank K
        ↥(d.spanAt Finset.univ ⊓ stdLag (r + 1) K)) := by
  have hspan := pointFrame_spanAt hσ e d
  have hlag := isLagrangian_pointFrame_span hσ d
  have hinf := inf_stdLag_pointFrame d
  have hmapstd : (stdLag (r + 2) K).map (e.pointIso hσ).toLinearMap =
      e.spanAt Finset.univ := e.map_stdLag_pointIso hσ
  have hfam : Even ((r + 2) - Module.finrank K
      ↥((stdLag (r + 2) K).map (e.pointIso hσ).toLinearMap ⊓ stdLag (r + 2) K)) := by
    rw [hmapstd]
    exact e.even_ruling
  have hL : ∀ y, quadPlus (r + 2) K (e.pointIso hσ y) = quadPlus (r + 2) K y :=
    e.pointIso_quadPlus hσ
  have hfin : Module.finrank K
      ↥((K ∙ stdE (K := K) (n := r + 2) 0 ⊔
          (d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1))) ⊓ stdLag (r + 2) K) =
      1 + Module.finrank K ↥(d.spanAt Finset.univ ⊓ stdLag (r + 1) K) := by
    rw [hinf]
    have hAdisj : K ∙ stdE (K := K) (n := r + 2) 0 ⊓
        ((d.spanAt Finset.univ ⊓ stdLag (r + 1) K).map
          (shiftEmb (K := K) (r + 1))) = ⊥ := by
      refine le_bot_iff.mp ?_
      calc K ∙ stdE (K := K) (n := r + 2) 0 ⊓
            ((d.spanAt Finset.univ ⊓ stdLag (r + 1) K).map
              (shiftEmb (K := K) (r + 1))) ≤
            K ∙ stdE (K := K) (n := r + 2) 0 ⊓
              LinearMap.range (shiftEmb (K := K) (r + 1)) :=
            inf_le_inf_left _ LinearMap.map_le_range
        _ = ⊥ := line_stdE_inf_range_shift (r + 1)
    have hA : Module.finrank K (K ∙ stdE (K := K) (n := r + 2) 0) = 1 := by
      rw [finrank_span_singleton]
      intro h
      have := congrFun h (Sum.inl (0 : Fin (r + 2)))
      simp [stdE] at this
    have hBC : Module.finrank K
        (((d.spanAt Finset.univ ⊓ stdLag (r + 1) K).map
          (shiftEmb (K := K) (r + 1)))) =
        Module.finrank K ↥(d.spanAt Finset.univ ⊓ stdLag (r + 1) K) :=
      finrank_map_shiftEmb _
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (K ∙ stdE (K := K) (n := r + 2) 0)
      ((d.spanAt Finset.univ ⊓ stdLag (r + 1) K).map (shiftEmb (K := K) (r + 1)))
    rw [hAdisj, finrank_bot, add_zero, hA, hBC] at h
    exact h
  have hle : Module.finrank K ↥(d.spanAt Finset.univ ⊓ stdLag (r + 1) K) ≤ r + 1 := by
    have hmono := Submodule.finrank_mono
      (inf_le_right : d.spanAt Finset.univ ⊓ stdLag (r + 1) K ≤ stdLag (r + 1) K)
    rwa [finrank_stdLag] at hmono
  have hEq : (r + 2) - Module.finrank K
      ↥((K ∙ stdE (K := K) (n := r + 2) 0 ⊔
          (d.spanAt Finset.univ).map (shiftEmb (K := K) (r + 1))) ⊓ stdLag (r + 2) K) =
      (r + 1) - Module.finrank K ↥(d.spanAt Finset.univ ⊓ stdLag (r + 1) K) := by
    rw [hfin]
    omega
  rw [hspan]
  rw [even_finrank_map_inf_stdLag_iff (n := r + 2) hL hfam hlag]
  rw [hEq]

@[expose] noncomputable def DChamber.pointEmb (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 2)) : DChamber σ (r + 1) → DChamber σ (r + 2) :=
  fun d =>
    { toFlipFrame := pointFrame hσ e d.toFlipFrame
      even_ruling := (even_pointFrame_iff hσ e d.toFlipFrame).mpr d.even_ruling }

@[simp] theorem DChamber.pointEmb_line_zero (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 2)) (d : DChamber σ (r + 1)) :
    (e.pointEmb hσ d).line 0 = e.line 0 := rfl

@[simp] theorem DChamber.pointEmb_line_succ (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 2)) (d : DChamber σ (r + 1)) (j : Fin (r + 1)) :
    (e.pointEmb hσ d).line j.succ = (d.line j).map (e.pointMap hσ) := rfl

private theorem isFlipflopPt_of_map_pointMap (hσ : IsUnitaryInvolution σ)
    (e : DChamber σ (r + 1)) {p : Submodule K (Fin r ⊕ Fin r → K)}
    (hp : IsFlipflopPt σ (p.map (e.pointMap hσ))) : IsFlipflopPt σ p := by
  have hrank := rank_map_eq (e.pointMap_injective hσ) p
  have hfin' : Module.finrank K (p.map (e.pointMap hσ)) = Module.finrank K p := by
    simpa [Module.finrank] using congrArg Cardinal.toNat hrank
  have hfin : Module.finrank K p = 1 := by
    rw [← hfin', hp.2]
  have hpne : p ≠ ⊥ := by
    intro hbot
    have h := hfin
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  have hline : p = K ∙ u := eq_span_singleton_of_mem_of_finrank_eq_one hfin hu hu0
  have hmap : p.map (e.pointMap hσ) = K ∙ (e.pointMap hσ u) := by
    rw [hline, Submodule.map_span, Set.image_singleton]
  have hlu0 : e.pointMap hσ u ≠ 0 := by
    intro h0
    exact hu0 (e.pointMap_injective hσ (by rw [h0, map_zero]))
  obtain ⟨hQu, huu⟩ := (isFlipflopPt_span_singleton_iff hlu0).mp (hmap ▸ hp)
  rw [hline]
  refine (isFlipflopPt_span_singleton_iff hu0).mpr ⟨?_, ?_⟩
  · rw [← e.quadPlus_pointMap hσ, hQu]
  · rw [← e.flipHerm_pointMap hσ]
    exact huu

theorem DChamber.pointEmb_injective (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 2)) :
    Function.Injective (e.pointEmb hσ) := by
  intro d₁ d₂ h
  apply DChamber.ext
  funext j
  have hline : (d₁.line j).map (e.pointMap hσ) = (d₂.line j).map (e.pointMap hσ) := by
    have := congrFun (congrArg (fun c : DChamber σ (r + 2) => c.line) h) j.succ
    simpa using this
  exact Submodule.map_injective_of_injective (e.pointMap_injective hσ) hline

theorem DChamber.exists_pointEmb_eq (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 2))
    {c : DChamber σ (r + 2)} (h : c.line 0 = e.line 0) :
    ∃ d : DChamber σ (r + 1), e.pointEmb hσ d = c := by
  let dline : Fin (r + 1) → Submodule K (Fin (r + 1) ⊕ Fin (r + 1) → K) :=
    fun j => (c.line j.succ).comap (e.pointMap hσ)
  have hle : ∀ j : Fin (r + 1), c.line j.succ ≤ LinearMap.range (e.pointMap hσ) := by
    intro j
    refine e.le_range_pointMap hσ ?_ ?_
    · intro u hu v hv
      rw [← h] at hu
      exact c.polar_eq_zero 0 j.succ (by simpa using (Fin.succ_ne_zero j).symm) u hu v hv
    · intro u hu v hv
      rw [← h] at hu
      exact c.flipHerm_eq_zero 0 j.succ (by simpa using (Fin.succ_ne_zero j).symm) u hu v hv
  have hdmap : ∀ j : Fin (r + 1), (dline j).map (e.pointMap hσ) = c.line j.succ := fun j =>
    Submodule.map_comap_eq_of_le (f := e.pointMap hσ) (hle j)
  have hpt : ∀ j : Fin (r + 1), IsFlipflopPt σ (dline j) := fun j =>
    isFlipflopPt_of_map_pointMap hσ e (hdmap j ▸ c.isFlipflopPt_line j.succ)
  let dframe : FlipFrame σ (r + 1) :=
    { line := dline
      isFlipflopPt_line := hpt
      polar_eq_zero := by
        intro i j hij u hu v hv
        have hu' : e.pointMap hσ u ∈ c.line i.succ := by
          rw [← hdmap i]
          exact Submodule.mem_map_of_mem hu
        have hv' : e.pointMap hσ v ∈ c.line j.succ := by
          rw [← hdmap j]
          exact Submodule.mem_map_of_mem hv
        have h0 : polar (quadPlus (r + 2) K) (e.pointMap hσ u)
            (e.pointMap hσ v) = 0 :=
          c.polar_eq_zero i.succ j.succ (fun hh => hij (by simpa using hh)) _ hu' _ hv'
        exact (e.polar_pointMap hσ u v).symm.trans h0
      flipHerm_eq_zero := by
        intro i j hij u hu v hv
        have hu' : e.pointMap hσ u ∈ c.line i.succ := by
          rw [← hdmap i]
          exact Submodule.mem_map_of_mem hu
        have hv' : e.pointMap hσ v ∈ c.line j.succ := by
          rw [← hdmap j]
          exact Submodule.mem_map_of_mem hv
        have h0 : flipHerm σ (e.pointMap hσ u) (e.pointMap hσ v) = 0 :=
          c.flipHerm_eq_zero i.succ j.succ (fun hh => hij (by simpa using hh)) _ hu' _ hv'
        exact (e.flipHerm_pointMap hσ u v).symm.trans h0 }
  have hframe : pointFrame hσ e dframe = c.toFlipFrame := by
    apply FlipFrame.ext
    funext i
    cases i using Fin.cases with
    | zero =>
      rw [pointFrame_line_zero]
      exact h.symm
    | succ j => rw [pointFrame_line_succ, hdmap j]
  let d : DChamber σ (r + 1) :=
    { toFlipFrame := dframe
      even_ruling :=
        (even_pointFrame_iff hσ e dframe).mp (by rw [hframe]; exact c.even_ruling) }
  refine ⟨d, ?_⟩
  apply DChamber.ext
  funext i
  cases i using Fin.cases with
  | zero =>
    rw [DChamber.pointEmb_line_zero]
    exact h.symm
  | succ j => rw [DChamber.pointEmb_line_succ, hdmap j]

private theorem pointFrame_sub_succ (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 2))
    (d : FlipFrame σ (r + 1)) (j : ℕ) (hj : j ≤ r + 1) :
    (pointFrame hσ e d).sub (j + 1) =
      e.line 0 ⊔ ((d.sub j).map (shiftEmb (K := K) (r + 1))).map
        (e.pointIso hσ).toLinearMap := by
  induction j with
  | zero =>
    rw [FlipFrame.sub_succ (c := pointFrame hσ e d) (j := 0) (by omega),
      FlipFrame.sub_zero, bot_sup_eq]
    have h0 : (⟨0, by omega⟩ : Fin (r + 2)) = 0 := Fin.ext rfl
    rw [h0, pointFrame_line_zero, d.sub_zero, Submodule.map_bot, Submodule.map_bot,
      sup_bot_eq]
  | succ j ih =>
    rw [FlipFrame.sub_succ (c := pointFrame hσ e d) (j := j + 1) (by omega),
      ih (by omega)]
    have hline : (⟨j + 1, by omega⟩ : Fin (r + 2)) =
        (⟨j, by omega⟩ : Fin (r + 1)).succ := Fin.ext rfl
    rw [hline, pointFrame_line_succ]
    have hd : d.sub (j + 1) = d.sub j ⊔ d.line ⟨j, by omega⟩ :=
      FlipFrame.sub_succ (c := d) (j := j) (by omega)
    rw [hd, Submodule.map_sup, Submodule.map_sup]
    have hpm : Submodule.map (e.pointMap hσ) (d.line ⟨j, by omega⟩) =
        Submodule.map (e.pointIso hσ).toLinearMap
          (Submodule.map (shiftEmb (K := K) (r + 1)) (d.line ⟨j, by omega⟩)) := by
      change Submodule.map ((e.pointIso hσ).toLinearMap.comp
          (shiftEmb (K := K) (r + 1))) (d.line ⟨j, by omega⟩) = _
      rw [Submodule.map_comp]
    rw [hpm, sup_assoc]

private theorem pointFrame_alt (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 2))
    (d : FlipFrame σ (r + 1)) :
    (pointFrame hσ e d).alt =
      e.line 0 ⊔ ((d.alt).map (shiftEmb (K := K) (r + 1))).map
        (e.pointIso hσ).toLinearMap := by
  have hY : dFlipSub σ ((pointFrame hσ e d).line (Fin.last (r + 1))) =
      ((dFlipSub σ (d.line (Fin.last r))).map (shiftEmb (K := K) (r + 1))).map
        (e.pointIso hσ).toLinearMap := by
    have hlast : (Fin.last (r + 1) : Fin (r + 2)) = (Fin.last r).succ := by
      apply Fin.ext
      simp [Fin.val_last]
    rw [hlast, pointFrame_line_succ]
    have hpm : Submodule.map (e.pointMap hσ) (d.line (Fin.last r)) =
        Submodule.map (e.pointIso hσ).toLinearMap
          (Submodule.map (shiftEmb (K := K) (r + 1)) (d.line (Fin.last r))) := by
      change Submodule.map ((e.pointIso hσ).toLinearMap.comp
        (shiftEmb (K := K) (r + 1))) (d.line (Fin.last r)) = _
      rw [Submodule.map_comp]
    rw [hpm]
    rw [← dFlipSub_map_of_comm (L := (e.pointIso hσ).toLinearMap) (e.pointIso_dFlip hσ)]
    rw [← dFlipSub_map_of_comm (L := shiftEmb (K := K) (r + 1)) (fun y =>
      (dFlip_shiftEmb (σ := σ) (r := r + 1) y).symm)]
  change ((pointFrame hσ e d).sub (r + 1) ⊔
      dFlipSub σ ((pointFrame hσ e d).line (Fin.last (r + 1)))) =
    e.line 0 ⊔ ((d.sub r ⊔ dFlipSub σ (d.line (Fin.last r))).map
      (shiftEmb (K := K) (r + 1))).map (e.pointIso hσ).toLinearMap
  rw [pointFrame_sub_succ hσ e d r (by omega), hY]
  rw [Submodule.map_sup, Submodule.map_sup]
  rw [sup_assoc]

theorem DChamber.elt_pointEmb_succ (hσ : IsUnitaryInvolution σ) (e : DChamber σ (r + 2))
    (d : DChamber σ (r + 1)) (i : Fin (r + 1)) :
    (e.pointEmb hσ d).elt i.succ = e.line 0 ⊔ (d.elt i).map (e.pointMap hσ) := by
  change (pointFrame hσ e d.toFlipFrame).elt i.succ = _
  rw [FlipFrame.elt]
  by_cases hlast : i.succ = Fin.last (r + 1)
  · rw [if_pos hlast]
    have hi : i = Fin.last r := by
      have hv := congrArg Fin.val hlast
      rw [Fin.val_succ, Fin.val_last] at hv
      clear hlast
      apply Fin.ext
      rw [Fin.val_last]
      omega
    subst hi
    rw [pointFrame_sub_succ hσ e d.toFlipFrame (r + 1) (by omega)]
    rw [FlipFrame.elt_last]
    congr 1
    change ((d.toFlipFrame.sub (r + 1)).map (shiftEmb (K := K) (r + 1))).map
        (e.pointIso hσ).toLinearMap =
      (d.toFlipFrame.sub (r + 1)).map
        ((e.pointIso hσ).toLinearMap.comp (shiftEmb (K := K) (r + 1)))
    rw [Submodule.map_comp]
  · rw [if_neg hlast]
    by_cases halt : (i.succ : ℕ) + 1 = r + 1
    · rw [if_pos halt]
      have hi : (i : ℕ) + 1 = r := by
        have hv := Fin.val_succ i
        omega
      rw [pointFrame_alt hσ e d.toFlipFrame]
      rw [d.elt_of_add_one_eq i hi]
      congr 1
      change ((d.toFlipFrame.alt).map (shiftEmb (K := K) (r + 1))).map
          (e.pointIso hσ).toLinearMap =
        (d.toFlipFrame.alt).map
          ((e.pointIso hσ).toLinearMap.comp (shiftEmb (K := K) (r + 1)))
      rw [Submodule.map_comp]
    · rw [if_neg halt]
      have hsub : (i.succ : ℕ) + 1 = (i : ℕ) + 1 + 1 := by rw [Fin.val_succ]
      rw [hsub]
      have hi_lt : (i : ℕ) < r + 1 := i.is_lt
      rw [pointFrame_sub_succ hσ e d.toFlipFrame ((i : ℕ) + 1) (by omega)]
      have hilab : (i : ℕ) + 1 < r := by
        have hxle : (i.succ : ℕ) ≤ r + 1 := Nat.lt_succ_iff.mp i.succ.is_lt
        have hxne1 : (i.succ : ℕ) ≠ r + 1 := by
          intro h
          exact hlast (Fin.ext (by simpa using h))
        have hxlt : (i.succ : ℕ) < r + 1 := lt_of_le_of_ne hxle hxne1
        have hxle' : (i.succ : ℕ) ≤ r := Nat.lt_succ_iff.mp hxlt
        have hxne : (i.succ : ℕ) ≠ r := by
          intro h
          exact halt (by rw [h])
        have hxlt' : (i.succ : ℕ) < r := lt_of_le_of_ne hxle' hxne
        rwa [Fin.val_succ] at hxlt'
      rw [d.elt_of_add_one_lt i hilab]
      congr 1
      change ((d.toFlipFrame.sub ((i : ℕ) + 1)).map
          (shiftEmb (K := K) (r + 1))).map (e.pointIso hσ).toLinearMap =
        (d.toFlipFrame.sub ((i : ℕ) + 1)).map
          ((e.pointIso hσ).toLinearMap.comp (shiftEmb (K := K) (r + 1)))
      rw [Submodule.map_comp]

theorem isTypeMorphism_pointEmb (hσ : IsUnitaryInvolution σ) {t : ℕ}
    (e : DChamber σ (t + 3)) :
    IsTypeMorphism (dChamberSystem σ (t + 1)) (dChamberSystem σ (t + 2)) Fin.succ
      (e.pointEmb hσ) := by
  intro i x y hxy
  rw [dChamberSystem_adj_iff] at hxy ⊢
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    rw [FlipFrame.elt_zero _ (by omega), FlipFrame.elt_zero _ (by omega),
      DChamber.pointEmb_line_zero, DChamber.pointEmb_line_zero]
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hk0
    have hji : j ≠ i := fun h => hk (by rw [h])
    rw [DChamber.elt_pointEmb_succ, DChamber.elt_pointEmb_succ, hxy j hji]

theorem isPanelLift_pointEmb (hσ : IsUnitaryInvolution σ) {t : ℕ}
    (e : DChamber σ (t + 3)) :
    IsPanelLift (dChamberSystem σ (t + 1)) (dChamberSystem σ (t + 2)) Fin.succ
      (e.pointEmb hσ) := by
  intro i x d hd
  rw [dChamberSystem_adj_iff] at hd
  have hx0 : (e.pointEmb hσ x).elt 0 = e.line 0 := by
    rw [FlipFrame.elt_zero _ (by omega), DChamber.pointEmb_line_zero]
  have hd0 : d.elt 0 = d.line 0 := FlipFrame.elt_zero _ (by omega)
  have hline : d.line 0 = e.line 0 := by
    have h0 := hd 0 (by simpa using (Fin.succ_ne_zero i).symm)
    rw [hx0, hd0] at h0
    exact h0.symm
  obtain ⟨y, hy⟩ := DChamber.exists_pointEmb_eq hσ e (c := d) hline
  refine ⟨y, ?_, hy⟩
  rw [dChamberSystem_adj_iff]
  intro j hj
  have hjs : j.succ ≠ Fin.succ i := fun h => hj (by simpa using h)
  have h0 := hd j.succ hjs
  rw [← hy] at h0
  rw [DChamber.elt_pointEmb_succ, DChamber.elt_pointEmb_succ] at h0
  exact DChamber.sup_map_pointMap_inj hσ e h0

theorem exists_fibre_gallery (hσ : IsUnitaryInvolution σ) (t : ℕ)
    (hconn : (dChamberSystem σ (t + 1)).Connected) {c c' : DChamber σ (t + 3)}
    (h : c.line 0 = c'.line 0) :
    ∃ τ, IsJGallery (dChamberSystem σ (t + 2)) {i | i ≠ 0} c τ ∧ galleryEnd c τ = c' := by
  obtain ⟨d₀, h₀⟩ := DChamber.exists_pointEmb_eq hσ c (c := c) rfl
  obtain ⟨d₁, h₁⟩ := DChamber.exists_pointEmb_eq hσ c (c := c') h.symm
  obtain ⟨γ, hγ, hend⟩ := hconn d₀ d₁
  refine ⟨galleryMapT Fin.succ (c.pointEmb hσ) γ, ⟨?_, ?_⟩, ?_⟩
  · have hgal := (isTypeMorphism_pointEmb hσ c).isGallery hγ
    rwa [h₀] at hgal
  · intro j hj
    obtain ⟨i, -, rfl⟩ :=
      (mem_galleryType_galleryMapT Fin.succ (c.pointEmb hσ) γ j).mp hj
    exact Fin.succ_ne_zero i
  · calc
      galleryEnd c (galleryMapT Fin.succ (c.pointEmb hσ) γ)
          = galleryEnd (c.pointEmb hσ d₀) (galleryMapT Fin.succ (c.pointEmb hσ) γ) := by
              rw [h₀]
      _ = c.pointEmb hσ (galleryEnd d₀ γ) :=
            galleryEnd_galleryMapT Fin.succ (c.pointEmb hσ) d₀ γ
      _ = c.pointEmb hσ d₁ := by rw [hend]
      _ = c' := h₁

theorem exists_flag_gallery (hσ : IsUnitaryInvolution σ) (s : ℕ)
    (hconn : (dChamberSystem σ (s + 1)).Connected) {c c' : DChamber σ (s + 4)}
    (h0 : c.line 0 = c'.line 0) (h1 : c.line 0 ⊔ c.line 1 = c'.line 0 ⊔ c'.line 1) :
    ∃ τ, IsJGallery (dChamberSystem σ (s + 3)) {i | i ≠ 0 ∧ i ≠ 1} c τ ∧
      galleryEnd c τ = c' := by
  obtain ⟨d, hd⟩ := DChamber.exists_pointEmb_eq hσ c (c := c) rfl
  obtain ⟨d', hd'⟩ := DChamber.exists_pointEmb_eq hσ c (c := c') h0.symm
  have hd1 : d.line 0 = d'.line 0 := by
    have hsup : c.line 0 ⊔ (d.line 0).map (c.pointMap hσ) =
        c.line 0 ⊔ (d'.line 0).map (c.pointMap hσ) := by
      have h1' := h1
      rw [← hd, ← hd'] at h1'
      have hl0d : (c.pointEmb hσ d).line 0 = c.line 0 :=
        DChamber.pointEmb_line_zero hσ c d
      have hl1d : (c.pointEmb hσ d).line 1 = (d.line 0).map (c.pointMap hσ) := by
        simpa using DChamber.pointEmb_line_succ hσ c d (0 : Fin (s + 3))
      have hl0d' : (c.pointEmb hσ d').line 0 = c.line 0 :=
        DChamber.pointEmb_line_zero hσ c d'
      have hl1d' : (c.pointEmb hσ d').line 1 = (d'.line 0).map (c.pointMap hσ) := by
        simpa using DChamber.pointEmb_line_succ hσ c d' (0 : Fin (s + 3))
      rw [hl0d, hl1d, hl0d', hl1d'] at h1'
      exact h1'
    exact DChamber.sup_map_pointMap_inj hσ c hsup
  obtain ⟨τ, hτ, hend⟩ := exists_fibre_gallery hσ s hconn (c := d) (c' := d') hd1
  refine ⟨galleryMapT Fin.succ (c.pointEmb hσ) τ, ⟨?_, ?_⟩, ?_⟩
  · have hgal := (isTypeMorphism_pointEmb hσ c).isGallery hτ.1
    rwa [hd] at hgal
  · intro j hj
    obtain ⟨i, hi, rfl⟩ :=
      (mem_galleryType_galleryMapT Fin.succ (c.pointEmb hσ) τ j).mp hj
    refine ⟨Fin.succ_ne_zero i, ?_⟩
    intro h
    exact hτ.2 i hi (Fin.succ_injective (s + 3) (by simpa using h))
  · calc
      galleryEnd c (galleryMapT Fin.succ (c.pointEmb hσ) τ)
          = galleryEnd (c.pointEmb hσ d) (galleryMapT Fin.succ (c.pointEmb hσ) τ) := by
              rw [hd]
      _ = c.pointEmb hσ (galleryEnd d τ) :=
            galleryEnd_galleryMapT Fin.succ (c.pointEmb hσ) d τ
      _ = c.pointEmb hσ d' := by rw [hend]
      _ = c' := hd'

theorem twoHomotopic_nil_of_isJGallery_ne_zero (hσ : IsUnitaryInvolution σ) (t : ℕ)
    (hsc : (dChamberSystem σ (t + 1)).SimplyTwoConnected) {e : DChamber σ (t + 3)}
    {γ : List (Fin (t + 3) × DChamber σ (t + 3))}
    (hγ : IsJGallery (dChamberSystem σ (t + 2)) {i | i ≠ 0} e γ)
    (hend : galleryEnd e γ = e) :
    (dChamberSystem σ (t + 2)).TwoHomotopic e γ [] := by
  obtain ⟨d₀, h₀⟩ := DChamber.exists_pointEmb_eq hσ e (c := e) rfl
  rw [← h₀]
  refine twoHomotopic_nil_of_isPanelLift (X := dChamberSystem σ (t + 1))
    (Y := dChamberSystem σ (t + 2)) (τ := Fin.succ) (f := e.pointEmb hσ)
    (isTypeMorphism_pointEmb hσ e) (isPanelLift_pointEmb hσ e)
    (DChamber.pointEmb_injective hσ e) hsc (x := d₀) (γ := γ) ?_ ?_ ?_
  · have hgal := hγ.1
    rwa [← h₀] at hgal
  · intro j hj
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero (hγ.2 j hj)
    exact ⟨i, rfl⟩
  · have he := hend
    rwa [← h₀] at he

end CFSG.ClassicalInvolution.PhanDn

end
