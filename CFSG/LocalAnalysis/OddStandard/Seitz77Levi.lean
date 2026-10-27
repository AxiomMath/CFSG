module

public import CFSG.LocalAnalysis.OddStandard.Seitz77LeviChart
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionDefs
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34

public section

namespace CFSG.OddStandard.Seitz77.Levi

open Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.ComponentClassification
  CFSG.ComponentClassification.PSL3Four CFSG.OddStandard.Seitz77.L34 CFSG.Open

@[expose] def ActsAs {G : Type*} [Group G] {W : Subgroup G}
    (ι : ↥W ≃* Multiplicative (Fin 2 → F4)) (g : G) (f : (Fin 2 → F4) → Fin 2 → F4) : Prop :=
  ∀ w : ↥W, ∃ hw : g * (w : G) * g⁻¹ ∈ W,
    ι ⟨g * (w : G) * g⁻¹, hw⟩ = Multiplicative.ofAdd (f (Multiplicative.toAdd (ι w)))

section ActsAsAPI

variable {G : Type*} [Group G] {W : Subgroup G} {ι : ↥W ≃* Multiplicative (Fin 2 → F4)}
  {g g' h : G} {f f' f₁ f₂ : (Fin 2 → F4) → Fin 2 → F4}

theorem ActsAs.conj_mem (hg : ActsAs ι g f) (w : ↥W) : g * (w : G) * g⁻¹ ∈ W := by
  obtain ⟨hw, -⟩ := hg w
  exact hw

theorem ActsAs.conj_eq (hg : ActsAs ι g f) (w : ↥W) :
    (⟨g * (w : G) * g⁻¹, hg.conj_mem w⟩ : ↥W) =
      ι.symm (Multiplicative.ofAdd (f (Multiplicative.toAdd (ι w)))) := by
  obtain ⟨hw, h⟩ := hg w
  apply ι.injective
  rw [MulEquiv.apply_symm_apply]
  exact h

theorem ActsAs.mem_normalizer [Finite G] (hg : ActsAs ι g f) : g ∈ normalizer (W : Set G) :=
  Subgroup.mem_normalizer_fintype fun n hn => hg.conj_mem ⟨n, hn⟩

theorem ActsAs.congr (hg : ActsAs ι g f) (e : f = f') : ActsAs ι g f' :=
  e ▸ hg

theorem ActsAs.comp (hg : ActsAs ι g f₁) (hh : ActsAs ι h f₂) : ActsAs ι (g * h) (f₁ ∘ f₂) := by
  intro w
  obtain ⟨hw₂, h₂⟩ := hh w
  obtain ⟨hw₁, h₁⟩ := hg ⟨h * (w : G) * h⁻¹, hw₂⟩
  have hmem : g * h * (w : G) * (g * h)⁻¹ ∈ W := by
    have : g * h * (w : G) * (g * h)⁻¹ = g * (h * (w : G) * h⁻¹) * g⁻¹ := by group
    rw [this]
    exact hw₁
  refine ⟨hmem, ?_⟩
  have key : (⟨g * h * (w : G) * (g * h)⁻¹, hmem⟩ : ↥W) =
      ⟨g * (h * (w : G) * h⁻¹) * g⁻¹, hw₁⟩ := Subtype.ext (by group)
  rw [key, h₁, h₂]
  rfl

theorem ActsAs.comm_of_same (hg : ActsAs ι g f) (hg' : ActsAs ι g' f) {w : G} (hw : w ∈ W) :
    g⁻¹ * g' * w = w * (g⁻¹ * g') := by
  have h1 := congrArg Subtype.val (hg.conj_eq ⟨w, hw⟩)
  have h2 := congrArg Subtype.val (hg'.conj_eq ⟨w, hw⟩)
  have h3 : g' * w * g'⁻¹ = g * w * g⁻¹ := h2.trans h1.symm
  calc g⁻¹ * g' * w = g⁻¹ * (g' * w * g'⁻¹) * g' := by group
    _ = g⁻¹ * (g * w * g⁻¹) * g' := by rw [h3]
    _ = w * (g⁻¹ * g') := by group

theorem ActsAs.comm_of_id (hg : ActsAs ι g id) {w : G} (hw : w ∈ W) : g * w = w * g := by
  have h1 := congrArg Subtype.val (hg.conj_eq ⟨w, hw⟩)
  have h2 : g * w * g⁻¹ = w := by simpa using h1
  calc g * w = g * w * g⁻¹ * g := by group
    _ = w * g := by rw [h2]

end ActsAsAPI

theorem cUp_zero_fun : (fun v : Fin 2 → F4 => ![v 0 + (0 : F4) * v 1, v 1]) = id := by
  funext v
  ext i
  fin_cases i <;> simp

theorem cUp_add_fun (γ γ' : F4) :
    (fun v : Fin 2 → F4 => ![v 0 + (γ + γ') * v 1, v 1]) =
      (fun v : Fin 2 → F4 => ![v 0 + γ * v 1, v 1]) ∘
        (fun v : Fin 2 → F4 => ![v 0 + γ' * v 1, v 1]) := by
  funext v
  ext i
  fin_cases i
  · simp
    ring
  · simp

theorem cLow_zero_fun : (fun v : Fin 2 → F4 => ![v 0, v 1 + (0 : F4) * v 0]) = id := by
  funext v
  ext i
  fin_cases i <;> simp

theorem cLow_add_fun (γ γ' : F4) :
    (fun v : Fin 2 → F4 => ![v 0, v 1 + (γ + γ') * v 0]) =
      (fun v : Fin 2 → F4 => ![v 0, v 1 + γ * v 0]) ∘
        (fun v : Fin 2 → F4 => ![v 0, v 1 + γ' * v 0]) := by
  funext v
  ext i
  fin_cases i
  · simp
  · simp
    ring

theorem dTor_cube_fun :
    ((fun v : Fin 2 → F4 => ![F4.ω * v 0, F4.ω * F4.ω * v 1]) ∘
      (fun v : Fin 2 → F4 => ![F4.ω * v 0, F4.ω * F4.ω * v 1]) ∘
        (fun v : Fin 2 → F4 => ![F4.ω * v 0, F4.ω * F4.ω * v 1])) = id := by
  have h3 := omega_cube
  funext v
  ext i
  fin_cases i
  · simp
    linear_combination (v 0) * h3
  · simp
    linear_combination (v 1 * (F4.ω * F4.ω * F4.ω + 1)) * h3

structure LeviData {G : Type*} [Group G] (A W : Subgroup G) where
  ι : ↥W ≃* Multiplicative (Fin 2 → F4)
  u : F4 → G
  l : F4 → G
  τ : G
  u_mem : ∀ γ, u γ ∈ A
  l_mem : ∀ γ, l γ ∈ A
  τ_mem : τ ∈ A
  act_u : ∀ γ, ActsAs ι (u γ) (fun v => ![v 0 + γ * v 1, v 1])
  act_l : ∀ γ, ActsAs ι (l γ) (fun v => ![v 0, v 1 + γ * v 0])
  act_τ : ActsAs ι τ (fun v => ![F4.ω * v 0, F4.ω * F4.ω * v 1])

section Coordinates

variable {G : Type*} [Group G]

@[expose] noncomputable def coordOfRange {W : Subgroup G} (κ : Multiplicative (Fin 2 → F4) →* G)
    (hκ : Function.Injective κ) (hr : κ.range = W) : ↥W ≃* Multiplicative (Fin 2 → F4) :=
  (MulEquiv.subgroupCongr hr.symm).trans (MonoidHom.ofInjective hκ).symm

theorem coe_coordOfRange_symm {W : Subgroup G} {κ : Multiplicative (Fin 2 → F4) →* G}
    {hκ : Function.Injective κ} {hr : κ.range = W} (v : Multiplicative (Fin 2 → F4)) :
    (((coordOfRange κ hκ hr).symm v : ↥W) : G) = κ v := by
  simp [coordOfRange, MonoidHom.ofInjective_apply]

theorem actsAs_of_range {W : Subgroup G} {κ : Multiplicative (Fin 2 → F4) →* G}
    {hκ : Function.Injective κ} {hr : κ.range = W} (g : G) (f : (Fin 2 → F4) → Fin 2 → F4)
    (h : ∀ v : Multiplicative (Fin 2 → F4),
      g * κ v * g⁻¹ = κ (Multiplicative.ofAdd (f (Multiplicative.toAdd v)))) :
    ActsAs (coordOfRange κ hκ hr) g f := by
  intro w
  set ι := coordOfRange κ hκ hr with hι
  set v := ι w with hv
  have hw : (w : G) = κ v := by
    have := coe_coordOfRange_symm (hκ := hκ) (hr := hr) v
    rw [hv, MulEquiv.symm_apply_apply] at this
    exact this
  have hmem : g * (w : G) * g⁻¹ ∈ W := by
    rw [hw, h v, ← hr]
    exact ⟨_, rfl⟩
  refine ⟨hmem, ?_⟩
  apply ι.symm.injective
  apply Subtype.ext
  rw [MulEquiv.symm_apply_apply, coe_coordOfRange_symm, ← h v]
  show g * (w : G) * g⁻¹ = g * κ v * g⁻¹
  rw [hw]

end Coordinates

section Charts

variable {G : Type*} [Group G]

@[expose] def coordU1 : Multiplicative (Fin 2 → F4) →* ↥(unipAll F4) where
  toFun v := ofCoords (Multiplicative.toAdd v 1) 0 (Multiplicative.toAdd v 0)
  map_one' := by
    rw [← ofCoords_zero]
    rfl
  map_mul' v v' := by
    rw [ofCoords_mul, ofCoords_inj]
    simp

@[expose] def coordU2 : Multiplicative (Fin 2 → F4) →* ↥(unipAll F4) where
  toFun v := ofCoords 0 (Multiplicative.toAdd v 1) (Multiplicative.toAdd v 0)
  map_one' := by
    rw [← ofCoords_zero]
    rfl
  map_mul' v v' := by
    rw [ofCoords_mul, ofCoords_inj]
    simp

theorem coordU1_apply (v : Multiplicative (Fin 2 → F4)) :
    coordU1 v = ofCoords (Multiplicative.toAdd v 1) 0 (Multiplicative.toAdd v 0) := rfl

theorem coordU2_apply (v : Multiplicative (Fin 2 → F4)) :
    coordU2 v = ofCoords 0 (Multiplicative.toAdd v 1) (Multiplicative.toAdd v 0) := rfl

theorem coordU1_injective : Function.Injective coordU1 := by
  intro v v' h
  rw [coordU1_apply, coordU1_apply, ofCoords_inj] at h
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact h.2.2
  · exact h.1

theorem coordU2_injective : Function.Injective coordU2 := by
  intro v v' h
  rw [coordU2_apply, coordU2_apply, ofCoords_inj] at h
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact h.2.2
  · exact h.2.1

theorem coordU1_range : coordU1.range = U1 := by
  ext x
  obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
  rw [ofCoords_mem_U1]
  constructor
  · rintro ⟨v, hv⟩
    rw [coordU1_apply, ofCoords_inj] at hv
    exact hv.2.1.symm
  · rintro rfl
    refine ⟨Multiplicative.ofAdd ![c, a], ?_⟩
    rw [coordU1_apply, ofCoords_inj]
    simp

theorem coordU2_range : coordU2.range = U2 := by
  ext x
  obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
  rw [ofCoords_mem_U2]
  constructor
  · rintro ⟨v, hv⟩
    rw [coordU2_apply, ofCoords_inj] at hv
    exact hv.1.symm
  · rintro rfl
    refine ⟨Multiplicative.ofAdd ![c, b], ?_⟩
    rw [coordU2_apply, ofCoords_inj]
    simp

end Charts

section Existence

variable {G : Type*} [Group G] [Finite G]

private theorem neg_sub_eq (x y γ : F4) : x - y * γ = x + γ * y := by
  rw [sub_eq_add_neg, neg_eq_self_of_card natCard_F4, mul_comm]

private theorem ω_mul_ω_zero : F4.ω * F4.ω * (0 : F4) = 0 := mul_zero _

theorem exists_leviData {A V W : Subgroup G}
    (hZ : Odd (Nat.card (center ↥A))) (e : ↥A ⧸ center ↥A ≃* PSL3Four.S)
    (hV : CFSG.ABGLocalTools.IsSylowOf 2 V A) (hWV : W ≤ V) (hWab : IsElemAbelian 2 W)
    (hW16 : Nat.card W = 16) : Nonempty (LeviData A W) := by
  obtain ⟨ι, h, hι, hr, hhA, -, hact, hl1, hl2⟩ := exists_chart_lifts_of_isSylowOf hZ e hV
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := radicals_of_chart hι hr
  have hmemA : ∀ u, ι u ∈ A := fun u => hV.le (by rw [← hr]; exact ⟨u, rfl⟩)
  rcases h13 W hWV hWab hW16 with hW | hW
  ·
    subst hW
    choose l hlA hl using hl1
    have hκ : Function.Injective (ι.comp coordU1) := hι.comp coordU1_injective
    have hκr : (ι.comp coordU1).range = U1.map ι := by
      rw [MonoidHom.range_comp, coordU1_range]
    refine ⟨{ ι := coordOfRange (ι.comp coordU1) hκ hκr
              u := fun γ => ι (ofCoords 0 γ 0)
              l := l
              τ := h
              u_mem := fun γ => hmemA _
              l_mem := hlA
              τ_mem := hhA
              act_u := fun γ => actsAs_of_range _ _ fun v => ?_
              act_l := fun γ => actsAs_of_range _ _ fun v => ?_
              act_τ := actsAs_of_range _ _ fun v => ?_ }⟩
    · simp only [MonoidHom.comp_apply, coordU1_apply, toAdd_ofAdd, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [← map_inv, ← map_mul, ← map_mul, ofCoords_conj_one, neg_sub_eq]
    · simp only [MonoidHom.comp_apply, coordU1_apply, toAdd_ofAdd, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      exact hl γ _ _
    · simp only [MonoidHom.comp_apply, coordU1_apply, toAdd_ofAdd, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [hact, ω_mul_ω_zero]
  ·
    subst hW
    choose l hlA hl using hl2
    have hκ : Function.Injective (ι.comp coordU2) := hι.comp coordU2_injective
    have hκr : (ι.comp coordU2).range = U2.map ι := by
      rw [MonoidHom.range_comp, coordU2_range]
    refine ⟨{ ι := coordOfRange (ι.comp coordU2) hκ hκr
              u := fun γ => ι (ofCoords γ 0 0)
              l := l
              τ := h
              u_mem := fun γ => hmemA _
              l_mem := hlA
              τ_mem := hhA
              act_u := fun γ => actsAs_of_range _ _ fun v => ?_
              act_l := fun γ => actsAs_of_range _ _ fun v => ?_
              act_τ := actsAs_of_range _ _ fun v => ?_ }⟩
    · simp only [MonoidHom.comp_apply, coordU2_apply, toAdd_ofAdd, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [← map_inv, ← map_mul, ← map_mul, ofCoords_conj_two]
    · simp only [MonoidHom.comp_apply, coordU2_apply, toAdd_ofAdd, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      exact hl γ _ _
    · simp only [MonoidHom.comp_apply, coordU2_apply, toAdd_ofAdd, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [hact, ω_mul_ω_zero]

end Existence

end CFSG.OddStandard.Seitz77.Levi

namespace CFSG.OddStandard.Seitz77

theorem Hyp.exists_leviData {G : Type} [Group G] [Finite G]
    {A V₁ V₂ W : Subgroup G} (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) : Nonempty (Levi.LeviData A W) := by
  obtain ⟨e⟩ := h.nonempty_equiv_S
  obtain ⟨hWV, hWab, hW16⟩ := hR.property hW
  exact Levi.exists_leviData h.odd e d.V_isSylow hWV hWab hW16

end CFSG.OddStandard.Seitz77
