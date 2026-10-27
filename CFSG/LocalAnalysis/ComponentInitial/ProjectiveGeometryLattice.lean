module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Length

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace ProjectiveGeometry

open Module

variable {K : Type*} [Field K] {n : ℕ}

abbrev Point (n : ℕ) (K : Type*) [Field K] : Type _ :=
  {L : Submodule K (Fin n → K) // finrank K L = 1}

abbrev Hyperplane (n : ℕ) (K : Type*) [Field K] : Type _ :=
  {H : Submodule K (Fin n → K) // finrank K H = n - 1}

theorem exists_eq_span_singleton {L : Submodule K (Fin n → K)} (hL : finrank K L = 1) :
    ∃ v : Fin n → K, v ≠ 0 ∧ L = K ∙ v := by
  have hL0 : L ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hL
    exact zero_ne_one hL
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  refine ⟨v, hv0, (Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hv) ?_).symm⟩
  rw [finrank_span_singleton hv0, hL]

theorem eq_of_le_of_finrank_eq_one {L L' : Submodule K (Fin n → K)} (hL : finrank K L = 1)
    (hL' : finrank K L' = 1) (h : L ≤ L') : L = L' :=
  Submodule.eq_of_le_of_finrank_eq h (hL.trans hL'.symm)

theorem le_of_forall_point {W W' : Submodule K (Fin n → K)}
    (h : ∀ L : Submodule K (Fin n → K), finrank K L = 1 → L ≤ W → L ≤ W') : W ≤ W' := by
  intro v hv
  by_cases hv0 : v = 0
  · rw [hv0]
    exact W'.zero_mem
  · exact h _ (finrank_span_singleton hv0) ((Submodule.span_singleton_le_iff_mem _ _).mpr hv)
      (Submodule.mem_span_singleton_self v)

theorem eq_of_forall_point {W W' : Submodule K (Fin n → K)}
    (h : ∀ L : Submodule K (Fin n → K), finrank K L = 1 → (L ≤ W ↔ L ≤ W')) : W = W' :=
  le_antisymm (le_of_forall_point fun L hL hle => (h L hL).mp hle)
    (le_of_forall_point fun L hL hle => (h L hL).mpr hle)

theorem exists_hyperplane_of_notMem {W : Submodule K (Fin n → K)} {v : Fin n → K} (hv : v ∉ W) :
    ∃ H : Submodule K (Fin n → K), finrank K H = n - 1 ∧ W ≤ H ∧ v ∉ H := by
  obtain ⟨φ, hφv, hφW⟩ := W.exists_dual_map_eq_bot_of_notMem hv inferInstance
  refine ⟨LinearMap.ker φ, ?_, fun w hw => ?_, fun h => hφv (LinearMap.mem_ker.mp h)⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr fun c =>
      ⟨(c / φ v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hφv]⟩
    rw [h2, finrank_top, Module.finrank_self, finrank_fin_fun] at h1
    omega
  · have : φ w ∈ W.map φ := Submodule.mem_map_of_mem hw
    rw [hφW, Submodule.mem_bot] at this
    exact this

theorem le_iff_forall_hyperplane {W L : Submodule K (Fin n → K)} (hL : finrank K L = 1) :
    L ≤ W ↔ ∀ H : Submodule K (Fin n → K), finrank K H = n - 1 → W ≤ H → L ≤ H := by
  refine ⟨fun h H _ hWH => h.trans hWH, fun h => ?_⟩
  obtain ⟨v, -, rfl⟩ := exists_eq_span_singleton hL
  rw [Submodule.span_singleton_le_iff_mem]
  by_contra hv
  obtain ⟨H, hH, hWH, hvH⟩ := exists_hyperplane_of_notMem hv
  exact hvH ((Submodule.span_singleton_le_iff_mem _ _).mp (h H hH hWH))

theorem finrank_orderIso (Φ : Submodule K (Fin n → K) ≃o Submodule K (Fin n → K))
    (W : Submodule K (Fin n → K)) : finrank K (Φ W) = finrank K W := by
  have h1 := Module.length_eq_finrank K (Φ W)
  have h2 := Module.length_eq_finrank K W
  rw [Module.length_submodule, Order.height_orderIso] at h1
  rw [Module.length_submodule] at h2
  exact_mod_cast h1.symm.trans h2

theorem orderIso_eq_of_forall_point (Φ Φ' : Submodule K (Fin n → K) ≃o Submodule K (Fin n → K))
    (h : ∀ L : Submodule K (Fin n → K), finrank K L = 1 → Φ L = Φ' L) : Φ = Φ' := by
  have hsymm : ∀ L' : Submodule K (Fin n → K), finrank K L' = 1 → Φ.symm L' = Φ'.symm L' := by
    intro L' hL'
    have hL : finrank K (Φ'.symm L') = 1 := (finrank_orderIso Φ'.symm L').trans hL'
    rw [OrderIso.symm_apply_eq, h _ hL, OrderIso.apply_symm_apply]
  refine RelIso.ext fun W => eq_of_forall_point fun L' hL' => ?_
  rw [← OrderIso.symm_apply_le, ← OrderIso.symm_apply_le, hsymm L' hL']

section Extension

variable (f : Point n K ≃ Point n K) (h : Hyperplane n K ≃ Hyperplane n K)

@[expose] noncomputable def hyperplaneImage (h : Hyperplane n K ≃ Hyperplane n K)
    (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) :=
  ⨅ (H : Hyperplane n K) (_ : W ≤ H), (h H : Submodule K (Fin n → K))

variable {f h}

theorem le_hyperplaneImage_iff
    (hfh : ∀ (L : Point n K) (H : Hyperplane n K),
      (L : Submodule K (Fin n → K)) ≤ H ↔ (f L : Submodule K (Fin n → K)) ≤ h H)
    (L : Point n K) (W : Submodule K (Fin n → K)) :
    (f L : Submodule K (Fin n → K)) ≤ hyperplaneImage h W ↔ (L : Submodule K (Fin n → K)) ≤ W := by
  rw [hyperplaneImage, le_iInf₂_iff, le_iff_forall_hyperplane L.2]
  constructor
  · intro hL H hH hWH
    exact (hfh L ⟨H, hH⟩).mpr (hL ⟨H, hH⟩ hWH)
  · intro hL H hWH
    exact (hfh L H).mp (hL H H.2 hWH)

theorem le_hyperplaneImage_iff'
    (hfh : ∀ (L : Point n K) (H : Hyperplane n K),
      (L : Submodule K (Fin n → K)) ≤ H ↔ (f L : Submodule K (Fin n → K)) ≤ h H)
    (L : Point n K) (W : Submodule K (Fin n → K)) :
    (L : Submodule K (Fin n → K)) ≤ hyperplaneImage h W ↔
      (f.symm L : Submodule K (Fin n → K)) ≤ W := by
  have := le_hyperplaneImage_iff hfh (f.symm L) W
  rwa [Equiv.apply_symm_apply] at this

theorem incidence_symm
    (hfh : ∀ (L : Point n K) (H : Hyperplane n K),
      (L : Submodule K (Fin n → K)) ≤ H ↔ (f L : Submodule K (Fin n → K)) ≤ h H)
    (L : Point n K) (H : Hyperplane n K) :
    (L : Submodule K (Fin n → K)) ≤ H ↔ (f.symm L : Submodule K (Fin n → K)) ≤ h.symm H := by
  rw [hfh (f.symm L) (h.symm H), Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[expose] noncomputable def latticeExtension
    (hfh : ∀ (L : Point n K) (H : Hyperplane n K),
      (L : Submodule K (Fin n → K)) ≤ H ↔ (f L : Submodule K (Fin n → K)) ≤ h H) :
    Submodule K (Fin n → K) ≃o Submodule K (Fin n → K) where
  toFun := hyperplaneImage h
  invFun := hyperplaneImage h.symm
  left_inv W := eq_of_forall_point fun L hL => by
    rw [le_hyperplaneImage_iff' (incidence_symm hfh) ⟨L, hL⟩, Equiv.symm_symm]
    exact le_hyperplaneImage_iff hfh ⟨L, hL⟩ W
  right_inv W := eq_of_forall_point fun L hL => by
    rw [le_hyperplaneImage_iff' hfh ⟨L, hL⟩]
    exact le_hyperplaneImage_iff (incidence_symm hfh) ⟨L, hL⟩ W
  map_rel_iff' {W W'} := by
    change hyperplaneImage h W ≤ hyperplaneImage h W' ↔ W ≤ W'
    constructor
    · intro hle
      refine le_of_forall_point fun L hL hLW => ?_
      have := ((le_hyperplaneImage_iff hfh ⟨L, hL⟩ W).mpr hLW).trans hle
      exact (le_hyperplaneImage_iff hfh ⟨L, hL⟩ W').mp this
    · intro hle
      refine le_of_forall_point fun L hL hLW => ?_
      rw [le_hyperplaneImage_iff' hfh ⟨L, hL⟩] at hLW ⊢
      exact hLW.trans hle

theorem latticeExtension_apply
    (hfh : ∀ (L : Point n K) (H : Hyperplane n K),
      (L : Submodule K (Fin n → K)) ≤ H ↔ (f L : Submodule K (Fin n → K)) ≤ h H)
    (W : Submodule K (Fin n → K)) : latticeExtension hfh W = hyperplaneImage h W :=
  rfl

end Extension

theorem incidence_lattice (f : Point n K ≃ Point n K) (h : Hyperplane n K ≃ Hyperplane n K)
    (hfh : ∀ (L : Point n K) (H : Hyperplane n K),
      (L : Submodule K (Fin n → K)) ≤ H ↔ (f L : Submodule K (Fin n → K)) ≤ h H) :
    ∃ Φ : Submodule K (Fin n → K) ≃o Submodule K (Fin n → K),
      ((∀ L : Point n K, Φ L = f L) ∧ ∀ H : Hyperplane n K, Φ H = h H) ∧
      (∀ Φ' : Submodule K (Fin n → K) ≃o Submodule K (Fin n → K),
        (∀ L : Point n K, Φ' L = f L) → (∀ H : Hyperplane n K, Φ' H = h H) → Φ' = Φ) ∧
      (∀ W : Submodule K (Fin n → K), finrank K (Φ W) = finrank K W) ∧
      (∀ W W' : Submodule K (Fin n → K), Φ (W ⊔ W') = Φ W ⊔ Φ W' ∧ Φ (W ⊓ W') = Φ W ⊓ Φ W') ∧
      ∀ (W : Submodule K (Fin n → K)) (L' : Point n K),
        (L' : Submodule K (Fin n → K)) ≤ Φ W ↔
          ∃ L : Point n K, (L : Submodule K (Fin n → K)) ≤ W ∧ f L = L' := by
  set Φ := latticeExtension hfh with hΦ
  have hpt : ∀ (L : Point n K) (W : Submodule K (Fin n → K)),
      (L : Submodule K (Fin n → K)) ≤ Φ W ↔ (f.symm L : Submodule K (Fin n → K)) ≤ W :=
    le_hyperplaneImage_iff' hfh
  have hΦL : ∀ L : Point n K, Φ L = f L := by
    intro L
    refine eq_of_forall_point fun L' hL' => ?_
    rw [hpt ⟨L', hL'⟩]
    constructor
    · intro hle
      have h1 := eq_of_le_of_finrank_eq_one (f.symm ⟨L', hL'⟩).2 L.2 hle
      have h2 : f.symm ⟨L', hL'⟩ = L := Subtype.ext h1
      rw [← h2, Equiv.apply_symm_apply]
    · intro hle
      have h1 := eq_of_le_of_finrank_eq_one hL' (f L).2 hle
      have h2 : (⟨L', hL'⟩ : Point n K) = f L := Subtype.ext h1
      rw [h2, Equiv.symm_apply_apply]
  refine ⟨Φ, ⟨hΦL, fun H => ?_⟩, fun Φ' hΦ' _ => ?_, fun W => finrank_orderIso Φ W,
    fun W W' => ⟨Φ.map_sup W W', Φ.map_inf W W'⟩, fun W L' => ?_⟩
  · refine eq_of_forall_point fun L' hL' => ?_
    rw [hpt ⟨L', hL'⟩, hfh, Equiv.apply_symm_apply]
  · exact orderIso_eq_of_forall_point Φ' Φ fun L hL => by
      rw [hΦ' ⟨L, hL⟩, hΦL ⟨L, hL⟩]
  · rw [hpt]
    exact ⟨fun hle => ⟨f.symm L', hle, Equiv.apply_symm_apply f L'⟩, by
      rintro ⟨L, hL, rfl⟩
      rwa [Equiv.symm_apply_apply]⟩

end ProjectiveGeometry

end CFSG.LocalAnalysis.ComponentInitial
