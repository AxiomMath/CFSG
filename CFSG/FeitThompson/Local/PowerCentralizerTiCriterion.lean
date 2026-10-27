module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Order.Atoms
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer (e : G ≃* H) (s : Set G) :
    (Subgroup.centralizer s).map e.toMonoidHom = Subgroup.centralizer (e '' s) := by
  ext b
  rw [Subgroup.mem_map_equiv (f := e), Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h y ⟨x, hx, rfl⟩
    have hx' := h x hx
    calc e x * b = e (x * e.symm b) := by simp
      _ = e (e.symm b * x) := by rw [hx']
      _ = b * e x := by simp
  · intro h x hx
    exact e.injective (by simpa using h (e x) ⟨x, hx, rfl⟩)

theorem isCoatom_map_conj {M : Subgroup G} (hM : IsCoatom M) (g : G) :
    IsCoatom (M.map (MulAut.conj g).toMonoidHom) := by
  have h := ((MulAut.conj g).mapSubgroup).isCoatom_iff M
  simp only [MulEquiv.coe_mapSubgroup] at h
  exact h.mpr hM

theorem conj_image_eq_conjAct_smul (D : Set G) (g : G) :
    (fun d => g⁻¹ * d * g) '' D = ConjAct.toConjAct g⁻¹ • D := by
  ext x
  simp [Set.mem_smul_set, ConjAct.smul_def]

variable {M : Subgroup G} {D : Set G} {k : ℕ}

theorem disjoint_conj_image_of_isCoatom_centralizer_pow
    (hM : IsCoatom M) (hMN : Subgroup.normalizer (M : Set G) = M)
    (hle : ∀ d ∈ D, Subgroup.centralizer {d ^ k} ≤ M)
    (huniq : ∀ d ∈ D, ∀ K : Subgroup G, IsCoatom K → Subgroup.centralizer {d ^ k} ≤ K → K = M)
    {g : G} (hg : g ∉ M) :
    Disjoint D ((fun d => g⁻¹ * d * g) '' D) := by
  rw [Set.disjoint_left]
  rintro y hy ⟨z, hz, rfl⟩
  rw [show (fun d => g⁻¹ * d * g) z = MulAut.conj g⁻¹ z by simp] at hy
  have hsub : Subgroup.centralizer {(MulAut.conj g⁻¹ z) ^ k}
      ≤ M.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← map_pow, show ({MulAut.conj g⁻¹ (z ^ k)} : Set G) = MulAut.conj g⁻¹ '' {z ^ k} by simp,
      ← map_centralizer]
    exact Subgroup.map_mono (hle z hz)
  have hKM := huniq _ hy _ (isCoatom_map_conj hM g⁻¹) hsub
  have hginv : g⁻¹ ∈ M := hMN ▸ Subgroup.mem_normalizer_iff_map_conj_eq.2 hKM
  exact hg (by simpa using inv_mem hginv)

theorem normalizer_eq_of_isCoatom_centralizer_pow
    (hM : IsCoatom M) (hMN : Subgroup.normalizer (M : Set G) = M)
    (hD : D.Nonempty) (hstab : ∀ m ∈ M, (fun d => m⁻¹ * d * m) '' D ⊆ D)
    (hle : ∀ d ∈ D, Subgroup.centralizer {d ^ k} ≤ M)
    (huniq : ∀ d ∈ D, ∀ K : Subgroup G, IsCoatom K → Subgroup.centralizer {d ^ k} ≤ K → K = M) :
    Subgroup.normalizer D = M := by
  refine le_antisymm (fun g hg => ?_) (fun m hm => ?_)
  ·
    by_contra hgM
    obtain ⟨y, hy⟩ := hD
    have hdisj := disjoint_conj_image_of_isCoatom_centralizer_pow hM hMN hle huniq hgM
    rw [Set.disjoint_left] at hdisj
    exact hdisj hy ⟨g * y * g⁻¹, (Subgroup.mem_set_normalizer_iff.1 hg y).1 hy, by group⟩
  ·
    rw [Subgroup.mem_set_normalizer_iff]
    refine fun d => ⟨fun hd => ?_, fun hd => ?_⟩
    · exact hstab m⁻¹ (inv_mem hm) ⟨d, hd, by simp⟩
    · exact hstab m hm ⟨m * d * m⁻¹, hd, by group⟩

theorem normalizer_eq_and_disjoint_conj_of_isCoatom_centralizer_pow
    (hM : IsCoatom M) (hMN : Subgroup.normalizer (M : Set G) = M)
    (hD : D.Nonempty) (hstab : ∀ m ∈ M, (fun d => m⁻¹ * d * m) '' D ⊆ D)
    (hle : ∀ d ∈ D, Subgroup.centralizer {d ^ k} ≤ M)
    (huniq : ∀ d ∈ D, ∀ K : Subgroup G, IsCoatom K → Subgroup.centralizer {d ^ k} ≤ K → K = M) :
    Subgroup.normalizer D = M ∧
      ∀ g : G, g ∉ M → D ∩ (fun d => g⁻¹ * d * g) '' D = ∅ := by
  refine ⟨normalizer_eq_of_isCoatom_centralizer_pow hM hMN hD hstab hle huniq, fun g hg => ?_⟩
  rw [← Set.disjoint_iff_inter_eq_empty]
  exact disjoint_conj_image_of_isCoatom_centralizer_pow hM hMN hle huniq hg

end CFSG.FeitThompson
