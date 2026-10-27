module

public import CFSG.ClassicalGroups.McLaughlin.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.ClassicalGroups.McLaughlin

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem inv_apply_apply_val (g : LinearMap.GeneralLinearGroup K V) (y : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) y) = y := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

private theorem apply_inv_apply_val (g : LinearMap.GeneralLinearGroup K V) (y : V) :
    (g : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y) = y := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply]

theorem mem_axisSpace_smul_iff {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ X) (v x : V) :
    x ∈ axisSpace X ((g : V →ₗ[K] V) v) ↔
      ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x ∈ axisSpace X v := by
  rw [mem_axisSpace_iff, mem_axisSpace_iff]
  constructor
  · intro hx φ hφ
    exact hx _ (isRootElt_conj hφ hg)
  · intro hx ψ hψ
    have h := isRootElt_conj hψ (X.inv_mem hg)
    rw [inv_apply_apply_val, inv_inv] at h
    have h2 := hx _ h
    rw [LinearMap.comp_apply, apply_inv_apply_val] at h2
    exact h2

private theorem axisSpace_smul_eq_map {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ X) (v : V) :
    axisSpace X ((g : V →ₗ[K] V) v) = (axisSpace X v).map (g : V →ₗ[K] V) := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x,
      (mem_axisSpace_smul_iff hg v x).mp hx, apply_inv_apply_val g x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [mem_axisSpace_smul_iff hg v, inv_apply_apply_val]
    exact hy

private theorem finrank_axisSpace_smul {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ X) (v : V) :
    finrank K (axisSpace X ((g : V →ₗ[K] V) v)) = finrank K (axisSpace X v) := by
  have hinj : Function.Injective (g : V →ₗ[K] V) := by
    intro a b hab
    have h' : ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
        ((g : V →ₗ[K] V) a) =
        ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) b) := by
      rw [hab]
    rwa [inv_apply_apply_val, inv_apply_apply_val] at h'
  rw [axisSpace_smul_eq_map hg v]
  exact ((Submodule.equivMapOfInjective _ hinj (axisSpace X v)).finrank_eq).symm

private theorem exists_isRootElt_of_notMem {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    {q x : V} (hx : x ∉ axisSpace X q) : ∃ φ : Dual K V, IsRootElt X q φ ∧ φ x ≠ 0 := by
  by_contra h
  apply hx
  rw [mem_axisSpace_iff]
  intro φ hφ
  by_contra hφx
  exact h ⟨φ, hφ, hφx⟩

private theorem axisSpace_le_of_mem {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v w : V}
    (hw : w ∈ axisSpace X v) {ψ : Dual K V} (hψ : IsRootElt X w ψ) (hψv : ψ v ≠ 0) :
    axisSpace X w ≤ axisSpace X v := by
  intro x hx
  rw [mem_axisSpace_iff] at hx ⊢
  intro φ hφ
  exact hx φ (isRootElt_comm hψ hφ (mem_axisSpace_iff.mp hw φ hφ) hψv)

theorem notMem_axisSpace_of_finrank_le [FiniteDimensional K V]
    {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v w : V}
    (hdim : finrank K (axisSpace X v) ≤ finrank K (axisSpace X w)) (hvw : v ∉ axisSpace X w) :
    w ∉ axisSpace X v := by
  intro hwv
  obtain ⟨ψ, hψ, hψv⟩ := exists_isRootElt_of_notMem hvw
  have hle : axisSpace X w ≤ axisSpace X v := axisSpace_le_of_mem hwv hψ hψv
  have hvv : v ∈ axisSpace X v := mem_axisSpace_iff.mpr (fun φ hφ => hφ.1)
  have hne : axisSpace X w ≠ axisSpace X v := fun h => hvw (by rw [h]; exact hvv)
  have hlt : finrank K (axisSpace X w) < finrank K (axisSpace X v) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  omega

theorem exists_map_of_notMem_axisSpace {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    {v w : V} (hw : IsCentre X w) (hvw : v ∉ axisSpace X w) (hwv : w ∉ axisSpace X v) :
    ∃ g ∈ X, (g : V →ₗ[K] V) v = w := by
  obtain ⟨φ, hφ, hφw⟩ := exists_isRootElt_of_notMem hwv
  obtain ⟨ψ, hψ, hψv⟩ := exists_isRootElt_of_notMem hvw
  obtain ⟨g, hg, hgv, -⟩ := (opposite_sl2 hφ hψ hφw hψv).1 w
    (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton w))) hw.1
  exact ⟨g, hg, hgv⟩

theorem finrank_axisSpace_eq_of_notMem [FiniteDimensional K V]
    {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v w : V} (hw : IsCentre X w)
    (hdim : finrank K (axisSpace X v) ≤ finrank K (axisSpace X w)) (hvw : v ∉ axisSpace X w) :
    finrank K (axisSpace X v) = finrank K (axisSpace X w) := by
  obtain ⟨g, hg, hgv⟩ :=
    exists_map_of_notMem_axisSpace hw hvw (notMem_axisSpace_of_finrank_le hdim hvw)
  rw [← hgv, finrank_axisSpace_smul hg]

theorem exists_isRootElt_avoid {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {q p s : V}
    (hp : p ∉ axisSpace X q) (hs : s ∉ axisSpace X q) :
    ∃ φ : Dual K V, IsRootElt X q φ ∧ φ p ≠ 0 ∧ φ s ≠ 0 := by
  obtain ⟨φ₁, hφ₁, hφ₁p⟩ := exists_isRootElt_of_notMem hp
  obtain ⟨φ₂, hφ₂, hφ₂s⟩ := exists_isRootElt_of_notMem hs
  by_cases h1 : φ₁ s = 0
  · by_cases h2 : φ₂ p = 0
    · refine ⟨φ₁ + φ₂, (centreForms X q).add_mem hφ₁ hφ₂, ?_, ?_⟩
      · simpa [h2] using hφ₁p
      · simpa [h1] using hφ₂s
    · exact ⟨φ₂, hφ₂, h2, hφ₂s⟩
  · exact ⟨φ₁, hφ₁, hφ₁p, h1⟩

private theorem axisSpace_ne_top {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v : V}
    (hv : IsCentre X v) : axisSpace X v ≠ ⊤ := by
  obtain ⟨φ, hφ0, hφ⟩ := hv.2
  intro h
  apply hφ0
  ext x
  have hx : x ∈ axisSpace X v := by
    rw [h]
    exact Submodule.mem_top
  exact (mem_axisSpace_iff.mp hx) φ hφ

private theorem span_eq_top_of_irred {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hirr : Irred X) {S : Set V} (hS : ∀ g ∈ X, ∀ u ∈ S, (g : V →ₗ[K] V) u ∈ S)
    {u0 : V} (hu0 : u0 ∈ S) (hu0ne : u0 ≠ 0) : Submodule.span K S = ⊤ := by
  have hinv : ∀ g ∈ X, ∀ w ∈ Submodule.span K S,
      (g : V →ₗ[K] V) w ∈ Submodule.span K S := by
    intro g hg w hw
    have hle : Submodule.span K S ≤ (Submodule.span K S).comap (g : V →ₗ[K] V) := by
      rw [Submodule.span_le]
      intro u hu
      exact Submodule.mem_comap.mpr (Submodule.subset_span (hS g hg u hu))
    exact hle hw
  rcases hirr _ hinv with h | h
  · exfalso
    apply hu0ne
    have hmem : u0 ∈ Submodule.span K S := Submodule.subset_span hu0
    rw [h, Submodule.mem_bot] at hmem
    exact hmem
  · exact h

private theorem finrank_axisSpace_eq_of_isMin [FiniteDimensional K V]
    {X : Subgroup (LinearMap.GeneralLinearGroup K V)} (hirr : Irred X) {m : ℕ} {u0 : V}
    (hu0 : IsCentre X u0) (hu0d : finrank K (axisSpace X u0) = m)
    (hmin : ∀ u, IsCentre X u → m ≤ finrank K (axisSpace X u)) :
    ∀ x, IsCentre X x → finrank K (axisSpace X x) = m := by
  intro x hx
  by_contra hne
  have hlt : m < finrank K (axisSpace X x) := lt_of_le_of_ne (hmin x hx) (Ne.symm hne)
  have hsub : ∀ u ∈ {u : V | IsCentre X u ∧ finrank K (axisSpace X u) = m},
      u ∈ axisSpace X x := by
    rintro u ⟨-, hud⟩
    by_contra hux
    have hle : finrank K (axisSpace X u) ≤ finrank K (axisSpace X x) := by omega
    have hdim := finrank_axisSpace_eq_of_notMem hx hle hux
    omega
  have hinv : ∀ g ∈ X, ∀ u ∈ {u : V | IsCentre X u ∧ finrank K (axisSpace X u) = m},
      (g : V →ₗ[K] V) u ∈ {u : V | IsCentre X u ∧ finrank K (axisSpace X u) = m} := by
    rintro g hg u ⟨hu, hud⟩
    exact ⟨isCentre_smul hg hu, by rw [finrank_axisSpace_smul hg, hud]⟩
  have htop := span_eq_top_of_irred hirr hinv
    (show u0 ∈ {u : V | IsCentre X u ∧ finrank K (axisSpace X u) = m} from ⟨hu0, hu0d⟩) hu0.1
  have hle : (⊤ : Submodule K V) ≤ axisSpace X x := by
    rw [← htop]
    exact Submodule.span_le.mpr hsub
  exact axisSpace_ne_top hx (eq_top_iff.mpr hle)

theorem finrank_axisSpace_eq [FiniteDimensional K V]
    {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hirr : Irred X) {v w : V} (hv : IsCentre X v) (hw : IsCentre X w) :
    Module.finrank K (axisSpace X v) = Module.finrank K (axisSpace X w) := by
  classical
  have H : ∃ n, ∃ u : V, IsCentre X u ∧ finrank K (axisSpace X u) = n := ⟨_, v, hv, rfl⟩
  obtain ⟨u0, hu0, hu0d⟩ := Nat.find_spec H
  have hmin : ∀ u, IsCentre X u → Nat.find H ≤ finrank K (axisSpace X u) :=
    fun u hu => Nat.find_min' H ⟨u, hu, rfl⟩
  rw [finrank_axisSpace_eq_of_isMin hirr hu0 hu0d hmin v hv,
    finrank_axisSpace_eq_of_isMin hirr hu0 hu0d hmin w hw]

theorem mem_axisSpace_comm [FiniteDimensional K V] {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hirr : Irred X) {v w : V} (hv : IsCentre X v) (hw : IsCentre X w) :
    w ∈ axisSpace X v ↔ v ∈ axisSpace X w := by
  have hd := finrank_axisSpace_eq hirr hv hw
  constructor
  · intro hwv
    by_contra hvw
    exact notMem_axisSpace_of_finrank_le hd.le hvw hwv
  · intro hvw
    by_contra hwv
    exact notMem_axisSpace_of_finrank_le hd.ge hwv hvw

theorem exists_map_centre [FiniteDimensional K V] {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hirr : Irred X) {v w : V} (hv : IsCentre X v) (hw : IsCentre X w) :
    ∃ g ∈ X, ∃ c : K, (g : V →ₗ[K] V) v = c • w := by
  by_contra hno
  have hsub : ∀ u ∈ {u : V | ∃ h ∈ X, (h : V →ₗ[K] V) v = u}, u ∈ axisSpace X w := by
    rintro u ⟨h, hh, rfl⟩
    have hpc : IsCentre X ((h : V →ₗ[K] V) v) := isCentre_smul hh hv
    have hwp : w ∈ axisSpace X ((h : V →ₗ[K] V) v) := by
      by_contra hwp
      have hpw : (h : V →ₗ[K] V) v ∉ axisSpace X w := fun hmem =>
        hwp ((mem_axisSpace_comm hirr hpc hw).mpr hmem)
      obtain ⟨g, hg, hgp⟩ := exists_map_of_notMem_axisSpace hw hpw hwp
      exact hno ⟨g * h, X.mul_mem hg hh, 1,
        by rw [Units.val_mul, Module.End.mul_apply, hgp, one_smul]⟩
    exact (mem_axisSpace_comm hirr hpc hw).mp hwp
  have hinv : ∀ g ∈ X, ∀ u ∈ {u : V | ∃ h ∈ X, (h : V →ₗ[K] V) v = u},
      (g : V →ₗ[K] V) u ∈ {u : V | ∃ h ∈ X, (h : V →ₗ[K] V) v = u} := by
    rintro g hg u ⟨h, hh, rfl⟩
    exact ⟨g * h, X.mul_mem hg hh, by rw [Units.val_mul, Module.End.mul_apply]⟩
  have hv0 : v ∈ {u : V | ∃ h ∈ X, (h : V →ₗ[K] V) v = u} := ⟨1, X.one_mem, by simp⟩
  have htop := span_eq_top_of_irred hirr hinv hv0 hv.1
  have hle : (⊤ : Submodule K V) ≤ axisSpace X w := by
    rw [← htop]
    exact Submodule.span_le.mpr hsub
  exact axisSpace_ne_top hw (eq_top_iff.mpr hle)

end CFSG.ClassicalGroups.McLaughlin
