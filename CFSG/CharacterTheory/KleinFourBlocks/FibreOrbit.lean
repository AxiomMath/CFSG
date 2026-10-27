module

public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport

public section

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Semidihedral.Principal.FreeSix

open scoped Classical

namespace CFSG.KleinFourBlocks

variable {G : Type*} [Group G]

@[expose] def fOrbit (V : Subgroup G) (f₀ : G → ℂ) : Set (G → ℂ) :=
  {f | ∃ m ∈ mV V, ∀ g, f g = f₀ (m⁻¹ * g * m)}

@[expose] def kOrbit (V : Subgroup G) (t : G) (f₀ : G → ℂ) : Set (G → ℂ) :=
  {f | ∃ k ∈ cT t ⊓ mV V, ∀ g, f g = f₀ (k⁻¹ * g * k)}

@[expose] def gOrbit (X : Set G) (f₀ : G → ℂ) : Set (G → ℂ) :=
  {f | ∃ k ∈ X, ∀ g, f g = f₀ (k⁻¹ * g * k)}

structure FreeBlockData (V : Subgroup G) (f₀ : G → ℂ) : Prop where
  supp : ∀ g, g ∉ dV V → f₀ g = 0
  cls : ∀ d ∈ dV V, ∀ g, f₀ (d⁻¹ * g * d) = f₀ g
  transV : ∀ v ∈ V, ∀ g, f₀ (v * g) = f₀ g
  stab : ∀ m ∈ mV V, (∀ g, f₀ (m⁻¹ * g * m) = f₀ g) → m ∈ dV V

theorem inv_conj_mem_V {V : Subgroup G} {m : G} (hm : m ∈ mV V) {v : G} (hv : v ∈ V) :
    m⁻¹ * v * m ∈ V := by
  have h' := (Subgroup.mem_normalizer_iff.mp ((mV V).inv_mem hm) v).mp hv
  rwa [inv_inv] at h'

theorem inv_conj_mem_dV {V : Subgroup G} {m : G} (hm : m ∈ mV V) {d : G} (hd : d ∈ dV V) :
    m⁻¹ * d * m ∈ dV V := by
  have h := (centralizer_conjugation_mem_iff V m⁻¹ d ((mV V).inv_mem hm)).mpr hd
  rwa [inv_inv] at h

theorem conj_mem_dV_iff {V : Subgroup G} {m : G} (hm : m ∈ mV V) {d : G} :
    m * d * m⁻¹ ∈ dV V ↔ d ∈ dV V :=
  centralizer_conjugation_mem_iff V m d hm

theorem fOrbit_self_mem (V : Subgroup G) (f₀ : G → ℂ) : f₀ ∈ fOrbit V f₀ :=
  ⟨1, (mV V).one_mem, fun g => by simp⟩

theorem fOrbit_smul_mem {V : Subgroup G} {f₀ : G → ℂ} {f : G → ℂ} (hf : f ∈ fOrbit V f₀) {k : G} (hk : k ∈ mV V) :
    (fun g => f (k⁻¹ * g * k)) ∈ fOrbit V f₀ := by
  obtain ⟨m, hm, hfm⟩ := hf
  refine ⟨k * m, (mV V).mul_mem hk hm, fun g => ?_⟩
  show f (k⁻¹ * g * k) = _
  rw [hfm]
  congr 1
  group

theorem kOrbit_subset_fOrbit {V : Subgroup G} {f₀ : G → ℂ} {f : G → ℂ} (hf : f ∈ fOrbit V f₀) (t : G) :
    kOrbit V t f ⊆ fOrbit V f₀ := by
  rintro f' ⟨k, hk, hf'⟩
  have : f' = fun g => f (k⁻¹ * g * k) := funext hf'
  rw [this]
  exact fOrbit_smul_mem hf hk.2

namespace FreeBlockData

variable {V : Subgroup G} {f₀ : G → ℂ} (h : FreeBlockData V f₀)
include h

theorem cls_orbit {f : G → ℂ} (hf : f ∈ fOrbit V f₀) :
    ∀ d ∈ dV V, ∀ g, f (d⁻¹ * g * d) = f g := by
  obtain ⟨m, hm, hfm⟩ := hf
  intro d hd g
  rw [hfm, hfm]
  have hd' : m⁻¹ * d * m ∈ dV V := inv_conj_mem_dV hm hd
  have e : m⁻¹ * (d⁻¹ * g * d) * m = (m⁻¹ * d * m)⁻¹ * (m⁻¹ * g * m) * (m⁻¹ * d * m) := by group
  rw [e]
  exact h.cls _ hd' _

theorem supp_orbit {f : G → ℂ} (hf : f ∈ fOrbit V f₀) : ∀ g, g ∉ dV V → f g = 0 := by
  obtain ⟨m, hm, hfm⟩ := hf
  intro g hg
  rw [hfm]
  apply h.supp
  intro hmem
  apply hg
  have := (conj_mem_dV_iff hm).mpr hmem
  rwa [show m * (m⁻¹ * g * m) * m⁻¹ = g by group] at this

theorem transV_orbit {f : G → ℂ} (hf : f ∈ fOrbit V f₀) :
    ∀ v ∈ V, ∀ g, f (v * g) = f g := by
  obtain ⟨m, hm, hfm⟩ := hf
  intro v hv g
  rw [hfm, hfm]
  have hv' : m⁻¹ * v * m ∈ V := inv_conj_mem_V hm hv
  have e : m⁻¹ * (v * g) * m = (m⁻¹ * v * m) * (m⁻¹ * g * m) := by group
  rw [e]
  exact h.transV _ hv' _

theorem stab_orbit {f : G → ℂ} (hf : f ∈ fOrbit V f₀) {m : G} (hm : m ∈ mV V)
    (hfix : ∀ g, f (m⁻¹ * g * m) = f g) : m ∈ dV V := by
  obtain ⟨m₀, hm₀, hfm⟩ := hf
  have hk : m₀⁻¹ * m * m₀ ∈ mV V :=
    (mV V).mul_mem ((mV V).mul_mem ((mV V).inv_mem hm₀) hm) hm₀
  have hkfix : ∀ g, f₀ ((m₀⁻¹ * m * m₀)⁻¹ * g * (m₀⁻¹ * m * m₀)) = f₀ g := by
    intro g
    have := hfix (m₀ * g * m₀⁻¹)
    rw [hfm, hfm] at this
    have e1 : m₀⁻¹ * (m⁻¹ * (m₀ * g * m₀⁻¹) * m) * m₀ =
        (m₀⁻¹ * m * m₀)⁻¹ * g * (m₀⁻¹ * m * m₀) := by group
    have e2 : m₀⁻¹ * (m₀ * g * m₀⁻¹) * m₀ = g := by group
    rw [e1, e2] at this
    exact this
  have hkD : m₀⁻¹ * m * m₀ ∈ dV V := h.stab _ hk hkfix
  have h2 := (conj_mem_dV_iff hm₀).mpr hkD
  rwa [show m₀ * (m₀⁻¹ * m * m₀) * m₀⁻¹ = m by group] at h2

end FreeBlockData

@[expose, instance_reducible] def funAction (V : Subgroup G) : MulAction (mV V) (G → ℂ) where
  smul m f := fun g => f ((m : G)⁻¹ * g * m)
  one_smul f := funext fun g => by
    change f (((1 : mV V) : G)⁻¹ * g * ((1 : mV V) : G)) = f g
    simp
  mul_smul m₁ m₂ f := funext fun g => by
    change f (((m₁ * m₂ : mV V) : G)⁻¹ * g * ((m₁ * m₂ : mV V) : G)) =
      f ((m₂ : G)⁻¹ * ((m₁ : G)⁻¹ * g * (m₁ : G)) * (m₂ : G))
    congr 1
    simp only [Subgroup.coe_mul]
    group

theorem fOrbit_eq_orbit (V : Subgroup G) (f₀ : G → ℂ) :
    letI := funAction V
    fOrbit V f₀ = MulAction.orbit (mV V) f₀ := by
  let := funAction V
  ext f
  constructor
  · rintro ⟨m, hm, hf⟩
    exact ⟨⟨m, hm⟩, funext fun g => (hf g).symm⟩
  · rintro ⟨⟨m, hm⟩, rfl⟩
    exact ⟨m, hm, fun g => rfl⟩

theorem kOrbit_eq_orbit (V : Subgroup G) (t : G) (f₀ : G → ℂ) :
    letI := funAction V
    kOrbit V t f₀ = MulAction.orbit ((cT t).subgroupOf (mV V)) f₀ := by
  let := funAction V
  ext f
  constructor
  · rintro ⟨k, hk, hf⟩
    exact ⟨⟨⟨k, hk.2⟩, hk.1⟩, funext fun g => (hf g).symm⟩
  · rintro ⟨⟨⟨k, hkM⟩, hkC⟩, rfl⟩
    exact ⟨k, ⟨hkC, hkM⟩, fun g => rfl⟩

section Structure

variable [Finite G] {V : Subgroup G} {f₀ : G → ℂ}

theorem orbit_structure_fun (hV : IsKleinFour V)
    (hAut : Function.Surjective V.normalizerMonoidHom) {t : G} (htV : t ∈ V) (ht1 : t ≠ 1)
    (h : FreeBlockData V f₀) :
    (fOrbit V f₀).ncard = 6 ∧
    ∃ fs : Fin 3 → (G → ℂ), (∀ j, fs j ∈ fOrbit V f₀) ∧
      (∀ j, (kOrbit V t (fs j)).ncard = 2) ∧
      (∀ j k, j ≠ k → Disjoint (kOrbit V t (fs j)) (kOrbit V t (fs k))) ∧
      fOrbit V f₀ = ⋃ j, kOrbit V t (fs j) := by
  let := funAction V
  set L : Subgroup (mV V) := (cT t).subgroupOf (mV V) with hLdef
  have hΩ : fOrbit V f₀ = MulAction.orbit (mV V) f₀ := fOrbit_eq_orbit V f₀
  have hLorbit : ∀ f, kOrbit V t f = MulAction.orbit L f := fun f => kOrbit_eq_orbit V t f
  have hstab : ∀ f ∈ MulAction.orbit (mV V) f₀,
      MulAction.stabilizer (mV V) f = (dV V).subgroupOf (mV V) := by
    intro f hf
    have hf' : f ∈ fOrbit V f₀ := hΩ ▸ hf
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hm
      exact h.stab_orbit hf' m.2 fun g => (congrFun hm g : f _ = f g)
    · intro hm
      funext g
      exact h.cls_orbit hf' _ hm g
  have hcard : (MulAction.orbit (mV V) f₀).ncard = 6 := by
    rw [← MulAction.index_stabilizer, hstab f₀ (MulAction.mem_orbit_self _), index_dV hV hAut]
  have hL2 : ∀ f ∈ MulAction.orbit (mV V) f₀, (MulAction.orbit L f).ncard = 2 := by
    intro f hf
    rw [← MulAction.index_stabilizer]
    have hLstab : MulAction.stabilizer L f = (MulAction.stabilizer (mV V) f).subgroupOf L := by
      ext l
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
      rfl
    rw [hLstab, hstab f hf]
    exact relIndex_dV_cT hV hAut htV ht1
  have hfin : (MulAction.orbit (mV V) f₀).Finite := Set.finite_range _
  obtain ⟨x, hxΩ, hdisj, hunion⟩ := exists_three_orbits (K := L) (MulAction.orbit (mV V) f₀)
    hcard hfin (fun l f hf => by
      obtain ⟨m, rfl⟩ := hf
      exact ⟨(l : mV V) * m, mul_smul (l : mV V) m f₀⟩) hL2
  refine ⟨hΩ ▸ hcard, x, fun j => hΩ ▸ hxΩ j, fun j => (hLorbit (x j)).symm ▸ hL2 (x j) (hxΩ j),
    fun j k hjk => ?_, ?_⟩
  · rw [hLorbit, hLorbit]
    exact hdisj j k hjk
  · rw [hΩ, hunion]
    exact Set.iUnion_congr fun j => (hLorbit (x j)).symm

end Structure

end CFSG.KleinFourBlocks
