module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OSteps

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

namespace E3S3O

section Gen

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem orbOf_conj (hc : ConjInvariant Ω) {K J : Subgroup G} (hK : K ∈ Ω) (g : G) :
    orbOf (TC.nbrAdj Ω) (conjSub g K) (conjSub g J) = conjSub g '' orbOf (TC.nbrAdj Ω) K J := by
  have hKg : conjSub g K ∈ Ω := hc g K hK
  have hgen : nbrGen (TC.nbrAdj Ω) (conjSub g K) = conjSub g (nbrGen (TC.nbrAdj Ω) K) := by
    rw [E3.nbrGen_eq_omegaNbrGen hKg, E3.nbrGen_eq_omegaNbrGen hK, E3.omegaNbrGen_conj hc]
  ext M
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [hgen, mem_conjSub_iff] at hl
    refine ⟨conjSub (g⁻¹ * l * g) J, ⟨_, hl, rfl⟩, ?_⟩
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨g * l * g⁻¹, ?_, ?_⟩
    · rw [hgen]
      exact conj_mem_conjSub hl
    · rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group

theorem conjSub_le_centralizer {H : Subgroup G} {u : G}
    (hH : H ≤ Subgroup.centralizer ({u} : Set G)) (g : G) :
    conjSub g H ≤ Subgroup.centralizer ({g * u * g⁻¹} : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hH hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * (g * u * g⁻¹) = g * ((g⁻¹ * x * g) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = g * u * g⁻¹ * x := by group

end Gen

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y}
  {R' T W : Subgroup Y}

namespace Ctx

variable (h : Ctx n R S t J u L Rd Sd S' R' T W)
include h

theorem fam_eq :
    CoreAssembly.conjClass (tightCore Rd) = CoreAssembly.conjClass (tightCore R) := by
  obtain ⟨g, hg⟩ := h.frame.maxAdj.1.2.1
  have hg' : conjSub g (tightCore R) = J := hg
  rw [h.core, ← hg', conjClass_conjSub]

theorem core_mem_nbr : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
  Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.frame.large.datum.hypOmegaGen h.frame.maxAdj.1.1
    h.frame.maxAdj.1.2.1 h.frame.maxAdj.1.2

theorem conjSub_J {c : Y} (hc : c ∈ Subgroup.centralizer ({u} : Set Y)) : conjSub c J = J := by
  have h1 := h.std.large.datum.le_normalizer_core hc
  rw [h.core] at h1
  exact mem_normalizer_iff_conjSub_eq.mp h1

theorem L_mem_nbr : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
  obtain ⟨l, hl, rfl⟩ := h.pi
  have h1 := omegaNbr_conj h.frame.large.datum.hypOmegaGen.conjInvariant h.core_mem_nbr l
  rwa [h.conjSub_J (h.frame.nbrGen_le_centralizer hl)] at h1

theorem exists_conj :
    ∃ g : Y, conjSub g (tightCore R) = J ∧ conjSub g J = L ∧ g * t * g⁻¹ = u := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := h.frame.large.datum
  have hc : ConjInvariant Ω := hd.hypOmegaGen.conjInvariant
  have hJn : J ∈ omegaNbr Ω (tightCore R) := h.frame.maxAdj.1.2
  set X := nbrGen (TC.nbrAdj Ω) J with hXdef
  have hXC : X ≤ Subgroup.centralizer ({u} : Set Y) := h.frame.nbrGen_le_centralizer
  obtain ⟨g₀, hg₀'⟩ := hJn.1
  have hg₀ : conjSub g₀ (tightCore R) = J := hg₀'
  have hJ₁ : conjSub g₀ J ∈ omegaNbr Ω J := by
    have h1 := omegaNbr_conj hc hJn g₀
    rwa [hg₀] at h1
  obtain ⟨l₁, hl₁, hl₁J⟩ := h.orbit hJ₁
  obtain ⟨l, hl, hlL⟩ := h.pi
  have hm : l * l₁⁻¹ ∈ X := X.mul_mem hl (X.inv_mem hl₁)
  have hgK : conjSub (l * l₁⁻¹ * g₀) (tightCore R) = J := by
    rw [conjSub_mul, hg₀, h.conjSub_J (hXC hm)]
  refine ⟨l * l₁⁻¹ * g₀, hgK, ?_, ?_⟩
  · rw [conjSub_mul, conjSub_mul, ← hl₁J, conjSub_inv_conjSub, hlL]
  · have h1 := hd.isUniqueInvolution_core.conj (l * l₁⁻¹ * g₀)
    rw [hgK] at h1
    exact h1.eq h.frame.inv

theorem le_centralizer_of_mem {s : Y} (hs : IsUniqueInvolution L s) {M : Subgroup Y}
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L) :
    M ≤ Subgroup.centralizer ({s} : Set Y) := by
  have hc := h.frame.large.datum.hypOmegaGen.conjInvariant
  obtain ⟨g, -, hgJ, -⟩ := h.exists_conj
  have hM' : conjSub g⁻¹ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
    have h1 := omegaNbr_conj hc hM g⁻¹
    rwa [← hgJ, conjSub_inv_conjSub] at h1
  have hus : g * u * g⁻¹ = s := by
    have h1 := h.frame.inv.conj g
    rw [hgJ] at h1
    exact h1.eq hs
  have h2 := conjSub_le_centralizer (h.frame.nbr_le_centralizer hM') g
  rwa [conjSub_conjSub_inv, hus] at h2

theorem J_mem_nbr : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L := by
  obtain ⟨g, hgK, hgJ, -⟩ := h.exists_conj
  have h1 := omegaNbr_conj h.frame.large.datum.hypOmegaGen.conjInvariant h.core_mem_nbr g
  rwa [hgK, hgJ] at h1

theorem mem_orbOf_of_mem {M : Subgroup Y}
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L) :
    M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L J := by
  have hc := h.frame.large.datum.hypOmegaGen.conjInvariant
  obtain ⟨g, hgK, hgJ, -⟩ := h.exists_conj
  have hM' : conjSub g⁻¹ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
    have h1 := omegaNbr_conj hc hM g⁻¹
    rwa [← hgJ, conjSub_inv_conjSub] at h1
  have e := orbOf_conj hc h.frame.maxAdj.1.2.1 (J := tightCore R) g
  rw [hgJ, hgK] at e
  rw [e]
  exact ⟨_, h.orbit hM', conjSub_conjSub_inv g M⟩

theorem mem_omegaNbr_of_mem_orbOf {M : Subgroup Y}
    (hM : M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L J) :
    M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L := by
  have hc := h.frame.large.datum.hypOmegaGen.conjInvariant
  obtain ⟨g, hgK, hgJ, -⟩ := h.exists_conj
  have e := orbOf_conj hc h.frame.maxAdj.1.2.1 (J := tightCore R) g
  rw [hgJ, hgK] at e
  rw [e] at hM
  obtain ⟨_, ⟨l, hl, rfl⟩, rfl⟩ := hM
  have h1 := omegaNbr_conj hc h.core_mem_nbr l
  rw [h.conjSub_J (h.frame.nbrGen_le_centralizer hl)] at h1
  have h2 := omegaNbr_conj hc h1 g
  rwa [hgJ] at h2

theorem mem_centralizer_u {s : Y} (hs : IsUniqueInvolution L s) :
    s ∈ Subgroup.centralizer ({u} : Set Y) :=
  h.frame.nbr_le_centralizer h.L_mem_nbr hs.mem

theorem mem_normalizer_core {s : Y} (hs : IsUniqueInvolution L s) :
    s ∈ Subgroup.normalizer (tightCore R : Set Y) := by
  have hΩG := h.frame.large.datum.hypOmegaGen
  obtain ⟨-, -, U, hU, hUL, hUN⟩ := h.star
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩG hU
  exact hUN (T3.mem_of_isPGroup hs hUL (Sec6Gen.isPGroup_of_mem_USet hΩG hU)
    (le_trans (by norm_num) hU4))

theorem mem_centralizer_a {s : Y} (hs : IsUniqueInvolution L s) :
    s ∈ Subgroup.centralizer ({u * t} : Set Y) := by
  have hsu := Subgroup.mem_centralizer_singleton_iff.mp (h.mem_centralizer_u hs)
  have hst : s * t * s⁻¹ = t :=
    h.frame.large.datum.isUniqueInvolution_core.conj_eq
      (mem_normalizer_iff_conjSub_eq.mp (h.mem_normalizer_core hs))
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc s * (u * t) = (s * u) * t := by group
    _ = (u * s) * t := by rw [hsu]
    _ = u * (s * t * s⁻¹) * s := by group
    _ = u * t * s := by rw [hst]

theorem not_xMem : ¬ XMem (CoreAssembly.conjClass (tightCore Rd)) (u * t) L := by
  rintro ⟨-, -, P, hP, hPx⟩
  apply h.notNbr
  have hLΩ := h.star.1
  have hLC := h.frame.nbr_le_centralizer h.L_mem_nbr
  refine ⟨hLΩ, h.star.2.1, P, mem_RSet_of_isSylow2In hLΩ hP, hP.1, fun p hp => ?_⟩
  have hpu := Subgroup.mem_centralizer_singleton_iff.mp (hLC (hP.1 hp))
  have hpa := hPx p hp
  have hpt : p * t = t * p := by
    have e : u * (p * t) = u * (t * p) := by
      calc u * (p * t) = (u * p) * t := by group
        _ = (p * u) * t := by rw [hpu]
        _ = p * (u * t) := by group
        _ = (u * t) * p := hpa
        _ = u * (t * p) := by group
    exact mul_left_cancel e
  exact h.frame.large.datum.le_normalizer_core (Subgroup.mem_centralizer_singleton_iff.mpr hpt)

end Ctx

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
