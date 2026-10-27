module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21Zt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9U

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc


section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

variable (Ω c) in
@[expose] noncomputable def coreLayer : Subgroup G := (coreHull Ω c).map (Subgroup.centralizer ({c} : Set G)).subtype

theorem coreLayer_le_centralizer : coreLayer Ω c ≤ Subgroup.centralizer ({c} : Set G) :=
  Subgroup.map_subtype_le _

theorem coreAt_le_coreLayer {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) :
    TwinADescent.coreAt c J ≤ coreLayer Ω c := by
  have := Subgroup.map_mono (f := (Subgroup.centralizer ({c} : Set G)).subtype) (le_coreHull hJ)
  rwa [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J)] at this

theorem coreLayer_le_of_forall {H : Subgroup G}
    (h : ∀ J ∈ tqMembers3 Ω c, TwinADescent.coreAt c J ≤ H) : coreLayer Ω c ≤ H := by
  unfold coreLayer coreHull
  rw [Subgroup.map_iSup]
  refine iSup_le fun L => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hL => ?_
  obtain ⟨_, ⟨J, hJ, rfl⟩, hLC, rfl⟩ := hL
  rw [Subgroup.map_subgroupOf_eq_of_le hLC]
  exact h J hJ

theorem conjSub_coreLayer (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {g : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) : conjSub g (coreLayer Ω c) = coreLayer Ω c := by
  have := conjSub_map (Subgroup.centralizer ({c} : Set G)).subtype
    (⟨g, hg⟩ : ↥(Subgroup.centralizer ({c} : Set G))) (coreHull Ω c)
  rw [conjSub_coreHull hΩ hc2] at this
  exact this

theorem oddCoreOf_coreLayer_le (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    oddCoreOf (coreLayer Ω c) ≤ oddCoreOf (Subgroup.centralizer ({c} : Set G)) :=
  oddCoreOf_le_of_normalizes coreLayer_le_centralizer fun g hg => conjSub_coreLayer hΩ hc2 hg

end Layer

section Frame

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem tz_facts (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) :
    (t * z) * (t * z) = 1 ∧ (t * z) * u = u * (t * z) := by
  have hzt : z * t = t * z := comm_zt hΩ hf
  refine ⟨?_, ?_⟩
  · calc (t * z) * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [hzt]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [hf.ht.sq, hf.hz.sq, one_mul]
  · calc (t * z) * u = t * (z * u) := by group
      _ = t * (u * z) := by rw [← u_comm_z hΩ hf]
      _ = (t * u) * z := by group
      _ = (u * t) * z := by rw [hf.htu]
      _ = u * (t * z) := by group

theorem alpha_u_tz (hs : AlphaSteps (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) :
    alphaOf (Subgroup.closure ({u, t * z} : Set Y)) =
      alphaOf (Subgroup.closure ({u, z} : Set Y)) := by
  have hΩ := hs.hyp
  have hzt : z * t = t * z := comm_zt hΩ hf
  obtain ⟨htz2, hutz⟩ := tz_facts hΩ hf
  have htz1 : t * z ≠ 1 := by
    intro e
    apply hf.t_ne_z
    have h2' : t = z⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [h2']; exact inv_eq_of_mul_eq_one_right hf.hz.sq
  have hne : u ≠ t * z := by
    intro h1
    apply Hat2A7S.twinFrame_t_not_mem_closure hΩ hf
    have hz' : z ∈ Subgroup.closure ({z, u} : Set Y) := Subgroup.subset_closure (by simp)
    have hu' : u ∈ Subgroup.closure ({z, u} : Set Y) := Subgroup.subset_closure (by simp)
    have : t = u * z := by
      calc t = (t * z) * z := by rw [mul_assoc, hf.hz.sq, mul_one]
        _ = u * z := by rw [← h1]
    rw [this]
    exact Subgroup.mul_mem _ hu' hz'
  have hA : IsElemAbelian2 (Subgroup.closure ({u, t * z} : Set Y)) 2 :=
    T7A.isElemAbelian2_closure_pair hf.hu2 htz2 hf.hu1 htz1 hne hutz.symm
  have hle : Subgroup.closure ({u, t * z} : Set Y) ≤ Subgroup.closure ({z, u, t} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  exact (hs.alpha_eq hf).2 _ hle hA

theorem oddCore_centralizer_u_comm_tz (hs : AlphaSteps (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥) {m : Y}
    (hm : m ∈ oddCoreOf (Subgroup.centralizer ({u} : Set Y))) : m * (t * z) = (t * z) * m := by
  have hA : alphaOf (Subgroup.closure ({u, t * z} : Set Y)) = ⊥ := by
    rw [alpha_u_tz hs hf]
    exact hα
  have huA : u ∈ Subgroup.closure ({u, t * z} : Set Y) := Subgroup.subset_closure (by simp)
  have htzA : t * z ∈ Subgroup.closure ({u, t * z} : Set Y) := Subgroup.subset_closure (by simp)
  exact T8.oddCoreOf_centralizer_commutes hA huA hf.hu1 htzA m hm

theorem coreLayer_le_normalizer_alpha_of_trivial
    (hs : AlphaSteps (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t)
    (hc2 : IsPGroup 2 (Subgroup.zpowers u)) {c₀ : Y} (hc₀ : c₀ = z ∨ c₀ = t * z)
    (htriv : ∀ y ∈ coreLayer (CoreAssembly.conjClass (tightCore R)) u,
      c₀ * y * c₀⁻¹ * y⁻¹ ∈ oddCoreOf (coreLayer (CoreAssembly.conjClass (tightCore R)) u)) :
    coreLayer (CoreAssembly.conjClass (tightCore R)) u ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨htz2, hutz⟩ := tz_facts hΩ hf
  have hc₀2 : c₀ * c₀ = 1 := by rcases hc₀ with rfl | rfl; exacts [hf.hz.sq, htz2]
  have hc₀u : c₀ * u = u * c₀ := by
    rcases hc₀ with rfl | rfl
    · exact (u_comm_z hΩ hf).symm
    · exact hutz
  have hα : alphaOf (Subgroup.closure ({u, c₀} : Set Y)) =
      alphaOf (Subgroup.closure ({u, z} : Set Y)) := by
    rcases hc₀ with rfl | rfl
    · rfl
    · exact alpha_u_tz hs hf
  have hcC : c₀ ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₀u
  have hcY : conjSub c₀ (coreLayer Ω u) = coreLayer Ω u := conjSub_coreLayer hΩ hc2 hcC
  have hOY : oddCoreOf (coreLayer Ω u) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) :=
    (oddCoreOf_coreLayer_le hΩ hc2).trans
      (oddCoreOf_centralizer_le_normalizer_alphaOf hf.hz.sq hf.hu1 (u_comm_z hΩ hf))
  intro y hy
  obtain ⟨m, hm, hmc⟩ := Q3T8.Asc77.exists_mem_oddCoreOf_centralizer_of_comm hc₀2 hcY htriv hy
  have hmY : m ∈ coreLayer Ω u := oddCoreOf_le_self _ hm
  have hmyY : m⁻¹ * y ∈ coreLayer Ω u := (coreLayer Ω u).mul_mem ((coreLayer Ω u).inv_mem hmY) hy
  have hmyC : m⁻¹ * y ∈ Subgroup.centralizer ({u} : Set Y) := coreLayer_le_centralizer hmyY
  have hle : Subgroup.closure ({u, c₀} : Set Y) ≤ Subgroup.centralizer ({m⁻¹ * y} : Set Y) := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hmyC).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hmc).symm
  have hxA : m⁻¹ * y ∈ Subgroup.centralizer
      ((Subgroup.closure ({u, c₀} : Set Y) : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hxN := centralizer_le_normalizer_alphaOf _ hxA
  rw [hα] at hxN
  have e : y = m * (m⁻¹ * y) := by group
  rw [e]
  exact Subgroup.mul_mem _ (hOY hm) hxN

theorem coreLayer_le_centralizer_of_trivial
    (hs : AlphaSteps (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t)
    (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥) {c₀ : Y} (hc₀ : c₀ = z ∨ c₀ = t * z)
    (htriv : ∀ y ∈ coreLayer (CoreAssembly.conjClass (tightCore R)) u,
      c₀ * y * c₀⁻¹ * y⁻¹ ∈ oddCoreOf (coreLayer (CoreAssembly.conjClass (tightCore R)) u)) :
    coreLayer (CoreAssembly.conjClass (tightCore R)) u ≤
      Subgroup.centralizer ({c₀} : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨htz2, hutz⟩ := tz_facts hΩ hf
  have hc₀2 : c₀ * c₀ = 1 := by rcases hc₀ with rfl | rfl; exacts [hf.hz.sq, htz2]
  have hc₀u : c₀ * u = u * c₀ := by
    rcases hc₀ with rfl | rfl
    · exact (u_comm_z hΩ hf).symm
    · exact hutz
  have hcC : c₀ ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₀u
  have hcY : conjSub c₀ (coreLayer Ω u) = coreLayer Ω u := conjSub_coreLayer hΩ hc2 hcC
  intro y hy
  obtain ⟨m, hm, hmc⟩ := Q3T8.Asc77.exists_mem_oddCoreOf_centralizer_of_comm hc₀2 hcY htriv hy
  have hmO : m ∈ oddCoreOf (Subgroup.centralizer ({u} : Set Y)) := oddCoreOf_coreLayer_le hΩ hc2 hm
  have hmC : m ∈ Subgroup.centralizer ({c₀} : Set Y) := by
    rcases hc₀ with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (oddCore_comm_of_alpha hα (Subgroup.subset_closure (by simp)) hf.hu1
          (Subgroup.subset_closure (by simp)) hmO)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (oddCore_centralizer_u_comm_tz hs hf hα hmO)
  have e : y = m * (m⁻¹ * y) := by group
  rw [e]
  exact (Subgroup.centralizer ({c₀} : Set Y)).mul_mem hmC hmc

end Frame

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
