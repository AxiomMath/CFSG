module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf4Twin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem X_le_cent : piGen π ≤ Subgroup.centralizer ({z} : Set G) :=
  S.hos.piGen_le_centralizer S.hπ S.hz

theorem trans_pi : ∀ J₁ ∈ π, ∀ J₂ ∈ π, ∃ x ∈ piGen π, conjSub x J₁ = J₂ :=
  transitive_of_maxOrb S.hos.graph S.hπ

theorem conj_pi_of_cent {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {J : Subgroup G}
    (hJ : J ∈ π) : conjSub c J ∈ π := by
  have := S.hos.conj_image_eq_of_centralizer S.hK S.hπ S.hH1 S.hz hc
  rw [← this]
  exact ⟨J, hJ, rfl⟩

theorem Q_eq_pi : conjSub g⁻¹ '' fam K (conjSub g (piGen π)) = π := by
  ext J
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    have ha : (a : G) ∈ conjSub g (piGen π) := a.2
    have hx : g⁻¹ * (a : G) * g ∈ piGen π := by
      have := mem_conjSub_iff.mp ha
      simpa using this
    have h : conjSub g⁻¹ (conjSub (a : G) K) = conjSub (g⁻¹ * (a : G) * g) (conjSub g⁻¹ K) := by
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    rw [h]
    exact stable_of_maxOrb S.hos.graph S.hπ _ hx _ S.conj_inv_mem
  · exact fun hJ => S.mem_Q_of_mem_pi hJ

theorem frattini {W : Subgroup G} (hWX : ∀ x ∈ piGen π, ∀ w ∈ W, x * w = w * x)
    (hW2 : ∀ c ∈ Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({g * z * g⁻¹} : Set G), ∀ w ∈ W, c * w * c⁻¹ ∈ W) :
    ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
  intro c hc w hw
  have hJ' : conjSub c (conjSub g K) ∈ π := S.conj_pi_of_cent hc S.hg
  obtain ⟨x, hx, hxJ⟩ := S.trans_pi _ hJ' _ S.hg
  rw [← conjSub_mul] at hxJ
  have hxc : x ∈ Subgroup.centralizer ({z} : Set G) := S.X_le_cent hx
  have hd : x * c ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ hxc hc
  have hu : (x * c) * (g * z * g⁻¹) * (x * c)⁻¹ = g * z * g⁻¹ := by
    have h1 := (S.hz.conj g).conj (x * c)
    rw [hxJ] at h1
    exact ((S.hz.conj g).eq h1).symm
  have hd2 : x * c ∈ Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
    refine ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have : (x * c) * (g * z * g⁻¹) = (g * z * g⁻¹) * (x * c) := by
      calc (x * c) * (g * z * g⁻¹) = ((x * c) * (g * z * g⁻¹) * (x * c)⁻¹) * (x * c) := by group
        _ = (g * z * g⁻¹) * (x * c) := by rw [hu]
    exact this
  have hw' := hW2 _ hd2 w hw
  have hcom := hWX x⁻¹ ((piGen π).inv_mem hx) _ hw'
  have heq : c * w * c⁻¹ = (x * c) * w * (x * c)⁻¹ := by
    calc c * w * c⁻¹ = x⁻¹ * ((x * c) * w * (x * c)⁻¹) * x := by group
      _ = (x⁻¹ * ((x * c) * w * (x * c)⁻¹)) * x := by group
      _ = (((x * c) * w * (x * c)⁻¹) * x⁻¹) * x := by rw [hcom]
      _ = (x * c) * w * (x * c)⁻¹ := by group
  rw [heq]
  exact hw'

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
