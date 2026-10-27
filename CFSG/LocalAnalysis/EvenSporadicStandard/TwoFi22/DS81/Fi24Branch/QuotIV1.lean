module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotKc
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotR
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Shape54Good
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C] [Finite C] {c : CInv C} {t : C} {R J : Subgroup C}
  {L1 : Subgroup c.Qt}

theorem zpowers_le_J (hR : RData c R) (hJ : JData c t R J) : zpowers c.z ≤ J := by
  exact Subgroup.zpowers_le.mpr (hJ.R_le hR.z_mem)

theorem qmap_t_mem (hJ : JData c t R J) (h : UniqueComp c R L1) : c.qmap t ∈ L1 := by
  apply h.R_le
  change c.qmap t ∈ R.map c.qmap
  exact Subgroup.mem_map.mpr ⟨t, hJ.t_mem, rfl⟩

theorem orderOf_qmap_t (hJ : JData c t R J) : orderOf (c.qmap t) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, hJ.t_sq, map_one]
  · intro h
    exact hJ.t_not (c.qmap_eq_one_iff.mp h)

theorem centralizer_qmap_t (hR : RData c R) (hJ : JData c t R J) :
    centralizer ({c.qmap t} : Set c.Qt) = c.bar J := by
  apply le_antisymm
  · intro g hg
    obtain ⟨g0, rfl⟩ := c.qmap_surjective g
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    change c.qmap g0 ∈ J.map c.qmap
    refine Subgroup.mem_map.mpr ⟨g0, ?_, rfl⟩
    apply (hJ.mem_iff g0).mpr
    have h1 : c.qmap (g0 * t * g0⁻¹ * t⁻¹) = 1 := by
      rw [show c.qmap (g0 * t * g0⁻¹ * t⁻¹) =
        c.qmap g0 * c.qmap t * (c.qmap g0)⁻¹ * (c.qmap t)⁻¹ by
          simp only [map_mul, map_inv]]
      rw [hg]
      group
    exact c.qmap_eq_one_iff.mp h1
  · intro g hg
    change g ∈ J.map c.qmap at hg
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c.qmap (j * t * j⁻¹ * t⁻¹) = 1 :=
      c.qmap_eq_one_iff.mpr ((hJ.mem_iff j).mp hj)
    have h2 : c.qmap j * c.qmap t * (c.qmap j)⁻¹ * (c.qmap t)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    exact mul_inv_eq_one.mp (by simpa only [mul_assoc, mul_inv_rev] using h2)

theorem O2In_eq_bar_R (hR : RData c R) (hJ : JData c t R J) (h : UniqueComp c R L1) :
    TwoFi22.O2In (L1 ⊓ centralizer ({c.qmap t} : Set c.Qt)) = c.bar R := by
  rw [centralizer_qmap_t hR hJ]
  apply le_antisymm
  ·
    intro x hx
    set W : Subgroup C := Subgroup.comap (G := C) (N := c.Qt) c.qmap
        (TwoFi22.O2In (L1 ⊓ c.bar J)) with hW
    have hW_le_R : W ≤ R := by
      refine hJ.two W ?_ ?_ ?_
      · intro y hy
        rw [hW, Subgroup.mem_comap] at hy
        exact (c.qmap_mem_bar_iff (zpowers_le_J hR hJ)).mp (TwoB.O2In_le _ hy).2
      · intro j hj w hw
        rw [hW, Subgroup.mem_comap] at hw ⊢
        have hjbar : c.qmap j ∈ c.bar J := Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
        have hn : ∀ k ∈ (L1 ⊓ c.bar J),
            c.qmap j * k * (c.qmap j)⁻¹ ∈ (L1 ⊓ c.bar J) := by
          intro k hk
          refine ⟨(L1_normal h).conj_mem k hk.1 (c.qmap j), ?_⟩
          exact (c.bar J).mul_mem ((c.bar J).mul_mem hjbar hk.2) ((c.bar J).inv_mem hjbar)
        have hn' : ∀ k ∈ (L1 ⊓ c.bar J),
            (c.qmap j)⁻¹ * k * c.qmap j ∈ (L1 ⊓ c.bar J) := by
          intro k hk
          refine ⟨(L1_normal h).conj_mem' k hk.1 (c.qmap j), ?_⟩
          exact (c.bar J).mul_mem ((c.bar J).mul_mem ((c.bar J).inv_mem hjbar) hk.2) hjbar
        have hconj := TwoB.conj_mem_O2In_of_conj_mem hn hn' (c.qmap w) hw
        simpa only [map_mul, map_inv] using hconj
      · exact c.isPGroup_comap (TwoB.isPGroup_O2In (L1 ⊓ c.bar J))
    have hxW : x ∈ c.bar W := by
      rw [hW, c.bar_comap]
      exact hx
    exact c.bar_mono hW_le_R hxW
  ·
    apply TwoB.le_O2In
    · exact le_inf h.R_le (c.bar_mono hJ.R_le)
    · refine ⟨fun m hm g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      change (m : c.Qt) ∈ R.map c.qmap at hm
      change ((g : c.Qt) * (m : c.Qt) * (g : c.Qt)⁻¹) ∈ R.map c.qmap
      obtain ⟨r, hr, hrm⟩ := Subgroup.mem_map.mp hm
      have hgJ : (g : c.Qt) ∈ J.map c.qmap := g.2.2
      obtain ⟨j, hj, hjg⟩ := Subgroup.mem_map.mp hgJ
      rw [← hrm, ← hjg]
      refine Subgroup.mem_map.mpr ⟨j * r * j⁻¹, hJ.R_normal j hj r hr, ?_⟩
      simp only [map_mul, map_inv]
    · exact bar_R_isPGroup hR

theorem card_O2In (hR : RData c R) (hJ : JData c t R J) (h : UniqueComp c R L1) :
    Nat.card ↥(TwoFi22.O2In (L1 ⊓ centralizer ({c.qmap t} : Set c.Qt))) = 2 ^ 12 := by
  rw [O2In_eq_bar_R hR hJ h]
  exact bar_R_card hR

theorem sq_O2In (hR : RData c R) (hJ : JData c t R J) (h : UniqueComp c R L1) :
    ∀ a ∈ TwoFi22.O2In (L1 ⊓ centralizer ({c.qmap t} : Set c.Qt)), a ^ 2 = 1 := by
  intro a ha
  rw [O2In_eq_bar_R hR hJ h] at ha
  exact bar_R_sq hR a ha

theorem cent_O2In (hR : RData c R) (hJ : JData c t R J) (h : UniqueComp c R L1) :
    L1 ⊓ centralizer ({c.qmap t} : Set c.Qt) ⊓
        centralizer (TwoFi22.O2In (L1 ⊓ centralizer ({c.qmap t} : Set c.Qt)) : Set c.Qt) ≤
      TwoFi22.O2In (L1 ⊓ centralizer ({c.qmap t} : Set c.Qt)) := by
  rw [O2In_eq_bar_R hR hJ h]
  intro g hg
  exact bar_R_cent hR hg.2

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
