module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec5_t_mem_centerIn [Finite G] (h52b : Asc82Lemma52b) {t : G} {L : Subgroup G}
    (h : Sec5Setting G t L) : t ∈ centerIn L := by
  obtain ⟨htL, -⟩ := h52b G t L h
  rw [sec5_mem_centerIn_iff]
  refine ⟨htL, fun y hy => ?_⟩
  have hyC : y ∈ centralizer ({t} : Set G) := h.component.le hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm

theorem sec5_t_not_conj_z [Finite G] (h37 : Asc82Lemma37) {t : G} {L S : Subgroup G} {z : G}
    (h : Sec5Ctx G t L S z) : ∀ g : G, g⁻¹ * z * g ≠ t := by
  intro g hg
  have hC : g⁻¹ * z * g ∈ centralizer ({t} : Set G) := by
    rw [hg]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbot := h37 G t L h.toSec3SettingLB z g h.pocket hC
  rw [hg] at hbot
  exact (sec5_layerCent_ne_bot_of_mem_centralizer h.component.isQuasisimple
    (sec4_t_mem_centralizer h.toSec3Setting)) (by unfold layerCent; exact hbot)

theorem sec5_inner_decomp [Finite G] (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b)
    (tab : Asc82Tab5) {t : G} {L : Subgroup G} (h : Sec5Setting G t L) {s : G}
    (hs2 : orderOf s = 2) (hsC : s ∈ centralizer ({t} : Set G)) (hk : Kind5 L s 0) : s ∈ L := by
  obtain ⟨l, hlL, c, hcC, hslc⟩ := innerOn_decompose hk.1
  have hsN : s ∈ normalizer (L : Set G) := by
    rw [hslc]
    exact (normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer hlL)
      (Subgroup.centralizer_le_normalizer (L : Set G) hcC)
  obtain ⟨w, hwL, hw2, hcCraw⟩ := tab.inner_lift G L h.isOm6Z2 s hs2 hsN hk
  set c' : G := w⁻¹ * s with hc'def
  have hcC : c' ∈ centralizer (L : Set G) := by rw [hc'def]; exact hcCraw
  have hwCt : w ∈ centralizer ({t} : Set G) := h.component.le hwL
  have hc'Ct : c' ∈ centralizer ({t} : Set G) := by
    rw [hc'def]
    exact mul_mem (inv_mem hwCt) hsC
  have hc't : c' * t = t * c' := Subgroup.mem_centralizer_singleton_iff.mp hc'Ct
  have hsc' : s = w * c' := by rw [hc'def]; group
  have hs1 : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hw1 : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
  have hcomm : w * c' = c' * w := Subgroup.mem_centralizer_iff.mp hcC w hwL
  have hc'1 : c' * c' = 1 := by
    have hss : s * s = c' * c' := by
      rw [hsc']
      calc (w * c') * (w * c') = w * (c' * w) * c' := by group
        _ = w * (w * c') * c' := by rw [hcomm.symm]
        _ = (w * w) * (c' * c') := by group
        _ = c' * c' := by rw [hw1, one_mul]
    rw [← hss]
    exact hs1
  have hct : c' = 1 ∨ c' = t :=
    sec4_eq_of_commute (h52a G t L h) hcC (sec4_t_mem_centralizer h.toSec3Setting) hc'1
      h.involution hc't
  rcases hct with h1 | h1
  · rw [h1, mul_one] at hsc'
    rw [hsc']
    exact hwL
  · rw [h1] at hsc'
    rw [hsc']
    exact mul_mem hwL (h52b G t L h).1

theorem sec5_pocket_class [Finite G] (h52b : Asc82Lemma52b) (tab : Asc82Tab5) {t : G}
    {L S : Subgroup G} {z : G} (h : Sec5Ctx G t L S z) {u : G} (hu : IsI4PlusIn L u) :
    u ∈ conjClassIn L z := by
  have hL : IsOm6Z2 L := h.toSec5Setting.isOm6Z2
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b h.toSec5Setting
  have hut : u ≠ t := by
    intro hut
    have huC : u ∈ centralizer (L : Set G) :=
      hut.symm ▸ sec4_t_mem_centralizer h.toSec3Setting
    exact (tab.pocket_kind G L hL u hu).2 huC
  rcases tab.inv_classes G L hL t htZ h.involution z h.pocket u hu.mem hu.1 hut with hzu | htz
  · exact hzu
  · exfalso
    obtain ⟨a, haL, hau⟩ := htz
    have h1 : IsI4PlusIn L (a⁻¹ * u * a) := by
      simpa using sec5_isI4PlusIn_conj hu (c := a⁻¹)
        (inv_mem (Subgroup.le_normalizer haL))
    have h2 : a⁻¹ * u * a = t * z := by rw [hau]; group
    exact (tab.tz_not_pocket G L hL t htZ h.involution z h.pocket) (h2 ▸ h1)

theorem sec5_nonpocket_class [Finite G] (h52b : Asc82Lemma52b) (tab : Asc82Tab5) {t : G}
    {L S : Subgroup G} {z : G} (h : Sec5Ctx G t L S z) {u : G} (huL : u ∈ L)
    (hu2 : orderOf u = 2) (hut : u ≠ t) (hnp : ¬ IsI4PlusIn L u) :
    u ∈ conjClassIn L (t * z) := by
  have hL : IsOm6Z2 L := h.toSec5Setting.isOm6Z2
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b h.toSec5Setting
  rcases tab.inv_classes G L hL t htZ h.involution z h.pocket u huL hu2 hut with hzu | htz
  · exfalso
    obtain ⟨a, haL, hau⟩ := hzu
    refine hnp ?_
    rw [hau]
    exact sec5_isI4PlusIn_conj h.pocket (Subgroup.le_normalizer haL)
  · exact htz

end CFSG.OddStandard.SmallF3.Omega
