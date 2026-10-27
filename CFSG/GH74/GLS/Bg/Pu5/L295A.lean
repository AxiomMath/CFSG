module

public import CFSG.GH74.GLS.Bg.Pu5.L295Basic
public import CFSG.GH74.GLS.Bg.Pu5.L295ADiag
public import CFSG.GH74.GLS.Bg.Pu5.L293Step0
public import CFSG.GH74.GLS.Bg.Pu5.BalStatements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G]

theorem cmap_one_self (L : Subgroup G) : cmap 1 L = L := by
  ext x
  simp

variable [Finite G]

theorem rigid_normalizes_or_swaps (hquat : II4_4_quat) (hG : IsKProperSimple G) (hgen : Gen4 G) {t : G}
    (ht : orderOf t = 2) {L L' : Subgroup G} (hL : IsRigidRankOneComp t L)
    (hL' : IsRigidRankOneComp t L') (hne : L ≠ L') {g : G} (hg : g ∈ centralizer ({t} : Set G)) :
    g ∈ normalizer (L : Set G) ∨ cmap g L = L' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hgL, hgL'⟩ := hcon
  have hle := rr_ncard_le_two hquat hG hgen ht
  have hgc : IsRigidRankOneComp t (cmap g L) := isRigidRankOneComp_cmap hL hg
  have h1 : L ≠ cmap g L := fun h =>
    hgL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have h2 : L' ≠ cmap g L := fun h => hgL' h.symm
  have h3 := (Set.two_lt_ncard_iff (Set.toFinite {K : Subgroup G | IsRigidRankOneComp t K})).2
    ⟨L, L', cmap g L, hL, hL', hgc, hne, h1, h2⟩
  omega

theorem l295a_step (hP0 : P0S) (hDL : DiagLayerS) (hBL0 : BL0S) (h293 : L293) {z t : G}
    {S K U : Subgroup G} (h : Cfg295 G z t S K U) {L : Subgroup G} (hL : IsRigidRankOneComp t L)
    {v : G} (hvU : v ∈ U) (hv2 : orderOf v = 2) (hvL : v ∉ normalizer (L : Set G)) {g : G}
    (hgU : g ∈ U) (hg1 : g ≠ 1) (hgL : g ∈ normalizer (L : Set G)) (hgz : g = z ∨ g = z * v) :
    False := by
  have hG := h.cfg.simple
  have ht2 : orderOf t = 2 := h.cfg.t_orderOf
  have hvt : v ∈ centralizer ({t} : Set G) := h.mem_cent_t hvU
  have hg2 : orderOf g = 2 := h.hU.orderOf_eq_two hgU hg1
  obtain ⟨Λ, -, hΛc, -, hcov, -, -⟩ := hDL G hG t v ht2 hv2 hvt L hL hvL
  have hΛle : Λ ≤ centralizer ({t} : Set G) ⊓ centralizer ({v} : Set G) := hΛc.1
  have hΛt : Λ ≤ centralizer ({t} : Set G) := hΛle.trans inf_le_left
  have hzv : z ∈ centralizer ({v} : Set G) := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (h.mem_cent_z hvU)
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  have hzC : z ∈ centralizer ({t} : Set G) ⊓ centralizer ({v} : Set G) :=
    ⟨h.cfg.z_mem_centralizer_t, hzv⟩
  have hzZ : z ∈ zStar (rigidProduct v) := hP0 G z t S K U h v hvU hv2
  have hcomm_z : ∀ l ∈ Λ, ⁅l, z⁆ ∈ pPrimeCoreOf 2 (centralizer ({v} : Set G)) :=
    hBL0 G hG t v ht2 hv2 hvt Λ (le_sSup hΛc) z hzC hzZ
  have hcomm_g : ∀ l ∈ Λ, ⁅l, g⁆ ∈ pPrimeCoreOf 2 (centralizer ({v} : Set G)) := by
    intro l hl
    rcases hgz with hgz | hgz
    · rw [hgz]
      exact hcomm_z l hl
    · have hlv : l * v = v * l := Subgroup.mem_centralizer_singleton_iff.1 (hΛle hl).2
      have h1 : ⁅l, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hlv
      have h2 : ⁅l, z * v⁆ = ⁅l, z⁆ * (z * ⁅l, v⁆ * z⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [hgz, h2, h1]
      simpa using hcomm_z l hl
  have hgt : g ∈ centralizer ({t} : Set G) := h.mem_cent_t hgU
  have hgv : g ∈ centralizer ({v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (h.hU.mul_comm' hgU hvU)
  have hgL' : g ∈ cSec L := cSec_of_commutators hv2 hvt hL hvL hgt hgv hgL hΛt hcov hcomm_g
  exact h293 G z t S h.cfg g hg2 (h.mem_cent_z hgU) hgt K h.hK (h.mem_cSec hgU) L hL hgL'

theorem l295a_of (hP0 : P0S) (hDL : DiagLayerS) (hBL0 : BL0S) (h293 : L293) (hquat : II4_4_quat) :
    L295aS := by
  intro G _ _ z t S K U h L hL u hu
  by_contra hnot
  have hG := h.cfg.simple
  have hgen := h.cfg.gen4
  have ht2 : orderOf t = 2 := h.cfg.t_orderOf
  have hz2 : orderOf z = 2 := h.cfg.hz
  have hzz : z * z = 1 := h.hU.mul_self' h.hzU
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hu1 : u ≠ 1 := fun h1 => hnot (by rw [h1]; exact one_mem _)
  have hu2 : orderOf u = 2 := h.hU.orderOf_eq_two hu hu1
  have hut : u ∈ centralizer ({t} : Set G) := h.mem_cent_t hu
  have hL' : IsRigidRankOneComp t (cmap u L) := isRigidRankOneComp_cmap hL hut
  have hne : L ≠ cmap u L := fun h' => hnot (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h'.symm)
  have hdich : ∀ g ∈ U, g ∈ normalizer (L : Set G) ∨ cmap g L = cmap u L := fun g hg =>
    rigid_normalizes_or_swaps hquat hG hgen ht2 hL hL' hne (h.mem_cent_t hg)
  by_cases hzL : z ∈ normalizer (L : Set G)
  · exact l295a_step hP0 hDL hBL0 h293 h hL hu hu2 hnot h.hzU hz1 hzL (Or.inl rfl)
  · have hzs : cmap z L = cmap u L := (hdich z h.hzU).resolve_left hzL
    have hex : ∃ x ∈ U, x ≠ 1 ∧ x ≠ z := by
      by_contra hcon
      push Not at hcon
      have hsub : (U : Set G) ⊆ {1, z} := fun x hx => by
        by_cases hx1 : x = 1
        · simp [hx1]
        · simp [hcon x hx hx1]
      have hcard : (U : Set G).ncard ≤ 2 := by
        calc (U : Set G).ncard ≤ ({1, z} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ ({z} : Set G).ncard + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      have hU4 : (U : Set G).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]
        exact h.hU.2
      omega
    obtain ⟨x, hxU, hx1, hxz⟩ := hex
    have hmul_ne : ∀ a b : G, a * b = 1 → b = a⁻¹ := fun a b hab => eq_inv_of_mul_eq_one_right hab
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    obtain ⟨u₀, hu₀U, hu₀1, hu₀z, hu₀L⟩ :
        ∃ u₀ ∈ U, u₀ ≠ 1 ∧ u₀ ≠ z ∧ u₀ ∈ normalizer (L : Set G) := by
      by_cases hxL : x ∈ normalizer (L : Set G)
      · exact ⟨x, hxU, hx1, hxz, hxL⟩
      · have hxs : cmap x L = cmap u L := (hdich x hxU).resolve_left hxL
        refine ⟨z * x, mul_mem h.hzU hxU, ?_, ?_, ?_⟩
        · intro h1
          apply hxz
          rw [hmul_ne z x h1, hzinv]
        · intro h1
          apply hx1
          exact mul_left_cancel (a := z) (b := x) (c := 1) (by rw [mul_one]; exact h1)
        · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
          show cmap (z * x) L = L
          rw [← cmap_cmap, hxs, ← hzs, cmap_cmap, hzz, cmap_one_self]
    have hvU : z * u₀ ∈ U := mul_mem h.hzU hu₀U
    have hv1 : z * u₀ ≠ 1 := by
      intro h1
      apply hu₀z
      rw [hmul_ne z u₀ h1, hzinv]
    have hv2 : orderOf (z * u₀) = 2 := h.hU.orderOf_eq_two hvU hv1
    have hu₀s : cmap u₀ L = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hu₀L
    have hvL : z * u₀ ∉ normalizer (L : Set G) := by
      intro hvN
      have h1 : cmap (z * u₀) L = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hvN
      rw [← cmap_cmap, hu₀s, hzs] at h1
      exact hne h1.symm
    have hgeq : z * (z * u₀) = u₀ := by rw [← mul_assoc, hzz, one_mul]
    refine l295a_step hP0 hDL hBL0 h293 h hL hvU hv2 hvL (g := z * (z * u₀)) ?_ ?_ ?_ (Or.inr rfl)
    · rw [hgeq]; exact hu₀U
    · rw [hgeq]; exact hu₀1
    · rw [hgeq]; exact hu₀L

end CFSG.GH74.GLS.Bg.Pu5
