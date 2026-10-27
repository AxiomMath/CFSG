module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2PositionB
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2Fusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandardSetting

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_linear_two (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  have hKt := inf_centralizer_eq_zpowers hset e hK1 (by omega) htC ht
  have hOut := isSolvable_outer_of_mulEquiv (by omega : 3 ≤ n) e
  obtain ⟨-, htX, -, hXc, -, hDC, hDq, -, hZ, hOutD⟩ :=
    neighbour_data_torusQ1 e hn hab htC hX₀ hX₀c hX hDe
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_torusQ1_of_seitzSetting hset hK1 e hn htC ht hab hX₀ hX₀c hX htX hDe
  obtain ⟨x, z, hxz, hz, -, ⟨hxzL, hz'⟩, -⟩ :=
    exists_conj_eq_mul_transvection_twoSided_two hset (by omega) hK e htC ht
  have hI : 2 ≤ (({a, b} : Finset (Fin n))ᶜ).card := by
    rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    omega
  obtain ⟨c, hc1, hcI⟩ := exists_conj_mem_blockSL_of_isInvolutionClass_one hI hz
  set m : L := e.symm c with hm
  set y : L := m * z * m⁻¹ with hy
  set g : G := x * (m : G)⁻¹ with hg
  have hey : e y = c * e z * c⁻¹ := by
    rw [hy, map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply]
  have hmt : (m : G) * t = t * m := mem_centralizer_iff.1 htC _ m.2
  have hgt : g⁻¹ * t * g = t * (y : G) := by
    have e1 : g⁻¹ * t * g = (m : G) * (x⁻¹ * t * x) * (m : G)⁻¹ := by rw [hg]; group
    rw [e1, hxz, hy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (m : G) * (t * z) * (m : G)⁻¹ = ((m : G) * t) * z * (m : G)⁻¹ := by group
      _ = t * ((m : G) * z * (m : G)⁻¹) := by rw [hmt]; group
  have hgyeq : g * (y : G) * g⁻¹ = x * z * x⁻¹ := by
    rw [hg, hy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hgy : g * (y : G) * g⁻¹ ∈ L := hgyeq ▸ hxzL
  have hy' : IsInvolutionClass 1 (e ⟨g * (y : G) * g⁻¹, hgy⟩) := by
    have heq : (⟨g * (y : G) * g⁻¹, hgy⟩ : L) = ⟨x * z * x⁻¹, hxzL⟩ := Subtype.ext hgyeq
    rw [heq]
    exact hz'
  have hXodd : Odd (Nat.card X) := hXc ▸ odd_natCard_add_one
  have hXJ : X ≤ ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype :=
    hX ▸ map_mono (map_mono hX₀)
  subst hDe
  exact not_normal_map_oddCore_of_conj_eq_mul_of_transvection hset.standardSetting hOut hn e ht
    hKt hab hXodd hXJ (hey ▸ hcI) (hey ▸ hc1) hgt hgy hy' htX (hDC.trans inf_le_left) hDq hZ hOutD
    hsyl

end CFSG.SeitzReduction.LinearPilot
