module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.L514T
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop115b
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

variable {G : Type} [Group G] [Finite G]

theorem k148f_autFix_eq {Y : Type} [Group Y] (α : MulAut Y) :
    CFSG.RankThree.PartTwo.Sec4.autFix α = CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub α := by
  ext v
  rw [CFSG.RankThree.PartTwo.Sec4.mem_autFix]
  exact Iff.rfl

theorem k148f_barX_cent {K : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hx3 : x ^ 3 = 1) :
    barX 3 K (K ⊓ Subgroup.centralizer ({x} : Set G)) =
      CFSG.RankThree.PartTwo.Sec4.autFix (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩) := by
  rw [k148f_autFix_eq, CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub_barAut_eq hx3 hxN]

theorem k148f_comp_F {K I' : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hx3 : x ^ 3 = 1) (hI' : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) I') :
    GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩))
      (barX 3 K I') := by
  rw [← k148f_barX_cent hxN hx3]
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop115b.barX_glaPComponent_of_le Nat.prime_three inf_le_left hI'

theorem k148f_subnormal_simple_aux {P : Type} [Group P] {H K : Subgroup P}
    (hH : CFSG.Open.IsSubnormal H K) : IsSimpleGroup ↥K → H = ⊥ ∨ H = K := by
  induction hH with
  | refl H' => intro _; exact Or.inr rfl
  | @step H M K' hHM hnorm hM ih =>
    intro hK'
    rcases ih hK' with hMb | hMK'
    · left
      exact le_bot_iff.1 (hMb ▸ hHM)
    · have hHK' : H ≤ K' := hHM.trans hMK'.le
      have hnK : (H.subgroupOf K').Normal := by
        subst hMK'
        exact hnorm
      rcases hK'.eq_bot_or_eq_top_of_normal (H.subgroupOf K') with h0 | hT
      · left
        ext x
        constructor
        · intro hx
          have hmem : (⟨x, hHK' hx⟩ : ↥K') ∈ H.subgroupOf K' := hx
          rw [h0, Subgroup.mem_bot] at hmem
          exact congrArg Subtype.val hmem
        · intro hx
          rw [Subgroup.mem_bot] at hx
          rw [hx]
          exact Subgroup.one_mem H
      · right
        ext x
        constructor
        · intro hx
          exact hHK' hx
        · intro hx
          have hmem : (⟨x, hx⟩ : ↥K') ∈ H.subgroupOf K' := by
            rw [hT]
            exact Subgroup.mem_top _
          exact hmem

theorem k148f_comp_eq_of_simple {P : Type} [Group P] [Finite P] {F S : Subgroup P} (hF : IsSimpleGroup ↥F)
    (hS : GLAPComponent 3 F S) : S = F := by
  rcases k148f_subnormal_simple_aux hS.2.1 hF with h | h
  · exfalso
    have hPS := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hS
    subst h
    obtain ⟨x, y, hxy⟩ := isQuasisimple_nontrivial hPS
    apply hxy
    have hz : ∀ z : PQuot 3 (⊥ : Subgroup P), z = 1 := by
      intro z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
      have : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
      rw [this, QuotientGroup.mk_one]
    rw [hz x, hz y]
  · exact h

theorem k148f_unique_X {K I' : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hx3 : x ^ 3 = 1) (hI' : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) I')
    (hF : ∀ S : Subgroup (PQuot 3 K),
      GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩)) S →
        S = barX 3 K I') :
    ∀ J : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) J → J = I' := by
  have hXK : K ⊓ Subgroup.centralizer ({x} : Set G) ≤ K := inf_le_left
  have hS0 : GLAPComponent 3 (barX 3 K (K ⊓ Subgroup.centralizer ({x} : Set G))) (barX 3 K I') := by
    rw [k148f_barX_cent hxN hx3]
    exact k148f_comp_F hxN hx3 hI'
  have hu : ∀ S : Subgroup (PQuot 3 K),
      GLAPComponent 3 (barX 3 K (K ⊓ Subgroup.centralizer ({x} : Set G))) S → S = barX 3 K I' := by
    intro S hS
    rw [k148f_barX_cent hxN hx3] at hS
    exact hF S hS
  obtain ⟨J₀, -, hJ₀u, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.l514t_comp_unique_transfer hXK hS0 hu
  intro J hJ
  exact (hJ₀u J hJ).trans (hJ₀u I' hI').symm

theorem k148f_normalizer_inf {K : Subgroup G} {x y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hxy : x * y = y * x) :
    y ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hxy' : y⁻¹ * x = x * y⁻¹ := by
    calc y⁻¹ * x = y⁻¹ * x * (y * y⁻¹) := by group
      _ = y⁻¹ * (x * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * x) * y⁻¹ := by rw [hxy]
      _ = x * y⁻¹ := by group
  have E1 : ∀ g : G, x * (y * g * y⁻¹) = y * (x * g) * y⁻¹ := fun g => by
    calc x * (y * g * y⁻¹) = (x * y) * g * y⁻¹ := by group
      _ = (y * x) * g * y⁻¹ := by rw [hxy]
      _ = y * (x * g) * y⁻¹ := by group
  have E2 : ∀ g : G, (y * g * y⁻¹) * x = y * (g * x) * y⁻¹ := fun g => by
    calc (y * g * y⁻¹) * x = y * g * (y⁻¹ * x) := by group
      _ = y * g * (x * y⁻¹) := by rw [hxy']
      _ = y * (g * x) * y⁻¹ := by group
  have hC : h * x = x * h ↔ (y * h * y⁻¹) * x = x * (y * h * y⁻¹) := by
    rw [E2 h, E1 h]
    constructor
    · intro e
      rw [e]
    · intro e
      exact mul_left_cancel (mul_right_cancel e)
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact and_congr (Subgroup.mem_normalizer_iff.1 hyN h) hC

theorem k148f_y_norm {K I' : Subgroup G} {x y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hxy : x * y = y * x) (hI' : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) I')
    (huniq : ∀ J : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) J → J = I') :
    y ∈ Subgroup.normalizer (I' : Set G) := by
  have hyX := k148f_normalizer_inf hyN hxy
  have hG := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hI' y
  rw [mem_normalizer_iff_gLBConj_eq.1 hyX] at hG
  exact mem_normalizer_iff_gLBConj_eq.2 (huniq _ hG)

end CFSG.LocalAnalysis.GLTheoremA.K148F

end
