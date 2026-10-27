module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Prf

variable {G : Type} [Group G]

theorem isQuasisimple_of_isCompIn {H J : Subgroup G} (hJ : IsCompIn H J) :
    CFSG.IsQuasisimple ↥J :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ.1) hJ.2.1

theorem comm_mul_of_commute {a b c d : G} (hbc : b * c = c * b) (hbd : b * d = d * b)
    (hda : d * a = a * d) : ⁅a * b, c * d⁆ = ⁅a, c⁆ := by
  have hda' : d * a⁻¹ = a⁻¹ * d := by
    calc d * a⁻¹ = a⁻¹ * (a * d) * a⁻¹ := by group
      _ = a⁻¹ * (d * a) * a⁻¹ := by rw [hda]
      _ = a⁻¹ * d := by group
  calc ⁅a * b, c * d⁆ = a * (b * c) * d * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * (c * b) * d * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by rw [hbc]
    _ = a * c * (b * d) * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by group
    _ = a * c * (d * b) * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by rw [hbd]
    _ = a * c * (d * a⁻¹) * d⁻¹ * c⁻¹ := by group
    _ = a * c * (a⁻¹ * d) * d⁻¹ * c⁻¹ := by rw [hda']
    _ = ⁅a, c⁆ := by simp only [commutatorElement_def]; group

theorem perfect_le_of_sup {A B J : Subgroup G} (hJ : ⁅J, J⁆ = J) (hle : J ≤ A ⊔ B)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    J ≤ A := by
  rw [← hJ]
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hAB (hle hx)
  obtain ⟨a', ha', b', hb', rfl⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hAB (hle hy)
  rw [comm_mul_of_commute (hAB a' ha' b hb).symm (hB b hb b' hb') (hAB a ha b' hb').symm]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha ha') (A.inv_mem ha)) (A.inv_mem ha')

theorem mem_centralizer_of_comm_central {J : Subgroup G} [Group.IsPerfect ↥J] {g : G}
    (hg : g ∈ normalizer (J : Set G))
    (h : ∀ j ∈ J, ∀ k ∈ J, k * (g * j * g⁻¹ * j⁻¹) = (g * j * g⁻¹ * j⁻¹) * k) :
    g ∈ centralizer (J : Set G) := by
  have h1 : YCfg.yAct J ⟨g, hg⟩ = 1 := by
    ext x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center ↥J) x
    show (YCfg.yAct J ⟨g, hg⟩) (QuotientGroup.mk j) = QuotientGroup.mk j
    rw [YCfg.yAct_apply_mk]
    show QuotientGroup.mk _ = QuotientGroup.mk j
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have := h (j : G) j.2 (k : G) k.2
    simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  exact (YCfg.yAct_eq_one_iff J ⟨g, hg⟩).mp h1

@[expose] def CenK (K : Subgroup G) (c : G) : Prop := c ∈ K ∧ ∀ k ∈ K, k * c = c * k

theorem CenK.mul {K : Subgroup G} {c c' : G} (h : CenK K c) (h' : CenK K c') : CenK K (c * c') :=
  ⟨K.mul_mem h.1 h'.1, fun k hk => by
    rw [← mul_assoc, h.2 k hk, mul_assoc, h'.2 k hk, mul_assoc]⟩

theorem CenK.inv {K : Subgroup G} {c : G} (h : CenK K c) : CenK K c⁻¹ :=
  ⟨K.inv_mem h.1, fun k hk => by
    have := h.2 k hk
    calc k * c⁻¹ = c⁻¹ * (c * k) * c⁻¹ := by group
      _ = c⁻¹ * (k * c) * c⁻¹ := by rw [this]
      _ = c⁻¹ * k := by group⟩

theorem CenK.conj {K : Subgroup G} {c g : G} (h : CenK K c) (hg : g ∈ normalizer (K : Set G)) :
    CenK K (g * c * g⁻¹) := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg c).1 h.1, fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) k).1 hk
    simpa using this
  have := h.2 _ hk'
  calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
    _ = (g * c * g⁻¹) * k := by group

theorem CenK.of_mem_inf {K L : Subgroup G} (hKL : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a) {c : G}
    (hcK : c ∈ K) (hcL : c ∈ L) : CenK K c :=
  ⟨hcK, fun k hk => hKL k hk c hcL⟩

end Prf

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
