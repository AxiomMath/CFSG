module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7A
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7C

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

section Stab



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.D₂_quot_comm (a b : d.D₂ ⧸ d.Y.subgroupOf d.D₂) : a * b = b * a :=
  ModSplit.quot_comm d.D₂ d.Y (fun _ hx _ hy =>
    h.D₂_commutator_mem_Y (h.comm_M_V₂_mem_W hKU) hx hy) a b

include h hKU in
theorem Data.Hyp.Cv₂_le_comm_sup_Y :
    Data.Cv₂ h hKU hf ≤ ⁅Data.Cv₂ h hKU hf, Data.Lam₁ h hKU hf⁆ ⊔ d.Y := by
  let ρ : ↥(Data.Lam₁ h hKU hf) →* MulAut (d.D₂ ⧸ d.Y.subgroupOf d.D₂) :=
    (ModSplit.actQuot d.D₂ d.Y).comp (Subgroup.inclusion (h.Lam₁_le_normDY hKU hf))
  let V₀ : Subgroup (d.D₂ ⧸ d.Y.subgroupOf d.D₂) :=
    ModSplit.fixSub (ModSplit.actQuot d.D₂ d.Y)
      ((d.tc (Data.Lam₁ h hKU hf)).subgroupOf (ModSplit.normDY d.D₂ d.Y))
  have hV₀mem : ∀ x : d.D₂, (QuotientGroup.mk x : d.D₂ ⧸ d.Y.subgroupOf d.D₂) ∈ V₀ ↔
      (x : G) ∈ Data.Cv₂ h hKU hf := by
    intro x
    rw [h.mem_Cv₂_iff hKU hf]
    constructor
    · intro hx
      refine ⟨x.2, fun g hg => ?_⟩
      have hgN : g ∈ ModSplit.normDY d.D₂ d.Y := h.tcLam₁_le_normDY hKU hf hg
      exact (ModSplit.actQuot_mk_eq_iff d.D₂ d.Y ⟨g, hgN⟩ x).1
        ((ModSplit.mem_fixSub _).1 hx ⟨g, hgN⟩ (Subgroup.mem_subgroupOf.2 hg))
    · rintro ⟨-, hx⟩
      refine (ModSplit.mem_fixSub _).2 fun g hg => ?_
      exact (ModSplit.actQuot_mk_eq_iff d.D₂ d.Y g x).2 (hx g (Subgroup.mem_subgroupOf.1 hg))
  have hV₀card : Nat.card V₀ = 2 ^ 4 := by
    have e : Nat.card (Data.Cv₂ h hKU hf) = Nat.card d.Y * Nat.card V₀ :=
      ModSplit.card_liftFix d.D₂ d.Y h.Y_le_D₂
        ((d.tc (Data.Lam₁ h hKU hf)).subgroupOf (ModSplit.normDY d.D₂ d.Y))
    rw [h.card_Cv₂ hKU hf, h.card_Y] at e
    omega
  have hV₀inv : ∀ g ∈ (⊤ : Subgroup ↥(Data.Lam₁ h hKU hf)), ∀ v ∈ V₀, ρ g v ∈ V₀ := by
    intro g _ v hv
    refine ModSplit.ρ_mem_fixSub_of_comm (ModSplit.actQuot d.D₂ d.Y)
      (g := Subgroup.inclusion (h.Lam₁_le_normDY hKU hf) g) (fun s hs => ?_) hv
    apply Subtype.ext
    exact (hf.comm_elem g (Data.Lam₁_le_K₀ h hKU hf g.2) s
      (h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) (Subgroup.mem_subgroupOf.1 hs))).symm
  have hfix : ∀ v ∈ V₀, (∀ g ∈ (⊤ : Subgroup ↥(Data.Lam₁ h hKU hf)), ρ g v = v) → v = 1 := by
    intro v hv hvfix
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    have hxC₂ : (x : G) ∈ Data.Cv₂ h hKU hf := (hV₀mem x).1 hv
    have hxC₁ : (x : G) ∈ Data.Cv₁ h hKU hf := by
      refine (h.mem_Cv₁_iff hKU hf).2 ⟨x.2, fun g hg => ?_⟩
      exact (ModSplit.actQuot_mk_eq_iff d.D₂ d.Y ⟨g, h.Lam₁_le_normDY hKU hf hg⟩ x).1
        (hvfix ⟨g, hg⟩ (Subgroup.mem_top _))
    have hxY : (x : G) ∈ d.Cv₁ h hKU hf ⊓ d.Cv₂ h hKU hf := Subgroup.mem_inf.2 ⟨hxC₁, hxC₂⟩
    rw [h.Cv₁_inf_Cv₂ hKU hf] at hxY
    exact (ModSplit.mk_eq_one_iff d.D₂ d.Y x).2 hxY
  have hperf : ⁅(⊤ : Subgroup ↥(Data.Lam₁ h hKU hf)), (⊤ : Subgroup ↥(Data.Lam₁ h hKU hf))⁆ =
      (⊤ : Subgroup ↥(Data.Lam₁ h hKU hf)) := by
    rw [← commutator_def]
    exact h.commutator_Lam₁_eq_top hKU hf
  have hclos := ModSplit.le_closure_commAct_of_fix_trivial ρ (h.D₂_quot_comm hKU)
    (k := CFSG.Fischer.F4) (by rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card]; norm_num) ⊤
    (Subgroup.topEquiv.trans (Data.lamEquiv h hKU hf)) hperf V₀ hV₀inv hV₀card hfix
  let T : Subgroup (d.D₂ ⧸ d.Y.subgroupOf d.D₂) :=
    ((⁅Data.Cv₂ h hKU hf, Data.Lam₁ h hKU hf⁆ ⊔ d.Y).subgroupOf d.D₂).map
      (QuotientGroup.mk' (d.Y.subgroupOf d.D₂))
  have hclosT : Subgroup.closure {x : d.D₂ ⧸ d.Y.subgroupOf d.D₂ |
      ∃ g ∈ (⊤ : Subgroup ↥(Data.Lam₁ h hKU hf)), ∃ w ∈ V₀, x = ρ g w * w⁻¹} ≤ T := by
    refine (Subgroup.closure_le T).2 ?_
    rintro _ ⟨g, -, w, hw, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    have hyC : (y : G) ∈ Data.Cv₂ h hKU hf := (hV₀mem y).1 hw
    obtain ⟨hgy, hgeq⟩ := ModSplit.actQuot_mk d.D₂ d.Y
      (Subgroup.inclusion (h.Lam₁_le_normDY hKU hf) g) y
    have hgy' : (g : G) * (y : G) * (g : G)⁻¹ ∈ d.D₂ := hgy
    refine ⟨⟨(g : G) * (y : G) * (g : G)⁻¹, hgy'⟩ * y⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ?_
      have hc : (g : G) * (y : G) * (g : G)⁻¹ * (y : G)⁻¹ ∈
          ⁅Data.Cv₂ h hKU hf, Data.Lam₁ h hKU hf⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator g.2 hyC
      exact mem_sup_left hc
    · show QuotientGroup.mk (⟨(g : G) * (y : G) * (g : G)⁻¹, hgy'⟩ * y⁻¹) =
        ρ g (QuotientGroup.mk y) * (QuotientGroup.mk y)⁻¹
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact congrArg (· * (QuotientGroup.mk y)⁻¹) hgeq.symm
  intro z hz
  have hzD : z ∈ d.D₂ := h.Cv₂_le_D₂ hKU hf hz
  have hzV₀ : (QuotientGroup.mk ⟨z, hzD⟩ : d.D₂ ⧸ d.Y.subgroupOf d.D₂) ∈ V₀ :=
    (hV₀mem ⟨z, hzD⟩).2 hz
  obtain ⟨u, hu, huz⟩ := Subgroup.mem_map.1 (hclosT (hclos hzV₀))
  have hu' : (u : G) ∈ ⁅Data.Cv₂ h hKU hf, Data.Lam₁ h hKU hf⁆ ⊔ d.Y :=
    Subgroup.mem_subgroupOf.1 hu
  have huz' : (QuotientGroup.mk u : d.D₂ ⧸ d.Y.subgroupOf d.D₂) = QuotientGroup.mk ⟨z, hzD⟩ := huz
  have h3 : (u : G)⁻¹ * z ∈ d.Y := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 huz')
  rw [show z = (u : G) * ((u : G)⁻¹ * z) by group]
  exact mul_mem hu' (mem_sup_right h3)

end Stab

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
