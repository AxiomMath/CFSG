module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7B
import all CFSG.Fischer.F4

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

@[expose] noncomputable def Data.Pp (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀) :
    Subgroup G :=
  d.tc (Data.Lam₁ h hKU hf) ⊔ (d.Y ⊓ d.tc K₀)

@[expose] noncomputable def Data.Nn (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀) :
    Subgroup G :=
  ⁅Data.N₃ h hKU hf, Data.N₃ h hKU hf⁆

section Perf



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.isSimpleGroup_Lam₁ : IsSimpleGroup ↥(Data.Lam₁ h hKU hf) := by
  haveI := Common.sl2_isSimpleGroup_of_charTwo (k := CFSG.Fischer.F4)
    (by rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card])
  exact (Data.lamEquiv h hKU hf).isSimpleGroup

include h hKU in
theorem Data.Hyp.commutator_Lam₁_eq_top : commutator ↥(Data.Lam₁ h hKU hf) = ⊤ := by
  haveI := h.isSimpleGroup_Lam₁ hKU hf
  have hnc : ¬ ∀ a b : ↥(Data.Lam₁ h hKU hf), a * b = b * a := by
    intro hc
    have hc' : ∀ A B : Matrix.SpecialLinearGroup (Fin 2) CFSG.Fischer.F4, A * B = B * A :=
      fun A B => by
        apply (Data.lamEquiv h hKU hf).symm.injective
        rw [map_mul, map_mul]
        exact hc _ _
    have hm : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) CFSG.Fischer.F4) * !![1, 0; 1, 1] ≠
        !![1, 0; 1, 1] * !![1, 1; 0, 1] := by decide
    exact hm (congrArg Subtype.val (hc' ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
        ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(Data.Lam₁ h hKU hf)) with hb | ht
  · exfalso
    refine hnc fun a b => ?_
    have hab : ⁅a, b⁆ ∈ commutator ↥(Data.Lam₁ h hKU hf) := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hb, Subgroup.mem_bot] at hab
    exact commutatorElement_eq_one_iff_mul_comm.1 hab
  · exact ht

include h hKU in
theorem Data.Hyp.Lam₁_perfect :
    ⁅Data.Lam₁ h hKU hf, Data.Lam₁ h hKU hf⁆ = Data.Lam₁ h hKU hf := by
  have := Subgroup.map_subtype_commutator (Data.Lam₁ h hKU hf)
  rw [h.commutator_Lam₁_eq_top hKU hf, Subgroup.map_top, Subgroup.range_subtype] at this
  exact this.symm

include h hKU in
theorem Data.Hyp.tcLam₁_perfect :
    ⁅d.tc (Data.Lam₁ h hKU hf), d.tc (Data.Lam₁ h hKU hf)⁆ = d.tc (Data.Lam₁ h hKU hf) := by
  rw [Data.tc, ← Subgroup.map_commutator, h.Lam₁_perfect hKU hf]

include h hKU in
theorem Data.Hyp.t_mem_normalizer_Y : d.t ∈ normalizer (d.Y : Set G) :=
  mem_normalizer_fintype fun y hy => by
    have := h.t_conj_mem_Y hy
    rw [h.t_inv]
    exact this

include h hKU in
theorem Data.Hyp.t_mem_normDY : d.t ∈ ModSplit.normDY d.D₂ d.Y :=
  Subgroup.mem_inf.2 ⟨h.t_mem_normalizer_D₂, h.t_mem_normalizer_Y hKU⟩

include h hKU in
theorem Data.Hyp.tc_Cv₁ : d.tc (Data.Cv₁ h hKU hf) = Data.Cv₂ h hKU hf := by
  unfold Data.Cv₁ Data.Cv₂ ModSplit.liftFixG Data.tc
  rw [ModSplit.map_conj_subgroupOf (ModSplit.normDY d.D₂ d.Y) _ (h.t_mem_normDY hKU),
    ModSplit.liftFix_map_conj d.D₂ d.Y _ ⟨d.t, h.t_mem_normDY hKU⟩]

include h hKU in
theorem Data.Hyp.tc_Cv₂ : d.tc (Data.Cv₂ h hKU hf) = Data.Cv₁ h hKU hf := by
  rw [← h.tc_Cv₁ hKU hf, h.tc_tc]

include h hKU in
theorem Data.Hyp.eq_one_of_mul_mem_D₂ {g μ : G} (hg : g ∈ Data.Lam₁ h hKU hf)
    (hμ : μ ∈ d.tc (Data.Lam₁ h hKU hf)) (hgμ : g * μ ∈ d.D₂) : g = 1 := by
  haveI := h.isSimpleGroup_Lam₁ hKU hf
  have hK := h.comm_M_V₂_mem_W hKU
  have hN₂ := h.Lam₁_le_normalizer_D₂ hKU hf (h.hD hKU)
  have hNY := h.Lam₁_le_normalizer_Y hKU hf
  let Kc : Subgroup ↥(Data.Lam₁ h hKU hf) :=
    { carrier := {a | ∀ z ∈ d.D₂, (a : G) * z * (a : G)⁻¹ * z⁻¹ ∈ d.Y}
      one_mem' := fun z _ => by simpa using d.Y.one_mem
      mul_mem' := by
        intro a b ha hb z hz
        have e : ((a * b : ↥(Data.Lam₁ h hKU hf)) : G) * z * ((a * b : ↥(Data.Lam₁ h hKU hf)) : G)⁻¹ *
            z⁻¹ = ((a : G) * ((b : G) * z * (b : G)⁻¹ * z⁻¹) * (a : G)⁻¹) *
              ((a : G) * z * (a : G)⁻¹ * z⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        rw [e]
        exact d.Y.mul_mem ((mem_normalizer_iff.1 (hNY a.2) _).1 (hb z hz)) (ha z hz)
      inv_mem' := by
        intro a ha z hz
        have hz' : (a : G)⁻¹ * z * (a : G) ∈ d.D₂ := by
          have hai : (a : G)⁻¹ ∈ Data.Lam₁ h hKU hf := (Data.Lam₁ h hKU hf).inv_mem a.2
          have := (mem_normalizer_iff.1 (hN₂ hai) z).1 hz
          simpa using this
        have h1 := ha _ hz'
        have e : ((a⁻¹ : ↥(Data.Lam₁ h hKU hf)) : G) * z * ((a⁻¹ : ↥(Data.Lam₁ h hKU hf)) : G)⁻¹ *
            z⁻¹ = ((a : G) * ((a : G)⁻¹ * z * (a : G)) * (a : G)⁻¹ *
              ((a : G)⁻¹ * z * (a : G))⁻¹)⁻¹ := by
          simp only [Subgroup.coe_inv]
          group
        rw [e]
        exact d.Y.inv_mem h1 }
  haveI : Kc.Normal := ⟨by
    intro a ha c z hz
    have hz' : (c : G)⁻¹ * z * (c : G) ∈ d.D₂ := by
      have hci : (c : G)⁻¹ ∈ Data.Lam₁ h hKU hf := (Data.Lam₁ h hKU hf).inv_mem c.2
      have := (mem_normalizer_iff.1 (hN₂ hci) z).1 hz
      simpa using this
    have h1 := ha _ hz'
    have e : ((c * a * c⁻¹ : ↥(Data.Lam₁ h hKU hf)) : G) * z *
        ((c * a * c⁻¹ : ↥(Data.Lam₁ h hKU hf)) : G)⁻¹ * z⁻¹ =
        (c : G) * ((a : G) * ((c : G)⁻¹ * z * (c : G)) * (a : G)⁻¹ *
          ((c : G)⁻¹ * z * (c : G))⁻¹) * (c : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    show (((c * a * c⁻¹ : ↥(Data.Lam₁ h hKU hf)) : G)) * z * _ * z⁻¹ ∈ d.Y
    rw [e]
    exact (mem_normalizer_iff.1 (hNY c.2) _).1 h1⟩
  have hmem : (⟨g, hg⟩ : ↥(Data.Lam₁ h hKU hf)) ∈ Kc := by
    intro z hz
    have hz' : z ∈ d.Cv₁ h hKU hf ⊔ d.Cv₂ h hKU hf := by
      rw [h.Cv₁_sup_Cv₂ hKU hf]
      exact hz
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer
      ((h.Cv₁_le_D₂ hKU hf).trans (h.D₂_le_normalizer_Cv₂ hKU hf)) hz'
    have hb₁D : b₁ ∈ d.D₂ := h.Cv₂_le_D₂ hKU hf hb₁
    have ha₁D : a₁ ∈ d.D₂ := h.Cv₁_le_D₂ hKU hf ha₁
    have hyb : μ * b₁ * μ⁻¹ * b₁⁻¹ ∈ d.Y := ((h.mem_Cv₂_iff hKU hf).1 hb₁).2 μ hμ
    have hcb : (g * μ) * b₁ * (g * μ)⁻¹ * b₁⁻¹ ∈ d.Y := h.D₂_commutator_mem_Y hK hgμ hb₁D
    have hgb : g * b₁ * g⁻¹ * b₁⁻¹ ∈ d.Y := by
      have e : g * b₁ * g⁻¹ * b₁⁻¹ = (g * (μ * b₁ * μ⁻¹ * b₁⁻¹) * g⁻¹)⁻¹ *
          ((g * μ) * b₁ * (g * μ)⁻¹ * b₁⁻¹) := by group
      rw [e]
      exact d.Y.mul_mem (d.Y.inv_mem ((mem_normalizer_iff.1 (hNY hg) _).1 hyb)) hcb
    have hga : g * a₁ * g⁻¹ * a₁⁻¹ ∈ d.Y := ((h.mem_Cv₁_iff hKU hf).1 ha₁).2 g hg
    have e2 : g * (a₁ * b₁) * g⁻¹ * (a₁ * b₁)⁻¹ =
        (g * a₁ * g⁻¹ * a₁⁻¹) * (a₁ * (g * b₁ * g⁻¹ * b₁⁻¹) * a₁⁻¹) := by group
    show g * (a₁ * b₁) * g⁻¹ * (a₁ * b₁)⁻¹ ∈ d.Y
    rw [e2]
    refine d.Y.mul_mem hga ?_
    have hc : a₁ * (g * b₁ * g⁻¹ * b₁⁻¹) = (g * b₁ * g⁻¹ * b₁⁻¹) * a₁ :=
      (mem_centralizer_iff.1 (D₂_le_centralizer_Y ha₁D) _ hgb).symm
    rw [hc]
    simpa using hgb
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Kc with hb | ht
  · rw [hb, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hle : d.Cv₂ h hKU hf ≤ d.Cv₁ h hKU hf := by
      intro b hb
      refine (h.mem_Cv₁_iff hKU hf).2 ⟨h.Cv₂_le_D₂ hKU hf hb, fun a ha => ?_⟩
      have : (⟨a, ha⟩ : ↥(Data.Lam₁ h hKU hf)) ∈ Kc := ht ▸ Subgroup.mem_top _
      exact this b (h.Cv₂_le_D₂ hKU hf hb)
    have hY : d.Cv₂ h hKU hf ≤ d.Y := by
      intro b hb
      have : b ∈ d.Cv₁ h hKU hf ⊓ d.Cv₂ h hKU hf := Subgroup.mem_inf.2 ⟨hle hb, hb⟩
      rwa [h.Cv₁_inf_Cv₂ hKU hf] at this
    have hc : Nat.card (d.Cv₂ h hKU hf) ≤ Nat.card d.Y := Subgroup.card_le_of_le hY
    rw [h.card_Cv₂ hKU hf, h.card_Y] at hc
    norm_num at hc

end Perf

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
