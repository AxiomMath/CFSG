module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41E8A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41P2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AInputs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

namespace S4A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem l41_e8_of (h : L41GPh5 t L S x₁ x₂ lam rho)
    (he8 : ∀ 𝒮 : Sylow 2 G, ∃ E : Subgroup G, E ≤ (𝒮 : Subgroup G) ∧
      (E.subgroupOf (𝒮 : Subgroup G)).Normal ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8) :
    L41E8Fact t S x₁ x₂ := by
  obtain ⟨𝒮, h𝒮⟩ := exists_sylow_gt h.normalizerFacts.V_pGroup h.normalizerFacts.V_not_sylow
  obtain ⟨E, hE𝒮, hEn, hEe, hEc⟩ := he8 𝒮
  have hS𝒮 : S < (𝒮 : Subgroup G) :=
    lt_of_le_of_lt (le_sup_right : S ≤ l41O2 t x₁ x₂ ⊔ S) h𝒮
  have d : L41E8Data t S 𝒮 E :=
    ⟨hS𝒮.le, l41_sylow_inf_invCent_eq h.toL41GPh1 𝒮 hS𝒮, hE𝒮, hEn, hEe, hEc,
      l41_e8_no_conj h hE𝒮 hEn hEc⟩
  have hF : E ⊓ S = fourGrp x₁ x₂ := d.inf_S_eq h.toL41GPh2
  have hFE : fourGrp x₁ x₂ ≤ E := hF ▸ inf_le_left
  have hFW := l41_e8_fourGrp_le_ctxW t x₁ x₂
  have hcardF : Nat.card (fourGrp x₁ x₂) = 4 := (h.wreath.fourGrp_eq_omega).2.2
  have hEN : E ≤ l41N t x₁ x₂ := d.le_N h.toL41GPh2
  have hVeq : (𝒮 : Subgroup G) ⊓ l41N t x₁ x₂ = l41V S t x₁ x₂ :=
    eq_of_isPGroup_of_odd_relIndex (H := l41N t x₁ x₂)
      (le_inf h𝒮.le h.normalizerFacts.V_le) inf_le_right
      ((show IsPGroup 2 (𝒮 : Subgroup G) from 𝒮.isPGroup').to_le inf_le_left)
      h.normalizerFacts.V_sylow
  have hEV : E ≤ l41V S t x₁ x₂ := by
    intro e he
    rw [← hVeq]
    exact ⟨hE𝒮 he, hEN he⟩
  have hEO : E ≤ l41O2 t x₁ x₂ := by
    rw [h.normalizerFacts.O2_eq]
    intro e he
    refine Subgroup.mem_inf.mpr ⟨hEN he, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact l41_e8_comm hEe (hFE hf) he
  have hEW : E ⊓ ctxW t x₁ x₂ = fourGrp x₁ x₂ := by
    apply le_antisymm
    · intro w hw
      obtain ⟨hwE, hwW⟩ := Subgroup.mem_inf.mp hw
      have hw2 : w * w = 1 := by
        have := hEe.2 w hwE
        rwa [pow_two] at this
      have hwA : w ∈ ctxE t x₁ x₂ := l41_omega_ctxW_le h.toL41GPh1 hwW hw2
      have hwS : w ∈ S := h.basic.normal_W.1 hwW
      rw [← hF]
      exact Subgroup.mem_inf.mpr ⟨hwE, hwS⟩
    · intro f hf
      exact Subgroup.mem_inf.mpr ⟨hFE hf, hFW hf⟩
  have hEnW : ¬ E ≤ ctxW t x₁ x₂ := by
    intro hEW'
    have hEA : E ≤ ctxE t x₁ x₂ := fun e he =>
      l41_omega_ctxW_le h.toL41GPh1 (hEW' he) (by
        have := hEe.2 e he
        rwa [pow_two] at this)
    have hEeqA : E = ctxE t x₁ x₂ :=
      Subgroup.eq_of_le_of_card_ge hEA (by rw [h.basic.A_elem.2, hEc])
    have htA : t ∈ ctxE t x₁ x₂ := Subgroup.subset_closure (by simp)
    exact d.no_conj 1 t (hEeqA ▸ htA) (by simp)
  have hNorm : NormalIn E (l41V S t x₁ x₂) :=
    ⟨hEV, fun g hg k hk => d.mem_conj hk (h𝒮.le hg)⟩
  have hFi : (fourGrp x₁ x₂).relIndex E = 2 := by
    have hmul := Subgroup.relIndex_mul_card (H := fourGrp x₁ x₂) (K := E)
    rw [inf_eq_left.mpr hFE, hcardF, hEc] at hmul
    omega
  have hcomm : ∀ e ∈ E, ∀ v ∈ l41V S t x₁ x₂, ⁅e, v⁆ ∈ fourGrp x₁ x₂ := by
    intro e he v hv
    have hvN : v ∈ l41N t x₁ x₂ := h.normalizerFacts.V_le hv
    have hvinvN : v⁻¹ ∈ l41N t x₁ x₂ := (l41N t x₁ x₂).inv_mem hvN
    have hFn := h.normalizerFacts.normal_F2.2
    have he' : v * e * v⁻¹ ∈ E := d.mem_conj he (h𝒮.le hv)
    have hinv' : (v * e * v⁻¹)⁻¹ = v * e * v⁻¹ := l41_e8_inv hEe he'
    have hbr : ⁅e, v⁆ = e * (v * e * v⁻¹) := by
      rw [commutatorElement_def]
      calc e * v * e⁻¹ * v⁻¹ = e * (v * e * v⁻¹)⁻¹ := by group
        _ = e * (v * e * v⁻¹) := by rw [hinv']
    rw [hbr]
    rcases mem_or_mem_or_mul_mem_of_relIndex_two hFE hFi he he' with h1 | h2 | h3
    · exact (fourGrp x₁ x₂).mul_mem h1 (hFn v hvN e h1)
    · have h4 : v⁻¹ * (v * e * v⁻¹) * v⁻¹⁻¹ ∈ fourGrp x₁ x₂ := hFn v⁻¹ hvinvN _ h2
      have h5 : v⁻¹ * (v * e * v⁻¹) * v⁻¹⁻¹ = e := by group
      rw [h5] at h4
      exact (fourGrp x₁ x₂).mul_mem h4 h2
    · exact h3
  exact ⟨E, hEO, hNorm, hEe, hEc, hEW, hEnW, d.no_conj, hcomm⟩

end S4A

theorem l41_e8_holds : L41E8Stmt :=
  fun h => S4A.l41_e8_of h.toG (Sec4Inputs.exists_normal_e8 h.inputs h.glob h.hyp)

end CFSG.OddStandard.SmallF3.HarrisU33
