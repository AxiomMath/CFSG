module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7G
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7F

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

@[expose] noncomputable def Data.N₂ (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀) :
    Subgroup G :=
  Data.Nn h hKU hf ⊔ d.tc (Data.Nn h hKU hf)

section Prod

variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.N₃_le_normalizer_Nn :
    Data.N₃ h hKU hf ≤ normalizer (Data.Nn h hKU hf : Set G) := fun _ hx =>
  mem_normalizer_commutator_of_mem (Subgroup.le_normalizer hx)

include h hKU in
theorem Data.Hyp.Y_le_normalizer_Nn : d.Y ≤ normalizer (Data.Nn h hKU hf : Set G) := fun _ hy =>
  h.N₃_le_normalizer_Nn hKU hf (h.Y_le_N₃ hKU hf hy)

include h hKU in
theorem Data.Hyp.I₁_le_tcNn : d.Y ⊓ d.tc K₀ ≤ d.tc (Data.Nn h hKU hf) := fun i hi => by
  have : i ∈ d.tc (Data.Nn h hKU hf) ⊓ d.Y := by
    rw [h.tcNn_inf_Y hKU hf]
    exact hi
  exact this.1

include h hKU in
theorem Data.Hyp.exists_Nn_mul_I₁ {x : G} (hx : x ∈ Data.N₃ h hKU hf) :
    ∃ n ∈ Data.Nn h hKU hf, ∃ i ∈ d.Y ⊓ d.tc K₀, x = n * i := by
  obtain ⟨z, hz, l, hl, rfl⟩ := h.exists_mul_of_mem_N₃ hKU hf hx
  have hz' : z ∈ d.Y ⊔ Data.Nn h hKU hf := by
    have h1 := h.Cv₂_le_comm_sup_Y hKU hf hz
    have h2 : ⁅Data.Cv₂ h hKU hf, Data.Lam₁ h hKU hf⁆ ⊔ d.Y ≤ d.Y ⊔ Data.Nn h hKU hf :=
      sup_le (le_sup_of_le_right (Subgroup.commutator_mono (Data.Cv₂_le_N₃ h hKU hf)
        (Data.Lam₁_le_N₃ h hKU hf))) le_sup_left
    exact h2 h1
  obtain ⟨y, hy, n, hn, rfl⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer
    (h.Y_le_normalizer_Nn hKU hf) hz'
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_of_mem_Y hKU hf hy
  refine ⟨a * n * l, mul_mem (mul_mem (h.I₀_le_Nn hKU hf ha) hn) (h.Lam₁_le_Nn hKU hf hl), b, hb, ?_⟩
  have e1 : n * b = b * n := h.comm_N₃_I₁ hKU hf (h.Nn_le_N₃ hKU hf hn) hb
  have e2 : l * b = b * l := h.comm_N₃_I₁ hKU hf (Data.Lam₁_le_N₃ h hKU hf hl) hb
  calc a * b * n * l = a * (b * n) * l := by group
    _ = a * (n * b) * l := by rw [← e1]
    _ = a * n * (b * l) := by group
    _ = a * n * (l * b) := by rw [← e2]
    _ = a * n * l * b := by group

include h hKU hf in
theorem Data.Hyp.card_I₁ : Nat.card ↥(d.Y ⊓ d.tc K₀) = 16 := by
  rw [← h.tc_I, Data.card_tc, h.card_Y_inf_K₀ hKU hf]

include h hKU in
theorem Data.Hyp.card_Nn : Nat.card (Data.Nn h hKU hf) = 15360 := by
  have hI : d.Y ⊓ d.tc K₀ ≤ normalizer (Data.Nn h hKU hf : Set G) := fun i hi =>
    h.N₃_le_normalizer_Nn hKU hf (h.Y_le_N₃ hKU hf hi.1)
  have hcard := PGrp.card_sup_mul_card_inf (A := d.Y ⊓ d.tc K₀) (B := Data.Nn h hKU hf) hI
  have hsup : (d.Y ⊓ d.tc K₀) ⊔ Data.Nn h hKU hf = Data.N₃ h hKU hf := by
    apply le_antisymm
    · exact sup_le (inf_le_left.trans (h.Y_le_N₃ hKU hf)) (h.Nn_le_N₃ hKU hf)
    · intro x hx
      obtain ⟨n, hn, i, hi, rfl⟩ := h.exists_Nn_mul_I₁ hKU hf hx
      have hc : n * i = i * n := h.comm_N₃_I₁ hKU hf (h.Nn_le_N₃ hKU hf hn) hi
      rw [hc]
      exact mul_mem (mem_sup_left hi) (mem_sup_right hn)
  rw [hsup, inf_comm (d.Y ⊓ d.tc K₀) (Data.Nn h hKU hf), h.Nn_inf_I₁ hKU hf, Subgroup.card_bot,
    mul_one, h.card_N₃ hKU hf, h.card_I₁ hKU hf] at hcard
  norm_num at hcard
  omega

include h hKU in
theorem Data.Hyp.exists_mul_of_mem_N₂ {x : G} (hx : x ∈ Data.N₂ h hKU hf) :
    ∃ n ∈ Data.Nn h hKU hf, ∃ m ∈ d.tc (Data.Nn h hKU hf), x = n * m :=
  KProd.exists_mul_of_mem_sup_of_comm (fun _ ha _ hb => h.comm_Nn_tcNn hKU hf ha hb) hx

include h hKU in
theorem Data.Hyp.tc_N₂ : d.tc (Data.N₂ h hKU hf) = Data.N₂ h hKU hf := by
  rw [Data.N₂, h.tc_sup, h.tc_tc, sup_comm]

theorem Data.Nn_le_N₂ : Data.Nn h hKU hf ≤ Data.N₂ h hKU hf := le_sup_left

theorem Data.tcNn_le_N₂ : d.tc (Data.Nn h hKU hf) ≤ Data.N₂ h hKU hf := le_sup_right

include h hKU in
theorem Data.Hyp.card_N₂ : Nat.card (Data.N₂ h hKU hf) = 15360 ^ 2 := by
  have hc : ∀ a ∈ Data.Nn h hKU hf, ∀ b ∈ d.tc (Data.Nn h hKU hf), a * b = b * a :=
    fun _ ha _ hb => h.comm_Nn_tcNn hKU hf ha hb
  rw [Data.N₂, ← Nat.card_congr (KProd.prodEquivSup _ _ hc (h.Nn_inf_tcNn hKU hf)).toEquiv,
    Nat.card_prod, Data.card_tc, h.card_Nn hKU hf]
  norm_num

include h hKU in
theorem Data.Hyp.Cv₂_le_N₂ : Data.Cv₂ h hKU hf ≤ Data.N₂ h hKU hf := fun z hz => by
  obtain ⟨n, hn, i, hi, hzni⟩ := h.exists_Nn_mul_I₁ hKU hf (Data.Cv₂_le_N₃ h hKU hf hz)
  rw [hzni]
  exact mul_mem (Data.Nn_le_N₂ h hKU hf hn) (Data.tcNn_le_N₂ h hKU hf (h.I₁_le_tcNn hKU hf hi))

include h hKU in
theorem Data.Hyp.D₂_le_N₂ : d.D₂ ≤ Data.N₂ h hKU hf := by
  rw [← h.Cv₁_sup_Cv₂ hKU hf]
  refine sup_le (fun x hx => ?_) (h.Cv₂_le_N₂ hKU hf)
  have h1 : d.t * x * d.t ∈ d.tc (Data.Cv₁ h hKU hf) :=
    (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hx)
  rw [h.tc_Cv₁ hKU hf] at h1
  have h2 : x ∈ d.tc (Data.N₂ h hKU hf) := (h.mem_tc).2 (h.Cv₂_le_N₂ hKU hf h1)
  rwa [h.tc_N₂ hKU hf] at h2

end Prod

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
