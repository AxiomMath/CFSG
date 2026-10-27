module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6U
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S5D

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem conj_conj_comm_of_commute {G : Type*} [Group G] {g g' : G} (hc : g * g' = g' * g)
    (y : G) : g' * (g * y * g⁻¹) * g'⁻¹ = g * (g' * y * g'⁻¹) * g⁻¹ := by
  calc g' * (g * y * g⁻¹) * g'⁻¹ = (g' * g) * y * (g' * g)⁻¹ := by group
    _ = (g * g') * y * (g * g')⁻¹ := by rw [hc]
    _ = g * (g' * y * g'⁻¹) * g⁻¹ := by group

@[expose] noncomputable def Data.Cv₁ (h : d.Hyp) (hKU : d.KUnitary)
    (hf : d.IsUnitaryFactor K₀) : Subgroup G :=
  ModSplit.liftFixG d.D₂ d.Y (Data.Lam₁ h hKU hf)

@[expose] noncomputable def Data.Cv₂ (h : d.Hyp) (hKU : d.KUnitary)
    (hf : d.IsUnitaryFactor K₀) : Subgroup G :=
  ModSplit.liftFixG d.D₂ d.Y (d.tc (Data.Lam₁ h hKU hf))

@[expose] noncomputable def Data.N₃ (h : d.Hyp) (hKU : d.KUnitary)
    (hf : d.IsUnitaryFactor K₀) : Subgroup G :=
  Data.Cv₂ h hKU hf ⊔ Data.Lam₁ h hKU hf

section Basic

variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.hD : d.D₁ ≤ normalizer (d.D₂ : Set G) :=
  h.D₁_le_normalizer_D₂ (h.comm_M_V₂_mem_W hKU) (fun m hm => h.M_le_normalizer_Y hKU hm)

include h hKU in
theorem Data.Hyp.Lam₁_le_normDY : Data.Lam₁ h hKU hf ≤ ModSplit.normDY d.D₂ d.Y :=
  le_inf (h.Lam₁_le_normalizer_D₂ hKU hf (h.hD hKU)) (h.Lam₁_le_normalizer_Y hKU hf)

include h hKU in
theorem Data.Hyp.tcLam₁_le_normDY : d.tc (Data.Lam₁ h hKU hf) ≤ ModSplit.normDY d.D₂ d.Y :=
  le_inf (h.tcLam₁_le_normalizer_D₂ hKU hf (h.hD hKU)) (h.tcLam₁_le_normalizer_Y hKU hf)

include h hKU in
theorem Data.Hyp.mem_Cv₁_iff {x : G} :
    x ∈ Data.Cv₁ h hKU hf ↔
      x ∈ d.D₂ ∧ ∀ g ∈ Data.Lam₁ h hKU hf, g * x * g⁻¹ * x⁻¹ ∈ d.Y :=
  ModSplit.mem_liftFixG_iff _ _ (h.Lam₁_le_normDY hKU hf)

include h hKU in
theorem Data.Hyp.mem_Cv₂_iff {x : G} :
    x ∈ Data.Cv₂ h hKU hf ↔
      x ∈ d.D₂ ∧ ∀ g ∈ d.tc (Data.Lam₁ h hKU hf), g * x * g⁻¹ * x⁻¹ ∈ d.Y :=
  ModSplit.mem_liftFixG_iff _ _ (h.tcLam₁_le_normDY hKU hf)

include h hKU in
theorem Data.Hyp.Cv₁_le_D₂ : Data.Cv₁ h hKU hf ≤ d.D₂ := fun _ hx =>
  ((h.mem_Cv₁_iff hKU hf).1 hx).1

include h hKU in
theorem Data.Hyp.Cv₂_le_D₂ : Data.Cv₂ h hKU hf ≤ d.D₂ := fun _ hx =>
  ((h.mem_Cv₂_iff hKU hf).1 hx).1

include h hKU in
theorem Data.Hyp.Y_le_Cv₂ : d.Y ≤ Data.Cv₂ h hKU hf := fun y hy =>
  (h.mem_Cv₂_iff hKU hf).2 ⟨h.Y_le_D₂ hy, fun g hg =>
    d.Y.mul_mem ((mem_normalizer_iff.1 (h.tcLam₁_le_normalizer_Y hKU hf hg) y).1 hy)
      (d.Y.inv_mem hy)⟩

include h hKU in
theorem Data.Hyp.card_Cv₂ : Nat.card (Data.Cv₂ h hKU hf) = 2 ^ 12 :=
  (h.splitting_D₂ hKU hf (h.hD hKU)).2.1

include h hKU in
theorem Data.Hyp.Cv₁_sup_Cv₂ : Data.Cv₁ h hKU hf ⊔ Data.Cv₂ h hKU hf = d.D₂ :=
  (h.splitting_D₂ hKU hf (h.hD hKU)).2.2.1

include h hKU in
theorem Data.Hyp.Cv₁_inf_Cv₂ : Data.Cv₁ h hKU hf ⊓ Data.Cv₂ h hKU hf = d.Y :=
  (h.splitting_D₂ hKU hf (h.hD hKU)).2.2.2

include h hKU in
theorem Data.Hyp.tcLam₁_le_normalizer_Cv₂ :
    d.tc (Data.Lam₁ h hKU hf) ≤ normalizer (Data.Cv₂ h hKU hf : Set G) := fun g hg =>
  mem_normalizer_fintype fun x hx => by
    have hx' := (h.mem_Cv₂_iff hKU hf).1 hx
    have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact (Data.Cv₂ h hKU hf).mul_mem (h.Y_le_Cv₂ hKU hf (hx'.2 g hg)) hx

include h hKU in
theorem Data.Hyp.Lam₁_le_normalizer_Cv₂ :
    Data.Lam₁ h hKU hf ≤ normalizer (Data.Cv₂ h hKU hf : Set G) := fun g hg =>
  mem_normalizer_fintype fun x hx => by
    have hx' := (h.mem_Cv₂_iff hKU hf).1 hx
    refine (h.mem_Cv₂_iff hKU hf).2 ⟨?_, fun g' hg' => ?_⟩
    · exact (mem_normalizer_iff.1 (h.Lam₁_le_normalizer_D₂ hKU hf (h.hD hKU) hg) x).1 hx'.1
    · have hc : g * g' = g' * g := hf.comm_elem g (Data.Lam₁_le_K₀ h hKU hf hg) g'
        (h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) hg')
      have e : g' * (g * x * g⁻¹) * g'⁻¹ * (g * x * g⁻¹)⁻¹ =
          g * (g' * x * g'⁻¹ * x⁻¹) * g⁻¹ := by
        rw [conj_conj_comm_of_commute hc x]
        group
      rw [e]
      exact (mem_normalizer_iff.1 (h.Lam₁_le_normalizer_Y hKU hf hg) _).1 (hx'.2 g' hg')

include h hKU in
theorem Data.Hyp.tcLam₁_le_normalizer_Cv₁ :
    d.tc (Data.Lam₁ h hKU hf) ≤ normalizer (Data.Cv₁ h hKU hf : Set G) := fun g' hg' =>
  mem_normalizer_fintype fun x hx => by
    have hx' := (h.mem_Cv₁_iff hKU hf).1 hx
    refine (h.mem_Cv₁_iff hKU hf).2 ⟨?_, fun g hg => ?_⟩
    · exact (mem_normalizer_iff.1 (h.tcLam₁_le_normalizer_D₂ hKU hf (h.hD hKU) hg') x).1 hx'.1
    · have hc : g * g' = g' * g := hf.comm_elem g (Data.Lam₁_le_K₀ h hKU hf hg) g'
        (h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) hg')
      have e : g * (g' * x * g'⁻¹) * g⁻¹ * (g' * x * g'⁻¹)⁻¹ =
          g' * (g * x * g⁻¹ * x⁻¹) * g'⁻¹ := by
        rw [← conj_conj_comm_of_commute hc x]
        group
      rw [e]
      exact (mem_normalizer_iff.1 (h.tcLam₁_le_normalizer_Y hKU hf hg') _).1 (hx'.2 g hg)

include h hKU in
theorem Data.Hyp.D₂_le_normalizer_Cv₂ : d.D₂ ≤ normalizer (Data.Cv₂ h hKU hf : Set G) :=
  fun g hg => mem_normalizer_fintype fun x hx => by
    have hx' := (h.mem_Cv₂_iff hKU hf).1 hx
    have hK := h.comm_M_V₂_mem_W hKU
    have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact (Data.Cv₂ h hKU hf).mul_mem (h.Y_le_Cv₂ hKU hf (h.D₂_commutator_mem_Y hK hg hx'.1))
      hx

end Basic

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
