module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7C
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7A

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

section Stab

variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.exists_mul_of_mem_N₃ {x : G} (hx : x ∈ Data.N₃ h hKU hf) :
    ∃ z ∈ Data.Cv₂ h hKU hf, ∃ g ∈ Data.Lam₁ h hKU hf, x = z * g := by
  have hx' : x ∈ Data.Lam₁ h hKU hf ⊔ Data.Cv₂ h hKU hf := by
    rw [sup_comm]
    exact hx
  obtain ⟨g, hg, z, hz, rfl⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer
    (h.Lam₁_le_normalizer_Cv₂ hKU hf) hx'
  exact ⟨g * z * g⁻¹, (mem_normalizer_iff.1 (h.Lam₁_le_normalizer_Cv₂ hKU hf hg) z).1 hz, g, hg,
    by group⟩

theorem Data.Cv₂_le_N₃ : Data.Cv₂ h hKU hf ≤ Data.N₃ h hKU hf := le_sup_left

theorem Data.Lam₁_le_N₃ : Data.Lam₁ h hKU hf ≤ Data.N₃ h hKU hf := le_sup_right

include h hKU in
theorem Data.Hyp.Y_le_N₃ : d.Y ≤ Data.N₃ h hKU hf := (h.Y_le_Cv₂ hKU hf).trans le_sup_left

include h hKU in
theorem Data.Hyp.comm_N₃_tcLam₁_mem_Y {g μ : G} (hg : g ∈ Data.N₃ h hKU hf)
    (hμ : μ ∈ d.tc (Data.Lam₁ h hKU hf)) : g * μ * g⁻¹ * μ⁻¹ ∈ d.Y := by
  obtain ⟨z, hz, l, hl, rfl⟩ := h.exists_mul_of_mem_N₃ hKU hf hg
  have hc : l * μ = μ * l := hf.comm_elem l (Data.Lam₁_le_K₀ h hKU hf hl) μ
    (h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) hμ)
  have hzμ : μ * z * μ⁻¹ * z⁻¹ ∈ d.Y := ((h.mem_Cv₂_iff hKU hf).1 hz).2 μ hμ
  have hlm : l * μ * l⁻¹ = μ := by rw [hc]; group
  have e : z * l * μ * (z * l)⁻¹ * μ⁻¹ = (μ * z * μ⁻¹ * z⁻¹)⁻¹ := by
    calc z * l * μ * (z * l)⁻¹ * μ⁻¹ = z * (l * μ * l⁻¹) * z⁻¹ * μ⁻¹ := by group
      _ = z * μ * z⁻¹ * μ⁻¹ := by rw [hlm]
      _ = (μ * z * μ⁻¹ * z⁻¹)⁻¹ := by group
  rw [e]
  exact d.Y.inv_mem hzμ

include h hKU in
theorem Data.Hyp.comm_N₃_I₁ {g i : G} (hg : g ∈ Data.N₃ h hKU hf) (hi : i ∈ d.Y ⊓ d.tc K₀) :
    g * i = i * g := by
  obtain ⟨z, hz, l, hl, rfl⟩ := h.exists_mul_of_mem_N₃ hKU hf hg
  have hzi : z * i = i * z :=
    (mem_centralizer_iff.1 (D₂_le_centralizer_Y (h.Cv₂_le_D₂ hKU hf hz)) i hi.1).symm
  have hli : l * i = i * l := hf.comm_elem l (Data.Lam₁_le_K₀ h hKU hf hl) i hi.2
  calc z * l * i = z * (l * i) := by group
    _ = z * (i * l) := by rw [hli]
    _ = (z * i) * l := by group
    _ = (i * z) * l := by rw [hzi]
    _ = i * (z * l) := by group

include h hKU in
theorem Data.Hyp.tcLam₁_le_normalizer_I₁ :
    d.tc (Data.Lam₁ h hKU hf) ≤ normalizer ((d.Y ⊓ d.tc K₀ : Subgroup G) : Set G) := fun g hg =>
  mem_normalizer_fintype fun x hx => by
    have hgK : g ∈ d.tc K₀ := h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) hg
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (h.tcLam₁_le_normalizer_Y hKU hf hg) x).1 hx.1,
      (d.tc K₀).mul_mem ((d.tc K₀).mul_mem hgK hx.2) ((d.tc K₀).inv_mem hgK)⟩

include h hKU in
theorem Data.Hyp.exists_mul_of_mem_Pp {x : G} (hx : x ∈ Data.Pp h hKU hf) :
    ∃ μ ∈ d.tc (Data.Lam₁ h hKU hf), ∃ i ∈ d.Y ⊓ d.tc K₀, x = μ * i :=
  PGrp.exists_mul_of_mem_sup_of_le_normalizer (h.tcLam₁_le_normalizer_I₁ hKU hf) hx

include h hKU in
theorem Data.Hyp.Pp_le_tc : Data.Pp h hKU hf ≤ d.tc K₀ :=
  sup_le (h.tc_mono (Data.Lam₁_le_K₀ h hKU hf)) inf_le_right

include h hKU in
theorem Data.Hyp.conj_tcLam₁_mem_Pp {g μ : G} (hg : g ∈ Data.N₃ h hKU hf)
    (hμ : μ ∈ d.tc (Data.Lam₁ h hKU hf)) : g * μ * g⁻¹ ∈ Data.Pp h hKU hf := by
  set X : Subgroup G := (d.tc (Data.Lam₁ h hKU hf)).map (MulAut.conj g).toMonoidHom with hX
  have hXperf : ⁅X, X⁆ = X := by
    rw [hX, ← Subgroup.map_commutator, h.tcLam₁_perfect hKU hf]
  have hXle : X ≤ (d.Y ⊓ K₀) ⊔ Data.Pp h hKU hf := by
    rintro _ ⟨μ', hμ', rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := h.exists_mul_of_mem_Y hKU hf
      (h.comm_N₃_tcLam₁_mem_Y hKU hf hg hμ')
    have e : (MulAut.conj g).toMonoidHom μ' = a * (b * μ') := by
      show g * μ' * g⁻¹ = a * (b * μ')
      calc g * μ' * g⁻¹ = (g * μ' * g⁻¹ * μ'⁻¹) * μ' := by group
        _ = (a * b) * μ' := by rw [hab]
        _ = a * (b * μ') := by group
    rw [e]
    exact mul_mem (mem_sup_left ha)
      (mem_sup_right (mul_mem (mem_sup_right hb) (mem_sup_left hμ')))
  have hXP : X ≤ Data.Pp h hKU hf :=
    le_of_perfect_le_sup_of_comm (A := d.Y ⊓ K₀) (B := Data.Pp h hKU hf)
      (fun a ha b hb => hf.comm_elem a ha.2 b (h.Pp_le_tc hKU hf hb))
      (fun a ha a' ha' => h.Y_comm ha.1 ha'.1)
      (by
        rw [eq_bot_iff]
        intro x hx
        have hx1 : x ∈ K₀ ⊓ d.tc K₀ := ⟨hx.1.2, h.Pp_le_tc hKU hf hx.2⟩
        rw [hf.inf_tc] at hx1
        exact hx1)
      hXperf hXle
  exact hXP ⟨μ, hμ, rfl⟩

include h hKU in
theorem Data.Hyp.N₃_le_normalizer_Pp :
    ∀ g ∈ Data.N₃ h hKU hf, ∀ p ∈ Data.Pp h hKU hf, g * p * g⁻¹ ∈ Data.Pp h hKU hf := by
  intro g hg p hp
  obtain ⟨μ, hμ, i, hi, rfl⟩ := h.exists_mul_of_mem_Pp hKU hf hp
  have hgi : g * i * g⁻¹ = i := by rw [h.comm_N₃_I₁ hKU hf hg hi]; group
  have e : g * (μ * i) * g⁻¹ = (g * μ * g⁻¹) * (g * i * g⁻¹) := by group
  rw [e, hgi]
  exact mul_mem (h.conj_tcLam₁_mem_Pp hKU hf hg hμ) (mem_sup_right hi)

include h hKU in
theorem Data.Hyp.stable_N₃_Pp :
    ∀ g ∈ Data.N₃ h hKU hf, ∀ p ∈ Data.Pp h hKU hf, g * p * g⁻¹ * p⁻¹ ∈ d.Y ⊓ d.tc K₀ := by
  intro g hg p hp
  obtain ⟨μ, hμ, i, hi, rfl⟩ := h.exists_mul_of_mem_Pp hKU hf hp
  have hgi : g * i * g⁻¹ = i := by rw [h.comm_N₃_I₁ hKU hf hg hi]; group
  have e : g * (μ * i) * g⁻¹ * (μ * i)⁻¹ = (g * μ * g⁻¹) * μ⁻¹ := by
    calc g * (μ * i) * g⁻¹ * (μ * i)⁻¹ = (g * μ * g⁻¹) * (g * i * g⁻¹) * i⁻¹ * μ⁻¹ := by group
      _ = (g * μ * g⁻¹) * i * i⁻¹ * μ⁻¹ := by rw [hgi]
      _ = (g * μ * g⁻¹) * μ⁻¹ := by group
  rw [e]
  refine Subgroup.mem_inf.2 ⟨h.comm_N₃_tcLam₁_mem_Y hKU hf hg hμ, ?_⟩
  have h1 : g * μ * g⁻¹ ∈ d.tc K₀ := h.Pp_le_tc hKU hf (h.conj_tcLam₁_mem_Pp hKU hf hg hμ)
  have h2 : μ ∈ d.tc K₀ := h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) hμ
  exact (d.tc K₀).mul_mem h1 ((d.tc K₀).inv_mem h2)

include h hKU in
theorem Data.Hyp.Nn_le_centralizer_Pp :
    Data.Nn h hKU hf ≤ centralizer (Data.Pp h hKU hf : Set G) :=
  commutator_le_centralizer_of_stable (N := Data.N₃ h hKU hf) (P := Data.Pp h hKU hf)
    (I := d.Y ⊓ d.tc K₀) (fun i hi i' hi' => h.Y_comm hi.1 hi'.1)
    (fun g hg i hi => h.comm_N₃_I₁ hKU hf hg hi) (h.N₃_le_normalizer_Pp hKU hf)
    (h.stable_N₃_Pp hKU hf)

include h hKU in
theorem Data.Hyp.Lam₁_le_Nn : Data.Lam₁ h hKU hf ≤ Data.Nn h hKU hf := by
  rw [← h.Lam₁_perfect hKU hf]
  exact Subgroup.commutator_mono (Data.Lam₁_le_N₃ h hKU hf) (Data.Lam₁_le_N₃ h hKU hf)

include h hKU in
theorem Data.Hyp.Nn_le_N₃ : Data.Nn h hKU hf ≤ Data.N₃ h hKU hf :=
  Subgroup.commutator_le_self _

include h hKU in
theorem Data.Hyp.comm_Nn_tcLam₁ {x μ : G} (hx : x ∈ Data.Nn h hKU hf)
    (hμ : μ ∈ d.tc (Data.Lam₁ h hKU hf)) : x * μ = μ * x :=
  (mem_centralizer_iff.1 (h.Nn_le_centralizer_Pp hKU hf hx) μ (mem_sup_left hμ)).symm

end Stab

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
