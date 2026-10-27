module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7E

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem mem_normalizer_commutator_of_mem {N : Subgroup G} {y : G}
    (hy : y ∈ normalizer (N : Set G)) : y ∈ normalizer ((⁅N, N⁆ : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  have h1 : (MulAut.conj y).toMonoidHom x ∈ (⁅N, N⁆).map (MulAut.conj y).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [Subgroup.map_commutator] at h1
  have hN : N.map (MulAut.conj y).toMonoidHom ≤ N := by
    rintro _ ⟨n, hn, rfl⟩
    exact (mem_normalizer_iff.1 hy n).1 hn
  exact Subgroup.commutator_mono hN hN h1

section Inter



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.card_Lam₁ : Nat.card (Data.Lam₁ h hKU hf) = 60 := by
  have h4 : Nat.card CFSG.Fischer.F4 = 4 := by
    rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card]
  rw [Nat.card_congr (Data.lamEquiv h hKU hf).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h4]
  norm_num

include h hKU in
theorem Data.Hyp.eq_one_of_mul_mem_D₂' {g μ : G} (hg : g ∈ Data.Lam₁ h hKU hf)
    (hμ : μ ∈ d.tc (Data.Lam₁ h hKU hf)) (hgμ : g * μ ∈ d.D₂) : g = 1 ∧ μ = 1 := by
  refine ⟨h.eq_one_of_mul_mem_D₂ hKU hf hg hμ hgμ, ?_⟩
  have hg' : d.t * g * d.t ∈ d.tc (Data.Lam₁ h hKU hf) :=
    (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hg)
  have hμ' : d.t * μ * d.t ∈ Data.Lam₁ h hKU hf := (h.mem_tc).1 hμ
  have hcgm : g * μ = μ * g := hf.comm_elem g (Data.Lam₁_le_K₀ h hKU hf hg) μ
    (h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) hμ)
  have hD : (d.t * μ * d.t) * (d.t * g * d.t) ∈ d.D₂ := by
    rw [h.t_conj_mul', ← hcgm]
    exact h.t_conj_mem_D₂ hgμ
  have h1 := h.eq_one_of_mul_mem_D₂ hKU hf hμ' hg' hD
  have : μ = d.t * (d.t * μ * d.t) * d.t := (h.t_conj_conj μ).symm
  rw [this, h1]
  simp [h.t_mul_t]

include h hKU in
theorem Data.Hyp.Cv₂_inf_Lam₁ : Data.Cv₂ h hKU hf ⊓ Data.Lam₁ h hKU hf = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxC, hxL⟩
  exact Subgroup.mem_bot.2 (h.eq_one_of_mul_mem_D₂ hKU hf hxL (d.tc _).one_mem
    (by rw [mul_one]; exact h.Cv₂_le_D₂ hKU hf hxC))

include h hKU in
theorem Data.Hyp.card_N₃ : Nat.card (Data.N₃ h hKU hf) = 2 ^ 12 * 60 := by
  have := PGrp.card_sup_mul_card_inf (A := Data.Lam₁ h hKU hf) (B := Data.Cv₂ h hKU hf)
    (h.Lam₁_le_normalizer_Cv₂ hKU hf)
  rw [inf_comm, h.Cv₂_inf_Lam₁ hKU hf, Subgroup.card_bot, mul_one, h.card_Lam₁ hKU hf,
    h.card_Cv₂ hKU hf] at this
  rw [Data.N₃, sup_comm, this]
  ring

include h hKU in
theorem Data.Hyp.Cv₁_le_normalizer_N₃ :
    Data.Cv₁ h hKU hf ≤ normalizer (Data.N₃ h hKU hf : Set G) := fun z₁ hz₁ =>
  mem_normalizer_fintype fun x hx => by
    obtain ⟨z, hz, l, hl, rfl⟩ := h.exists_mul_of_mem_N₃ hKU hf hx
    have hz1 : z₁ * z * z₁⁻¹ ∈ Data.Cv₂ h hKU hf :=
      (mem_normalizer_iff.1 (h.D₂_le_normalizer_Cv₂ hKU hf (h.Cv₁_le_D₂ hKU hf hz₁)) z).1 hz
    have hy : z₁ * l * z₁⁻¹ * l⁻¹ ∈ d.Y := by
      have h1 := ((h.mem_Cv₁_iff hKU hf).1 hz₁).2 l hl
      have e : z₁ * l * z₁⁻¹ * l⁻¹ = (l * z₁ * l⁻¹ * z₁⁻¹)⁻¹ := by group
      rw [e]
      exact d.Y.inv_mem h1
    have e2 : z₁ * (z * l) * z₁⁻¹ = (z₁ * z * z₁⁻¹) * ((z₁ * l * z₁⁻¹ * l⁻¹) * l) := by group
    rw [e2]
    exact (Data.N₃ h hKU hf).mul_mem (Data.Cv₂_le_N₃ h hKU hf hz1)
      ((Data.N₃ h hKU hf).mul_mem (h.Y_le_N₃ hKU hf hy) (Data.Lam₁_le_N₃ h hKU hf hl))

include h hKU in
theorem Data.Hyp.tcLam₁_le_normalizer_N₃ :
    d.tc (Data.Lam₁ h hKU hf) ≤ normalizer (Data.N₃ h hKU hf : Set G) := fun μ hμ =>
  mem_normalizer_fintype fun x hx => by
    obtain ⟨z, hz, l, hl, rfl⟩ := h.exists_mul_of_mem_N₃ hKU hf hx
    have hc : l * μ = μ * l := hf.comm_elem l (Data.Lam₁_le_K₀ h hKU hf hl) μ
      (h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) hμ)
    have hzC : μ * z * μ⁻¹ ∈ Data.Cv₂ h hKU hf :=
      (mem_normalizer_iff.1 (h.tcLam₁_le_normalizer_Cv₂ hKU hf hμ) z).1 hz
    have hlμ : μ * l * μ⁻¹ = l := by rw [← hc]; group
    have e : μ * (z * l) * μ⁻¹ = (μ * z * μ⁻¹) * (μ * l * μ⁻¹) := by group
    rw [e, hlμ]
    exact (Data.N₃ h hKU hf).mul_mem (Data.Cv₂_le_N₃ h hKU hf hzC) (Data.Lam₁_le_N₃ h hKU hf hl)

include h hKU in
theorem Data.Hyp.tc_N₃ :
    d.tc (Data.N₃ h hKU hf) = Data.Cv₁ h hKU hf ⊔ d.tc (Data.Lam₁ h hKU hf) := by
  rw [Data.N₃, h.tc_sup, h.tc_Cv₂]

include h hKU in
theorem Data.Hyp.tcN₃_le_normalizer_N₃ :
    d.tc (Data.N₃ h hKU hf) ≤ normalizer (Data.N₃ h hKU hf : Set G) := by
  rw [h.tc_N₃ hKU hf]
  exact sup_le (h.Cv₁_le_normalizer_N₃ hKU hf) (h.tcLam₁_le_normalizer_N₃ hKU hf)

include h hKU in
theorem Data.Hyp.N₃_le_normalizer_tcN₃ :
    Data.N₃ h hKU hf ≤ normalizer (d.tc (Data.N₃ h hKU hf) : Set G) := fun g hg =>
  mem_normalizer_fintype fun x hx => by
    have hx' : d.t * x * d.t ∈ Data.N₃ h hKU hf := (h.mem_tc).1 hx
    have hg' : d.t * g * d.t ∈ d.tc (Data.N₃ h hKU hf) :=
      (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hg)
    have e : d.t * (g * x * g⁻¹) * d.t = (d.t * g * d.t) * (d.t * x * d.t) * (d.t * g * d.t)⁻¹ := by
      rw [h.t_conj_inv', h.t_conj_mul', h.t_conj_mul']
    show g * x * g⁻¹ ∈ d.tc (Data.N₃ h hKU hf)
    rw [h.mem_tc, e]
    exact (mem_normalizer_iff.1 (h.tcN₃_le_normalizer_N₃ hKU hf hg') _).1 hx'


include h hKU in
theorem Data.Hyp.Y_le_tcN₃ : d.Y ≤ d.tc (Data.N₃ h hKU hf) := fun y hy => by
  rw [h.mem_tc]
  exact h.Y_le_N₃ hKU hf (h.t_conj_mem_Y hy)

include h hKU in
theorem Data.Hyp.N₃_inf_tcN₃ : Data.N₃ h hKU hf ⊓ d.tc (Data.N₃ h hKU hf) = d.Y := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    rw [h.tc_N₃ hKU hf] at hx2
    obtain ⟨z, hz, g, hg, rfl⟩ := h.exists_mul_of_mem_N₃ hKU hf hx1
    obtain ⟨μ, hμ, z', hz', hx⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer
      (h.tcLam₁_le_normalizer_Cv₁ hKU hf) (by rw [sup_comm]; exact hx2)
    have hz'' : μ * z' * μ⁻¹ ∈ Data.Cv₁ h hKU hf :=
      (mem_normalizer_iff.1 (h.tcLam₁_le_normalizer_Cv₁ hKU hf hμ) z').1 hz'
    have e : z * g = (μ * z' * μ⁻¹) * μ := by rw [hx]; group
    have hgi : g⁻¹ ∈ Data.Lam₁ h hKU hf := (Data.Lam₁ h hKU hf).inv_mem hg
    have hcgm : g⁻¹ * μ = μ * g⁻¹ := hf.comm_elem g⁻¹ (Data.Lam₁_le_K₀ h hKU hf hgi) μ
      (h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) hμ)
    have hD : g⁻¹ * μ ∈ d.D₂ := by
      have e2 : μ * g⁻¹ = (μ * z' * μ⁻¹)⁻¹ * z := by
        calc μ * g⁻¹ = (μ * z' * μ⁻¹)⁻¹ * (((μ * z' * μ⁻¹) * μ)) * g⁻¹ := by group
          _ = (μ * z' * μ⁻¹)⁻¹ * (z * g) * g⁻¹ := by rw [← e]
          _ = (μ * z' * μ⁻¹)⁻¹ * z := by group
      rw [hcgm, e2]
      exact d.D₂.mul_mem (d.D₂.inv_mem (h.Cv₁_le_D₂ hKU hf hz'')) (h.Cv₂_le_D₂ hKU hf hz)
    obtain ⟨hg1, hμ1⟩ := h.eq_one_of_mul_mem_D₂' hKU hf hgi hμ hD
    have hg1' : g = 1 := inv_eq_one.1 hg1
    have hzz' : z = z' := by
      have := e
      rw [hg1', hμ1] at this
      simpa using this
    have hzC : z ∈ Data.Cv₁ h hKU hf ⊓ Data.Cv₂ h hKU hf := ⟨hzz' ▸ hz', hz⟩
    rw [h.Cv₁_inf_Cv₂ hKU hf] at hzC
    rw [hg1', mul_one]
    exact hzC
  · exact le_inf (h.Y_le_N₃ hKU hf) (h.Y_le_tcN₃ hKU hf)

include h hKU in
theorem Data.Hyp.Nn_inf_Y : Data.Nn h hKU hf ⊓ d.Y = d.Y ⊓ K₀ := by
  apply le_antisymm
  · rintro y ⟨hyN, hyY⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_of_mem_Y hKU hf hyY
    have hbN : b ∈ Data.Nn h hKU hf := by
      have := (Data.Nn h hKU hf).mul_mem ((Data.Nn h hKU hf).inv_mem (h.I₀_le_Nn hKU hf ha)) hyN
      simpa using this
    have hb1 : b ∈ Data.Nn h hKU hf ⊓ (d.Y ⊓ d.tc K₀) := ⟨hbN, hb⟩
    rw [h.Nn_inf_I₁ hKU hf, Subgroup.mem_bot] at hb1
    rw [hb1, mul_one]
    exact ha
  · intro x hx
    exact ⟨h.I₀_le_Nn hKU hf hx, hx.1⟩

include h hKU in
theorem Data.Hyp.tcNn_eq :
    d.tc (Data.Nn h hKU hf) = ⁅d.tc (Data.N₃ h hKU hf), d.tc (Data.N₃ h hKU hf)⁆ :=
  Subgroup.map_commutator _ _ _

include h hKU in
theorem Data.Hyp.tcNn_le_tcN₃ : d.tc (Data.Nn h hKU hf) ≤ d.tc (Data.N₃ h hKU hf) :=
  h.tc_mono (h.Nn_le_N₃ hKU hf)

include h hKU in
theorem Data.Hyp.tcNn_inf_Y : d.tc (Data.Nn h hKU hf) ⊓ d.Y = d.Y ⊓ d.tc K₀ := by
  apply le_antisymm
  · rintro z ⟨hzT, hzY⟩
    have h1 : d.t * z * d.t ∈ Data.Nn h hKU hf ⊓ d.Y := ⟨(h.mem_tc).1 hzT, h.t_conj_mem_Y hzY⟩
    rw [h.Nn_inf_Y hKU hf] at h1
    exact ⟨hzY, (h.mem_tc).2 h1.2⟩
  · rintro z ⟨hzY, hzK⟩
    refine ⟨(h.mem_tc).2 (h.I₀_le_Nn hKU hf ⟨h.t_conj_mem_Y hzY, (h.mem_tc).1 hzK⟩), hzY⟩

include h hKU in
theorem Data.Hyp.Nn_inf_tcNn : Data.Nn h hKU hf ⊓ d.tc (Data.Nn h hKU hf) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzN, hzT⟩
  have hz3 : z ∈ Data.N₃ h hKU hf ⊓ d.tc (Data.N₃ h hKU hf) :=
    ⟨h.Nn_le_N₃ hKU hf hzN, h.tcNn_le_tcN₃ hKU hf hzT⟩
  rw [h.N₃_inf_tcN₃ hKU hf] at hz3
  have h1 : z ∈ d.Y ⊓ K₀ := by
    rw [← h.Nn_inf_Y hKU hf]
    exact ⟨hzN, hz3⟩
  have h2 : z ∈ d.Y ⊓ d.tc K₀ := by
    rw [← h.tcNn_inf_Y hKU hf]
    exact ⟨hzT, hz3⟩
  have h3 : z ∈ K₀ ⊓ d.tc K₀ := ⟨h1.2, h2.2⟩
  rw [hf.inf_tc] at h3
  exact h3

include h hKU in
theorem Data.Hyp.comm_Nn_tcNn {x y : G} (hx : x ∈ Data.Nn h hKU hf)
    (hy : y ∈ d.tc (Data.Nn h hKU hf)) : x * y = y * x := by
  have hyN : y ∈ normalizer (Data.Nn h hKU hf : Set G) := by
    have hy3 : y ∈ d.tc (Data.N₃ h hKU hf) := h.tcNn_le_tcN₃ hKU hf hy
    exact mem_normalizer_commutator_of_mem (h.tcN₃_le_normalizer_N₃ hKU hf hy3)
  have hxN : x ∈ normalizer (d.tc (Data.Nn h hKU hf) : Set G) := by
    rw [h.tcNn_eq hKU hf]
    exact mem_normalizer_commutator_of_mem
      (h.N₃_le_normalizer_tcN₃ hKU hf (h.Nn_le_N₃ hKU hf hx))
  have hc1 : x * y * x⁻¹ * y⁻¹ ∈ Data.Nn h hKU hf := by
    have h1 : y * x⁻¹ * y⁻¹ ∈ Data.Nn h hKU hf :=
      (mem_normalizer_iff.1 hyN x⁻¹).1 ((Data.Nn h hKU hf).inv_mem hx)
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact (Data.Nn h hKU hf).mul_mem hx h1
  have hc2 : x * y * x⁻¹ * y⁻¹ ∈ d.tc (Data.Nn h hKU hf) := by
    have h1 : x * y * x⁻¹ ∈ d.tc (Data.Nn h hKU hf) := (mem_normalizer_iff.1 hxN y).1 hy
    exact (d.tc (Data.Nn h hKU hf)).mul_mem h1 ((d.tc (Data.Nn h hKU hf)).inv_mem hy)
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ Data.Nn h hKU hf ⊓ d.tc (Data.Nn h hKU hf) := ⟨hc1, hc2⟩
  rw [h.Nn_inf_tcNn hKU hf, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 (by simpa [commutatorElement_def] using h3)

end Inter

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
