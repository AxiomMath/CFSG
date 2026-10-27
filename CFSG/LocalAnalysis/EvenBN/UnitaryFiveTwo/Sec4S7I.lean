module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7H

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem eq_of_mul_eq_mul_of_inf_eq_bot {G : Type*} [Group G] {A B : Subgroup G}
    (hi : A ⊓ B = ⊥) {a a' b b' : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (e : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [e]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
  rw [hi, Subgroup.mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  exact ⟨h3, mul_left_cancel (h3 ▸ e)⟩

section Delta



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.t_conj_mem_tcNn {n : G} (hn : n ∈ Data.Nn h hKU hf) :
    d.t * n * d.t ∈ d.tc (Data.Nn h hKU hf) :=
  (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hn)

@[expose] noncomputable def Data.delta (h : d.Hyp) (hKU : d.KUnitary)
    (hf : d.IsUnitaryFactor K₀) : ↥(Data.Nn h hKU hf) →* G :=
  MonoidHom.mk' (fun n => (n : G) * (d.t * (n : G) * d.t)) fun a b => by
    have hc : (b : G) * (d.t * (a : G) * d.t) = (d.t * (a : G) * d.t) * (b : G) :=
      h.comm_Nn_tcNn hKU hf b.2 (h.t_conj_mem_tcNn hKU hf a.2)
    show (a : G) * (b : G) * (d.t * ((a : G) * (b : G)) * d.t) =
      ((a : G) * (d.t * (a : G) * d.t)) * ((b : G) * (d.t * (b : G) * d.t))
    rw [← h.t_conj_mul']
    calc (a : G) * (b : G) * ((d.t * (a : G) * d.t) * (d.t * (b : G) * d.t))
        = (a : G) * ((b : G) * (d.t * (a : G) * d.t)) * (d.t * (b : G) * d.t) := by group
      _ = (a : G) * ((d.t * (a : G) * d.t) * (b : G)) * (d.t * (b : G) * d.t) := by rw [hc]
      _ = ((a : G) * (d.t * (a : G) * d.t)) * ((b : G) * (d.t * (b : G) * d.t)) := by group

include h hKU in
theorem Data.Hyp.delta_eq_mul (n : ↥(Data.Nn h hKU hf)) :
    Data.delta h hKU hf n = (n : G) * (d.t * (n : G) * d.t) := rfl

include h hKU in
theorem Data.Hyp.delta_injective : Function.Injective (Data.delta h hKU hf) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have h1 : (n : G) * (d.t * (n : G) * d.t) = 1 := hn
  have h2 : (n : G) ∈ d.tc (Data.Nn h hKU hf) := by
    have : (n : G) = (d.t * (n : G) * d.t)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (d.tc _).inv_mem (h.t_conj_mem_tcNn hKU hf n.2)
  have h3 : (n : G) ∈ Data.Nn h hKU hf ⊓ d.tc (Data.Nn h hKU hf) := ⟨n.2, h2⟩
  rw [h.Nn_inf_tcNn hKU hf, Subgroup.mem_bot] at h3
  exact Subtype.ext h3

include h hKU in
theorem Data.Hyp.delta_mem_H (n : ↥(Data.Nn h hKU hf)) :
    Data.delta h hKU hf n ∈ d.H := by
  have hc : (n : G) * (d.t * (n : G) * d.t) = (d.t * (n : G) * d.t) * (n : G) :=
    h.comm_Nn_tcNn hKU hf n.2 (h.t_conj_mem_tcNn hKU hf n.2)
  refine mem_centralizer_singleton_iff.2 ?_
  have e : d.t * ((n : G) * (d.t * (n : G) * d.t)) * d.t = (n : G) * (d.t * (n : G) * d.t) := by
    calc d.t * ((n : G) * (d.t * (n : G) * d.t)) * d.t
        = (d.t * (n : G) * d.t) * (n : G) * (d.t * d.t) := by group
      _ = (d.t * (n : G) * d.t) * (n : G) := by rw [h.t_mul_t, mul_one]
      _ = (n : G) * (d.t * (n : G) * d.t) := hc.symm
  show (n : G) * (d.t * (n : G) * d.t) * d.t = d.t * ((n : G) * (d.t * (n : G) * d.t))
  calc (n : G) * (d.t * (n : G) * d.t) * d.t
      = (d.t * ((n : G) * (d.t * (n : G) * d.t)) * d.t) * d.t := by rw [e]
    _ = d.t * ((n : G) * (d.t * (n : G) * d.t)) := by
      rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]

include h hKU in
theorem Data.Hyp.range_delta :
    (Data.delta h hKU hf).range = Data.N₂ h hKU hf ⊓ d.H := by
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    exact ⟨mul_mem (Data.Nn_le_N₂ h hKU hf n.2)
      (Data.tcNn_le_N₂ h hKU hf (h.t_conj_mem_tcNn hKU hf n.2)), h.delta_mem_H hKU hf n⟩
  · rintro x ⟨hx, hxH⟩
    obtain ⟨n, hn, m, hm, rfl⟩ := h.exists_mul_of_mem_N₂ hKU hf hx
    have hxt' : d.t * (n * m) = (n * m) * d.t := (mem_centralizer_singleton_iff.1 hxH).symm
    have hxt : d.t * (n * m) * d.t = n * m := by
      rw [hxt', mul_assoc, h.t_mul_t, mul_one]
    have htmt : d.t * m * d.t ∈ Data.Nn h hKU hf := (h.mem_tc).1 hm
    have htnt : d.t * n * d.t ∈ d.tc (Data.Nn h hKU hf) := h.t_conj_mem_tcNn hKU hf hn
    have hcomm : (d.t * m * d.t) * (d.t * n * d.t) = (d.t * n * d.t) * (d.t * m * d.t) :=
      (h.comm_Nn_tcNn hKU hf htmt htnt).symm.symm
    have e : n * m = (d.t * m * d.t) * (d.t * n * d.t) := by
      rw [hcomm, h.t_conj_mul', hxt]
    obtain ⟨-, hmn⟩ := eq_of_mul_eq_mul_of_inf_eq_bot (h.Nn_inf_tcNn hKU hf) hn htmt hm htnt e
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [h.delta_eq_mul hKU hf]
    show n * (d.t * n * d.t) = n * m
    rw [hmn]

include h hKU in
theorem Data.Hyp.delta_mem_A₂_sup_K₂ (n : ↥(Data.Nn h hKU hf)) :
    Data.delta h hKU hf n ∈ d.A₂ ⊔ d.K₂ := by
  obtain ⟨z, hz, l, hl, hn⟩ := h.exists_mul_of_mem_N₃ hKU hf (h.Nn_le_N₃ hKU hf n.2)
  have hzt : d.t * z * d.t ∈ Data.Cv₁ h hKU hf := by
    have : z ∈ d.tc (Data.Cv₁ h hKU hf) := by
      rw [h.tc_Cv₁ hKU hf]
      exact hz
    exact (h.mem_tc).1 this
  have hD₂l : l * (d.t * z * d.t) * l⁻¹ ∈ d.D₂ :=
    (mem_normalizer_iff.1 (h.Lam₁_le_normalizer_D₂ hKU hf (h.hD hKU) hl) _).1
      (h.Cv₁_le_D₂ hKU hf hzt)
  have hθ : l * (d.t * l * d.t) ∈ d.K₂ := by
    have := Data.theta_mem_K₂_of_mem_Lam₁ h hKU hf ⟨l, Data.Lam₁_le_K₀ h hKU hf hl⟩ hl
    rwa [Data.theta_apply] at this
  have hd₀ : z * (l * (d.t * z * d.t) * l⁻¹) ∈ d.D₂ :=
    d.D₂.mul_mem (h.Cv₂_le_D₂ hKU hf hz) hD₂l
  have hKH : d.K₂ ≤ d.H := fun k hk => h.L_le_H (d.pull_le_L _ hk)
  have e : Data.delta h hKU hf n =
      (z * (l * (d.t * z * d.t) * l⁻¹)) * (l * (d.t * l * d.t)) := by
    rw [h.delta_eq_mul hKU hf]
    show (n : G) * (d.t * (n : G) * d.t) = _
    rw [hn, ← h.t_conj_mul' z l]
    group
  have hd₀H : z * (l * (d.t * z * d.t) * l⁻¹) ∈ d.H := by
    have : z * (l * (d.t * z * d.t) * l⁻¹) =
        Data.delta h hKU hf n * (l * (d.t * l * d.t))⁻¹ := by
      rw [e]
      group
    rw [this]
    exact d.H.mul_mem (h.delta_mem_H hKU hf n) (d.H.inv_mem (hKH hθ))
  have hA : z * (l * (d.t * z * d.t) * l⁻¹) ∈ d.A₂ := by
    rw [← h.D₂_inf_H]
    exact ⟨hd₀, hd₀H⟩
  rw [e]
  exact mul_mem (mem_sup_left hA) (mem_sup_right hθ)

include h hKU in
theorem Data.Hyp.Q₀_le_Nn : Data.Q₀ h hf ≤ Data.Nn h hKU hf := by
  intro k hk
  obtain ⟨hk0, hθ⟩ := (Data.mem_Q₀ h hf).1 hk
  have hX₂K₂ : d.X₂ ≤ d.K₂ := d.pull_mono X₂sub_le_K₂sub
  have hN : d.X₂ ≤ normalizer (d.F : Set G) := fun x hx =>
    mem_normalizer_fintype fun f hf' => Data.K₂_conj_mem_F (hX₂K₂ hx) hf'
  obtain ⟨x, hx, f, hfF, hxf⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer hN hθ
  obtain ⟨k₁, hk₁⟩ := Data.exists_theta_eq h hKU hf (Data.K₂_le_K₃ (hX₂K₂ hx))
  have hk₁U : (k₁ : G) ∈ Data.U₁ h hf :=
    (Data.mem_U₁ h hf).2 ⟨k₁.2, by rw [hk₁]; exact hx⟩
  have hfmem : f ∈ ((d.Y ⊓ K₀).subgroupOf K₀).map (Data.theta h hf) := by
    rw [h.map_theta_I₀ hKU hf]
    exact hfF
  obtain ⟨k₂, hk₂, hk₂f⟩ := hfmem
  have hkk : (⟨k, hk0⟩ : ↥K₀) = k₁ * k₂ :=
    Data.theta_injective h hf (by rw [hxf, map_mul, hk₁, hk₂f])
  have : k = (k₁ : G) * (k₂ : G) := congrArg Subtype.val hkk
  rw [this]
  exact mul_mem (h.Lam₁_le_Nn hKU hf (mem_sup_left hk₁U))
    (h.I₀_le_Nn hKU hf (Subgroup.mem_subgroupOf.1 hk₂))

include h hKU in
theorem Data.Hyp.M_le_N₂ : d.D₁ ⊓ centralizer ({d.e₂} : Set G) ≤ Data.N₂ h hKU hf := by
  intro m hm
  have h1 : Data.Q₀ h hf ⊔ d.tc (Data.Q₀ h hf) ≤ Data.N₂ h hKU hf :=
    sup_le ((h.Q₀_le_Nn hKU hf).trans (Data.Nn_le_N₂ h hKU hf))
      ((h.tc_mono (h.Q₀_le_Nn hKU hf)).trans (Data.tcNn_le_N₂ h hKU hf))
  exact h1 (h.M_le_Q₀_sup hKU hf hm)

include h hKU in
theorem Data.Hyp.D₁_le_N₂ : d.D₁ ≤ Data.N₂ h hKU hf := by
  rw [h.D₁_eq_D₃e₂_sup_M]
  exact sup_le ((h.D₃e₂_le_D₂).trans (h.D₂_le_N₂ hKU hf)) (h.M_le_N₂ hKU hf)

include h hKU in
theorem Data.Hyp.P_le_N₂ : d.P ≤ Data.N₂ h hKU hf :=
  sup_le (h.D₁_le_N₂ hKU hf) (h.D₂_le_N₂ hKU hf)

end Delta

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
