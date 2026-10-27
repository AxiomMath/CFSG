module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7D
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7Mod

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

section Transport



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.theta_mem_F_of_mem_I₀ {x : G} (hx : x ∈ d.Y ⊓ K₀) :
    Data.theta h hf ⟨x, hx.2⟩ ∈ d.F := by
  rw [← h.sec4_6.2.2.2.1]
  have htx : d.t * x * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hx.2)
  have hcomm : x * (d.t * x * d.t) = (d.t * x * d.t) * x := hf.comm_elem x hx.2 _ htx
  rw [Data.theta_apply]
  refine Subgroup.mem_inf.2 ⟨d.Y.mul_mem hx.1 (h.t_conj_mem_Y hx.1),
    mem_centralizer_singleton_iff.2 ?_⟩
  have e1 : d.t * (x * (d.t * x * d.t)) = ((d.t * x * d.t) * x) * d.t := by
    calc d.t * (x * (d.t * x * d.t)) = d.t * x * d.t * x * d.t := by group
      _ = ((d.t * x * d.t) * x) * d.t := rfl
  rw [e1, ← hcomm]

include h hKU in
theorem Data.Hyp.map_theta_I₀ :
    ((d.Y ⊓ K₀).subgroupOf K₀).map (Data.theta h hf) = d.F := by
  have hle : ((d.Y ⊓ K₀).subgroupOf K₀).map (Data.theta h hf) ≤ d.F := by
    rintro _ ⟨k, hk, rfl⟩
    exact h.theta_mem_F_of_mem_I₀ hKU hf (x := (k : G)) (Subgroup.mem_subgroupOf.1 hk)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (Data.theta_injective h hf),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : d.Y ⊓ K₀ ≤ K₀)).toEquiv,
    h.card_Y_inf_K₀ hKU hf, d.card_F]
  norm_num

include h hKU in
theorem Data.Hyp.map_theta_Lam₁ :
    ((Data.Lam₁ h hKU hf).subgroupOf K₀).map (Data.theta h hf) = d.K₂ := by
  rw [← Data.range_thetaLam h hKU hf]
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨(k : G), Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨Subgroup.inclusion (Data.Lam₁_le_K₀ h hKU hf) g, Subgroup.mem_subgroupOf.2 g.2, rfl⟩

theorem Data.comm_F_K₂ : ⁅d.F, d.K₂⁆ = d.F := by
  show ⁅Fsub.map d.ι, K₂sub.map d.ι⁆ = Fsub.map d.ι
  rw [← Subgroup.map_commutator, commutator_Fsub_K₂sub]

include h hKU in
theorem Data.Hyp.I₀_le_commutator :
    d.Y ⊓ K₀ ≤ ⁅d.Y ⊓ K₀, Data.Lam₁ h hKU hf⁆ := by
  have hmap : (⁅(d.Y ⊓ K₀).subgroupOf K₀, (Data.Lam₁ h hKU hf).subgroupOf K₀⁆).map
      (Data.theta h hf) = ((d.Y ⊓ K₀).subgroupOf K₀).map (Data.theta h hf) := by
    rw [Subgroup.map_commutator, h.map_theta_I₀ hKU hf, h.map_theta_Lam₁ hKU hf,
      Data.comm_F_K₂]
  have heq : ⁅(d.Y ⊓ K₀).subgroupOf K₀, (Data.Lam₁ h hKU hf).subgroupOf K₀⁆ =
      (d.Y ⊓ K₀).subgroupOf K₀ := Subgroup.map_injective (Data.theta_injective h hf) hmap
  intro x hx
  have h1 : (⟨x, hx.2⟩ : ↥K₀) ∈
      ⁅(d.Y ⊓ K₀).subgroupOf K₀, (Data.Lam₁ h hKU hf).subgroupOf K₀⁆ := by
    rw [heq]
    exact Subgroup.mem_subgroupOf.2 hx
  have h2 : (⁅(d.Y ⊓ K₀).subgroupOf K₀, (Data.Lam₁ h hKU hf).subgroupOf K₀⁆).map K₀.subtype =
      ⁅d.Y ⊓ K₀, Data.Lam₁ h hKU hf⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le inf_le_right,
      Subgroup.map_subgroupOf_eq_of_le (Data.Lam₁_le_K₀ h hKU hf)]
  rw [← h2]
  exact ⟨_, h1, rfl⟩

include h hKU in
theorem Data.Hyp.I₀_le_Nn : d.Y ⊓ K₀ ≤ Data.Nn h hKU hf :=
  (h.I₀_le_commutator hKU hf).trans (Subgroup.commutator_mono
    (inf_le_left.trans (h.Y_le_N₃ hKU hf)) (Data.Lam₁_le_N₃ h hKU hf))

include h hKU in
theorem Data.Hyp.eq_one_of_comm_Lam₁ {x : G} (hx : x ∈ d.Y ⊓ K₀)
    (hc : ∀ g ∈ Data.Lam₁ h hKU hf, g * x = x * g) : x = 1 := by
  obtain ⟨φ, hφF, hφ⟩ := h.theta_mem_F_of_mem_I₀ hKU hf hx
  have hφ1 : φ = 1 := by
    refine eq_one_of_comm_K₂sub hφF fun k hk => ?_
    have hk₂ : d.ι k ∈ (Data.thetaLam h hKU hf).range := by
      rw [Data.range_thetaLam]
      exact ⟨k, hk, rfl⟩
    obtain ⟨g, hg⟩ := hk₂
    apply d.ι_injective
    rw [map_mul, map_mul, hφ, ← hg]
    have hgx : (Subgroup.inclusion (Data.Lam₁_le_K₀ h hKU hf) g) * (⟨x, hx.2⟩ : ↥K₀) =
        (⟨x, hx.2⟩ : ↥K₀) * (Subgroup.inclusion (Data.Lam₁_le_K₀ h hKU hf) g) :=
      Subtype.ext (hc g g.2)
    show Data.theta h hf (Subgroup.inclusion (Data.Lam₁_le_K₀ h hKU hf) g) *
        Data.theta h hf ⟨x, hx.2⟩ = Data.theta h hf ⟨x, hx.2⟩ *
          Data.theta h hf (Subgroup.inclusion (Data.Lam₁_le_K₀ h hKU hf) g)
    rw [← map_mul, ← map_mul, hgx]
  have hθ1 : Data.theta h hf ⟨x, hx.2⟩ = 1 := by rw [← hφ, hφ1, map_one]
  have : (⟨x, hx.2⟩ : ↥K₀) = 1 := Data.theta_injective h hf (by rw [hθ1, map_one])
  exact congrArg Subtype.val this

include h hKU in
theorem Data.Hyp.Nn_inf_I₁ : Data.Nn h hKU hf ⊓ (d.Y ⊓ d.tc K₀) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxN, hxI⟩
  have hx' : d.t * x * d.t ∈ d.Y ⊓ K₀ := ⟨h.t_conj_mem_Y hxI.1, (h.mem_tc).1 hxI.2⟩
  have hc : ∀ g ∈ Data.Lam₁ h hKU hf, g * (d.t * x * d.t) = (d.t * x * d.t) * g := by
    intro g hg
    have hg' : d.t * g * d.t ∈ d.tc (Data.Lam₁ h hKU hf) :=
      (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hg)
    have hxg := h.comm_Nn_tcLam₁ hKU hf hxN hg'
    have e1 : g * (d.t * x * d.t) = d.t * ((d.t * g * d.t) * x) * d.t := by
      conv_lhs => rw [← h.t_conj_conj g]
      exact h.t_conj_mul' (d.t * g * d.t) x
    have e2 : (d.t * x * d.t) * g = d.t * (x * (d.t * g * d.t)) * d.t := by
      conv_lhs => rw [← h.t_conj_conj g]
      exact h.t_conj_mul' x (d.t * g * d.t)
    rw [e1, e2, hxg]
  have h1 := h.eq_one_of_comm_Lam₁ hKU hf hx' hc
  have : x = d.t * (d.t * x * d.t) * d.t := (h.t_conj_conj x).symm
  rw [this, h1]
  simp [h.t_mul_t]

end Transport

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
