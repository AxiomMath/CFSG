module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6P

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem comm_inv_of_comm' {X : Type*} [Group X] {p x : X} (h : p * x = x * p) :
    x * p⁻¹ = p⁻¹ * x := by
  calc x * p⁻¹ = p⁻¹ * (p * x) * p⁻¹ := by group
    _ = p⁻¹ * (x * p) * p⁻¹ := by rw [h]
    _ = p⁻¹ * x := by group

theorem comm_mul_comm {X : Type*} [Group X] {p₁ p₂ q₁ q₂ : X}
    (h11 : p₁ * q₁ = q₁ * p₁) (h12 : p₁ * q₂ = q₂ * p₁)
    (h21 : p₂ * q₁ = q₁ * p₂) (h22 : p₂ * q₂ = q₂ * p₂) :
    p₁ * q₁ * (p₂ * q₂) * (p₁ * q₁)⁻¹ * (p₂ * q₂)⁻¹ =
      (p₁ * p₂ * p₁⁻¹ * p₂⁻¹) * (q₁ * q₂ * q₁⁻¹ * q₂⁻¹) := by
  have hq₁ : q₁ ∈ centralizer ({p₁, p₂} : Set X) := mem_centralizer_iff.2 fun g hg => by
    rcases hg with rfl | hg
    · exact h11
    · rw [Set.mem_singleton_iff.1 hg]
      exact h21
  have hq₂ : q₂ ∈ centralizer ({p₁, p₂} : Set X) := mem_centralizer_iff.2 fun g hg => by
    rcases hg with rfl | hg
    · exact h12
    · rw [Set.mem_singleton_iff.1 hg]
      exact h22
  have hQc : q₁ * q₂ * q₁⁻¹ ∈ centralizer ({p₁, p₂} : Set X) :=
    (centralizer ({p₁, p₂} : Set X)).mul_mem
      ((centralizer ({p₁, p₂} : Set X)).mul_mem hq₁ hq₂)
      ((centralizer ({p₁, p₂} : Set X)).inv_mem hq₁)
  have hQd : q₁ * q₂ * q₁⁻¹ * q₂⁻¹ ∈ centralizer ({p₁, p₂} : Set X) :=
    (centralizer ({p₁, p₂} : Set X)).mul_mem hQc
      ((centralizer ({p₁, p₂} : Set X)).inv_mem hq₂)
  have e1 : p₁ * (q₁ * q₂ * q₁⁻¹) = (q₁ * q₂ * q₁⁻¹) * p₁ :=
    mem_centralizer_iff.1 hQc p₁ (by simp)
  have e2 : p₂ * (q₁ * q₂ * q₁⁻¹ * q₂⁻¹) = (q₁ * q₂ * q₁⁻¹ * q₂⁻¹) * p₂ :=
    mem_centralizer_iff.1 hQd p₂ (by simp)
  have e1' := comm_inv_of_comm' e1
  have e2' := comm_inv_of_comm' e2
  calc p₁ * q₁ * (p₂ * q₂) * (p₁ * q₁)⁻¹ * (p₂ * q₂)⁻¹
      = p₁ * (q₁ * p₂) * q₂ * q₁⁻¹ * p₁⁻¹ * q₂⁻¹ * p₂⁻¹ := by group
    _ = p₁ * (p₂ * q₁) * q₂ * q₁⁻¹ * p₁⁻¹ * q₂⁻¹ * p₂⁻¹ := by rw [← h21]
    _ = p₁ * p₂ * ((q₁ * q₂ * q₁⁻¹) * p₁⁻¹) * q₂⁻¹ * p₂⁻¹ := by group
    _ = p₁ * p₂ * (p₁⁻¹ * (q₁ * q₂ * q₁⁻¹)) * q₂⁻¹ * p₂⁻¹ := by rw [e1']
    _ = p₁ * p₂ * p₁⁻¹ * ((q₁ * q₂ * q₁⁻¹ * q₂⁻¹) * p₂⁻¹) := by group
    _ = p₁ * p₂ * p₁⁻¹ * (p₂⁻¹ * (q₁ * q₂ * q₁⁻¹ * q₂⁻¹)) := by rw [e2']
    _ = (p₁ * p₂ * p₁⁻¹ * p₂⁻¹) * (q₁ * q₂ * q₁⁻¹ * q₂⁻¹) := by group

theorem Data.theta_conj_K₀ (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) (k : ↥K₀) {α : G}
    (hα : α ∈ K₀) :
    Data.theta h hf k * α * (Data.theta h hf k)⁻¹ = k * α * (k : G)⁻¹ := by
  rw [Data.theta_apply]
  have hb : d.t * (k : G) * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact k.2)
  have hc : (d.t * (k : G) * d.t) * α = α * (d.t * (k : G) * d.t) :=
    (hf.comm_elem α hα _ hb).symm
  calc (k : G) * (d.t * k * d.t) * α * ((k : G) * (d.t * k * d.t))⁻¹
      = k * ((d.t * (k : G) * d.t) * α) * (d.t * (k : G) * d.t)⁻¹ * (k : G)⁻¹ := by group
    _ = k * (α * (d.t * (k : G) * d.t)) * (d.t * (k : G) * d.t)⁻¹ * (k : G)⁻¹ := by rw [hc]
    _ = k * α * (k : G)⁻¹ := by group

theorem Data.theta_conj_tc (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) (k : ↥K₀) {β : G}
    (hβ : β ∈ d.tc K₀) :
    Data.theta h hf k * β * (Data.theta h hf k)⁻¹ =
      (d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹ := by
  rw [Data.theta_apply]
  have hb : d.t * (k : G) * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact k.2)
  have hγ : (d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹ ∈ d.tc K₀ :=
    (d.tc K₀).mul_mem ((d.tc K₀).mul_mem hb hβ) ((d.tc K₀).inv_mem hb)
  have hc : (k : G) * ((d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹) =
      ((d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹) * k := hf.comm_elem k k.2 _ hγ
  calc (k : G) * (d.t * k * d.t) * β * ((k : G) * (d.t * k * d.t))⁻¹
      = (k : G) * ((d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹) * (k : G)⁻¹ := by group
    _ = ((d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹) * k * (k : G)⁻¹ := by rw [hc]
    _ = (d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹ := by group

section Coords



variable (h : d.Hyp) (hKU : d.KUnitary)

include h hKU in
theorem Data.Hyp.proj_mem_W (hf : d.IsUnitaryFactor K₀) {α β : G} (hα : α ∈ d.Y ⊓ K₀)
    (hβ : β ∈ d.Y ⊓ d.tc K₀) (hW : α * β ∈ d.W) : α ∈ d.W := by
  refine Subgroup.mem_inf.2 ⟨hα.1, ?_⟩
  have hA₂ : d.A₂ ≤ centralizer ({α} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (h.Y_comm_A₂ hα.1 ha)
  have hX₂ : d.X₂ ≤ centralizer ({α} : Set G) := by
    intro x hx
    have hK₃ : x ∈ d.K₃ := d.pull_mono X₂sub_le_K₃sub' hx
    obtain ⟨k, hk⟩ := Data.exists_theta_eq h hKU hf hK₃
    have hxS : x ∈ d.S := d.pull_mono X₂sub_le_Ssub hx
    have hcomm : x * (α * β) = (α * β) * x :=
      mem_centralizer_iff.1 (Subgroup.mem_inf.1 hW).2 x hxS
    have e1 : x * α * x⁻¹ = k * α * (k : G)⁻¹ := by rw [← hk]; exact Data.theta_conj_K₀ h hf k hα.2
    have e2 : x * β * x⁻¹ = (d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹ := by
      rw [← hk]; exact Data.theta_conj_tc h hf k hβ.2
    have hb : d.t * (k : G) * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact k.2)
    have hα' : (k : G) * α * (k : G)⁻¹ ∈ K₀ := K₀.mul_mem (K₀.mul_mem k.2 hα.2) (K₀.inv_mem k.2)
    have hβ' : (d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹ ∈ d.tc K₀ :=
      (d.tc K₀).mul_mem ((d.tc K₀).mul_mem hb hβ.2) ((d.tc K₀).inv_mem hb)
    have hprod : (k * α * (k : G)⁻¹) * ((d.t * (k : G) * d.t) * β * (d.t * (k : G) * d.t)⁻¹) =
        α * β := by
      rw [← e1, ← e2]
      calc x * α * x⁻¹ * (x * β * x⁻¹) = x * (α * β) * x⁻¹ := by group
        _ = (α * β) * x * x⁻¹ := by rw [hcomm]
        _ = α * β := by group
    obtain ⟨he1, -⟩ := hf.unique hα' hα.2 hβ' hβ.2 hprod
    refine mem_centralizer_singleton_iff.2 ?_
    have : x * α * x⁻¹ = α := by rw [e1]; exact he1
    calc x * α = x * α * x⁻¹ * x := by group
      _ = α * x := by rw [this]
  have hS : d.S ≤ centralizer ({α} : Set G) := by
    rw [d.S_eq_sup]
    exact sup_le hA₂ hX₂
  exact mem_centralizer_iff.2 fun s hs => mem_centralizer_singleton_iff.1 (hS hs)

include h hKU in
theorem Data.Hyp.comm_mem_W (hf : d.IsUnitaryFactor K₀) {a : G} (ha : a ∈ K₀)
    (hyS : a * (d.t * a * d.t) ∈ d.S) {v₀ v₁ : G} (hv₀ : v₀ ∈ d.Y ⊓ K₀)
    (hv₁ : v₁ ∈ d.Y ⊓ d.tc K₀) (hv : v₀ * v₁ ∈ d.V₂) :
    a * v₀ * a⁻¹ * v₀⁻¹ ∈ d.W := by
  obtain ⟨y, hy⟩ : ∃ y : G, y = a * (d.t * a * d.t) := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : G, α = a * v₀ * a⁻¹ * v₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : G, β = y * v₁ * y⁻¹ * v₁⁻¹ := ⟨_, rfl⟩
  have hyS' : y ∈ d.S := by rw [hy]; exact hyS
  have hV : y * (v₀ * v₁) * y⁻¹ * (v₀ * v₁)⁻¹ ∈ d.W := ((h.mem_V₂_iff).1 hv).2 y hyS'
  have hyY : y ∈ normalizer (d.Y : Set G) := h.S_le_normalizer_Y hyS'
  have hθ : y = Data.theta h hf ⟨a, ha⟩ := by
    rw [hy]
    exact (Data.theta_apply h hf ⟨a, ha⟩).symm
  have e0 : y * v₀ * y⁻¹ = a * v₀ * a⁻¹ := by
    rw [hθ]
    exact Data.theta_conj_K₀ h hf ⟨a, ha⟩ hv₀.2
  have e1 : y * v₁ * y⁻¹ = (d.t * a * d.t) * v₁ * (d.t * a * d.t)⁻¹ := by
    rw [hθ]
    exact Data.theta_conj_tc h hf ⟨a, ha⟩ hv₁.2
  have hb : d.t * a * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact ha)
  have hαK : α ∈ K₀ := by
    rw [hα]
    exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem ha hv₀.2) (K₀.inv_mem ha)) (K₀.inv_mem hv₀.2)
  have hαY : α ∈ d.Y := by
    rw [hα, ← e0]
    exact d.Y.mul_mem ((mem_normalizer_iff.1 hyY v₀).1 hv₀.1) (d.Y.inv_mem hv₀.1)
  have hβtc : β ∈ d.tc K₀ := by
    rw [hβ, e1]
    exact (d.tc K₀).mul_mem ((d.tc K₀).mul_mem ((d.tc K₀).mul_mem hb hv₁.2)
      ((d.tc K₀).inv_mem hb)) ((d.tc K₀).inv_mem hv₁.2)
  have hβY : β ∈ d.Y := by
    rw [hβ]
    exact d.Y.mul_mem ((mem_normalizer_iff.1 hyY v₁).1 hv₁.1) (d.Y.inv_mem hv₁.1)
  have hcβ : v₀ * β = β * v₀ := hf.comm_elem v₀ hv₀.2 β hβtc
  have h1 : y * v₀ * y⁻¹ * v₀⁻¹ = α := by rw [hα, e0]
  have hprod : y * (v₀ * v₁) * y⁻¹ * (v₀ * v₁)⁻¹ = α * β := by
    calc y * (v₀ * v₁) * y⁻¹ * (v₀ * v₁)⁻¹
        = (y * v₀ * y⁻¹ * v₀⁻¹) * v₀ * (y * v₁ * y⁻¹ * v₁⁻¹) * v₀⁻¹ := by group
      _ = α * (v₀ * β) * v₀⁻¹ := by rw [h1, ← hβ]; simp only [mul_assoc]
      _ = α * (β * v₀) * v₀⁻¹ := by rw [hcβ]
      _ = α * β := by group
  have hW : α * β ∈ d.W := by rw [← hprod]; exact hV
  rw [← hα]
  exact h.proj_mem_W hKU hf ⟨hαY, hαK⟩ ⟨hβY, hβtc⟩ hW

include h hKU in
theorem Data.Hyp.comm_M_V₂_mem_W :
    ∀ v ∈ d.V₂, ∀ m ∈ d.D₁ ⊓ centralizer ({d.e₂} : Set G), m * v * m⁻¹ * v⁻¹ ∈ d.W := by
  obtain ⟨K₀, hf⟩ := hKU.exists_isUnitaryFactor
  have hf₁ := Data.IsUnitaryFactor.tc_factor h hf
  intro v hv m hm
  have hvY : v ∈ d.Y := ((h.mem_V₂_iff).1 hv).1
  obtain ⟨v₀, hv₀, v₁, hv₁, hvv⟩ := h.exists_mul_of_mem_Y hKU hf hvY
  have hmK : m ∈ d.K := h.M_le_K (h.Y_le_K' hKU) (Data.Hyp.K₃_le_K hKU) hm
  have hmK' : m ∈ K₀ ⊔ d.tc K₀ := by rw [← hf.K_eq_tc]; exact hmK
  obtain ⟨a, ha, b, hb, hmab⟩ := KProd.exists_mul_of_mem_sup_of_comm hf.comm_elem hmK'
  have hθa : a * (d.t * a * d.t) ∈ d.X₂ ⊔ d.F := h.theta_component_mem hKU hf hm ha hb hmab
  have hba : b * a = a * b := (hf.comm_elem a ha b hb).symm
  have hθb : b * (d.t * b * d.t) ∈ d.X₂ ⊔ d.F := by
    refine h.theta_component_mem hKU hf₁ hm hb ?_ (by rw [hmab, hba])
    rw [h.tc_tc]
    exact ha
  have hvv' : v₀ * v₁ ∈ d.V₂ := by rw [← hvv]; exact hv
  have hW₀ : a * v₀ * a⁻¹ * v₀⁻¹ ∈ d.W :=
    h.comm_mem_W hKU hf ha (d.X₂_sup_F_le_S hθa) hv₀ hv₁ hvv'
  have hv₀' : v₀ ∈ d.Y ⊓ d.tc (d.tc K₀) := by rw [h.tc_tc]; exact hv₀
  have hcomm_v : v₁ * v₀ = v₀ * v₁ := h.Y_comm hv₁.1 hv₀.1
  have hW₁ : b * v₁ * b⁻¹ * v₁⁻¹ ∈ d.W :=
    h.comm_mem_W hKU hf₁ hb (d.X₂_sup_F_le_S hθb) hv₁ hv₀' (by rw [hcomm_v]; exact hvv')
  rw [hmab, hvv, comm_mul_comm (hf.comm_elem a ha b hb) (hf.comm_elem a ha v₁ hv₁.2)
    (hf.comm_elem v₀ hv₀.2 b hb) (hf.comm_elem v₀ hv₀.2 v₁ hv₁.2)]
  exact d.W.mul_mem hW₀ hW₁

end Coords

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
