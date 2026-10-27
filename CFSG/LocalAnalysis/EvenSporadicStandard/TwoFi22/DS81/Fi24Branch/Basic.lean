module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.LocalOfData

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G]

@[expose] def Nrm (E : Subgroup G) : Subgroup G := normalizer (E : Set G)

@[expose] def CNz (E : Subgroup G) (z : G) : Subgroup G :=
  normalizer (E : Set G) ⊓ centralizer ({z} : Set G)

@[expose] def Pg (E : Subgroup G) (z : G) : Subgroup G := TwoFi22.O2In (CNz E z)

@[expose] def Vtz (t z : G) : Subgroup G := closure {t, z}

@[expose] def Kg (t z : G) : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)

@[expose] def Jg (t z : G) : Subgroup G := normalizer (Vtz t z : Set G)

@[expose] def OKg (t z : G) : Subgroup G := TwoFi22.O2In (Kg t z)

@[expose] def Rg (t z : G) : Subgroup G := TwoFi22.O2In (Jg t z)

@[expose] def Cz (z : G) : Subgroup G := centralizer ({z} : Set G)

theorem mem_Nrm {E : Subgroup G} {x : G} :
    x ∈ Nrm E ↔ ∀ y, y ∈ E ↔ x * y * x⁻¹ ∈ E := mem_normalizer_iff

theorem mem_CNz {E : Subgroup G} {z x : G} :
    x ∈ CNz E z ↔ x ∈ normalizer (E : Set G) ∧ x * z = z * x := by
  simp only [CNz, mem_inf, mem_centralizer_singleton_iff]

theorem mem_Kg {t z x : G} : x ∈ Kg t z ↔ x * t = t * x ∧ x * z = z * x := by
  simp only [Kg, mem_inf, mem_centralizer_singleton_iff]

theorem mem_Cz {z x : G} : x ∈ Cz z ↔ x * z = z * x := by
  simp only [Cz, mem_centralizer_singleton_iff]

theorem CNz_le_Nrm (E : Subgroup G) (z : G) : CNz E z ≤ Nrm E := inf_le_left

theorem CNz_le_Cz (E : Subgroup G) (z : G) : CNz E z ≤ Cz z := inf_le_right

theorem Pg_le_CNz (E : Subgroup G) (z : G) : Pg E z ≤ CNz E z := TwoB.O2In_le _

theorem OKg_le_Kg (t z : G) : OKg t z ≤ Kg t z := TwoB.O2In_le _

theorem Rg_le_Jg (t z : G) : Rg t z ≤ Jg t z := TwoB.O2In_le _

theorem Kg_comm_Vtz {t z k v : G} (hk : k ∈ Kg t z) (hv : v ∈ Vtz t z) : k * v * k⁻¹ = v := by
  rw [mem_Kg] at hk
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [hk.1]; group
    · rw [hk.2]; group
  | one => simp
  | mul x y _ _ hx hy =>
    calc k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      _ = x * y := by rw [hx, hy]
  | inv x _ hx =>
    calc k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [hx]

theorem Kg_le_Jg (t z : G) : Kg t z ≤ Jg t z := by
  intro k hk
  rw [Jg, mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    rw [Kg_comm_Vtz hk hv]
    exact hv
  · intro hv
    have h := Kg_comm_Vtz (inv_mem hk) hv
    rw [inv_inv] at h
    have e : k⁻¹ * (k * v * k⁻¹) * k = v := by group
    rw [e] at h
    rw [h]
    exact hv

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
