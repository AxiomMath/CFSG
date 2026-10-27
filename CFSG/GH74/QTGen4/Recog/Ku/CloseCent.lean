module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseFin
public import CFSG.GH74.QTGen4.Recog.Ku.A6Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

theorem kuSpV_add_self (v : SpV) : v + v = 0 := by
  funext i
  show v i + v i = 0
  generalize v i = x
  revert x
  decide

variable {G : Type} [Group G]

abbrev kuDelta (E : Subgroup G) (x : G) : Subgroup G := E ⊓ Subgroup.centralizer ({x} : Set G)

namespace KuA6Model

variable [Finite G] {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z)
include Ψ

theorem E_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  intro a ha b hb
  obtain ⟨u, rfl⟩ := Ψ.surj a ha
  obtain ⟨v, rfl⟩ := Ψ.surj b hb
  rw [← Ψ.add, ← Ψ.add, add_comm]

theorem E_mul_self : ∀ a ∈ E, a * a = 1 := by
  intro a ha
  obtain ⟨u, rfl⟩ := Ψ.surj a ha
  rw [← Ψ.add, kuSpV_add_self, Ψ.Φ_zero]

theorem E_le_centralizer_z : E ≤ Subgroup.centralizer ({z} : Set G) := by
  intro a ha
  have hz : z ∈ E := by
    have := Ψ.mem (spE 0)
    rwa [Ψ.e0] at this
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact Ψ.E_comm z hz a ha

theorem exists_conj_z {e : G} (he : e ∈ E) (he1 : e ≠ 1) : ∃ g : G, g * z * g⁻¹ = e := by
  obtain ⟨v, rfl⟩ := Ψ.surj e he
  have hv : v ≠ 0 := by
    rintro rfl
    exact he1 Ψ.Φ_zero
  obtain ⟨σ, hσ, hσv⟩ := exists_alt_act_spE0 v hv
  obtain ⟨n, hn⟩ := Ψ.π_surj σ (Equiv.Perm.mem_alternatingGroup.mpr hσ)
  refine ⟨(n : G), ?_⟩
  have h := Ψ.act n (spE 0)
  rw [Ψ.e0, hn, hσv] at h
  exact h

end KuA6Model

end CFSG.GH74.QTGen4.Ku
