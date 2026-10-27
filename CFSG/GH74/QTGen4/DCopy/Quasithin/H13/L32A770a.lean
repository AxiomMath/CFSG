module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A713
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL24

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem hz_le_normalizer_U_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) :
    hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := by
  rw [fsuU_eq_conjClosure_hz_F4 hMod h]
  exact le_normalizer_conjClosure V _

theorem comm_mul_comm_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) {s : G} (hs : s ∈ hz T V)
    {u₁ u₂ : G} (hu₁ : u₁ ∈ fsuU T V) (hu₂ : u₂ ∈ fsuU T V) :
    u₁ * s * u₁⁻¹ * s⁻¹ * (u₂ * s * u₂⁻¹ * s⁻¹) = u₁ * u₂ * s * (u₁ * u₂)⁻¹ * s⁻¹ := by
  have hcomm : ∀ {a b : G}, a ∈ fsuU T V → b ∈ fsuU T V → a * b = b * a :=
    fun ha hb => F7.isElemAbelian_comm (isElemAbelian_fsuU_of_F4 h hMod) ha hb
  have hN := hz_le_normalizer_U_F4 h hMod hs
  have ha : s * u₁⁻¹ * s⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp (inv_mem hu₁)
  have hb : s * u₂⁻¹ * s⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp (inv_mem hu₂)
  calc u₁ * s * u₁⁻¹ * s⁻¹ * (u₂ * s * u₂⁻¹ * s⁻¹)
        = u₁ * ((s * u₁⁻¹ * s⁻¹) * u₂) * (s * u₂⁻¹ * s⁻¹) := by group
    _ = u₁ * (u₂ * (s * u₁⁻¹ * s⁻¹)) * (s * u₂⁻¹ * s⁻¹) := by rw [hcomm ha hu₂]
    _ = u₁ * u₂ * ((s * u₁⁻¹ * s⁻¹) * (s * u₂⁻¹ * s⁻¹)) := by group
    _ = u₁ * u₂ * ((s * u₂⁻¹ * s⁻¹) * (s * u₁⁻¹ * s⁻¹)) := by rw [hcomm ha hb]
    _ = u₁ * u₂ * s * (u₁ * u₂)⁻¹ * s⁻¹ := by group

end CFSG.Quasithin.H13.L32A
