module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5S136a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem lemma_13_6_5_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) :
    Subgroup.centralizer ({S.v12} : Set G) ⊓ Subgroup.normalizer (baum T : Set G) ≤
      Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer ({S.v12} : Set G) := by
  intro x hx
  obtain ⟨hxv, hxS⟩ := Subgroup.mem_inf.mp hx
  have hxM := S.normalizer_baum_le_F4 h517 hxS
  refine ⟨?_, hxv⟩

  have hne : Subgroup.zpowers S.v12 ≠ ⊥ := by
    intro h
    have : S.v12 = 1 := (Subgroup.zpowers_eq_bot).mp h
    have h1 : S.frame.ψ ⟨S.v12, S.v12_mem_V⟩ = 1 := by
      have : (⟨S.v12, S.v12_mem_V⟩ : ↥V) = 1 := Subtype.ext this
      rw [this, map_one]
    rw [S.psi_v12] at h1
    exact E12_ne_one h1
  have hle : Subgroup.zpowers S.v12 ≤ V := Subgroup.zpowers_le.mpr S.v12_mem_V
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) :=
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hxv
      exact ((Commute.zpow_left hc.symm k).eq))
  exact S.mem_normalizer_V_of_F4 h1222 hxM hne hle hxN

end Setting

end CFSG.Quasithin.H13.A5
