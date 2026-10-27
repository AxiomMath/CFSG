module

public import CFSG.GH74.GLS.SP.Local.SPLSetBasic

public section

open Subgroup CFSG.GH74.GLS.LU.Local

namespace CFSG.GH74.GLS.SP.Local

theorem cen_C_K {G : Type} [Group G] [Finite G] {D : SPLNot0 G} (hs : SPLSetup D) {c : G}
    (hc : c ∈ Cz D.z) (hcK : ∀ k ∈ D.K, c * k = k * c) : c ∈ zpowers D.z := by
  have := hs.isCyclic_A0
  have hD : c ∈ Dz D.z D.K₁ D.K₂ :=
    ⟨hc, mem_centralizer_iff.mpr fun k hk => (hcK k hk).symm⟩
  obtain ⟨a, ha, i, hai⟩ := Dz_decomp hs.comps hs.gen_syl hD
  have ha1 : a = 1 := by
    have h : A0 D.z = ⊥ := hs.O2
    rw [h] at ha
    exact Subgroup.mem_bot.mp ha
  rw [hai, ha1, one_mul]
  exact Subgroup.zpow_mem _ (mem_zpowers _) i

theorem eq_one_of_mem_F_cen_K {G : Type} [Group G] [Finite G] {D : SPLNot0 G} (hs : SPLSetup D)
    {y : G} (hy : y ∈ D.F) (hyK : ∀ k ∈ D.K, y * k = k * y) : y = 1 := by
  have hz : y ∈ zpowers D.z := cen_C_K hs (F_le_C hs hy) hyK
  have hK : y ∈ D.K := zpowers_le.mpr (Subgroup.mem_sup_left (z_mem_K₁ hs)) hz
  have h : y ∈ D.F ⊓ D.K := ⟨hy, hK⟩
  rw [F_inf_K_eq hs] at h
  exact Subgroup.mem_bot.mp h

end CFSG.GH74.GLS.SP.Local
