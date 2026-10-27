module

public import CFSG.Quasithin.H13.A6S1514
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1357

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem UH_le_T_F4
    (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two_F4)
    (h13315 : Stmt13_3_15_F4) {H : Subgroup G} (hH : H ∈ S.Hz) : conjClosure S.V3 H ≤ T := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le_of_sylow S.h13.sylow hF.T_le_H)

theorem lemma13_5_14_one_F4
    (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two_F4)
    (h13315 : Stmt13_3_15_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hU : ⁅conjClosure S.V3 H, S.L1⁆ ⊔ fsuV1 T V = conjClosure S.V3 H) :
    ⁅conjClosure S.V3 H, S.L1⁆ = conjClosure S.V3 H ∧ conjClosure S.V3 H ≤ S.L1 := by
  have hV1 : fsuV1 T V ≤ ⁅conjClosure S.V3 H, S.L1⁆ :=
    (S.V1_le_V2.trans S.V2_le_V3).trans (S.commutator_V3_L1.ge.trans
      (Subgroup.commutator_mono (le_conjClosure _ _) le_rfl))
  have h1 : ⁅conjClosure S.V3 H, S.L1⁆ = conjClosure S.V3 H :=
    calc ⁅conjClosure S.V3 H, S.L1⁆ = ⁅conjClosure S.V3 H, S.L1⁆ ⊔ fsuV1 T V :=
          (sup_eq_left.mpr hV1).symm
      _ = conjClosure S.V3 H := hU
  refine ⟨h1, ?_⟩
  rw [← h1, Subgroup.commutator_le]
  intro u hu l hl
  have huN : u ∈ Subgroup.normalizer (S.L1 : Set G) :=
    S.T_le_normalizer_L1 (S.UH_le_T_F4 hNS h1356two h13315 hH hu)
  have : u * l * u⁻¹ ∈ S.L1 := (Subgroup.mem_normalizer_iff.mp huN l).mp hl
  rw [commutatorElement_def]
  exact S.L1.mul_mem this (S.L1.inv_mem hl)

theorem lemma13_5_14_two_F4
    (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two_F4)
    (h13315 : Stmt13_3_15_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hle : conjClosure S.V3 H ≤ S.L1) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) :
    (∀ u (hu : u ∈ conjClosure S.V3 H),
        S.frame.ρ ⟨u, S.frame.L_le (S.L1_le.trans inf_le_left (hle hu))⟩ ∈ K4L) ∧
      ∀ σ ∈ K4L, ∃ u, ∃ hu : u ∈ conjClosure S.V3 H,
        S.frame.ρ ⟨u, S.frame.L_le (S.L1_le.trans inf_le_left (hle hu))⟩ = σ := by
  have hUN : ∀ u ∈ conjClosure S.V3 H, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    S.frame.L_le (S.L1_le.trans inf_le_left (hle hu))
  have hT := S.UH_le_T_F4 hNS h1356two h13315 hH

  have hK4 : ∀ u (hu : u ∈ conjClosure S.V3 H), S.frame.ρ ⟨u, hUN u hu⟩ ∈ K4L := by
    intro u hu
    obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := ⟨u, hUN u hu⟩) (hle hu)
    refine mem_K4L _ h4 h5 hs ?_
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨u, hT hu⟩
    refine pow_four_of_pow_two_pow (k := k) ?_
    rw [← map_pow]
    have : (⟨u, hUN u hu⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  refine ⟨hK4, fun σ hσ => ?_⟩
  by_cases hσ1 : σ = 1
  · exact ⟨1, Subgroup.one_mem _, by rw [hσ1]; exact map_one _⟩

  obtain ⟨u₀, hu₀, hne⟩ : ∃ u₀, ∃ hu₀ : u₀ ∈ conjClosure S.V3 H,
      S.frame.ρ ⟨u₀, hUN u₀ hu₀⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hna (S.isElemAbelian_UH_of_le fun u hu => (S.rho_eq_one_iff _).1 (hcon u hu))

  obtain ⟨c, hcL1, hc⟩ := S.exists_L1_c012
  have hcH : (c : G) ∈ H := (le_sup_left.trans hH.1.1) hcL1
  have hUH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) := le_normalizer_conjClosure _ _
  rcases K4L_orbit _ (hK4 u₀ hu₀) σ hσ hne hσ1 with h | h | h
  · exact ⟨u₀, hu₀, h.symm⟩
  · have hm : (c : G) * u₀ * (c : G)⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hUH hcH) u₀).mp hu₀
    refine ⟨_, hm, ?_⟩
    have e : (⟨(c : G) * u₀ * (c : G)⁻¹, hUN _ hm⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        c * ⟨u₀, hUN u₀ hu₀⟩ * c⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hc, h]
  · have hm : (c : G)⁻¹ * u₀ * (c : G)⁻¹⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hUH (H.inv_mem hcH)) u₀).mp hu₀
    refine ⟨_, hm, ?_⟩
    have e : (⟨(c : G)⁻¹ * u₀ * (c : G)⁻¹⁻¹, hUN _ hm⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = c⁻¹ * ⟨u₀, hUN u₀ hu₀⟩ * c⁻¹⁻¹ := rfl
    rw [e, inv_inv, map_mul, map_mul, map_inv, hc, h]

end Setting4

end CFSG.Quasithin.H13.A6
