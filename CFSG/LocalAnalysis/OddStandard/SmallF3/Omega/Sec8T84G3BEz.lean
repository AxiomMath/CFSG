module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BCu
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BRq

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {E E0 Y Y' V V' F F' P H : Subgroup G}

namespace Sec8T84G3BSide

theorem exists_z (hP : Sec8T84FactP) (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) :
    ∃ z ∈ sec8t84g_Q E E0, z ∈ Y ∧ (∀ u ∈ V' ⊔ F', z * u = u * z) ∧
      z ∉ oddCoreIn (normalizer (E : Set G)) ∧ z ^ 3 ∈ oddCoreIn (sec8t84g_Q E E0) := by
  haveI hNn : ((oddCoreIn (normalizer (E : Set G))).subgroupOf Y).Normal := S.ydata.O_norm
  let π : ↥Y →* ↥Y ⧸ (oddCoreIn (normalizer (E : Set G))).subgroupOf Y := QuotientGroup.mk' _
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ x : ↥Y, π x = 1 ↔ (x : G) ∈ oddCoreIn (normalizer (E : Set G)) :=
    fun x => QuotientGroup.eq_one_iff x
  have hNJ := sec8t84g3b_normJ_ydata hP S.ydata S.P_syl S.F_le_P S.F_e16 S.F_ne
  obtain ⟨g, hg3, hgN, -, -⟩ :=
    (sec8t84g3b_pfacts_ydata hP S.ydata S.P_syl S.F_le_P S.F_e16 S.F_ne).y_exists
  have hodd : Odd (orderOf g) := by rw [hg3]; decide
  obtain ⟨z, hzZ, hzY, hzg⟩ := sec8t84g3b_range_gen S π hπs hker rfl rfl hNJ g hgN hodd
  have hZQ : sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F') ≤ sec8t84g_Q E E0 :=
    sec8t84g3b_Z_le (fun y hy _ _ => hy) S.U_le_Q
  have hZC : sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F') ≤
      centralizer ((V' ⊔ F' : Subgroup G) : Set G) :=
    sec8t84g3b_Z_le (fun y _ hc _ => hc) (fun u hu => Subgroup.mem_centralizer_iff.mpr
      (fun u' hu' => (S.UU'_comm u hu u' hu').symm))
  refine ⟨z, hZQ hzZ, hzY, fun u hu => (Subgroup.mem_centralizer_iff.mp (hZC hzZ) u hu).symm,
    ?_, ?_⟩
  · intro hz
    have h1 : π ⟨z, hzY⟩ = 1 := (hker _).mpr hz
    rw [hzg] at h1
    rw [h1, orderOf_one] at hg3
    exact absurd hg3 (by norm_num)
  · have h1 : g ^ 3 = 1 := by
      have := pow_orderOf_eq_one g
      rwa [hg3] at this
    have h2 : π (⟨z, hzY⟩ ^ 3) = 1 := by rw [map_pow, hzg]; exact h1
    have h3 := (hker _).mp h2
    rw [Subgroup.coe_pow] at h3
    rw [S.O_eq]
    exact ⟨Subgroup.pow_mem _ (hZQ hzZ) 3, h3⟩

theorem exists_cent_eq (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4)
    (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) (hW : E ⊔ E0 = (V ⊔ F) ⊔ (V' ⊔ F'))
    (hinf : (V ⊔ F) ⊓ (V' ⊔ F') = ⊥) :
    ∃ z ∈ sec8t84g_Q E E0, z ^ 3 ∈ oddCoreIn (sec8t84g_Q E E0) ∧
      (E ⊔ E0) ⊓ centralizer ({z} : Set G) = V' ⊔ F' := by
  obtain ⟨z, hzQ, hzY, hzc, hzN, hz3⟩ := S.exists_z hP
  have hodd : Odd (orderOf z) := sec8t84g3b_odd_of_pow (by decide : Odd 3) hz3
  have hU : (V ⊔ F) ⊓ centralizer ({z} : Set G) = ⊥ := by
    have h1 := (S.cent_U hP hS4 hW hzY (Y'.one_mem) (by rwa [mul_one]) (k := 1)
      (by rwa [mul_one, pow_one])).2 hzN
    simpa using h1
  have hU' : (V' ⊔ F') ⊓ centralizer ({z} : Set G) = V' ⊔ F' :=
    inf_eq_left.mpr (fun u hu => Subgroup.mem_centralizer_iff.mpr (fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]; exact hzc u hu))
  refine ⟨z, hzQ, hz3, ?_⟩
  rw [hW, sec8t84g3b_cent_sup hinf (fun u hu u' hu' => S.UU'_comm u hu u' hu')
    (S.conj_U_of_odd hW hzQ hodd) (fun u hu => by rw [hzc u hu, mul_inv_cancel_right]; exact hu),
    hU, hU', bot_sup_eq]

end Sec8T84G3BSide

end CFSG.OddStandard.SmallF3.Omega
