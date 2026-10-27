module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ILayer
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCore
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38Four
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IClass

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {L : Subgroup G}

theorem sec4I_layer_of_hasType [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {s : G} (hss : s * s = 1)
    {y : ProjOrth Sec4IQ} (hy : Sec4IActs e s y) {r : ℕ} {α : ℤˣ} (hty : HasType y r α)
    (hcase : r = 2 ∨ (r = 4 ∧ α = -1) ∨ r = 6) :
    ∃ u : G, u ∈ CFSG.inSubgroup CFSG.layer (L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      orderOf u = 2 := by
  obtain ⟨-, t, htt, htype, hyt⟩ := hty
  have htd : invDim t = r := congrArg Prod.fst htype
  have hts : invSign t = α := congrArg Prod.snd htype
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Sec4IQ) t
  rw [sec4IQ_finrank] at hsum
  have hQU := nondegenerate_restrict_commSp sec4IQ_nondegenerate htt
  rcases hcase with rfl | ⟨rfl, rfl⟩ | rfl
  · have hx : (piOrth Sec4IQ * t) * (piOrth Sec4IQ * t) = 1 := piOrth_mul_mul_self htt
    have hxd : invDim (piOrth Sec4IQ * t) = 5 := by
      have h1 := congrArg Prod.fst (invType_piOrth_mul sec4IQ_nondegenerate htt)
      rw [sec4IQ_finrank, htd] at h1
      exact h1
    have hxy : toProj Sec4IQ (piOrth Sec4IQ * t) = y := by
      rw [map_mul, toProj_piOrth, one_mul]
      exact hyt
    have hsum' := finrank_fixSp_add_finrank_commSp (Q := Sec4IQ) (piOrth Sec4IQ * t)
    have hcd : Module.finrank (ZMod 3) (commSp (piOrth Sec4IQ * t)) = 5 := hxd
    rw [sec4IQ_finrank] at hsum'
    exact sec4I_exists_layer_of_block_lift hL e hss hy hx hxy (by omega) (by omega)
      (isQuasisimple_omegaGroup_five (nondegenerate_restrict_commSp sec4IQ_nondegenerate hx) hcd)
  · have hcd : Module.finrank (ZMod 3) (commSp t) = 4 := htd
    exact sec4I_exists_layer_of_block_lift hL e hss hy htt hyt (by omega) (by omega)
      (isQuasisimple_omegaGroup_four_minus hQU hcd hts)
  · have hcd : Module.finrank (ZMod 3) (commSp t) = 6 := htd
    rcases Int.units_eq_one_or α with rfl | rfl
    · exact sec4I_exists_layer_of_block_lift hL e hss hy htt hyt (by omega) (by omega)
        (isQuasisimple_omegaGroup_six_plus hQU hcd hts)
    · exact sec4I_exists_layer_of_block_lift hL e hss hy htt hyt (by omega) (by omega)
        (isQuasisimple_omegaGroup_six_minus hQU hcd hts)

theorem asc82Fact43_holds : Asc82Fact43 := by
  intro G _ _ L hL s hs2 hsN hlayer
  obtain ⟨e⟩ := sec4I_exists_model hL
  have hss := mul_self_eq_one_of_orderOf_eq_two hs2
  obtain ⟨y, hy⟩ := exists_sec4IActs e hsN
  have hyy := hy.sq hss
  have hnot : ∀ u : G, u ∈ CFSG.inSubgroup CFSG.layer
      (L ⊓ Subgroup.centralizer ({s} : Set G)) → orderOf u = 2 → False := by
    intro u hu hord
    rw [hlayer, Subgroup.mem_bot] at hu
    rw [hu, orderOf_one] at hord
    exact absurd hord (by decide)
  by_cases hy1 : y = 1
  · exfalso
    have hc : s ∈ Subgroup.centralizer (L : Set G) := (Sec4IActs.eq_one_iff hL hy).mp hy1
    have hLC : L ≤ Subgroup.centralizer ({s} : Set G) := fun l hl => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hc l hl
    obtain ⟨x, hx⟩ := exists_hasType_seven sec4IQ_nondegenerate sec4IQ_finrank (r := 4)
      (Or.inr (Or.inl rfl)) (1 : ℤˣ)
    have hxΩ : x ∈ Sec4IOmega :=
      (hasType_mem_omegaProj_iff_seven sec4IQ_nondegenerate sec4IQ_finrank hx
        (Or.inr (Or.inl rfl))).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    obtain ⟨l, hl⟩ := (sec4ICover_odd hL e).surjective ⟨x, hxΩ⟩
    have hl1 : (l : G) ≠ 1 := by
      intro h
      have h1 : l = 1 := Subtype.ext h
      rw [h1, map_one] at hl
      exact hx.1 (congrArg Subtype.val hl.symm)
    have hmem : (l : G) ∈ CFSG.inSubgroup CFSG.layer
        (L ⊓ Subgroup.centralizer ({s} : Set G)) := by
      rw [inf_eq_left.mpr hLC]
      refine ⟨l, ?_, rfl⟩
      rw [CFSG.WholeGroup.layer_eq_top_of_isQuasisimple hL.1]
      exact Subgroup.mem_top l
    rw [hlayer, Subgroup.mem_bot] at hmem
    exact hl1 hmem
  · rcases hasType_of_involution_seven sec4IQ_nondegenerate sec4IQ_finrank sec4IQ_quadSign hyy
      hy1 with h | h | h | h | h | h
    · obtain ⟨u, hu, hord⟩ := sec4I_layer_of_hasType hL e hss hy h (Or.inl rfl)
      exact (hnot u hu hord).elim
    · obtain ⟨u, hu, hord⟩ := sec4I_layer_of_hasType hL e hss hy h (Or.inl rfl)
      exact (hnot u hu hord).elim
    · have hΩ : y ∈ Sec4IOmega :=
        (hasType_mem_omegaProj_iff_seven sec4IQ_nondegenerate sec4IQ_finrank h
          (Or.inr (Or.inl rfl))).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      obtain ⟨u, hu, hord, hρu, hc⟩ := sec4I_exists_inner hL e hy hΩ hyy hy1
      refine ⟨u, (sec4I_isI4PlusIn_iff hL e).mpr ⟨hu, hord, ?_⟩, hc⟩
      rw [hρu]
      exact h
    · obtain ⟨u, hu, hord⟩ := sec4I_layer_of_hasType hL e hss hy h (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact (hnot u hu hord).elim
    · obtain ⟨u, hu, hord⟩ := sec4I_layer_of_hasType hL e hss hy h (Or.inr (Or.inr rfl))
      exact (hnot u hu hord).elim
    · obtain ⟨u, hu, hord⟩ := sec4I_layer_of_hasType hL e hss hy h (Or.inr (Or.inr rfl))
      exact (hnot u hu hord).elim

end CFSG.OddStandard.SmallF3.Omega
