module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Model
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.Blueprint.SourceClassicalTransport

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoHypIICover.U62

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Fischer (T46)
open CFSG.Sporadic.Schreier (evalCodes_mem)

theorem u62R_mem (j : ℕ) : u62R j ∈ u62Sb :=
  evalCodes_mem u62Sb (fun g hg => subset_closure hg) _

@[expose] def u62RepW
    (j : ℕ) : ↥u62AutW :=
  ⟨u62R j, u62S_le_u62AutW (u62Sb_le_u62S (u62R_mem j))⟩

theorem u62_yCensus
    (hF : U62Facts) :
    YCensus (T46.subgroupOf u62AutW) (· ≤ T46.subgroupOf u62AutW) := by
  refine yCensusII_of_sylowReps_inner (u62AutModel hF).normal (not_four_dvd_index hF)
    (u62Sylow hF) (k := 43) u62RepW ?_ ?_
  · intro u hu huX hu2 hu1
    rw [coe_u62Sylow hF, mem_subgroupOf] at hu
    rw [mem_subgroupOf] at huX
    have ho : orderOf (u : Equiv.Perm (Fin 693)) = 2 :=
      orderOf_eq_prime (by rw [← coe_pow, hu2, coe_one]) (fun h1 => hu1 (Subtype.ext h1))
    obtain ⟨j, hj, c, hc, e⟩ := hF.2.2.2.2.1 u (mem_u62Sb_of_mem_T46 hF hu huX) ho
    refine ⟨j, hj, ⟨c, u62S_le_u62AutW (u62Sb_le_u62S hc)⟩, ?_, Subtype.ext ?_⟩
    · rw [coe_u62Sylow hF, mem_subgroupOf]
      exact u62Sb_le_u62S hc
    · rw [coe_mul, coe_mul, coe_inv]
      exact e
  · intro j hj _ b hb hb2 hbX hcomm
    rw [coe_u62Sylow hF, mem_subgroupOf] at hb
    rw [mem_subgroupOf] at hbX
    have hb2' : (b : Equiv.Perm (Fin 693)) ^ 2 = 1 := by rw [← coe_pow, hb2, coe_one]
    have hcomm' : (b : Equiv.Perm (Fin 693)) * u62R j = u62R j * b := by
      have := congrArg Subtype.val hcomm
      rwa [coe_mul, coe_mul] at this
    have hs : (b : Equiv.Perm (Fin 693)) * u62Phi ∈ u62Sb := by
      rcases (mem_u62S_iff hF).1 hb with h | h
      · exact absurd (u62Sb_le_T46 h) hbX
      · exact h
    have hbs : (b : Equiv.Perm (Fin 693)) * u62Phi * u62Phi = b := by
      rw [mul_assoc, u62Phi_mul_self, mul_one]
    have hM := hF.2.2.2.2.2 j hj _ hs (by rw [hbs]; exact hb2') (by rw [hbs]; exact hcomm')
    rw [hbs] at hM
    have hXmap : (T46.subgroupOf u62AutW).map u62AutW.subtype = T46 := by
      rw [subgroupOf_map_subtype, inf_eq_left.mpr T46_le_u62AutW]
    have hEmap : (closure ({u62RepW j, b} : Set ↥u62AutW)).map u62AutW.subtype =
        closure {u62R j, (b : Equiv.Perm (Fin 693))} := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← monoW_map_iff u62AutW.subtype u62AutW.subtype_injective, hXmap, hEmap]
    exact hM

theorem hypII_of_psu_six_two_of_facts
    (hF : U62Facts) {A : Type} [Group A] (hA : commutator A = ⊤)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (A ⧸ center A) .PSU 6 2 1) :
    AS76b.HypII A := by
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h
    statedClassicalModel_T46
  exact hypII_of_yCensus (u62AutModel hF) (u62_yCensus hF) hA e

end CFSG.ComponentClassification.RankTwoHypIICover.U62
