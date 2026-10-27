module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291G2RankCnt
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47f
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47 G2Rank
open scoped commutatorElement

theorem inG2Prime_holds : InG2Prime := by
  intro p hp hp5 G _ _ hG
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := default
  obtain ⟨F, hF, hFfin, hFcard, ⟨e⟩⟩ := exists_mulEquiv_sylow_G2 hp hG.2 P
  haveI : CharP F p := charP_of_natCard_eq_pow hp hFcard
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have h3 : (3 : F) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  rw [← (CFSG.SectionRank.pRank_sylow P).1]
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEP hEa => ?_
  have hEc : ∀ a b : G, a ∈ E → b ∈ E → a * b = b * a := fun a b ha hb => by
    have := hEa.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  let E1 : Subgroup ↥(P : Subgroup G) := E.subgroupOf P
  let E2 : Subgroup ↥(posUnipotent .G2 F) := E1.map e.toMonoidHom
  let E3 : Subgroup (ModGL .G2 F) := E2.map (posUnipotent .G2 F).subtype
  have hc1 : Nat.card E1 = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
  have hc2 : Nat.card E2 = Nat.card E1 :=
    Nat.card_congr (E1.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm
  have hc3 : Nat.card E3 = Nat.card E2 :=
    Nat.card_congr (E2.equivMapOfInjective _ (posUnipotent .G2 F).subtype_injective).toEquiv.symm
  have hE3 : E3 ≤ heightSeries .G2 F 1 := by
    rw [heightSeries_one]
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  have hcomm : ∀ x ∈ E3, ∀ y ∈ E3, ⁅x, y⁆ = 1 := by
    rintro _ ⟨u, ⟨v, hv, rfl⟩, rfl⟩ _ ⟨u', ⟨v', hv', rfl⟩, rfl⟩
    have hv2 : (v : G) ∈ E := Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 hv)
    have hv2' : (v' : G) ∈ E := Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 hv')
    have hvv : v * v' = v' * v := Subtype.ext (hEc _ _ hv2 hv2')
    have h1 : e v * e v' = e v' * e v := by rw [← map_mul, ← map_mul, hvv]
    exact commutatorElement_eq_one_iff_mul_comm.2 (congrArg Subtype.val h1)
  have hle := card_le_cube h2 h3 E3 hE3 hcomm
  rw [hc3, hc2, hc1, hFcard, pow_one] at hle
  exact hle

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
