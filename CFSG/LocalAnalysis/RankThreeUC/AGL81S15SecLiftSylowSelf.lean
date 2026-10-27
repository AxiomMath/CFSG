module

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521SecLiftTorus
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PG
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFiveAux
import CFSG.GroupTheory.PermSylowTwo.Alt
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHBinaryFlagBlocks
import CFSG.LieType.SteinbergBROddSylowCore
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2FinInv
public import CFSG.GH74.KGroups.PSLN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.ComponentInitial
open CFSG.QuasithinUnique

private theorem nonempty_mulEquiv_projectiveSL_of_isL5Two {S : Type} [Group S] (h : IsL5Two S) :
    Nonempty (S ≃* LinearFlag.projectiveSL 5 (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨i, hv⟩, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  have hd' : i = .A 4 q := hd
  subst hd'
  obtain ⟨hp, hn⟩ := small1522_simple_center_aux2 Nat.prime_two hq
  have hmod := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  rw [hp, hn] at hmod
  obtain ⟨e₁⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated (F := ZMod 2) 5 2 1 (by norm_num)
    (by rw [Nat.card_zmod, pow_one]) hmod
  exact ⟨e₁.trans
    (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 5 (ZMod 2))).symm⟩

private theorem inf_normalizer_le_of_isL5Two {G : Type} [Group G] [Finite G] {M S : Subgroup G}
    (h : IsL5Two ↥M) (hS : IsSylowTwoOf S M) : M ⊓ Subgroup.normalizer (S : Set G) ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_projectiveSL_of_isL5Two h
  obtain ⟨P₀, hP₀⟩ := LinearFlag.exists_sylow_projUnitriangular (K := ZMod 2) 2
    (show 1 ≤ 5 by norm_num)
  have hN₀ : Subgroup.normalizer ((P₀ : Subgroup (LinearFlag.projectiveSL 5 (ZMod 2))) :
      Set (LinearFlag.projectiveSL 5 (ZMod 2))) = P₀ := by
    rw [hP₀, LinearFlag.normalizer_projUnitriangular 2, LinearFlag.projUpperTriangular,
      SteinbergCH.upperTriangular_eq_unitriangular_of_card_two (Nat.card_zmod 2),
      LinearFlag.projUnitriangular]
  obtain ⟨P, hP⟩ := CFSG.LieType.SteinbergBR.OddSylow.exists_selfNormalizing_of_equiv e P₀ hN₀
  have hN := CFSG.Quasithin.E9P2.FinInv.normalizer_eq_of_isSylowTwoOf
    (CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_subgroupOf_top hS)
    (CFSG.Quasithin.E9P2.FinInv.isSylowTwoOf_top_of_sylow P) hP
  intro x hx
  obtain ⟨hxM, hxN⟩ := Subgroup.mem_inf.mp hx
  have h1 : (⟨x, hxM⟩ : ↥M) ∈ Subgroup.normalizer ((S.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hS.1, Subgroup.mem_subgroupOf]
    exact hxN
  rw [hN, Subgroup.mem_subgroupOf] at h1
  exact h1

variable {X : Type} [Group X] [Finite X]

private theorem isSylowTwoOf_map_toStar_inf {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hL : LiftOf T L Ls) (hLn : L.Normal) :
    IsSylowTwoOf ((T ⊓ L).map (toStar T)) Ls := by
  rw [← hL.2]
  exact CFSG.AGLEmbedding.AscEightFive.isSylowTwoOf_map (CFSG.Quasithin.A4.isSylowTwoOf_inf_normal
    hX.sylow le_top (Subgroup.normalizer_eq_top_iff.2 hLn).ge) (toStar T)

theorem gnA_le_map_normalizer_two_of_inf_normalizer_le {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hL : LiftOf T L Ls) (hLn : L.Normal)
    (hN : Ls ⊓ Subgroup.normalizer ((T ⊓ L).map (toStar T) : Set (X ⧸ gnC T)) ≤
      (T ⊓ L).map (toStar T)) :
    gnA T T₂ Ls ≤ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T) := by
  intro a ha
  obtain ⟨n, hnA, hnN, b, hb, rfl⟩ := gnA_frattini_two hX hg hL hLn ha
  have hTN : T ≤ Subgroup.normalizer (T₂ : Set X) := IsGNPair.le_normalizer₂ hg.pair
  exact Subgroup.mul_mem _ (Subgroup.map_mono (inf_le_inf_right L hTN)
    (hN (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hnA).2, hnN⟩))) hb

theorem gnA_le_map_normalizer_two_of_A8_L5 {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hL : LiftOf T L Ls)
    (hLn : L.Normal) (hbig : Nonempty (↥Ls ≃* alternatingGroup (Fin 8)) ∨ IsL5Two ↥Ls) :
    gnA T T₂ Ls ≤ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T) := by
  have hS := isSylowTwoOf_map_toStar_inf hX hL hLn
  refine gnA_le_map_normalizer_two_of_inf_normalizer_le hX hg hL hLn ?_
  rcases hbig with he | h
  · obtain ⟨e⟩ := he
    exact CFSG.GroupTheory.PermSylowTwo.inf_normalizer_le_of_mulEquiv_alt (by norm_num) e hS
  · exact inf_normalizer_le_of_isL5Two h hS

end CFSG.LocalAnalysis.RankThreeUC.S15
