module

public import CFSG.ClassicalInvolution.Q3.Q3TIVLayer
public import CFSG.ClassicalInvolution.Q3.Q3WAComp
public import CFSG.ClassicalInvolution.RouteD.TwinYR2XO
public import CFSG.ClassicalInvolution.Q3.Q3NGInv
public import CFSG.ClassicalInvolution.Q3.Q3TCCtx
public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3WAETLocal
public import CFSG.ClassicalInvolution.Q3.Q3WAStarMain
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt TwinElt.u range_le_iSup_fund_of_commuting)


namespace TwinLoc3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} (c : TwinLoc3 tY nY Ω z) {K T : Subgroup G}

include c

theorem mem_centralizingMembers_u (e : TwinElt K T z)
    (hKiso : ∀ N ∈ centralizingMembers Ω {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers Ω {z}, N ≠ T → Commutes T N) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) (hNT : N ≠ T) :
    N ∈ centralizingMembers Ω {e.u} :=
  e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm

theorem xOrbit (hCF : CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalGeneration 3 tY nY 1)
    (e : TwinElt K T z) (hK : K ∈ centralizingMembers Ω {z})
    (hT : T ∈ centralizingMembers Ω {z}) (hKT : K ≠ T)
    (hKiso : ∀ N ∈ centralizingMembers Ω {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers Ω {z}, N ≠ T → Commutes T N) {J N : Subgroup G}
    (hJ : J ∈ centralizingMembers Ω {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) (hNT : N ≠ T) :
    ∃ y ∈ locLayer Ω e.u, conjSub y J = N := by
  have hgen := range_le_iSup_fund_of_commuting hCF c.rf.nonempty c.d.ψ
  set H : Subgroup G := ⨆ (L : Subgroup G) (_ : L ∈ centralizingMembers Ω {z} ∧ L ≠ K ∧
    L ≠ T), L with hH
  have hHle : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K → L ≠ T → L ≤ H :=
    fun L hL hLK hLT => le_iSup₂_of_le L ⟨hL, hLK, hLT⟩ le_rfl
  have hHu : H ≤ locLayer Ω e.u :=
    iSup₂_le fun L hL => le_centralizingLayer
      (c.mem_centralizingMembers_u e hKiso hTiso hL.1 hL.2.1 hL.2.2)
  set A : Subgroup (locQuot Ω z) := (H.subgroupOf (locLayer Ω z)).map (Gaps.locMk Ω z) with hA
  have hfundA : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      R.map c.d.ψ ≤ A := by
    intro R hR
    obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (c.d.mem_fam R hR)
    have hLK : L ≠ K := fun h => c.not_fund_of_isolated hL (h ▸ hKiso) hR (h ▸ hLR)
    have hLT : L ≠ T := fun h => c.not_fund_of_isolated hL (h ▸ hTiso) hR (h ▸ hLR)
    rw [← hLR]
    exact Subgroup.map_mono (Subgroup.comap_mono (hHle L hL hLK hLT))
  have hrangeA : c.d.ψ.range ≤ A := hgen.trans (iSup₂_le fun R hR => hfundA R hR)
  obtain ⟨RJ, hRJ, hJR⟩ := c.big_of_ne hK hT hKT hKiso hTiso hJ hJK hJT
  obtain ⟨RN, hRN, hNR⟩ := c.big_of_ne hK hT hKT hKiso hTiso hN hNK hNT
  obtain ⟨g, hg⟩ := c.rf.y.sc RJ hRJ RN hRN
  have hg' : RN = RJ.map (MulAut.conj g).toMonoidHom := hg
  obtain ⟨y', hy', hyg⟩ := Subgroup.mem_map.mp (hrangeA ⟨g, rfl⟩)
  have hy : (y' : G) ∈ H := Subgroup.mem_subgroupOf.mp hy'
  refine ⟨y', hHu hy, ?_⟩
  have hyz : (y' : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    centralizingLayer_le_centralizer Ω {z} y'.2
  have hJy : conjSub (y' : G) J ∈ centralizingMembers Ω {z} := by
    refine ⟨c.hΩ.conjInvariant _ J hJ.1, fun x hx => ?_⟩
    have h1 : (y' : G)⁻¹ * x * y' ∈ J := mem_conjSub_iff.mp hx
    have h2 := hJ.2 h1
    have e' : x = (y' : G) * ((y' : G)⁻¹ * x * y') * (y' : G)⁻¹ := by group
    rw [e']
    exact mul_mem (mul_mem hyz h2) (inv_mem hyz)
  refine locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hJy hN ?_
  rw [Gaps.locImg_conjSub_layer J y', hyg, hJR, hNR, hg']
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

theorem oneComponent (hCF : CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalGeneration
      3 tY nY 1)
    (e : TwinElt K T z) (hK : K ∈ centralizingMembers Ω {z})
    (hT : T ∈ centralizingMembers Ω {z}) (hKT : K ≠ T)
    (hKiso : ∀ N ∈ centralizingMembers Ω {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers Ω {z}, N ≠ T → Commutes T N)
    (hP1u : LocalOddCentral Ω {e.u}) (hO3u : LocalOddThreeFree3 Ω e.u)
    (hNC : ∀ M ∈ centralizingMembers Ω {e.u}, ∃ N ∈ centralizingMembers Ω {z},
      N ≠ K ∧ N ≠ T ∧ ¬ Commutes M N)
    {ι : Type} (D : LieSystemData3 ι (locQuot Ω e.u) (locFamily Ω e.u)) :
    ∃ i₀ : ι, (∀ i : ι, i = i₀) ∧ ∀ N ∈ centralizingMembers Ω {z}, N ≠ K → N ≠ T →
      N ∈ compMembers3 Ω e.u D i₀ := by
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member hKiso hTiso
  have hJu := c.mem_centralizingMembers_u e hKiso hTiso hJ hJK hJT
  obtain ⟨i₀, hi₀, -⟩ := exists_unique_comp3 c.hΩ c.hex hP1u hO3u D hJu
  have hmem : ∀ N ∈ centralizingMembers Ω {z}, N ≠ K → N ≠ T →
      N ∈ compMembers3 Ω e.u D i₀ := by
    intro N hN hNK hNT
    refine ⟨c.mem_centralizingMembers_u e hKiso hTiso hN hNK hNT, ?_⟩
    obtain ⟨y, hy, hyN⟩ := c.xOrbit hCF e hK hT hKT hKiso hTiso hJ hJK hJT hN hNK hNT
    rw [← hyN, Gaps.locImg_conjSub_layer J ⟨y, hy⟩]
    rintro _ ⟨j, hj, rfl⟩
    exact ((range_normal3 D i₀).conj_mem j (hi₀.2 hj) _)
  refine ⟨i₀, fun i => ?_, hmem⟩
  by_contra hne
  obtain ⟨R, -, hRmem⟩ := D.meets i
  obtain ⟨M₀, hM₀, hM₀R⟩ := mem_locFamily_iff.mp hRmem
  have hM₀i : M₀ ∈ compMembers3 Ω e.u D i :=
    ⟨hM₀, hM₀R ▸ Subgroup.map_le_range _ _⟩
  obtain ⟨N, hN, hNK, hNT, hNc⟩ := hNC M₀ hM₀
  exact hNc (commutes_of_ne_comp3 c.hΩ c.hex hP1u hO3u D hne hM₀i (hmem N hN hNK hNT))

end TwinLoc3

end CFSG.ClassicalInvolution.Q3.Q3TIV
