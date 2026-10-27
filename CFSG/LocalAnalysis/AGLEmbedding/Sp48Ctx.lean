module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Pkg
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Moved

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Ctx

variable {G : Type} [Group G] [Finite G]

@[expose] def piOf (M H L : Subgroup G) : Subgroup G := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L

@[expose] def blkOf (M L : Subgroup G) (k : G) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
  barM M (L.map (MulAut.conj k).toMonoidHom)

omit [Finite G] in
theorem blkOf_one (M L : Subgroup G) : blkOf M L 1 = barM M L := by
  have e : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
    ext x
    simp
  rw [blkOf, e]

variable {P : Sylow 3 G} {M H R X U A L : Subgroup G}

structure Sp48Ctx (P : Sylow 3 G) (M H R X U A L : Subgroup G) : Prop where
  data : D1Sp48Data₂ P M H R X U A
  h84 : Asc81bEightFour
  h85 : Asc81bEightFive
  h86 : Asc81bEightSix
  h93 : Asc81bNineThree
  hD2 : D1NoXBlock
  hB3 : StmtBlockThree
  hb : StmtBlockInnerNormalizer
  hOut : KFactBlockThreeOut
  hNine : KFactBlockThreeOrderNine
  hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥
  block : IsWeakSBlock M (pCoreOf 2 H) L

theorem Sp48Ctx.h3 (c : Sp48Ctx P M H R X U A L) : D1PhaseThree 3 P M H R := c.data.surv.ph3

theorem Sp48Ctx.blk_component (c : Sp48Ctx P M H R X U A L) {k : G} (hk : k ∈ H ⊓ M) :
    IsComponentOf (blkOf M L k) ⊤ :=
  (c.h3.isWeakSBlock_map_conj c.block hk).component

theorem Sp48Ctx.relIndex_dvd (c : Sp48Ctx P M H R X U A L)
    {I : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hI : I ≤ barM M (piOf M H L)) (hI3 : IsPGroup 3 I)
    {k : G} (hk : k ∈ H ⊓ M) (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) :
    (Subgroup.centralizer (blkOf M L k : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex I ∣
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) :=
  relIndex_dvd_sylow hI3 (c.h3.relIndex_centralizer_dvd c.h84 c.h86 c.hD2 c.hb c.block hI hk) SL

omit [Finite G] in
theorem barPi_le_barE (M H L : Subgroup G) :
    barM M (piOf M H L) ≤ barM M (blockClosure M (H ⊓ M) L) :=
  Subgroup.map_mono (Subgroup.comap_mono inf_le_right)

theorem Sp48Ctx.eq_one (c : Sp48Ctx P M H R X U A L) {q : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hq : q ∈ barM M (piOf M H L)) (hq3 : IsPGroup 3 (Subgroup.zpowers q))
    (hqC : ∀ k ∈ H ⊓ M, q ∈ Subgroup.centralizer (blkOf M L k : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    q = 1 :=
  eq_one_of_centralizes_orbit inf_le_right c.block.toIsTwoPrimeComponent c.hO
    (barPi_le_barE M H L hq) hq3 hqC

theorem Sp48Ctx.pow_three (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (hs : Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) = 3)
    {q : ↥M ⧸ CFSG.pCore 2 ↥M} (hq : q ∈ barM M (piOf M H L))
    (hq3 : IsPGroup 3 (Subgroup.zpowers q)) : q ^ 3 = 1 := by
  refine c.eq_one (Subgroup.pow_mem _ hq 3)
    (hq3.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers q) 3)))
    fun k hk => pow_mem_of_relIndex_dvd ?_
  rw [← hs]
  exact c.relIndex_dvd (Subgroup.zpowers_le.mpr hq) hq3 hk SL

end Ctx

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Bounds2

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

theorem Sp48Ctx.card_le_two (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) {k₁ : G} (hk₁ : k₁ ∈ H ⊓ M)
    (h2 : ∀ k ∈ H ⊓ M, blkOf M L k = barM M L ∨ blkOf M L k = blkOf M L k₁)
    {I : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hI : I ≤ barM M (piOf M H L)) (hI3 : IsPGroup 3 I) :
    Nat.card I ≤ Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) := by
  set C₀ := Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₀
  set C₁ := Subgroup.centralizer (blkOf M L k₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₁
  have hbot : (C₀ ⊓ C₁) ⊓ I = ⊥ := by
    rw [eq_bot_iff]
    rintro q ⟨⟨hq0, hq1⟩, hqI⟩
    rw [Subgroup.mem_bot]
    refine c.eq_one (hI hqI) (hI3.to_le (Subgroup.zpowers_le.mpr hqI)) fun k hk => ?_
    rcases h2 k hk with h1 | h1 <;> rw [h1] <;> assumption
  have e : (C₀ ⊓ C₁).relIndex I = Nat.card I := by
    rw [← Subgroup.inf_relIndex_right, hbot, Subgroup.relIndex_bot_left]
  have hpos : 0 < Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) := Nat.card_pos
  have h0 : C₀.relIndex I ≤ Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) := by
    have := c.relIndex_dvd hI hI3 (H ⊓ M).one_mem SL
    rw [blkOf_one] at this
    exact Nat.le_of_dvd hpos this
  have h1 : C₁.relIndex I ≤ Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) :=
    Nat.le_of_dvd hpos (c.relIndex_dvd hI hI3 hk₁ SL)
  calc Nat.card I = (C₀ ⊓ C₁).relIndex I := e.symm
    _ ≤ C₀.relIndex I * C₁.relIndex I := Subgroup.relIndex_inf_le
    _ ≤ _ := Nat.mul_le_mul h0 h1

end Bounds2

end CFSG.AGLEmbedding
