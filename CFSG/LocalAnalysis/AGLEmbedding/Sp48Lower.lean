module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Ctx

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Lower

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

@[expose] def sylConj (M H L : Subgroup G) (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (g : ↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
  ((SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)).map
    (blockParabolic M (pCoreOf 2 H) L).subtype).map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem card_sylConj (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (g : ↥M ⧸ CFSG.pCore 2 ↥M) :
    Nat.card (sylConj M H L SL g) =
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) := by
  rw [sylConj, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

omit [Finite G] in
theorem isPGroup_sylConj (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (g : ↥M ⧸ CFSG.pCore 2 ↥M) : IsPGroup 3 (sylConj M H L SL g) :=
  (SL.isPGroup'.map _).map _

omit [Finite G] in
theorem sylConj_le_blk (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) {k : G}
    (hkM : k ∈ M) :
    sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hkM⟩) ≤ blkOf M L k := by
  rw [blkOf, barM_map_conj hkM]
  refine Subgroup.map_mono ?_
  rintro _ ⟨x, -, rfl⟩
  exact blockParabolic_le_barM' M (pCoreOf 2 H) L x.2

theorem Sp48Ctx.sylConj_le_barPi (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) {k : G} (hk : k ∈ H ⊓ M) :
    sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩) ≤ barM M (piOf M H L) := by
  have hkS : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (c.h3.inf_eq_inf_normalizer_twoCore ▸ hk).2
  refine le_trans ?_ (blockParabolic_conj_le_barPi c.h3.inf_eq_inf_normalizer_twoCore
    c.block.le hk)
  rw [blockParabolic_map_conj hk.2 hkS]
  refine Subgroup.map_mono ?_
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem Sp48Ctx.blk_le_centralizer (c : Sp48Ctx P M H R X U A L) {k k' : G} (hk : k ∈ H ⊓ M)
    (hk' : k' ∈ H ⊓ M) (hne : blkOf M L k ≠ blkOf M L k') :
    blkOf M L k ≤ Subgroup.centralizer (blkOf M L k' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (c.blk_component hk)
      (c.blk_component hk') hne)

theorem Sp48Ctx.sup_sylConj (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) {B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hB : B ≤ barM M (piOf M H L)) (hB3 : IsPGroup 3 B) {k : G} (hk : k ∈ H ⊓ M)
    (hBC : B ≤ Subgroup.centralizer (blkOf M L k : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    B ⊔ sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩) ≤
        barM M (piOf M H L) ∧
      IsPGroup 3 (B ⊔ sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      Nat.card (B ⊔ sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) =
        Nat.card B * Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) := by
  have hcard := card_sup_of_le_centralizer_component c.hO (c.blk_component hk)
    (sylConj_le_blk SL hk.2) (isPGroup_sylConj SL _) hBC
  rw [card_sylConj] at hcard
  refine ⟨sup_le hB (c.sylConj_le_barPi SL hk), ?_, hcard⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hB3.exists_card_eq
  obtain ⟨f, hf⟩ := SL.isPGroup'.exists_card_eq
  exact IsPGroup.of_card (n := a + f) (by rw [hcard, ha, hf, pow_add])

end Lower

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Lower2

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

theorem Sp48Ctx.sq_dvd (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) {k₁ : G} (hk₁ : k₁ ∈ H ⊓ M)
    (h01 : blkOf M L 1 ≠ blkOf M L k₁) :
    Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) ∣
      Nat.card (R ⊓ piOf M H L : Subgroup G) := by
  have h1 : (1 : G) ∈ H ⊓ M := (H ⊓ M).one_mem
  have hB₀ := c.sylConj_le_barPi SL h1
  have hBC := (sylConj_le_blk SL h1.2).trans (c.blk_le_centralizer h1 hk₁ h01)
  obtain ⟨hle, h3g, hcard⟩ := c.sup_sylConj SL hB₀ (isPGroup_sylConj SL _) hk₁ hBC
  rw [card_sylConj] at hcard
  rw [← hcard]
  exact c.data.card_dvd_of_le_barPi c.hB3 c.block hle h3g

theorem Sp48Ctx.cube_dvd (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) {k₁ k₂ : G} (hk₁ : k₁ ∈ H ⊓ M)
    (hk₂ : k₂ ∈ H ⊓ M) (h01 : blkOf M L 1 ≠ blkOf M L k₁) (h02 : blkOf M L 1 ≠ blkOf M L k₂)
    (h12 : blkOf M L k₁ ≠ blkOf M L k₂) :
    Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) ∣
      Nat.card (R ⊓ piOf M H L : Subgroup G) := by
  have h1 : (1 : G) ∈ H ⊓ M := (H ⊓ M).one_mem
  have hB₀ := c.sylConj_le_barPi SL h1
  have hBC := (sylConj_le_blk SL h1.2).trans (c.blk_le_centralizer h1 hk₁ h01)
  obtain ⟨hle, h3g, hcard⟩ := c.sup_sylConj SL hB₀ (isPGroup_sylConj SL _) hk₁ hBC
  rw [card_sylConj] at hcard
  have hBC₂ : sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨1, h1.2⟩) ⊔
      sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k₁, hk₁.2⟩) ≤
      Subgroup.centralizer (blkOf M L k₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    sup_le ((sylConj_le_blk SL h1.2).trans (c.blk_le_centralizer h1 hk₂ h02))
      ((sylConj_le_blk SL hk₁.2).trans (c.blk_le_centralizer hk₁ hk₂ h12))
  obtain ⟨hle', h3g', hcard'⟩ := c.sup_sylConj SL hle h3g hk₂ hBC₂
  rw [hcard] at hcard'
  rw [← hcard']
  exact c.data.card_dvd_of_le_barPi c.hB3 c.block hle' h3g'

theorem Sp48Ctx.four_dvd (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) {k₁ k₂ k₃ : G} (hk₁ : k₁ ∈ H ⊓ M)
    (hk₂ : k₂ ∈ H ⊓ M) (hk₃ : k₃ ∈ H ⊓ M) (h01 : blkOf M L 1 ≠ blkOf M L k₁)
    (h02 : blkOf M L 1 ≠ blkOf M L k₂) (h03 : blkOf M L 1 ≠ blkOf M L k₃)
    (h12 : blkOf M L k₁ ≠ blkOf M L k₂) (h13 : blkOf M L k₁ ≠ blkOf M L k₃)
    (h23 : blkOf M L k₂ ≠ blkOf M L k₃) :
    Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) ∣
      Nat.card (R ⊓ piOf M H L : Subgroup G) := by
  have h1 : (1 : G) ∈ H ⊓ M := (H ⊓ M).one_mem
  set S₀ := sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨1, h1.2⟩) with hS₀
  set S₁ := sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k₁, hk₁.2⟩) with hS₁
  set S₂ := sylConj M H L SL (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k₂, hk₂.2⟩) with hS₂
  have hB₀ := c.sylConj_le_barPi SL h1
  have hBC := (sylConj_le_blk SL h1.2).trans (c.blk_le_centralizer h1 hk₁ h01)
  obtain ⟨hle, h3g, hcard⟩ := c.sup_sylConj SL hB₀ (isPGroup_sylConj SL _) hk₁ hBC
  rw [card_sylConj] at hcard
  have hBC₂ : S₀ ⊔ S₁ ≤ Subgroup.centralizer (blkOf M L k₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    sup_le ((sylConj_le_blk SL h1.2).trans (c.blk_le_centralizer h1 hk₂ h02))
      ((sylConj_le_blk SL hk₁.2).trans (c.blk_le_centralizer hk₁ hk₂ h12))
  obtain ⟨hle', h3g', hcard'⟩ := c.sup_sylConj SL hle h3g hk₂ hBC₂
  rw [hcard] at hcard'
  have hBC₃ : S₀ ⊔ S₁ ⊔ S₂ ≤
      Subgroup.centralizer (blkOf M L k₃ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    sup_le (sup_le ((sylConj_le_blk SL h1.2).trans (c.blk_le_centralizer h1 hk₃ h03))
      ((sylConj_le_blk SL hk₁.2).trans (c.blk_le_centralizer hk₁ hk₃ h13)))
      ((sylConj_le_blk SL hk₂.2).trans (c.blk_le_centralizer hk₂ hk₃ h23))
  obtain ⟨hle'', h3g'', hcard''⟩ := c.sup_sylConj SL hle' h3g' hk₃ hBC₃
  rw [hcard'] at hcard''
  rw [← hcard'']
  exact c.data.card_dvd_of_le_barPi c.hB3 c.block hle'' h3g''

end Lower2

end CFSG.AGLEmbedding
