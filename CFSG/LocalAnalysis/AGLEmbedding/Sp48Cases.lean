module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Lower

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Shared

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

theorem Sp48Ctx.Q_facts (c : Sp48Ctx P M H R X U A L) :
    barM M (R ⊓ piOf M H L) ≤ barM M (piOf M H L) ∧ IsPGroup 3 (barM M (R ⊓ piOf M H L)) ∧
      Nat.card (barM M (R ⊓ piOf M H L)) = Nat.card (R ⊓ piOf M H L : Subgroup G) := by
  have h3 := c.h3
  have hRP : IsPGroup 3 (R ⊓ piOf M H L : Subgroup G) := h3.isPGroup_R.to_le inf_le_left
  have hRM : (R ⊓ piOf M H L : Subgroup G) ≤ M := inf_le_left.trans h3.le_M
  exact ⟨Subgroup.map_mono (Subgroup.comap_mono inf_le_right),
    (hRP.comap_subtype (K := M)).map _,
    card_barM_of_isPGroup Nat.prime_three (by norm_num) hRM hRP⟩

theorem Sp48Ctx.U_le_of_dvd (c : Sp48Ctx P M H R X U A L)
    (h81 : 3 ^ 4 ∣ Nat.card (R ⊓ piOf M H L : Subgroup G)) : U ≤ R ⊓ piOf M H L := by
  rcases (c.data.Pi_cases c.hB3 c.block).2 with h1 | h1 | h1 | h1
  · have h1' : (R ⊓ piOf M H L : Subgroup G) = X := h1
    rw [h1', c.data.card_X] at h81
    norm_num at h81
  · have h1' : (R ⊓ piOf M H L : Subgroup G) = A := h1
    rw [h1', c.data.card_A] at h81
    norm_num at h81
  · have h1' : (R ⊓ piOf M H L : Subgroup G) = U := h1
    rw [h1']
  · have h1' : (R ⊓ piOf M H L : Subgroup G) = R := h1
    rw [h1']
    exact c.data.U_le

theorem Sp48Ctx.card_le (c : Sp48Ctx P M H R X U A L) :
    Nat.card (R ⊓ piOf M H L : Subgroup G) ≤ 3 ^ 5 :=
  c.data.card_R ▸ Subgroup.card_le_of_le inf_le_left

theorem Sp48Ctx.three_dvd (c : Sp48Ctx P M H R X U A L) :
    3 ∣ Nat.card (blockParabolic M (pCoreOf 2 H) L) := by
  have h3 := c.h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, ⟨hyS, hyL⟩, hy3, l, hl, hlQ⟩ := c.hB3 h3 c.block
  have hyM : y ∈ M := c.block.le hyL
  set yb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ with hyb
  have hyP : yb ∈ blockParabolic M (pCoreOf 2 H) L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hyS, hyL⟩)
  have hyb1 : yb ≠ 1 := by
    intro h1
    apply hlQ
    have hlM : l ∈ M := c.block.le hl
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨y, hyM⟩ * ⟨l, hlM⟩ * ⟨y, hyM⟩⁻¹ *
        ⟨l, hlM⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hyb, h1]
      group
    exact coe_mem_pCoreOf_two_of_mk_eq_one _ h2
  obtain ⟨a, ha⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
  have hya : (⟨y, hyM⟩ : M) ^ 3 ^ a = 1 := Subtype.ext (by simpa using congrArg Subtype.val ha)
  have hyba : yb ^ 3 ^ a = 1 := by rw [hyb, ← map_pow, hya, map_one]
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hyba)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hb
    exact hyb1 hb
  have h3o : 3 ∣ orderOf yb := hb ▸ dvd_pow_self 3 hb0
  exact h3o.trans (Subgroup.orderOf_dvd_natCard _ hyP)

theorem Sp48Ctx.sylow_card (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) :
    Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) = 3 ∨
      3 ^ 2 ∣ Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := SL.dvd_card_of_dvd_card c.three_dvd
  obtain ⟨f, hf⟩ := SL.isPGroup'.exists_card_eq
  rw [hf] at h3 ⊢
  rcases f with _ | _ | f
  · norm_num at h3
  · left; norm_num
  · right
    exact pow_dvd_pow 3 (by omega)

theorem Sp48Ctx.not_U_le (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (hs : Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) = 3) :
    ¬ U ≤ R ⊓ piOf M H L := by
  intro hU
  have h3 := c.h3
  obtain ⟨u, -, huU, -, hu9, -⟩ := c.data.homocyclic
  have hUM : U ≤ M := c.data.U_le.trans h3.le_M
  have hU3 : IsPGroup 3 U := h3.isPGroup_R.to_le c.data.U_le
  set ub := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨u, hUM huU⟩ with hub
  have hQ := c.Q_facts
  have huQ : ub ∈ barM M (R ⊓ piOf M H L) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hU huU))
  have h1 := c.pow_three SL hs (hQ.1 huQ) (hQ.2.1.to_le (Subgroup.zpowers_le.mpr huQ))
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hub, orderOf_mk_of_isPGroup Nat.prime_three (by norm_num) hUM hU3 huU, hu9] at h2
  norm_num at h2

end Shared

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section ManyBlocks

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

theorem Sp48Ctx.false_of_four (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (hs : Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) = 3) {k₁ k₂ k₃ : G}
    (hk₁ : k₁ ∈ H ⊓ M) (hk₂ : k₂ ∈ H ⊓ M) (hk₃ : k₃ ∈ H ⊓ M)
    (h01 : blkOf M L 1 ≠ blkOf M L k₁) (h02 : blkOf M L 1 ≠ blkOf M L k₂)
    (h03 : blkOf M L 1 ≠ blkOf M L k₃) (h12 : blkOf M L k₁ ≠ blkOf M L k₂)
    (h13 : blkOf M L k₁ ≠ blkOf M L k₃) (h23 : blkOf M L k₂ ≠ blkOf M L k₃) : False := by
  have h := c.four_dvd SL hk₁ hk₂ hk₃ h01 h02 h03 h12 h13 h23
  rw [hs] at h
  exact c.not_U_le SL hs (c.U_le_of_dvd (by norm_num at h ⊢; exact h))

theorem Sp48Ctx.false_of_three_big (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (hs : 3 ^ 2 ∣ Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L))) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ H ⊓ M) (hk₂ : k₂ ∈ H ⊓ M) (h01 : blkOf M L 1 ≠ blkOf M L k₁)
    (h02 : blkOf M L 1 ≠ blkOf M L k₂) (h12 : blkOf M L k₁ ≠ blkOf M L k₂) : False := by
  have h := c.cube_dvd SL hk₁ hk₂ h01 h02 h12
  have hle := Nat.le_of_dvd Nat.card_pos h
  have h9 : 9 ≤ Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) :=
    Nat.le_of_dvd Nat.card_pos (by simpa using hs)
  have h243 : Nat.card (R ⊓ piOf M H L : Subgroup G) ≤ 243 := le_trans c.card_le (by norm_num)
  have h81 : 81 ≤ Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) := by nlinarith
  have h729 : 729 ≤ Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) *
      Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) := by nlinarith
  omega

end ManyBlocks

end CFSG.AGLEmbedding
