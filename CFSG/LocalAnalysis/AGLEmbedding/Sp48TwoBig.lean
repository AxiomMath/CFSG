module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Cases

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section TwoBigAux

variable {G : Type} [Group G] [Finite G]

theorem pow_three_of_not_cyclic {Y : Type*} [Group Y] [Finite Y] {Q : Subgroup Y}
    (hQ : Nat.card Q = 9) (hc : ¬ IsCyclic Q) {x : Y} (hx : x ∈ Q) : x ^ 3 = 1 := by
  set x' : Q := ⟨x, hx⟩ with hx'
  have h9 : orderOf x' ∣ 3 ^ 2 := by
    have := orderOf_dvd_natCard x'
    rw [hQ] at this
    simpa using this
  obtain ⟨b, hb2, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
  have hb1 : b ≤ 1 := by
    by_contra h
    have hb' : b = 2 := by omega
    apply hc
    exact isCyclic_of_orderOf_eq_card x' (by rw [hb, hb', hQ]; norm_num)
  have h3 : orderOf x' ∣ 3 := by
    rw [hb]
    exact (Nat.pow_dvd_pow 3 hb1).trans (by norm_num)
  have := orderOf_dvd_iff_pow_eq_one.mp h3
  have := congrArg Subtype.val this
  simpa using this

theorem pow_three_of_mem_sup {Y : Type*} [Group Y] {S₀ S₁ : Subgroup Y}
    (hC : S₀ ≤ Subgroup.centralizer (S₁ : Set Y)) (h₀ : ∀ x ∈ S₀, x ^ 3 = 1)
    (h₁ : ∀ x ∈ S₁, x ^ 3 = 1) {x : Y} (hx : x ∈ S₀ ⊔ S₁) : x ^ 3 = 1 := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right S₀ S₁
    (hC.trans (Subgroup.centralizer_le_normalizer _))] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have hab : Commute a b := (Subgroup.mem_centralizer_iff.mp (hC ha) b hb).symm
  rw [hab.mul_pow, h₀ a ha, h₁ b hb, one_mul]

variable {M H L : Subgroup G}

omit [Finite G] in
theorem pow_three_of_mem_sylConj (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (hSL : ∀ x ∈ (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)), x ^ 3 = 1)
    (g : ↥M ⧸ CFSG.pCore 2 ↥M) {x : ↥M ⧸ CFSG.pCore 2 ↥M} (hx : x ∈ sylConj M H L SL g) :
    x ^ 3 = 1 := by
  obtain ⟨_, ⟨l, hl, rfl⟩, rfl⟩ := hx
  have h1 := hSL l hl
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
  rw [conj_pow, ← Subgroup.coe_pow, h1]
  simp

end TwoBigAux

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section TwoBig

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

theorem Sp48Ctx.false_of_two_big (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (hs : 3 ^ 2 ∣ Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L))) {k₁ : G}
    (hk₁ : k₁ ∈ H ⊓ M) (h01 : blkOf M L 1 ≠ blkOf M L k₁)
    (h2 : ∀ k ∈ H ⊓ M, blkOf M L k = barM M L ∨ blkOf M L k = blkOf M L k₁) : False := by
  have h3 := c.h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Pib := barM M (piOf M H L) with hPib
  set Q := barM M (R ⊓ piOf M H L) with hQ
  obtain ⟨hQPi, hQ3, hQcard⟩ := c.Q_facts
  have hsq := c.sq_dvd SL hk₁ h01
  obtain ⟨f, hf⟩ := SL.isPGroup'.exists_card_eq
  have hf2 : 2 ≤ f := by
    rw [hf] at hs
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hs
  have hfle : f ≤ 2 := by
    by_contra hlt
    have h27 : 3 ^ 3 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle := Nat.le_of_dvd Nat.card_pos hsq
    have h243 : Nat.card (R ⊓ piOf M H L : Subgroup G) ≤ 243 :=
      le_trans c.card_le (by norm_num)
    rw [hf] at hle
    nlinarith
  have hs9 : Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) = 9 := by
    rw [hf, show f = 2 by omega]
    norm_num
  rw [hs9] at hsq
  have hup := c.card_le_two SL hk₁ h2 hQPi hQ3
  rw [hs9, hQcard] at hup
  have h81 : Nat.card (R ⊓ piOf M H L : Subgroup G) = 81 :=
    le_antisymm hup (Nat.le_of_dvd Nat.card_pos hsq)
  have hUle := c.U_le_of_dvd (by rw [h81]; norm_num)
  have hPLK : blockParabolic M (pCoreOf 2 H) L ≤ barM M (H ⊓ M) :=
    (blockParabolic_le_barM hKeq c.block.le le_rfl).trans
      (Subgroup.map_mono (Subgroup.comap_mono inf_le_left))
  have hLVa := (c.hNine G M (pCoreOf 2 H) L h3.isKGroup.1 h3.asc81bHyp c.block
    (h3.nineThree c.h93 c.block) (h3.nineThree_not_one c.h85 c.hD2 c.block).1
    (h3.not_isSylowTwoOf_inf c.h85 c.hD2 c.block)
    (fun l hl hcond => c.hb h3 c.h84 c.h86 c.hD2 c.block l hl hcond)
    (fun W hW hWW => c.data.coprime_of_perfect (hW.trans hPLK) hWW)).1 SL
  have hnc : ¬ IsCyclic (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) :=
    fun hc => hLVa ⟨hc, hs9⟩
  have hSL3 : ∀ x ∈ (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)), x ^ 3 = 1 :=
    fun x hx => pow_three_of_not_cyclic hs9 hnc hx
  have h1 : (1 : G) ∈ H ⊓ M := (H ⊓ M).one_mem
  set S₀ := sylConj M H L SL (mk ⟨1, h1.2⟩) with hS₀
  set S₁ := sylConj M H L SL (mk ⟨k₁, hk₁.2⟩) with hS₁
  have hBC : S₀ ≤ Subgroup.centralizer (blkOf M L k₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (sylConj_le_blk SL h1.2).trans (c.blk_le_centralizer h1 hk₁ h01)
  obtain ⟨hTle, hT3, hTcard⟩ := c.sup_sylConj SL (c.sylConj_le_barPi SL h1)
    (isPGroup_sylConj SL _) hk₁ hBC
  rw [card_sylConj, hs9] at hTcard
  have hT3' : ∀ x ∈ S₀ ⊔ S₁, x ^ 3 = 1 := fun x hx =>
    pow_three_of_mem_sup (hBC.trans (Subgroup.centralizer_le (sylConj_le_blk SL hk₁.2)))
      (fun y hy => pow_three_of_mem_sylConj SL hSL3 _ hy)
      (fun y hy => pow_three_of_mem_sylConj SL hSL3 _ hy) hx
  have hsyl : ∀ B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), B ≤ Pib → IsPGroup 3 B →
      Nat.card B = 81 → ∃ P₁ : Sylow 3 Pib, B.subgroupOf Pib = P₁ := by
    intro B hB hB3 hBc
    obtain ⟨P₁, hP₁⟩ := (hB3.comap_subtype (K := Pib)).exists_le_sylow
    refine ⟨P₁, Subgroup.eq_of_le_of_card_ge hP₁ ?_⟩
    have hP₁c : Nat.card ((P₁ : Subgroup Pib).map Pib.subtype) ∣
        Nat.card (R ⊓ piOf M H L : Subgroup G) :=
      c.data.card_dvd_of_le_barPi c.hB3 c.block
        (Subgroup.map_subtype_le (P₁ : Subgroup Pib)) (P₁.isPGroup'.map _)
    rw [h81, Subgroup.card_map_of_injective Pib.subtype_injective] at hP₁c
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hBc]
    exact Nat.le_of_dvd (by norm_num) hP₁c
  obtain ⟨P₁, hP₁⟩ := hsyl Q hQPi hQ3 (by rw [hQcard, h81])
  obtain ⟨P₂, hP₂⟩ := hsyl (S₀ ⊔ S₁) hTle hT3 (by rw [hTcard])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Pib P₁ P₂
  obtain ⟨u, -, huU, -, hu9, -⟩ := c.data.homocyclic
  have hUM : U ≤ M := c.data.U_le.trans h3.le_M
  have hU3 : IsPGroup 3 U := h3.isPGroup_R.to_le c.data.U_le
  have huQ : mk ⟨u, hUM huU⟩ ∈ Q :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hUle huU))
  set y : Pib := ⟨mk ⟨u, hUM huU⟩, hQPi huQ⟩ with hy
  have hyP₁ : y ∈ (P₁ : Subgroup Pib) := by
    rw [← hP₁]
    exact Subgroup.mem_subgroupOf.mpr huQ
  have hgy : MulAut.conj g • y ∈ (P₂ : Subgroup Pib) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P₁ : Subgroup Pib) hyP₁
  rw [← hP₂, Subgroup.mem_subgroupOf] at hgy
  have hcube := hT3' _ hgy
  have hcube' : (MulAut.conj g • y) ^ 3 = 1 := Subtype.ext (by simpa using hcube)
  rw [MulAut.smul_def, MulAut.conj_apply, conj_pow, mul_inv_eq_one, mul_eq_left] at hcube'
  have hy3 : (mk ⟨u, hUM huU⟩) ^ 3 = 1 := by
    have := congrArg Subtype.val hcube'
    simpa [hy] using this
  have h9 := orderOf_dvd_of_pow_eq_one hy3
  rw [orderOf_mk_of_isPGroup Nat.prime_three (by norm_num) hUM hU3 huU, hu9] at h9
  norm_num at h9

end TwoBig

end CFSG.AGLEmbedding
