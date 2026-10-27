module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOdd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore ordSL
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG OddCentralSplit)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open scoped MatrixGroups

section Images

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem map_ctEmbed_eq_of_N1 (e : L ≃* StatedSp 3 K) (k : Fin 3) {F : Type} [Field F]
    [CharP F 2] (σ : K ≃+* F) (β : StatedSp 2 K →* StatedSp 2 K)
    (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* G) (hΦE : ∀ x, Φ x ∈ neighbourCore e k)
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β x))) =
      ((e.symm (complSpEquiv k x : complSp K k) : L) : G))
    (T₄ : Subgroup (StatedSp 2 K)) :
    (((T₄.map β).map (statedSpMap (σ : K →+* F) 2)).map (ctEmbed 1)).map
        (Φ.codRestrict _ hΦE) =
      (modelToG e (T₄.map (complSpHom k))).subgroupOf (neighbourCore e k) := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    rw [mem_subgroupOf]
    change Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β x))) ∈ _
    rw [hN1]
    exact symm_mem_modelToG e ⟨x, hx, rfl⟩
  · intro hy
    rw [mem_subgroupOf] at hy
    obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
    refine ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    change Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β x))) = (y : G)
    rw [hN1, ← hxy]
    rfl

theorem natCard_map_blockSpecialLinear_oddFix {F : Type} [Field F] {E : Type*} [Group E]
    (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* E)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F)) :
    Nat.card ((blockSpecialLinear (K := F) oddFixBlock).map Φ) =
      Nat.card (SpecialLinearGroup (Fin 3) F) := by
  have hinj : Function.Injective (Φ.comp (blockSpecialLinear (K := F) oddFixBlock).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ hx1
    have hxc : x ∈ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) := hker hx1
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hxc
    have h00 : (x : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) 0 0 = 1 :=
      (mem_blockSpecialLinear.1 hx 0 0 (Or.inl (by decide))).trans (Matrix.one_apply_eq _)
    have hr1 : r = 1 := by
      rw [← hr] at h00
      simpa using h00
    apply Subtype.ext
    change x = 1
    apply Subtype.ext
    rw [← hr, hr1, map_one]
    rfl
  have hr : (Φ.comp (blockSpecialLinear (K := F) oddFixBlock).subtype).range =
      (blockSpecialLinear (K := F) oddFixBlock).map Φ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr, ← natCard_blockSpecialLinear_oddFix]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Images

section Piece

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem cube_dvd_natCard_pieceCore_zero_of_odd_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* StatedSp 3 K} (hn : SpThreeOddNormalized e f 2 true) :
    (Nat.card K) ^ 3 ∣ Nat.card (pieceCore e ({0} : Finset (Fin 3))) := by
  obtain ⟨F, _, _, _, σ, Φ, hF, hrange, hker, hN1⟩ := hn
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hFK : Nat.card F = Nat.card K := (Nat.card_congr σ.toEquiv).symm
  have hF4 : 4 ≤ Nat.card F := hFK ▸ hK4
  have hΦE : ∀ x, Φ x ∈ neighbourCore e 2 := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hker' : Φ'.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  set Y := modelToG e ((siegelTorus K 2).map (complSpHom (K := K) 2)) with hYdef
  have hY : Y ≤ neighbourCore e 2 := by
    refine (UnitaryPilot.modelToG_mono e ?_).trans
      (modelToG_complSp_le_neighbourCore e hK4 (by norm_num) 2)
    rintro _ ⟨x, -, rfl⟩
    exact (complSpEquiv 2 x).2
  rw [pieceCore_eq e (k := 2) (by decide), inf_centralizer_eq_of_le_sup (H := neighbourCore e 2)
    (X := modelToG e (rootTorusSp K 2)) (Y := Y) (centralizerPerfectCore_le_centralizer _)
    (UnitaryPilot.modelToG_mono e map_siegelTorus_two_le_leviTorusSp_zero)
    (by
      rw [← UnitaryPilot.modelToG_sup]
      exact UnitaryPilot.modelToG_mono e leviTorusSp_zero_le_sup),
    perfectCore_inf_centralizer_eq_map hY,
    Subgroup.card_map_of_injective (neighbourCore e 2).subtype_injective]
  have hTY := map_ctEmbed_eq_of_N1 e 2 σ tauSp Φ hΦE (fun x => hN1 x) (siegelTorus K 2)
  rw [map_tauSp_siegelTorus_eq σ, ← hΦ'] at hTY
  have h1 : (blockSpecialLinear (K := F) oddFixBlock).map Φ' ≤ perfectCore (centralizer
      ((Y.subgroupOf (neighbourCore e 2) : Subgroup (neighbourCore e 2)) :
        Set (neighbourCore e 2))) := by
    refine (Subgroup.map_mono (blockSpecialLinear_oddFix_le_perfectCore_centralizer hF4)).trans ?_
    have h2 := map_perfectCore_centralizer_le Φ' (oddStdTorus F)
    rw [oddStdTorus, hTY] at h2
    exact h2
  have h3 := Subgroup.card_dvd_of_le h1
  rw [natCard_map_blockSpecialLinear_oddFix Φ' hker'] at h3
  rw [← hFK]
  exact (cube_dvd_natCard_SL_three).trans h3

theorem ordSL_two_eq (q : ℕ) : ordSL 2 q = q * (q ^ 2 - 1) := by
  simp [ordSL]

theorem not_cube_dvd_sq_mul_fourth_sub_one {q : ℕ} (hq2 : 2 ∣ q) (hq : 0 < q) :
    ¬ q ^ 3 ∣ q ^ 2 * ((q ^ 2) ^ 2 - 1) := by
  intro h
  have h1 : q ^ 2 * q ∣ q ^ 2 * ((q ^ 2) ^ 2 - 1) := by rwa [← pow_succ]
  have h2 : q ∣ (q ^ 2) ^ 2 - 1 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
  have hev : Even ((q ^ 2) ^ 2) :=
    Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_iff_two_dvd.2 hq2, two_ne_zero⟩, two_ne_zero⟩
  have hq1 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hodd : Odd ((q ^ 2) ^ 2 - 1) := Nat.Even.sub_odd hq1 hev odd_one
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (hq2.trans h2))

omit [CharP K 2] in
theorem false_of_siegelFieldParam_of_cube_dvd [Finite K] (hK : 4 ≤ Nat.card K)
    (hq2 : 2 ∣ Nat.card K) {F' : Type}
    [Field F'] [Finite F'] (hF' : Nat.card F' = Nat.card K ^ 2) {e : L ≃* StatedSp 3 K} {t : G}
    {ι : K →+* F'} {σ' : F' ≃+* F'} (S : SiegelFieldParam e t ι σ')
    (h3 : (Nat.card K) ^ 3 ∣ Nat.card (pieceCore e ({0} : Finset (Fin 3)))) : False := by
  have h2 := S.natCard_pieceCore_singleton hK (by norm_num) (j := 0) (by decide)
  rw [h2, ordSL_two_eq, hF'] at h3
  exact not_cube_dvd_sq_mul_fourth_sub_one hq2 (by omega) h3

omit [CharP K 2] in
theorem false_of_siegelSwapParam_of_cube_dvd [Finite K] (hK : 4 ≤ Nat.card K)
    (hq2 : 2 ∣ Nat.card K) {e : L ≃* StatedSp 3 K} {t : G} (S : SiegelSwapParam e t)
    (h3 : (Nat.card K) ^ 3 ∣ Nat.card (pieceCore e ({0} : Finset (Fin 3)))) : False := by
  have h2 := S.natCard_pieceCore_singleton hK (by norm_num) (j := 0) (by decide)
  rw [h2, ordSL_two_eq, sq] at h3
  exact not_cube_dvd_sq_mul_sq_sub_one hq2 (by omega) h3

end Piece

@[expose] def SpThreeLinearOddTrivialSiegelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .linearOdd) → SpThreeOddTwisted e →
        t ∈ centralizer (modelToG e (siegelTorus K 3) : Set G) →
        (((modelToG e (siegelLevi K 3)).subgroupOf
          (centralizer (modelToG e (siegelTorus K 3) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (siegelTorus K 3) : Set G))))).Normal → False

theorem spThreeLinearOddTwistedFalseInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (htriv : SpThreeLinearOddTrivialSiegelInput) : SpThreeLinearOddTwistedFalseInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot htw
  have htC : t ∈ centralizer (L : Set G) := by
    have h1 : t ∈ zpowers t := mem_zpowers t
    rw [← hKt] at h1
    exact h1.1
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hq2 : 2 ∣ Nat.card K := by
    rw [hKc]
    exact dvd_pow_self 2 (by omega)
  have h3 := cube_dvd_natCard_pieceCore_zero_of_odd_twisted hKc hf
    (spThreeOddNormalized_of_twisted hset hKc hf e htC hto 2 (hroot 2) htw)
  obtain ⟨F', _, _, ι, σ', hσ, hfix⟩ := exists_quadraticExtension K
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  have hF' : Nat.card F' = Nat.card K ^ 2 := by
    rw [LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix, hKc, ← pow_mul,
      mul_comm]
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf le_rfl e htC hto
    (oddCentralSplit_siegelLevi (by norm_num)) ι hσ1 hσσ hfix with ⟨htX, hnorm⟩ | hS | hS
  · exact htriv G L hset f K hKc hf e t hto hKt hroot htw htX hnorm
  · obtain ⟨S⟩ := hS
    exact false_of_siegelFieldParam_of_cube_dvd hK4 hq2 hF' S h3
  · obtain ⟨S⟩ := hS
    exact false_of_siegelSwapParam_of_cube_dvd hK4 hq2 S h3

theorem spThreeKindCoverInput_linearOdd_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hs : SpThreeLinearOddStandardInput) (htriv : SpThreeLinearOddTrivialSiegelInput) :
    SpThreeKindCoverInput .linearOdd :=
  spThreeKindCoverInput_linearOdd_of_oriented hs
    (spThreeLinearOddTwistedFalseInput_of_clauses hcat hdet htriv)

end CFSG.SeitzReduction.SymplecticPilot
