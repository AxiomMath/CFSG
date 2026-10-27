module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOddModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphNormalOdd

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open LinearFlag
open scoped MatrixGroups

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] def SpThreeOddNormalized (e : L ≃* StatedSp 3 K) (f : ℕ) (k : Fin 3) (b : Bool) :
    Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : K ≃+* F)
    (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* G),
    Nat.card F = 2 ^ f ∧ Φ.range = neighbourCore e k ∧
      Φ.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) ∧
      ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (cond b (tauSp x) x))) =
        ((e.symm (complSpEquiv k x : complSp K k) : L) : G)

theorem spThreeOddNormalized_false_or_true {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .linearOdd) :
    SpThreeOddNormalized e f k false ∨ SpThreeOddNormalized e f k true := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K k)) : Set G) :=
    le_normalizer_neighbourCore e htC k
  obtain ⟨F, _, _, _, σ, ρ, hF, hρ, hker, hN1⟩ :=
    exists_normalized_neighbourCore_linearOdd_three hset hKc hf e htC ht k rfl rfl hk hN
  have : Group.IsPerfect (centralizerPerfectCore (modelToG e (rootTorusSp K k))) :=
    Subgroup.isPerfect_iff.2 (perfectCore_perfect _)
  have hF2 : Nat.card F ≠ 2 := by
    rw [hF]
    intro h2
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating (2 * 2) F :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by norm_num) hF2
      (fun h' => absurd h'.1 (by norm_num)) (fun h' => absurd h'.1 (by norm_num))
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := F4Pilot.exists_lift_of_central (proj (2 * 2 + 1) F)
    (proj_surjective _ _)
    (fun E' _ _ π' hπ' hker' =>
      CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating (m := 2 * 2)
        (by norm_num) hsep hπ' hker') ρ hρ hker
  have hrange : ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp Φ₀).range =
      neighbourCore e k := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  have hkerΦ : ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp Φ₀).ker ≤
      center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) := by
    intro g hg
    have hg₀ : Φ₀ g = 1 := (centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype_injective
      (by rw [map_one]; exact hg)
    have h1 := hΦ₀ g
    rw [hg₀, map_one, eq_comm, proj_eq_one_iff] at h1
    exact LinearFlag.scalars_le_center (2 * 2 + 1) F h1
  have hDE : ∀ x : StatedSp 2 K, ((e.symm (complSpEquiv k x : complSp K k) : L) : G) ∈
      centralizerPerfectCore (modelToG e (rootTorusSp K k)) := by
    intro x
    exact modelToG_complSp_le_neighbourCore e hK4 (by norm_num) k
      (symm_mem_modelToG e (complSpEquiv k x).2)
  let ιD : StatedSp 2 K →* centralizerPerfectCore (modelToG e (rootTorusSp K k)) :=
    ((L.subtype.comp e.symm.toMonoidHom).comp
      ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom)).codRestrict _ hDE
  have : Group.IsPerfect (StatedSp 2 K) := isPerfect_statedSp_of_four_le hK4 2
  have key : ∀ (β : StatedSp 2 K →* StatedSp 2 K),
      (∀ (x : StatedSp 2 K) (y : centralizerPerfectCore (modelToG e (rootTorusSp K k))),
        (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
          ρ y = ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 (β x))) →
      ∀ x : StatedSp 2 K, ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp
        Φ₀) (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β x))) =
          ((e.symm (complSpEquiv k x : complSp K k) : L) : G) := by
    intro β hβ x
    have heq := LinearPilot.eq_of_comp_eq_of_ker_le_center (S := StatedSp 2 K) hker
      (φ := Φ₀.comp ((ctEmbed 1).comp ((statedSpMap (σ : K →+* F) 2).comp β))) (ψ := ιD)
      (fun x => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hΦ₀,
          hβ x (ιD x) rfl]
        rfl)
    exact congrArg (fun Ψ : StatedSp 2 K →* centralizerPerfectCore
      (modelToG e (rootTorusSp K k)) => ((Ψ x : centralizerPerfectCore
        (modelToG e (rootTorusSp K k))) : G)) heq
  rcases hN1 with h1 | h1
  · exact Or.inl ⟨F, inferInstance, inferInstance, inferInstance, σ,
      (centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp Φ₀, hF,
      hrange, hkerΦ, key (MonoidHom.id _) h1⟩
  · exact Or.inr ⟨F, inferInstance, inferInstance, inferInstance, σ,
      (centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp Φ₀, hF,
      hrange, hkerΦ, key tauSp h1⟩

end Lift

section Edge

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

omit [Finite G] [CharP K 2] in
theorem map_ctTorus_eq_of_N1 (e : L ≃* StatedSp 3 K) (k : Fin 3) {F : Type} [Field F]
    [CharP F 2] (σ : K ≃+* F) (β : StatedSp 2 K →* StatedSp 2 K)
    (βF : StatedSp 2 F →* StatedSp 2 F)
    (hβ : ∀ κ : Kˣ, statedSpMap (σ : K →+* F) 2 (β (rootTorusHom K 2 0 κ)) =
      βF (rootTorusHom F 2 0 (Units.map (σ : K →+* F) κ)))
    (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* G) (hΦE : ∀ x, Φ x ∈ neighbourCore e k)
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β x))) =
      ((e.symm (complSpEquiv k x : complSp K k) : L) : G)) :
    (((rootTorusSp F 0).map βF).map (ctEmbed 1)).map (Φ.codRestrict _ hΦE) =
      (modelToG e (rootTorusSp K (k.succAbove 0))).subgroupOf (neighbourCore e k) := by
  have hval : ∀ κ : Kˣ, Φ (ctEmbed 1 (βF (rootTorusHom F 2 0 (Units.map (σ : K →+* F) κ)))) =
      ((e.symm (rootTorusHom K 3 (k.succAbove 0) κ) : L) : G) := by
    intro κ
    rw [← hβ, hN1, coe_complSpEquiv_rootTorusHom]
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨μ, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    rw [mem_subgroupOf]
    set κ : Kˣ := Units.map (σ.symm : F →+* K) μ with hκ
    have hμ : Units.map (σ : K →+* F) κ = μ := by
      ext
      simp [hκ]
    change Φ (ctEmbed 1 (βF (rootTorusHom F 2 0 μ))) ∈ _
    rw [← hμ, hval]
    exact symm_mem_modelToG e (rootTorusHom_mem_rootTorusSp _ κ)
  · intro hy
    rw [mem_subgroupOf] at hy
    obtain ⟨x, hx, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
    obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
    refine ⟨_, ⟨_, ⟨_, rootTorusHom_mem_rootTorusSp 0 (Units.map (σ : K →+* F) κ), rfl⟩,
      rfl⟩, ?_⟩
    apply Subtype.ext
    change Φ _ = (y : G)
    rw [hval, hxy]

theorem cube_dvd_natCard_edgeCoreSp_of_odd_std {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {e : L ≃* StatedSp 3 K} {k : Fin 3} (hn : SpThreeOddNormalized e f k false) :
    (Nat.card K) ^ 3 ∣ Nat.card (edgeCoreSp e k (k.succAbove 0)) := by
  obtain ⟨F, _, _, _, σ, Φ, hF, hrange, hker, hN1⟩ := hn
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hFK : Nat.card F = Nat.card K := (Nat.card_congr σ.toEquiv).symm
  have hF4 : 4 ≤ Nat.card F := hFK ▸ hK4
  have hle := modelToG_rootTorusSp_le_neighbourCore_three hK4 e (k := k) (a := 0) rfl
  rw [natCard_edgeCoreSp_eq e k _ hle]
  have hΦE : ∀ x, Φ x ∈ neighbourCore e k := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hTY := map_ctTorus_eq_of_N1 e k σ (MonoidHom.id _) (MonoidHom.id _)
    (fun κ => statedSpMap_rootTorusHom (σ : K →+* F) 0 κ) Φ hΦE (fun x => hN1 x)
  rw [Subgroup.map_id, ← hΦ'] at hTY
  have h1 : (blockSpecialLinear (K := F) oddFixBlock).map Φ' ≤ perfectCore (centralizer
      (((modelToG e (rootTorusSp K (k.succAbove 0))).subgroupOf (neighbourCore e k) :
        Subgroup (neighbourCore e k)) : Set (neighbourCore e k))) := by
    refine (Subgroup.map_mono (blockSpecialLinear_oddFix_le_perfectCore_centralizer hF4)).trans ?_
    have h2 := map_perfectCore_centralizer_le Φ' (oddStdTorus F)
    rw [oddStdTorus, hTY] at h2
    exact h2
  have hinj : Function.Injective (Φ'.comp (blockSpecialLinear (K := F) oddFixBlock).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ hx1
    have hxk : x ∈ Φ.ker := by
      have : Φ' x = 1 := hx1
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val this
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hker hxk)
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
  have h3 : Nat.card ((blockSpecialLinear (K := F) oddFixBlock).map Φ') =
      Nat.card (SpecialLinearGroup (Fin 3) F) := by
    have hr : (Φ'.comp (blockSpecialLinear (K := F) oddFixBlock).subtype).range =
        (blockSpecialLinear (K := F) oddFixBlock).map Φ' := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hr, ← natCard_blockSpecialLinear_oddFix]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h4 := Subgroup.card_dvd_of_le h1
  rw [h3] at h4
  rw [← hFK]
  exact (cube_dvd_natCard_SL_three).trans h4

theorem not_cube_dvd_natCard_edgeCoreSp_of_odd_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* StatedSp 3 K} {k : Fin 3} (hn : SpThreeOddNormalized e f k true) :
    ¬ (Nat.card K) ^ 3 ∣ Nat.card (edgeCoreSp e k (k.succAbove 0)) := by
  obtain ⟨F, _, _, _, σ, Φ, hF, hrange, hker, hN1⟩ := hn
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hFK : Nat.card F = Nat.card K := (Nat.card_congr σ.toEquiv).symm
  have hF4 : 4 ≤ Nat.card F := hFK ▸ hK4
  have hle := modelToG_rootTorusSp_le_neighbourCore_three hK4 e (k := k) (a := 0) rfl
  rw [natCard_edgeCoreSp_eq e k _ hle]
  have hΦE : ∀ x, Φ x ∈ neighbourCore e k := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hker' : Φ'.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  have hTY := map_ctTorus_eq_of_N1 e k σ tauSp tauSp
    (fun κ => statedSpMap_tauSp_rootTorusHom (σ : K →+* F) 0 κ) Φ hΦE (fun x => hN1 x)
  rw [← hΦ'] at hTY
  have hQ := le_map_perfectCore_centralizer Φ' hΦ's hker' (oddTwTorus F)
    (Q := perfectCore (centralizer
      (((modelToG e (rootTorusSp K (k.succAbove 0))).subgroupOf (neighbourCore e k) :
        Subgroup (neighbourCore e k)) : Set (neighbourCore e k))))
    (perfectCore_perfect _) (by rw [oddTwTorus, hTY]; exact perfectCore_le _)
  have h1 := (Subgroup.card_dvd_of_le (hQ.trans (Subgroup.map_mono
    (perfectCore_centralizer_oddTwTorus_le hF4)))).trans (Subgroup.card_map_dvd _ _)
  rw [natCard_sup_oddTw, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFK] at h1
  have hq2 : 2 ∣ Nat.card K := by
    rw [hKc]
    exact dvd_pow_self 2 (by omega)
  exact fun h2 => not_cube_dvd_sq_mul_sq_sub_one hq2 (by omega) (h2.trans h1)

end Edge

section Orient

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def SpThreeOddStandard (e : L ≃* StatedSp 3 K) : Prop :=
  ∀ k l : Fin 3, k ≠ l → (Nat.card K) ^ 3 ∣ Nat.card (edgeCoreSp e k l)

@[expose] def SpThreeOddTwisted (e : L ≃* StatedSp 3 K) : Prop :=
  ∀ k l : Fin 3, k ≠ l → ¬ (Nat.card K) ^ 3 ∣ Nat.card (edgeCoreSp e k l)

theorem spThreeOddStandard_or_twisted (e : L ≃* StatedSp 3 K) :
    SpThreeOddStandard e ∨ SpThreeOddTwisted e := by
  by_cases h : (Nat.card K) ^ 3 ∣ Nat.card (edgeCoreSp e 0 1)
  · exact Or.inl fun k l hkl => by rw [natCard_edgeCoreSp_eq_zero_one e hkl]; exact h
  · exact Or.inr fun k l hkl => by rw [natCard_edgeCoreSp_eq_zero_one e hkl]; exact h

variable [Finite K] [CharP K 2]

theorem spThreeOddNormalized_of_twisted {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .linearOdd) (htw : SpThreeOddTwisted e) :
    SpThreeOddNormalized e f k true := by
  rcases spThreeOddNormalized_false_or_true hset hKc hf e htC ht k hk with h | h
  · exact absurd (cube_dvd_natCard_edgeCoreSp_of_odd_std hKc hf h)
      (htw k _ (ne_succAbove_zero_three k))
  · exact h

end Orient

@[expose] def SpThreeLinearOddStandardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .linearOdd) → SpThreeOddStandard e →
        SpGlobalCoverType e f .linearOdd

@[expose] def SpThreeLinearOddTwistedFalseInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .linearOdd) → SpThreeOddTwisted e → False

theorem spThreeKindCoverInput_linearOdd_of_oriented (hs : SpThreeLinearOddStandardInput)
    (ht : SpThreeLinearOddTwistedFalseInput) : SpThreeKindCoverInput .linearOdd := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot
  rcases spThreeOddStandard_or_twisted e with h | h
  · exact hs G L hset f K hKc hf e t hto hKt hroot h
  · exact (ht G L hset f K hKc hf e t hto hKt hroot h).elim

end CFSG.SeitzReduction.SymplecticPilot
