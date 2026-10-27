module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Escape9
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Factor81
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GuestConj

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_quasithinOmegaOneCenter (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
  have := Setup.characteristic_omegaOneCenterOf T
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := T) ((CFSG.Quasithin.omegaOneCenterOf T).subgroupOf T)
  rwa [Subgroup.map_subgroupOf_eq_of_le (Setup.omegaOneCenterOf_le T)] at h1

theorem D2L34BetaConf.card_le_nine_of_le_normalizer {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {Q : Subgroup G} (hQ1 : Q ≠ ⊥) (hQ2 : IsPGroup 2 Q)
    (hQM : ¬ Subgroup.normalizer (Q : Set G) ≤ M) {X : Subgroup G}
    (hX : X ≤ M ⊓ Subgroup.normalizer (Q : Set G)) (hXp : IsPGroup 3 X) (hXc : ¬ IsCyclic X) :
    Nat.card X ≤ 9 :=
  D2L34BetaConf.card_le_nine_of_not_isCyclic hc hstr ⟨Q, hQ1, hQ2, rfl⟩ hQM
    (hX.trans inf_le_right) (hX.trans inf_le_left) hXp hXc

theorem D2L34BetaConf.exists_elemAbelian_of_thompsonJ_le {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hJ : CFSG.Quasithin.thompsonJ T ≤ Subgroup.centralizer
      (CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter T) M : Set G)) :
    ∃ W₁ W₂ : Subgroup G, W₁ ≤ M ⊓ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) ∧
      W₂ ≤ M ⊓ Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set G) ∧
      Nat.card W₁ = 9 ∧ Nat.card W₂ = 9 ∧ W₁ ⊓ W₂ = ⊥ ∧
      IsElemAbelian 3 (W₁ ⊔ W₂ : Subgroup G) ∧ Nat.card (W₁ ⊔ W₂ : Subgroup G) = 81 ∧
      ¬ 3 ∣ ((W₁ ⊔ W₂).subgroupOf M).index := by
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := CFSG.Quasithin.conjClosure Z M with hVdef
  set J := CFSG.Quasithin.thompsonJ T with hJdef
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := CFSG.Quasithin.le_normalizer_conjClosure Z M
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
  have hZ2 : IsPGroup 2 Z := hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
  have hJ1 : J ≠ ⊥ := Setup.thompsonJ_ne_bot hT.2.1 hT1
  have hJ2 : IsPGroup 2 J := hT.2.1.to_le (CFSG.Quasithin.B6.thompsonJ_le T)
  have hNZ : ¬ Subgroup.normalizer (Z : Set G) ≤ M := fun h =>
    hNT ((normalizer_le_normalizer_quasithinOmegaOneCenter T).trans h)
  have hNJ : ¬ Subgroup.normalizer (J : Set G) ≤ M := fun h =>
    hNT ((GammaExtra.normalizer_le_normalizer_thompsonJ T).trans h)
  obtain ⟨-, hfac⟩ := CFSG.Quasithin.B2_7_of_le_factor hMV hT hJ
  have hfac' : ∀ m ∈ M, ∃ c ∈ M ⊓ Subgroup.centralizer (V : Set G),
      ∃ b ∈ M ⊓ Subgroup.normalizer (J : Set G), m = c * b := by
    intro m hm
    obtain ⟨n, hn, c, hc', he⟩ := hfac m⁻¹ (M.inv_mem hm)
    refine ⟨c⁻¹, (M ⊓ Subgroup.centralizer (V : Set G)).inv_mem hc', n⁻¹,
      (M ⊓ Subgroup.normalizer (J : Set G)).inv_mem hn, ?_⟩
    rw [← mul_inv_rev, ← he, inv_inv]
  have hCn : M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
      Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_inf Subgroup.le_normalizer
      (CFSG.Quasithin.B2F.le_normalizer_centralizer hMV)
  have hCZ : M ⊓ Subgroup.centralizer (V : Set G) ≤
      M ⊓ Subgroup.normalizer (Z : Set G) := by
    refine inf_le_inf_left M fun x hx => ?_
    have hxZ : ∀ z ∈ Z, z * x = x * z := fun z hz =>
      Subgroup.mem_centralizer_iff.mp hx z (CFSG.Quasithin.le_conjClosure Z M hz)
    have hxZ' : ∀ z ∈ Z, z * x⁻¹ = x⁻¹ * z := fun z hz =>
      Subgroup.mem_centralizer_iff.mp ((Subgroup.centralizer (V : Set G)).inv_mem hx) z
        (CFSG.Quasithin.le_conjClosure Z M hz)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [← hxZ z hz, mul_inv_cancel_right]
      exact hz
    · intro hz
      have h1 := hxZ' _ hz
      have h2 : z = x * z * x⁻¹ := by
        calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
          _ = (x * z * x⁻¹) * x⁻¹ * x := by rw [← h1]
          _ = x * z * x⁻¹ := by group
      rw [h2]
      exact hz
  obtain ⟨W₁, W₂, hW₁C, hW₂B, hW₁c, hW₂c, hW₁₂, hWel, hWc, -, hWidx, -⟩ :=
    exists_elemAbelian_of_normal_mul inf_le_left hCn inf_le_left hfac'
      (fun X hX hXp hXc => D2L34BetaConf.card_le_nine_of_le_normalizer hc hstr hZ1 hZ2 hNZ
        (hX.trans hCZ) hXp hXc)
      (fun X hX hXp hXc => D2L34BetaConf.card_le_nine_of_le_normalizer hc hstr hJ1 hJ2 hNJ hX
        hXp hXc)
      (hc.esc.four_le_pRank_M hc.beta)
  exact ⟨W₁, W₂, hW₁C.trans hCZ, hW₂B, hW₁c, hW₂c, hW₁₂, hWel, hWc, hWidx⟩

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
