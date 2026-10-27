module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFTrivial
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NonConstrainedBranch
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Escape9
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Factor81
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34BetaConf3.card_le_nine_of_le_normalizer (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {Q : Subgroup G} (hQ1 : Q ≠ ⊥) (hQ2 : IsPGroup 2 Q)
    (hQM : ¬ Subgroup.normalizer (Q : Set G) ≤ M) {X : Subgroup G}
    (hX : X ≤ M ⊓ Subgroup.normalizer (Q : Set G)) (hXp : IsPGroup 3 X) (hXc : ¬ IsCyclic X) :
    Nat.card X ≤ 9 :=
  D2L34BetaConf3.card_le_nine_of_not_isCyclic hc hstr ⟨Q, hQ1, hQ2, rfl⟩ hQM
    (hX.trans inf_le_right) (hX.trans inf_le_left) hXp hXc

omit [D2Amb3 G] in
theorem D2L34BetaConf3.false_of_thompsonJ_le_of_coprime_of_card
    (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (h3 : 3 ≤ Open.pRank 3 M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(ffC M T))
    (hcard : ∀ E : Subgroup G, thompsonJ T ≠ ⊥ → IsPGroup 2 (thompsonJ T) →
      ¬ Subgroup.normalizer (thompsonJ T : Set G) ≤ M →
      E ≤ M ⊓ Subgroup.normalizer (thompsonJ T : Set G) → IsElemAbelian 3 E →
      Nat.card E = 3 ^ 3 → IsPGroup 3 E → ¬ IsCyclic E → Nat.card E ≤ 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter T) M with hVdef
  set J := CFSG.Quasithin.thompsonJ T with hJdef
  have hMV : M ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (quasithinOmegaOneCenter T) M
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hJ1 : J ≠ ⊥ := Setup.thompsonJ_ne_bot hT.2.1 hT1
  have hJ2 : IsPGroup 2 J := hT.2.1.to_le (CFSG.Quasithin.B6.thompsonJ_le T)
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
  have hC3' : ¬ 3 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G)) := by
    have : M ⊓ Subgroup.centralizer (V : Set G) = ffC M T := inf_comm _ _
    rwa [this]
  have hCcop : Nat.Coprime 3 (Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC3'
  obtain ⟨W, W₂, hWM, hWp, hWidx, hW₂B, hW₂W, hWfac⟩ :=
    exists_sylow_of_normal_mul (inf_le_left : M ⊓ Subgroup.centralizer (V : Set G) ≤ M) hCn
      (inf_le_left : M ⊓ Subgroup.normalizer (J : Set G) ≤ M) hfac'
  have hWB : W ≤ M ⊓ Subgroup.normalizer (J : Set G) := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hWfac w hw
    have ha1 : a = 1 := eq_one_of_isPGroup_of_mem_coprime hCcop hWp ha.1 ha.2
    rw [ha1, one_mul]
    exact hW₂B hb
  obtain ⟨E, hEW, hEel, hEc⟩ := exists_elemAbelian_le_sylow_pow hWM hWp hWidx h3
  have hEp : IsPGroup 3 E := hWp.to_le hEW
  have hEcyc : ¬ IsCyclic E :=
    not_isCyclic_of_isElemAbelian hEel (by rw [hEc]; norm_num)
  have h9 := hcard E hJ1 hJ2 hNJ (hEW.trans hWB) hEel hEc hEp hEcyc
  rw [hEc] at h9
  norm_num at h9

theorem D2L34BetaConf3.false_of_thompsonJ_le_of_coprime
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (h3 : 3 ≤ Open.pRank 3 M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(ffC M T)) : False :=
  hc.false_of_thompsonJ_le_of_coprime_of_card h3 hT hNT hJ hC3
    fun _ hJ1 hJ2 hNJ hE _ _ hEp hEcyc =>
      D2L34BetaConf3.card_le_nine_of_le_normalizer hc hstr hJ1 hJ2 hNJ hE hEp hEcyc

end CFSG.LocalAnalysis.RankThreeTheoremC
