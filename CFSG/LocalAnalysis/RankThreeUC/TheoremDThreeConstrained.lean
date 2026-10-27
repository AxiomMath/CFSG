module

public import CFSG.LocalAnalysis.RankThreeUC.Assembly
public import CFSG.LocalAnalysis.RankThreeUC.WitnessGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5End
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFFamily
import CFSG.GroupTheory.SteinbergBKOddMetacyclicTorsion
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFH0Consumer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.FFH0Final
import CFSG.LocalAnalysis.RankThreeUC.TIModule
import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual
import CFSG.LocalAnalysis.RankThreeUC.TheoremDSolvableQuotient
public import CFSG.LocalAnalysis.RankThreeUC.CoreWitness
import CFSG.Quasithin.Background.C118NoOuter

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)
open scoped Pointwise

@[expose] def KFactHuppertProductThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (W A B E : Subgroup G), IsPGroup 3 W → A ≤ W → B ≤ W →
    IsCyclic A → IsCyclic B → (∀ w ∈ W, ∃ a ∈ A, ∃ b ∈ B, w = a * b) →
    E ≤ W → IsElemAbelian 3 E → Nat.card E ≠ 27

@[expose] def KFactHuppertMetacyclicThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (W A B : Subgroup G), IsPGroup 3 W → A ≤ W → B ≤ W →
    IsCyclic A → IsCyclic B → (∀ w ∈ W, ∃ a ∈ A, ∃ b ∈ B, w = a * b) → CFSG.IsMetacyclic W

theorem card_ne_twentySeven_of_metacyclic {G : Type} [Group G] [Finite G] {W E : Subgroup G}
    (hW : IsPGroup 3 W) (hmeta : CFSG.IsMetacyclic W) (hEW : E ≤ W)
    (hE : IsElemAbelian 3 E) : Nat.card E ≠ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup W := E.subgroupOf W with hQ
  have hQmeta : CFSG.IsMetacyclic Q :=
    (CFSG.GroupTheory.SteinbergBK.isMetacyclic_subgroup hmeta Q).1
  have hQp : IsPGroup 3 Q := hW.to_subgroup Q
  have hcard : Nat.card (CFSG.omega₁ (G := Q) (p := 3)) ≤ 3 ^ 2 :=
    CFSG.GroupTheory.SteinbergBK.card_omega₁_le (p := 3) (by norm_num) hQp hQmeta
  have htop : CFSG.omega₁ (G := Q) (p := 3) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    apply Subgroup.subset_closure
    have h3 : ((x : W) : G) ^ 3 = 1 := hE.2 _ (Subgroup.mem_subgroupOf.mp x.2)
    change x ^ 3 ^ 1 = 1
    exact Subtype.ext (Subtype.ext (by simpa using h3))
  rw [htop, Subgroup.card_top] at hcard
  have hEQ : Nat.card E = Nat.card Q :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEW).toEquiv).symm
  omega

theorem kFactHuppertProductThree_of_metacyclic (h : KFactHuppertMetacyclicThree) :
    KFactHuppertProductThree :=
  fun G _ _ W A B _ hW hA hB hAc hBc hprod hEW hE =>
    card_ne_twentySeven_of_metacyclic hW (h G W A B hW hA hB hAc hBc hprod) hEW hE

section Generic

variable {G : Type} [Group G] [Finite G]

theorem ffGroupStepGen {M T : Subgroup G} (hF : CharTwo M) (hT : IsSylowTwoOf T M)
    (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
    (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU))))
    (hMN : M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) :
      Set G))
    (hcard : ∀ L ∈ I, Nat.card L = 6) (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L)
    (hSyl : IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)))
    (hperm : ∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) (hfam : S3Family I) :
    ∀ L ∈ I, ∃ H₀ : Subgroup G, H₀ ≤ M ∧ L ≤ autI hU H₀ ∧
        (∀ Q : Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)),
          Q ≤ autI hU H₀ → IsPGroup 3 Q → Nat.card Q ≤ 3) ∧
        InClassG H₀ (baum T) ∧
        (IsL2OrA3Block H₀ (twoResidual H₀) →
          ∃ Y : Subgroup G, Y ≤ M ∧ IsSubnormal Y M ∧ InClassXBlock Y) := by
  intro L hL
  obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  have hVM : conjClosure (quasithinOmegaOneCenter T) M ≤ M :=
    hle.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
  have hVT : conjClosure (quasithinOmegaOneCenter T) M ≤ T :=
    hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
  have hBJ : autI hU (baum T) ≤ autI hU (thompsonJ M) :=
    autI_baum_le_autI_thompsonJ hMN hT hVT hfam hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
      hperm
  have hctx : FFCtx M T (conjClosure (quasithinOmegaOneCenter T) M) hU hMN I :=
    ⟨hVM, rfl, hT, hF, hcard, hJM, hSyl, hperm, hfam, hBJ⟩
  obtain ⟨H₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    FFH0Hyp.exists_H₀ invariantCyclicSupplement ⟨hF, hT, hle, hfam, hcard, hJM, hSyl, hperm, hL⟩
      hMN
  exact ⟨H₀, FFH0Spec.conclusion hctx hL
    (⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :
      FFH0Spec M T (conjClosure (quasithinOmegaOneCenter T) M) hU L H₀)⟩

theorem exists_ffPairData_gen (hN : NoXBlockFor G) {M T : Subgroup G} (hM : GLBIsMaxTwoLocal M)
    (hF : CharTwo M) (hT : IsSylowTwoOf T M)
    (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
    (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU))))
    (hMN : M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) :
      Set G))
    (hcard : ∀ L ∈ I, Nat.card L = 6) (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L)
    (hSyl : IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)))
    (hperm : ∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) (hfam : S3Family I) :
    ∃ C₁ C₂ : Subgroup G, FFPairData M T hU I C₁ C₂ := by
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hM.1
    rw [eq_bot_iff, ← h]
    exact B6.pCoreOf_two_le_of_isSylowTwoOf hT
  obtain ⟨C₁, C₂, h1, h1Z, h1char, h2, h2B, h2char, hall⟩ := theoremC118 G T hT.2.1 hT1
  have hZV : quasithinOmegaOneCenter T ≤ conjClosure (quasithinOmegaOneCenter T) M :=
    le_conjClosure _ M
  have hC₁T : C₁ ≤ T := h1Z.trans (C1GN.omegaOneCenterOf_le_self T)
  have hC₂T : C₂ ≤ baum T := h2B
  have hC₁B : C₁ ≤ baum T := h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)
  refine ⟨C₁, C₂, h1, hT.2.1.to_le hC₁T, h2, hT.2.1.to_le (h2B.trans (C1GN.baum_le T)), ?_, ?_,
    ?_, ?_, ?_⟩
  · exact (normalizer_le_normalizer_of_characteristic_subgroupOf hC₁T h1char)
  · exact (normalizer_le_normalizer_baum T).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hC₂T h2char)
  · intro x hx
    have hxc : ∀ c ∈ C₁, c * x = x * c := fun c hc =>
      Subgroup.mem_centralizer_iff.1 hx.1 c (hZV (h1Z hc))
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxc)
  · exact fun x hx => normalizer_le_normalizer_of_characteristic_subgroupOf hC₂T h2char hx.2
  · intro L hL
    obtain ⟨H₀, hHM, hHL, hH3, hGcl, hblock⟩ :=
      ffGroupStepGen hF hT hU I hMN hcard hJM hSyl hperm hfam L hL
    refine ⟨H₀, hHM, hHL, hH3, ?_⟩
    have hd := hall G H₀ (baum T).subtype (baum T).subtype_injective
      (by rwa [Subgroup.range_subtype])
    rw [Subgroup.map_subgroupOf_eq_of_le hC₁B, Subgroup.map_subgroupOf_eq_of_le h2B] at hd
    rcases hd with h | h | h
    · left
      intro x hx
      have hxc : ∀ c ∈ C₁, c * x = x * c := fun c hc =>
        ((Subgroup.mem_centralizer_iff.1 (h hc).2 x hx)).symm
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxc)
    · exact Or.inr h
    · exfalso
      obtain ⟨Y, hYM, hYs, hYX⟩ := hblock h
      exact hN M Y hM hYM hYs hYX

private theorem exists_elemAbelian_le_sylow_three_pow {M W : Subgroup G} {k : ℕ} (hWM : W ≤ M)
    (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (hk : k ≤ Open.pRank 3 M) :
    ∃ E : Subgroup G, E ≤ W ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEM, hEel, hEc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := k) hk
  have hEp : IsPGroup 3 (E.subgroupOf M) := by
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hEc]
  obtain ⟨S', hS'⟩ := hEp.exists_le_sylow
  have hWp' : IsPGroup 3 (W.subgroupOf M) :=
    hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWM).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S' (hWp'.toSylow hWidx)
  have hgcoe : MulAut.conj g • (S' : Subgroup M) = W.subgroupOf M := by
    have := congrArg (fun S : Sylow 3 M => (S : Subgroup M)) hg
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this
  refine ⟨E.map (MulAut.conj (g : G)).toMonoidHom, ?_,
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEel _, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxS : (⟨x, hEM hx⟩ : M) ∈ (S' : Subgroup M) := hS' (Subgroup.mem_subgroupOf.mpr hx)
    have hmem : MulAut.conj g • (⟨x, hEM hx⟩ : M) ∈ MulAut.conj g • (S' : Subgroup M) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hxS
    rw [hgcoe, Subgroup.mem_subgroupOf] at hmem
    simpa [MulAut.smul_def] using hmem
  · rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective, hEc]

theorem false_of_pairData_cyclic (hHup : KFactHuppertProductThree) {M T V : Subgroup G}
    {hU : IsElemAbelian 2 V} (hT : IsSylowTwoOf T M) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData M T hU I C₁ C₂)
    (hcyc₁ : ∀ Q : Subgroup G, Q ≤ M → Q ≤ Subgroup.normalizer (C₁ : Set G) → IsPGroup 3 Q →
      IsCyclic Q)
    (hcyc₂ : ∀ Q : Subgroup G, Q ≤ M → Q ≤ Subgroup.normalizer (C₂ : Set G) → IsPGroup 3 Q →
      IsCyclic Q)
    (h3 : 3 ≤ CFSG.Open.pRank 3 M) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, hCM₁, hJ₂, hH⟩ := hdat
  choose! Hf hHM hHL hH3 hHcase using hH
  set KA : Subgroup G := ⨆ L ∈ I, ⨆ (_ : Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L with hKA
  set KB : Subgroup G := ⨆ L ∈ I, ⨆ (_ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L
    with hKB
  have hKAM : KA ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKBM : KB ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKBN : KB ≤ Subgroup.normalizer (C₂ : Set G) :=
    iSup₂_le fun L hL => iSup_le fun h => (hHcase L hL).resolve_left h
  have hKAN : KA ≤ Subgroup.normalizer (C₁ : Set G) := iSup₂_le fun L hL => iSup_le fun h => h
  have hcov : ∀ L ∈ I, L ≤ autI hU KA ∨ L ≤ autI hU KB := by
    intro L hL
    by_cases h : Hf L ≤ Subgroup.normalizer (C₁ : Set G)
    · exact Or.inl ((hHL L hL).trans (autI_mono hU (le_iSup₂_of_le L hL
        (le_iSup (fun _ : Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L) h))))
    · exact Or.inr ((hHL L hL).trans (autI_mono hU
        (le_iSup₂_of_le L hL (le_iSup (fun _ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L)
          h))))
  set CM : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ M with hCM
  set 𝒜 : Subgroup G := CM ⊔ KA with h𝒜
  set ℬ : Subgroup G := KB ⊔ (M ⊓ Subgroup.normalizer (baum T : Set G)) with hℬ
  have h𝒜M : 𝒜 ≤ M := sup_le inf_le_right hKAM
  have hℬM : ℬ ≤ M := sup_le hKBM inf_le_left
  have h𝒜N : 𝒜 ≤ Subgroup.normalizer (C₁ : Set G) := sup_le hCM₁ hKAN
  have hℬN : ℬ ≤ Subgroup.normalizer (C₂ : Set G) := sup_le hKBN hJ₂
  have hfac : ∀ m ∈ M, ∃ a ∈ 𝒜, ∃ b ∈ ℬ, m = a * b := by
    intro m hm
    obtain ⟨c, hc', a, ha, b, hb, n, hn, rfl⟩ := exists_factor_of_covering hMN hT (C1GN.baum_le T)
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
      (normalizer_inf_sup_le_normalizer_baum T _) hI hSylJ hJM hKAM hKBM hcov m hm
    exact ⟨c * a, Subgroup.mul_mem _ (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right ha),
      b * n, Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hn),
      by group⟩
  obtain ⟨W, hWM, hWp, hWidx, hWfac⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_sylow_eq_mul_of_mul (p := 3) h𝒜M hℬM hfac
  obtain ⟨E, hEW, hEel, hEc⟩ := exists_elemAbelian_le_sylow_three_pow (k := 3) hWM hWp hWidx h3
  have hE27 : Nat.card E = 27 := by rw [hEc]; norm_num
  have hA := hcyc₁ (W ⊓ 𝒜) (inf_le_left.trans hWM) (inf_le_right.trans h𝒜N)
    (hWp.to_le inf_le_left)
  have hB := hcyc₂ (W ⊓ ℬ) (inf_le_left.trans hWM) (inf_le_right.trans hℬN)
    (hWp.to_le inf_le_left)
  exact hHup G W (W ⊓ 𝒜) (W ⊓ ℬ) E hWp inf_le_left inf_le_left hA hB hWfac hEW hEel hE27

theorem IsWitnessGen.normalizer_le_of_threeConstrained_three (hHup : KFactHuppertProductThree)
    (hI59 : AGL81I59) (hX : NoXBlockFor G) (hS : StandingGen G)
    {P : Sylow 3 G} {M : Subgroup G} (hp : IsWitnessPrime 3 P) (hw : IsWitnessGen 3 P M)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ Subgroup.centralizer (uCore M T : Set G))
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(autOn M (uCore M T))) :
    Subgroup.normalizer (T : Set G) ≤ M := by
  by_contra hNT
  have := hS.simple
  have hT' : IsSylowTwoOf T M := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  have hMtop : M ≠ ⊤ := twoLocal_ne_top hS.nonab hw.maxLocal.1
  have hKg : CFSG.Open.IsKGroup ↥M :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hS.kProper) M hMtop
  have hF : CharTwo M := hS.charTwo M hw.maxLocal.1
  rw [uCore_eq_conjClosure M T] at hJe hcon
  set V := conjClosure (quasithinOmegaOneCenter T) M with hVdef
  have hFF : FFConclusion M T V := hI59 G M T V hKg hF hT' rfl hcon hJe
  obtain ⟨hU', hMN', I, -, hcard, hJM, hSyl, hperm, hfam⟩ :=
    exists_family_of_ffConclusion hT' hJe hFF
  obtain ⟨C₁, C₂, hdat⟩ :=
    exists_ffPairData_gen hX hw.maxLocal hF hT' hU' I hMN' hcard hJM hSyl hperm hfam
  obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT' hF (le_refl _)
  have hVT : V ≤ T := hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT'))
  have hBS : autI hU' (baum T) ≤ autI hU' (thompsonJ M) :=
    autI_baum_le_autI_thompsonJ hMN' hT' hVT hfam hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT')
      hperm
  have hSylB : IsSylowTwoOf (autI hU' (baum T)) (autI hU' (thompsonJ M)) :=
    isSylowTwoOf_of_le_of_le hSyl (autI_mono hU' (thompsonJ_le_baum T)) hBS
      (isPGroup_autI hU' (hT'.2.1.to_le (C1GN.baum_le T)))
  have hcyc : ∀ C : Subgroup G, C ≠ ⊥ → IsPGroup 2 C →
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) →
      ∀ Q : Subgroup G, Q ≤ M → Q ≤ Subgroup.normalizer (C : Set G) → IsPGroup 3 Q →
        IsCyclic Q := by
    intro C hC1 hC2 hNC Q hQM hQN hQp
    by_contra hnc
    have h2 : 2 ≤ CFSG.Open.pRank 3 (M ⊓ Subgroup.normalizer (C : Set G)) :=
      (two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hQp hnc).trans
        (pRank_mono 3 Nat.prime_three.one_lt (le_inf hQM hQN))
    have hCM : Subgroup.normalizer (C : Set G) ≤ M :=
      hw.u2 _ ⟨C, hC1, hC2, rfl⟩ (by rwa [inf_comm])
    exact hNT (hNC.trans hCM)
  have h3 : 3 ≤ CFSG.Open.pRank 3 M := hw.three_le_pRank hp
  obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, -, -, -⟩ := id hdat
  exact false_of_pairData_cyclic hHup hT' hMN' hfam hSylB hJM hdat
    (hcyc C₁ hC₁1 hC₁2 hT₁) (hcyc C₂ hC₂1 hC₂2 hT₂) h3

theorem normalizer_le_of_threeConstrained_three (hHup : KFactHuppertProductThree)
    (hI59 : AGL81I59) (hX : Setting G → NoXBlockFor G) (hS : Standing G) (hUC : rankThreeUC G)
    {P : Sylow 3 G} {M : Subgroup G} (hp : 3 ∈ rankThreeSigmaA G) (hw : IsWitness 3 P M)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ Subgroup.centralizer (uCore M T : Set G))
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(autOn M (uCore M T))) :
    Subgroup.normalizer (T : Set G) ≤ M :=
  IsWitnessGen.normalizer_le_of_threeConstrained_three hHup hI59
    (hX (setting_of_rankThreeUC hS hUC)) hS.toGen (IsWitnessPrime.of_mem_sigmaA hS hp P) hw.toGen
    hT hJe hcon

private theorem pow_eq_one_of_mem_iSup_comm {Ω : Type*} [Group Ω] (n : ℕ)
    (𝓕 : Finset (Subgroup Ω)) (hn : ∀ H ∈ 𝓕, ∀ x ∈ H, x ^ n = 1)
    (hc : ∀ H ∈ 𝓕, ∀ H' ∈ 𝓕, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a) :
    ∀ x ∈ ⨆ H ∈ 𝓕, H, x ^ n = 1 := by
  classical
  induction 𝓕 using Finset.induction_on with
  | empty =>
    intro x hx
    have : (⨆ H ∈ (∅ : Finset (Subgroup Ω)), H) = ⊥ := by simp
    rw [this, Subgroup.mem_bot] at hx
    rw [hx, one_pow]
  | insert H₀ 𝓕 hH₀ ih =>
    intro x hx
    rw [Finset.iSup_insert] at hx
    have hn' : ∀ H ∈ 𝓕, ∀ x ∈ H, x ^ n = 1 := fun H hH => hn H (Finset.mem_insert_of_mem hH)
    have hc' : ∀ H ∈ 𝓕, ∀ H' ∈ 𝓕, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a :=
      fun H hH H' hH' => hc H (Finset.mem_insert_of_mem hH) H' (Finset.mem_insert_of_mem hH')
    have hK : (⨆ H ∈ 𝓕, H) ≤ Subgroup.centralizer (H₀ : Set Ω) := by
      refine iSup₂_le fun H hH b hb => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hne : H₀ ≠ H := fun h => hH₀ (h ▸ hH)
      exact hc H₀ (Finset.mem_insert_self _ _) H (Finset.mem_insert_of_mem hH) hne a ha b hb
    have hnorm : (⨆ H ∈ 𝓕, H) ≤ Subgroup.normalizer (H₀ : Set Ω) :=
      hK.trans (Subgroup.centralizer_le_normalizer _)
    have hx' : x ∈ ((H₀ ⊔ ⨆ H ∈ 𝓕, H : Subgroup Ω) : Set Ω) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left H₀ _ hnorm] at hx'
    obtain ⟨h, hh, k, hk, rfl⟩ := hx'
    have hcomm : Commute h k := Subgroup.mem_centralizer_iff.1 (hK hk) h hh
    rw [hcomm.mul_pow, hn H₀ (Finset.mem_insert_self _ _) h hh, ih hn' hc' k hk, one_mul]

private theorem pow_six_of_actsAsNaturalL2_aux {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {U : Subgroup W} (hN : CFSG.Quasithin.ActsAsNaturalL2 L U) :
    ∀ x ∈ L, x ^ 6 = 1 := by
  obtain ⟨e, -, -⟩ := hN
  have h6 : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), g ^ 6 = 1 := by decide
  intro x hx
  have h1 : e (⟨x, hx⟩ ^ 6) = 1 := by rw [map_pow]; exact h6 _
  have h2 : (⟨x, hx⟩ : ↥L) ^ 6 = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

omit [Finite G] in
theorem pow_six_mem_centralizer_of_thompsonJ_ff {H T V : Subgroup G}
    (hFF : FFConclusion H T V) :
    ∀ x ∈ CFSG.Quasithin.thompsonJ H, x ^ 6 ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hU, hred, I, -, hN, hcomm, -, hnat, -⟩ := hFF
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hHN (CFSG.Quasithin.thompsonJ_le_self H hx)
  have hconv := CFSG.Quasithin.convI_mem_autI hU hx hxN
  rw [hN] at hconv
  have h6 := pow_eq_one_of_mem_iSup_comm 6 I
    (fun L hL => pow_six_of_actsAsNaturalL2_aux (hnat L hL)) hcomm _ hconv
  have h7 : CFSG.Quasithin.convI hU ((⟨x, hxN⟩ : Subgroup.normalizer (V : Set G)) ^ 6) = 1 := by
    rw [map_pow]
    exact h6
  exact (CFSG.Quasithin.convI_eq_one_iff hU _).mp h7

theorem IsWitnessGen.normalizer_le_of_threeConstrained_ge5 (hI59 : AGL81I59)
    (hS : StandingGen G) {p : ℕ} {P : Sylow p G} (hp : IsWitnessPrime p P) (hp5 : 5 ≤ p)
    {M : Subgroup G} (hw : IsWitnessGen p P M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ Subgroup.centralizer (uCore M T : Set G))
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(autOn M (uCore M T))) :
    Subgroup.normalizer (T : Set G) ≤ M := by
  have := hS.simple
  by_cases hK : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (uCore M T : Set G))
  · have hUe := (uCore_le_and_isElemAbelian hS.charTwo hw.maxLocal.1 hT).2
    exact hw.normalizer_le_of_isTI_uCore hS hT (hw.isTI_of_two_le_pRank hp.prime
      (elementary_isPGroup 2 _ hUe) (le_normalizer_uCore M T) hK)
  · have hT' : IsSylowTwoOf T M := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
    have hMtop : M ≠ ⊤ := twoLocal_ne_top hS.nonab hw.maxLocal.1
    have hKg : CFSG.Open.IsKGroup ↥M :=
      CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
        (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hS.kProper) M hMtop
    have hF : CharTwo M := hS.charTwo M hw.maxLocal.1
    rw [uCore_eq_conjClosure M T] at hJe hcon hK
    have hFF : FFConclusion M T (conjClosure (quasithinOmegaOneCenter T) M) :=
      hI59 G M T _ hKg hF hT' rfl hcon hJe
    have h6 := pow_six_mem_centralizer_of_thompsonJ_ff hFF
    have hJ := pRank_thompsonJ_le_of_pow_six hp.prime hp5 h6
    rw [← uCore_eq_conjClosure M T] at hK h6 hJ
    exact hw.normalizer_le_of_pRank_thompsonJ_le_one hS hp hT (by omega)

theorem normalizer_le_of_threeConstrained_ge5 (hI59 : AGL81I59) (hS : Standing G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) (hp5 : 5 ≤ p) {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ Subgroup.centralizer (uCore M T : Set G))
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(autOn M (uCore M T))) :
    Subgroup.normalizer (T : Set G) ≤ M :=
  IsWitnessGen.normalizer_le_of_threeConstrained_ge5 hI59 hS.toGen
    (IsWitnessPrime.of_mem_sigmaA hS hp P) hp5 hw.toGen hT hJe hcon

theorem IsWitnessGen.normalizer_le_of_threeConstrained (hHup : KFactHuppertProductThree)
    (hI59 : AGL81I59) (hX : NoXBlockFor G) (hS : StandingGen G) {p : ℕ} {P : Sylow p G}
    (hp : IsWitnessPrime p P) {M : Subgroup G} (hw : IsWitnessGen p P M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ Subgroup.centralizer (uCore M T : Set G))
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(autOn M (uCore M T))) :
    Subgroup.normalizer (T : Set G) ≤ M := by
  have hprime := hp.prime
  have hodd := hp.odd
  by_cases h3 : p = 3
  · subst h3
    exact IsWitnessGen.normalizer_le_of_threeConstrained_three hHup hI59 hX hS hp hw hT hJe hcon
  · have h5 : 5 ≤ p := by
      have h2 := hprime.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hprime (by norm_num)
      omega
    exact IsWitnessGen.normalizer_le_of_threeConstrained_ge5 hI59 hS hp h5 hw hT hJe hcon

theorem normalizer_le_of_threeConstrained (hHup : KFactHuppertProductThree) (hI59 : AGL81I59)
    (hX : Setting G → NoXBlockFor G) (hS : Standing G) (hUC : rankThreeUC G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hw : IsWitness p P M)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ Subgroup.centralizer (uCore M T : Set G))
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(autOn M (uCore M T))) :
    Subgroup.normalizer (T : Set G) ≤ M :=
  IsWitnessGen.normalizer_le_of_threeConstrained hHup hI59 (hX (setting_of_rankThreeUC hS hUC))
    hS.toGen (IsWitnessPrime.of_mem_sigmaA hS hp P) hw.toGen hT hJe hcon

end Generic

end CFSG.LocalAnalysis.RankThreeUC
