module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Pair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.E81

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.Tits.MsidePrelim

@[expose] def FFQuotientConstrained : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M →
    CFSG.ABGLocalTools.IsPConstrained 3 ↥M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M → ∀ S : Sylow 3 ↥(ffC M T),
      ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) →
      CFSG.ABGLocalTools.IsPConstrained 3
        ↥(autOn M (conjClosure (quasithinOmegaOneCenter T) M))

section Endgame

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}

theorem card_eq_card_autI_mul (hMN : M ≤ Subgroup.normalizer (V : Set G)) {𝒜 : Subgroup G}
    (hCA : Subgroup.centralizer (V : Set G) ⊓ M ≤ 𝒜) (h𝒜M : 𝒜 ≤ M) :
    Nat.card 𝒜 = Nat.card (autI hU 𝒜) * Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M) := by
  have hle : autI hU 𝒜 ≤ autI hU M := autI_mono hU h𝒜M
  have h := card_preAutM_of_le hU hMN hle
  have hpre : preAutM hU hMN (autI hU 𝒜) = 𝒜 := by
    ext g
    rw [mem_preAutM]
    constructor
    · rintro ⟨hgM, hg⟩
      have := mem_sup_of_actM_mem_autI h𝒜M hgM hg
      rwa [sup_eq_left.2 hCA] at this
    · intro hg
      refine ⟨h𝒜M hg, ?_⟩
      rw [actM_eq_convI]
      exact convI_mem_autI hU hg _
  rw [hpre] at h
  exact h

theorem nine_dvd_card_of_not_isCyclic {D : Subgroup G} (hDp : IsPGroup 3 D) (hDc : ¬ IsCyclic D) :
    9 ∣ Nat.card D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hDp.exists_card_eq
  rcases k with _ | _ | k
  · have hD : D = ⊥ := Subgroup.eq_bot_of_card_eq D (by simpa using hk)
    exact absurd (hD ▸ isCyclic_of_subsingleton ..) hDc
  · exact absurd (isCyclic_of_prime_card (p := 3) (by simpa using hk)) hDc
  · rw [hk]
    exact ⟨3 ^ k, by ring⟩

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.exists_factorization_of_pairData3_of_card
    {T : Subgroup G} (hT : IsSylowTwoOf T M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData M T hU I C₁ C₂) {D : Subgroup G}
    (hDCM : D ≤ Subgroup.centralizer (V : Set G) ⊓ M) (hDp : IsPGroup 3 D) (hDc : ¬ IsCyclic D)
    (hcard9 : ∀ {N Q : Subgroup G}, IsTwoLocal N → ¬ N ≤ M → Q ≤ N → Q ≤ M → IsPGroup 3 Q →
      ¬ IsCyclic Q → D ≤ Q → Nat.card Q ≤ 9) :
    ∃ B : Subgroup G, B ≤ M ∧ B ≤ Subgroup.normalizer (C₂ : Set G) ∧
      ∀ m ∈ M, ∃ c ∈ Subgroup.centralizer (V : Set G) ⊓ M, ∃ b ∈ B, m = c * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, hCM₁, hJ₂, hH⟩ := hdat
  have hN₁ : ¬ Subgroup.normalizer (C₁ : Set G) ≤ M := fun h => hNT (hT₁.trans h)
  have hN₂ : ¬ Subgroup.normalizer (C₂ : Set G) ≤ M := fun h => hNT (hT₂.trans h)
  set CM : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ M with hCM
  choose! Hf hHM hHL hH3 hHcase using hH
  have hnoA : ∀ L ∈ I, ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G) := by
    intro L hL hLA
    set 𝒜 : Subgroup G := CM ⊔ Hf L with h𝒜
    have h𝒜M : 𝒜 ≤ M := sup_le inf_le_right (hHM L hL)
    have h𝒜N : 𝒜 ≤ Subgroup.normalizer (C₁ : Set G) := sup_le hCM₁ hLA
    have hcardA := card_eq_card_autI_mul (hU := hU) hMN (𝒜 := 𝒜) le_sup_left h𝒜M
    have h3 : 3 ∣ Nat.card (autI hU 𝒜) := by
      have hLle : L ≤ autI hU 𝒜 := (hHL L hL).trans (autI_mono hU le_sup_right)
      have := Subgroup.card_dvd_of_le hLle
      rw [hcard L hL] at this
      exact (show 3 ∣ 6 by norm_num).trans this
    have h9 : 9 ∣ Nat.card CM :=
      (nine_dvd_card_of_not_isCyclic hDp hDc).trans (Subgroup.card_dvd_of_le hDCM)
    have h27 : 3 ^ 3 ∣ Nat.card 𝒜 := by
      rw [hcardA]
      exact (show 3 ^ 3 = 3 * 9 by norm_num) ▸ Nat.mul_dvd_mul h3 h9
    have hDA : D ≤ 𝒜 := hDCM.trans le_sup_left
    have hDp' : IsPGroup 3 (D.subgroupOf 𝒜) :=
      hDp.of_equiv (Subgroup.subgroupOfEquivOfLe hDA).symm
    obtain ⟨Q', hDQ'⟩ := hDp'.exists_le_sylow
    set Q : Subgroup G := (Q' : Subgroup ↥𝒜).map 𝒜.subtype with hQ
    have hQp : IsPGroup 3 Q := Q'.isPGroup'.map 𝒜.subtype
    have hQ𝒜 : Q ≤ 𝒜 := Subgroup.map_subtype_le _
    have hDQ : D ≤ Q := fun x hx => ⟨⟨x, hDA hx⟩, hDQ' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hQc : ¬ IsCyclic Q := fun hcyc => hDc (Subgroup.isCyclic_of_le hDQ)
    have hQcard : 3 ^ 3 ∣ Nat.card Q := by
      have := Sylow.pow_dvd_card_of_pow_dvd_card (n := 3) Q' h27
      rwa [Nat.card_congr (Subgroup.equivMapOfInjective _ 𝒜.subtype 𝒜.subtype_injective).toEquiv]
        at this
    have hQ9 := hcard9
      (⟨C₁, hC₁1, hC₁2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₁ : Set G))) hN₁
      (hQ𝒜.trans h𝒜N) (hQ𝒜.trans h𝒜M) hQp hQc hDQ
    have := Nat.le_of_dvd Nat.card_pos hQcard
    omega
  have hB : ∀ L ∈ I, Hf L ≤ Subgroup.normalizer (C₂ : Set G) := fun L hL =>
    (hHcase L hL).resolve_left (hnoA L hL)
  set KB : Subgroup G := ⨆ L ∈ I, Hf L with hKB
  have hKBM : KB ≤ M := iSup₂_le fun L hL => hHM L hL
  have hKBN : KB ≤ Subgroup.normalizer (C₂ : Set G) := iSup₂_le fun L hL => hB L hL
  have hcov : ∀ L ∈ I, L ≤ autI hU (⊥ : Subgroup G) ∨ L ≤ autI hU KB := fun L hL =>
    Or.inr ((hHL L hL).trans (autI_mono hU (le_iSup₂ (f := fun L (_ : L ∈ I) => Hf L) L hL)))
  set B : Subgroup G := KB ⊔ (M ⊓ Subgroup.normalizer (baum T : Set G)) with hBdef
  have hBM : B ≤ M := sup_le hKBM inf_le_left
  have hBN : B ≤ Subgroup.normalizer (C₂ : Set G) := sup_le hKBN hJ₂
  refine ⟨B, hBM, hBN, ?_⟩
  intro m hm
  obtain ⟨c, hc', a, ha, b, hb, n, hn, rfl⟩ := exists_factor_of_covering hMN hT (C1GN.baum_le T)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
    (normalizer_inf_sup_le_normalizer_baum T _) hI hSylJ hJM
    (bot_le : (⊥ : Subgroup G) ≤ M) hKBM hcov m hm
  rw [Subgroup.mem_bot] at ha
  subst ha
  exact ⟨c, hc', b * n, Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
    (Subgroup.mem_sup_right hn), by group⟩


theorem false_of_noncyclic_pair_data {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K₀) (hstr : GLBStronglyEmbedded 3 M)
    (hAll : D2L34AllResidue P M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData M T hU I C₁ C₂) {D : Subgroup G}
    (hDCM : D ≤ Subgroup.centralizer (V : Set G) ⊓ M) (hDp : IsPGroup 3 D) (hDc : ¬ IsCyclic D) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B, hBM, hBN, hfac⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_factorization_of_pairData3_of_card hT hNT hMN hI
      hcard hSylJ hJM hdat hDCM hDp hDc fun hN hNM hQN hQM hQp hQc _ =>
        D2L34BetaConf.card_le_nine_of_not_isCyclic hc hstr hN hNM hQN hQM hQp hQc
  obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, hCM₁, -, -⟩ := hdat
  have hN₁ : ¬ Subgroup.normalizer (C₁ : Set G) ≤ M := fun h => hNT (hT₁.trans h)
  have hN₂ : ¬ Subgroup.normalizer (C₂ : Set G) ≤ M := fun h => hNT (hT₂.trans h)
  set CM : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ M with hCM
  have hCMn : M ≤ Subgroup.normalizer (CM : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).1
      (centralizer_inf_subgroupOf_normal hU hMN)
  have hC9 : ∀ X : Subgroup G, X ≤ CM → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9 :=
    fun X hX hXp hXc => D2L34BetaConf.card_le_nine_of_not_isCyclic hc hstr
      (⟨C₁, hC₁1, hC₁2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₁ : Set G))) hN₁
      (hX.trans hCM₁) (hX.trans inf_le_right) hXp hXc
  have hB9 : ∀ X : Subgroup G, X ≤ B → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9 :=
    fun X hX hXp hXc => D2L34BetaConf.card_le_nine_of_not_isCyclic hc hstr
      (⟨C₂, hC₂1, hC₂2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₂ : Set G))) hN₂
      (hX.trans hBN) (hX.trans hBM) hXp hXc
  obtain ⟨W₁, W₂, hW₁C, hW₂B, hW₁c, hW₂c, -, hWel, hWc, -, -, -⟩ :=
    exists_elemAbelian_of_normal_mul inf_le_right hCMn hBM hfac hC9 hB9
      (hc.esc.four_le_pRank_M hc.beta)
  have hW₁p : IsPGroup 3 W₁ := IsPGroup.of_card (n := 2) (by rw [hW₁c]; norm_num)
  have hW₂p : IsPGroup 3 W₂ := IsPGroup.of_card (n := 2) (by rw [hW₂c]; norm_num)
  have hW₁el : IsElemAbelian 3 W₁ := isElemAbelian_of_le hWel le_sup_left
  have hW₂el : IsElemAbelian 3 W₂ := isElemAbelian_of_le hWel le_sup_right
  exact D2L34BetaConf.false_of_two_escapes hc hstr hAll hT hNT hC₁1 hC₁2 hT₁ hC₂1 hC₂2 hT₂
    (le_inf (hW₁C.trans inf_le_right) (hW₁C.trans hCM₁))
    (le_inf (hW₂B.trans hBM) (hW₂B.trans hBN)) hW₁p hW₂p
    (not_isCyclic_of_isElemAbelian hW₁el (by rw [hW₁c]; norm_num))
    (not_isCyclic_of_isElemAbelian hW₂el (by rw [hW₂c]; norm_num))
    (IsPGroup.of_card (n := 4) (by rw [hWc]; norm_num)) (by rw [hWc]; norm_num)

end Endgame

theorem ffNoncyclicInput_of_nodes
    (hI59 : AGL81I59) (hK : FFQuotientConstrained) (hP : FFPairStep) (hB : FFBaumStar) :
    FFNoncyclicInput := by
  intro d G _ _ P M A H R Rbar K₀ hc hstr hAll hcon T hT hNT S hS
  have hMtop : M ≠ ⊤ := fun h => hc.esc.not_le (h ▸ le_top)
  have hKg : CFSG.Open.IsKGroup ↥M :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hc.glob.kProper) M hMtop
  have hF : CharTwo M := hc.glob.charTwo M hc.esc.maxTwoLocal_M.1
  have hJ := D2L34BetaConf.thompsonJ_not_le_centralizer hc hstr hAll hT hNT
  have hconAut := hK d G P M A H R Rbar K₀ hc hstr hAll hcon T hT hNT S hS
  have hFF : FFConclusion M T (conjClosure (quasithinOmegaOneCenter T) M) :=
    hI59 G M T _ hKg hF hT rfl hconAut hJ
  obtain ⟨hU, hMN, I, hne, hcard, hJM, hSyl, hperm, hI⟩ := exists_family_of_ffConclusion hT hJ hFF
  obtain ⟨C₁, C₂, hdat⟩ := hP d G P M A H R Rbar K₀ hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl
    hperm hI
  have hBS := hB d G P M A H R Rbar K₀ hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm hI
  have hSylB : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)) :=
    isSylowTwoOf_of_le_of_le hSyl (autI_mono hU (thompsonJ_le_baum T)) hBS
      (isPGroup_autI hU (hT.2.1.to_le (C1GN.baum_le T)))
  refine false_of_noncyclic_pair_data hc hstr hAll hT hNT hMN hI hcard hSylB hJM hdat
    (D := (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) (Subgroup.map_subtype_le _)
    (S.isPGroup'.map _) hS

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
