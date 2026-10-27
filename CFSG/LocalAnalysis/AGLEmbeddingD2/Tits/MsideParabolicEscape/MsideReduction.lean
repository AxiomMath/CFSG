module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaCoreFree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.PurityOfOrderThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NoConjugateInA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.CoreFreeTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PCoreQuotient

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.QuasithinUnique
open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3)
open scoped Pointwise

@[expose] def PermutableOrderThreeAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M D₀ P₀ Rc : Subgroup G),
    D₀ ≤ M → (D₀.subgroupOf M).Normal → Nat.Coprime 3 (Nat.card D₀) →
    P₀ ≤ M → Nat.card P₀ = 3 → ((P₀ ⊔ D₀).subgroupOf M).Normal →
    Rc ≤ M → IsPGroup 2 Rc → ¬ 2 ∣ ((Rc ⊓ D₀).subgroupOf D₀).index →
    ∃ P₁ : Subgroup G, P₁ ≤ P₀ ⊔ D₀ ∧ Nat.card P₁ = 3 ∧ (P₁ : Set G) * Rc = Rc * P₁

@[expose] def threePrimeResidual {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}

@[expose] def D2L34Kmax {G : Type} [Group G] [Finite G] (H : Subgroup G) : Prop :=
  ∀ N : Subgroup G, GLBIsMaxTwoLocal N → threePrimeResidual H ≤ N → N = H

@[expose] def D2L34BetaMSideInput : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal

@[expose] def D2L34BetaMSideBase : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M →
    ∃ U : Subgroup G, IsBetaBase H M U ∧ A ≤ Subgroup.normalizer (U : Set G) ∧
      Subgroup.normalizer (U : Set G) ≤ H ∧
      IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) ∧
      IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M))

@[expose] def D2L34BetaMSideX : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    D2L34AllResidue P M → D2L34Kmax H →
    GLBStronglyEmbedded 3 M ∧ ∃ U Q : Subgroup G, IsBetaBase H M U ∧ Q ≤ M ∧ Nat.card Q = 3 ∧
      IsS3Parabolic U (U ⊔ Q) ∧ ∀ g : G, ¬ Q.map (MulAut.conj g).toMonoidHom ≤ H


@[expose] def PermutedConcl {G : Type} [Group G] (H M : Subgroup G) : Prop :=
  ∃ U P₁ : Subgroup G, IsBetaBase H M U ∧ P₁ ≤ M ∧ Nat.card P₁ = 3 ∧
    (P₁ : Set G) * U = U * P₁ ∧ Subgroup.normalizer (U : Set G) ⊓ M ≤ H ∧
    ∀ g : G, ¬ P₁.map (MulAut.conj g).toMonoidHom ≤ H

@[expose] def D2L34BetaMSidePermuted : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ∀ U : Subgroup G, IsBetaBase H M U → A ≤ Subgroup.normalizer (U : Set G) →
      Subgroup.normalizer (U : Set G) ≤ H →
      IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) →
      IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) → PermutedConcl H M

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.permutedConcl_of_orderThree
    (hperm : PermutableOrderThreeAt)
    {d : TauCeti.ValidLieTypeIndex} {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {P₀ : Subgroup G} (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hNn : ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal) {U : Subgroup G}
    (hU : IsBetaBase H M U) (hNHU : Subgroup.normalizer (U : Set G) ≤ H)
    (hsylU : IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M)) : PermutedConcl H M := by
  have hNH : Subgroup.normalizer (U : Set G) ⊓ M ≤ H := inf_le_left.trans hNHU
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D₀ := GLBPrimeCore 3 M with hD₀
  have hD₀M : D₀ ≤ M := glbPrimeCore_le 3 M
  have hD₀n : (D₀.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hD₀M).mpr (le_normalizer_glbPrimeCore 3 M)
  have hD₀cop : Nat.Coprime 3 (Nat.card D₀) := glbPrimeCore_coprime 3 M
  have hWM : (primeComplementCore (G := H) 3).map H.subtype ≤ M := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp (hc.esc.primeComplementCore_le_inf hw)).2
  have hT₀M : pCoreOf 2 (H ⊓ M) ≤ M :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 (H ⊓ M)).trans inf_le_right
  have hUM : U ≤ M := hU.2.2.1.trans (sup_le hWM hT₀M)
  have hU2 : IsPGroup 2 U := hU.1
  have hsyl : ¬ 2 ∣ ((U ⊓ D₀).subgroupOf D₀).index := hsylU.2.2
  obtain ⟨P₁, hP₁N, hP₁c, hperm'⟩ :=
    hperm G M D₀ P₀ U hD₀M hD₀n hD₀cop hP₀M hP₀ hNn hUM hU2 hsyl
  have hNM : P₀ ⊔ D₀ ≤ M := sup_le hP₀M hD₀M
  have hP₁M : P₁ ≤ M := hP₁N.trans hNM
  have hP₁p : IsPGroup 3 P₁ := IsPGroup.of_card (n := 1) (by rw [hP₁c]; simp)
  have hP₁1 : P₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP₁c
    omega
  have hNcard : ¬ 3 ^ 2 ∣ Nat.card (P₀ ⊔ D₀ : Subgroup G) := by
    have hnorm : P₀ ≤ Subgroup.normalizer (D₀ : Set G) :=
      hP₀M.trans (le_normalizer_glbPrimeCore 3 M)
    have hinf : P₀ ⊓ D₀ = ⊥ := (Subgroup.disjoint_of_coprime_natCard
      (by rw [hP₀]; exact hD₀cop)).eq_bot
    have hfac : ∀ x ∈ P₀ ⊔ D₀, ∃ p ∈ P₀, ∃ r ∈ D₀, x = p * r := by
      intro x hx
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P₀ D₀ hnorm,
        Set.mem_mul] at hx
      obtain ⟨p, hp, r, hr, rfl⟩ := hx
      exact ⟨p, hp, r, hr, rfl⟩
    have hrel := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.relIndex_sup_eq_three_of_mul
      hP₀ hinf hfac
    have h1 := Subgroup.card_mul_index (D₀.subgroupOf (P₀ ⊔ D₀))
    have h2 : Nat.card (D₀.subgroupOf (P₀ ⊔ D₀)) = Nat.card D₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    have h3 : (D₀.subgroupOf (P₀ ⊔ D₀)).index = 3 := hrel
    rw [h2, h3] at h1
    intro hdvd
    rw [← h1] at hdvd
    have h3d : 3 ∣ Nat.card D₀ := by omega
    have := Nat.Coprime.coprime_dvd_right h3d hD₀cop
    norm_num at this
  have hR9 := hc.card_R_eq_nine hstr
  have hAR : A = R := Subgroup.eq_of_le_of_card_ge hc.esc.A_le
    (by rw [hR9, hc.esc.card_A]; norm_num)
  have hnoH : ∀ g : G, ¬ P₁.map (MulAut.conj g).toMonoidHom ≤ H := by
    intro g hg
    have hXp : IsPGroup 3 (P₁.map (MulAut.conj g).toMonoidHom) := hP₁p.map _
    obtain ⟨h, hh, hle⟩ := S3AmalgamBound.exists_conj_le_of_isSylow (p := 3) hc.esc.isSylow hg hXp
    refine D2Escape.false_of_map_conj_le_of_normal_of_l34 hc.esc hstr hc.l34 hc.iso hc.le_K hNM
      hNn hNcard hP₁p hP₁1 hP₁N (g := h * g) ?_
    rintro _ ⟨y, hy, rfl⟩
    have := hle ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← hAR] at this
    simpa [MulAut.conj_apply, mul_assoc] using this
  exact ⟨U, P₁, hU, hP₁M, hP₁c, hperm', hNH, hnoH⟩

theorem d2L34BetaMSidePermuted_of_input
    (hperm : PermutableOrderThreeAt)
    (hin : D2L34BetaMSideInput) :
    ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
      (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
      GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
      CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
      ∀ U : Subgroup G, IsBetaBase H M U → A ≤ Subgroup.normalizer (U : Set G) →
        Subgroup.normalizer (U : Set G) ≤ H →
        IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) →
      IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) → PermutedConcl H M := by
  intro d G _ _ P M A H R Rbar K hc hstr hOnly hKmax hcon U hU hAU hNHU hsylU _hUQ
  obtain ⟨P₀, hP₀M, hP₀, hNn⟩ := hin d G P M A H R Rbar K hc hstr hOnly hKmax hcon
  exact hc.toConf3.permutedConcl_of_orderThree hperm hstr hP₀M hP₀ hNn hU hNHU hsylU

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.AGLEmbeddingD2.Tits in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.exists_s3Parabolic_of_permuted3 {G : Type}
    [Group G] [Finite G] {H M : Subgroup G} (hP : PermutedConcl H M) :
    ∃ U Q : Subgroup G, IsBetaBase H M U ∧ Q ≤ M ∧ Nat.card Q = 3 ∧
      IsS3Parabolic U (U ⊔ Q) ∧ ∀ g : G, ¬ Q.map (MulAut.conj g).toMonoidHom ≤ H := by
  obtain ⟨U, P₁, hU, hP₁M, hP₁c, hperm', hNH, hnoH⟩ := hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 U := hU.1
  have hcoe := S3AmalgamBound.coe_sup_eq_mul_of_permutable hperm'
  have hinf' : P₁ ⊓ U = ⊥ := by
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    exact (Subgroup.disjoint_of_coprime_natCard (by
      rw [hP₁c, hk]; exact Nat.Coprime.pow_right k (by norm_num))).eq_bot
  have hfac' : ∀ x ∈ P₁ ⊔ U, ∃ p ∈ P₁, ∃ r ∈ U, x = p * r := by
    intro x hx
    rw [← SetLike.mem_coe, hcoe, Set.mem_mul] at hx
    obtain ⟨p, hp, r, hr, rfl⟩ := hx
    exact ⟨p, hp, r, hr, rfl⟩
  have hrel' : U.relIndex (U ⊔ P₁) = 3 := by
    rw [sup_comm]
    exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.relIndex_sup_eq_three_of_mul
      hP₁c hinf' hfac'
  have hnn : ¬ (U ⊔ P₁) ≤ Subgroup.normalizer (U : Set G) := by
    intro hle
    have hP₁n : P₁ ≤ Subgroup.normalizer (U : Set G) := le_sup_right.trans hle
    apply hnoH 1
    have hPH : P₁ ≤ H := fun x hx => hNH ⟨hP₁n hx, hP₁M hx⟩
    rintro _ ⟨y, hy, rfl⟩
    simpa using hPH hy
  refine ⟨U, P₁, hU, hP₁M, hP₁c, ⟨?_, ?_⟩, hnoH⟩
  · exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isSylowTwoOf_of_relIndex_three
      le_sup_left hU2 hrel'
  · exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.nonempty_quotient_pCore_mulEquiv_perm_three_of_le
      le_sup_left hU2 hrel' hnn

theorem d2L34BetaMSideX_of_permuted
    (hK : KFactNormalRankFourThree) (hbase : D2L34BetaMSideBase)
    (hP : D2L34BetaMSidePermuted) : D2L34BetaMSideX := by
  intro d G _ _ P M A H R Rbar K hc hOnly hKmax
  have hstr : GLBStronglyEmbedded 3 M :=
    D2Escape.stronglyEmbedded_of_normalRankFour hK hc.esc hc.glob hc.beta
  refine ⟨hstr, ?_⟩
  obtain ⟨U₀, hU₀, hAU₀, hNU₀, hsyl₀, hUQ₀⟩ := hbase d G P M A H R Rbar K hc hstr hOnly
  exact CFSG.LocalAnalysis.RankThreeTheoremC.exists_s3Parabolic_of_permuted3
    (hP d G P M A H R Rbar K hc hstr hOnly hKmax U₀ hU₀ hAU₀ hNU₀ hsyl₀ hUQ₀)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
