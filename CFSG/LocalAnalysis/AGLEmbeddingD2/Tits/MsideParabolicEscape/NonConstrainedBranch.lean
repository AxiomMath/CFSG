module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MsideReduction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SimpleQuotientCentre

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.QuasithinUnique
open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3)
open scoped Pointwise

variable {G : Type} [Group G]

omit [Group G] in
theorem eq_one_of_isPGroup_of_mem_coprime {G : Type} [Group G] {p : ℕ} {Y D : Subgroup G}
    (hDp : Nat.Coprime p (Nat.card D)) (hY : IsPGroup p Y) {x : G} (hxY : x ∈ Y) (hxD : x ∈ D) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hY ⟨x, hxY⟩
  have h1 : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : x ^ Nat.card D = 1 := by
    have h : (⟨x, hxD⟩ : D) ^ Nat.card D = 1 := pow_card_eq_one'
    have := congrArg Subtype.val h
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hd1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf x ∣ Nat.card D := orderOf_dvd_of_pow_eq_one h2
  have hc : Nat.Coprime (orderOf x) (Nat.card D) :=
    (Nat.Coprime.pow_left k hDp).coprime_dvd_left hd1
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc hd2)

theorem false_of_map_conj_le_of_centralizing {p : ℕ} (hp : p.Prime) {M A L D Y : Subgroup G}
    (hM : GLBStronglyEmbedded p M) (hAM : A ≤ M) (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal)
    (hDp : Nat.Coprime p (Nat.card D))
    (hAL : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ D)
    (hZ : ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ D) → x ∈ D)
    (hY : IsPGroup p Y) (hY1 : Y ≠ ⊥) (hYL : Y ≤ L) {g : G}
    (hg : Y.map (MulAut.conj g).toMonoidHom ≤ A) : False := by
  have hgM : g ∈ M :=
    mem_of_map_conj_le_of_stronglyEmbedded hp hM hY hY1 (hYL.trans hLM) hAM hg
  have hYg : IsPGroup p (Y.map (MulAut.conj g).toMonoidHom) := hY.map _
  have hbot : Y.map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxA : x ∈ A := hg hx
    have hx' := hx
    obtain ⟨y, hy, rfl⟩ := hx'
    have hxL : g * y * g⁻¹ ∈ L := by
      have := hLn.conj_mem ⟨y, hLM (hYL hy)⟩ (Subgroup.mem_subgroupOf.mpr (hYL hy)) ⟨g, hgM⟩
      simpa using Subgroup.mem_subgroupOf.mp this
    have hxA' : g * y * g⁻¹ ∈ A := by simpa [MulAut.conj_apply] using hxA
    have hxD : g * y * g⁻¹ ∈ D := hZ _ hxL (fun l hl => hAL _ hxA' l hl)
    exact eq_one_of_isPGroup_of_mem_coprime hDp hYg hx hxD
  apply hY1
  have hcard : Nat.card (Y.map (MulAut.conj g).toMonoidHom) = Nat.card Y :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [hbot, Subgroup.card_bot] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard.symm

variable [Finite G]

@[expose] def SimpleNonabelianModulo (L D : Subgroup G) : Prop :=
  ∃ hn : (D.subgroupOf L).Normal, haveI := hn
    IsSimpleGroup (L ⧸ D.subgroupOf L) ∧ ¬ IsMulCommutative (L ⧸ D.subgroupOf L)

omit [Finite G] in
theorem mem_of_commutators_mem_of_simpleNonabelianModulo {L D : Subgroup G}
    (h : SimpleNonabelianModulo L D) {x : G} (hxL : x ∈ L)
    (hx : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ D) : x ∈ D := by
  obtain ⟨hn, hs, hnab⟩ := h
  haveI := hn
  have := OrdinaryProofs.center_quotient_eq_bot_of_simple (L := L) (D := D) hnab ⟨x, hxL⟩
    (fun l => Subgroup.mem_subgroupOf.mpr (hx l l.2))
  exact Subgroup.mem_subgroupOf.mp this

@[expose] def D2L34BetaMSideNonConstrainedInput : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ U : Subgroup G, IsBetaBase H M U → A ≤ Subgroup.normalizer (U : Set G) →
      Subgroup.normalizer (U : Set G) ≤ H →
      IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) →
      IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) →
      ∃ P₁ L : Subgroup G, L ≤ M ∧ (L.subgroupOf M).Normal ∧ P₁ ≤ L ∧
        Nat.card P₁ = 3 ∧ (P₁ : Set G) * U = U * P₁ ∧
        (∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ GLBPrimeCore 3 M) ∧
        SimpleNonabelianModulo L (GLBPrimeCore 3 M)

open CFSG.AGLEmbeddingD2.Tits CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.d2L34BetaMSidePermuted3_of_nonconstrained
    {G : Type} [Group G] [Finite G]
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {U : Subgroup G} (hU : IsBetaBase H M U)
    (hNHU : Subgroup.normalizer (U : Set G) ≤ H) {P₁ L : Subgroup G} (hLM : L ≤ M)
    (hLn : (L.subgroupOf M).Normal) (hP₁L : P₁ ≤ L) (hP₁c : Nat.card P₁ = 3)
    (hperm' : (P₁ : Set G) * U = U * P₁)
    (hAL : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ GLBPrimeCore 3 M)
    (hsimple : SimpleNonabelianModulo L (GLBPrimeCore 3 M)) : PermutedConcl H M := by
  have hP₁p : IsPGroup 3 P₁ := IsPGroup.of_card (n := 1) (by rw [hP₁c]; simp)
  have hP₁1 : P₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP₁c
    omega
  have hR9 := hc.card_R_eq_nine hstr
  have hAR : A = R := Subgroup.eq_of_le_of_card_ge hc.esc.A_le
    (by rw [hR9, hc.esc.card_A]; norm_num)
  have hP₁M : P₁ ≤ M := hP₁L.trans hLM
  refine ⟨U, P₁, hU, hP₁M, hP₁c, hperm', inf_le_left.trans hNHU, ?_⟩
  intro g hg
  have hXp : IsPGroup 3 (P₁.map (MulAut.conj g).toMonoidHom) := hP₁p.map _
  obtain ⟨h, hh, hle⟩ := S3AmalgamBound.exists_conj_le_of_isSylow (p := 3) hc.esc.isSylow hg hXp
  refine false_of_map_conj_le_of_centralizing Nat.prime_three hstr hc.esc.A_le_M hLM hLn
    (glbPrimeCore_coprime 3 M) hAL
    (fun x hx h => mem_of_commutators_mem_of_simpleNonabelianModulo hsimple hx h) hP₁p hP₁1 hP₁L
    (g := h * g) ?_
  rintro _ ⟨y, hy, rfl⟩
  have := hle ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  rw [← hAR] at this
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem d2L34BetaMSidePermuted_of_nonconstrained
    (hin : D2L34BetaMSideNonConstrainedInput) :
    ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
      (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
      GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
      ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
      ∀ U : Subgroup G, IsBetaBase H M U → A ≤ Subgroup.normalizer (U : Set G) →
        Subgroup.normalizer (U : Set G) ≤ H →
        IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) →
        IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) → PermutedConcl H M := by
  intro d G _ _ P M A H R Rbar K hc hstr hOnly hKmax hcon U hU hAU hNHU hsylU hUQ
  obtain ⟨P₁, L, hLM, hLn, hP₁L, hP₁c, hperm', hAL, hsimple⟩ :=
    hin d G P M A H R Rbar K hc hstr hOnly hKmax hcon U hU hAU hNHU hsylU hUQ
  exact CFSG.LocalAnalysis.RankThreeTheoremC.d2L34BetaMSidePermuted3_of_nonconstrained hc.toConf3
    hstr hU hNHU hLM hLn hP₁L hP₁c hperm' hAL hsimple

theorem d2L34BetaMSidePermuted_of_branches
    (hperm : PermutableOrderThreeAt)
    (hin : D2L34BetaMSideInput) (hnc : D2L34BetaMSideNonConstrainedInput) :
    D2L34BetaMSidePermuted := by
  intro d G _ _ P M A H R Rbar K hc hstr hOnly hKmax U hU hAU hNHU hsylU hUQ
  by_cases hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M
  · exact d2L34BetaMSidePermuted_of_input hperm hin d G P M A H R Rbar K hc hstr hOnly hKmax hcon
      U hU hAU hNHU hsylU hUQ
  · exact d2L34BetaMSidePermuted_of_nonconstrained hnc d G P M A H R Rbar K hc hstr hOnly hKmax
      hcon U hU hAU hNHU hsylU hUQ

theorem d2L34BetaMSideX_of_input
    (hperm : PermutableOrderThreeAt) (hbase : D2L34BetaMSideBase) (hin : D2L34BetaMSideInput)
    (hnc : D2L34BetaMSideNonConstrainedInput) : D2L34BetaMSideX :=
  d2L34BetaMSideX_of_permuted
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.kFactNormalRankFourThree hbase
    (d2L34BetaMSidePermuted_of_branches hperm hin hnc)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
