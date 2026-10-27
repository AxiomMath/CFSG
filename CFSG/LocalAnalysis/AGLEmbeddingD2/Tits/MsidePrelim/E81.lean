module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.TwoOfThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.ThompsonNontrivial
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PermuteNine

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]

theorem D2L34BetaConf3.two_le_pRank_of_isSylowTwoOf {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) : 2 ≤ CFSG.pRank 2 ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hVle, hVel, hVred⟩ :=
    CFSG.Quasithin.conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := CFSG.Quasithin.conjClosure Z M with hVdef
  have hVT : V ≤ T :=
    (hVle.trans inf_le_left).trans (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hZV : Z ≤ V := CFSG.Quasithin.le_conjClosure Z M
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
  have hZ2 : IsPGroup 2 Z := hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
  refine CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.two_le_pRank_of_elemAbelian hT.2.1 hVT
    hVel ?_
  by_contra hlt
  replace hlt := not_le.mp hlt
  obtain ⟨k, hk⟩ := (hT.2.1.to_le hVT).exists_card_eq
  obtain ⟨j, hj⟩ := hZ2.exists_card_eq
  have hj1 : j ≠ 0 := by
    rintro rfl
    apply hZ1
    rw [← Subgroup.card_eq_one, hj, pow_zero]
  have hjk : 2 ^ j ≤ 2 ^ k := by
    rw [← hj, ← hk]
    exact Subgroup.card_le_of_le hZV
  have hk1 : k ≤ 1 := by
    by_contra h
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hjk' : j ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hjk
  have hjk'' : j = k := by omega
  have hZVeq : Z = V := Subgroup.eq_of_le_of_card_ge hZV (by rw [hj, hk, hjk''])
  have hMZ : M ≤ Subgroup.normalizer (Z : Set G) := hZVeq ▸ hVred.2.1
  have hNZ : Subgroup.normalizer (Z : Set G) = M :=
    hc.esc.maxTwoLocal_M.2 _ ⟨Z, hZ1, hZ2, rfl⟩ hMZ
  exact hNT ((normalizer_le_normalizer_quasithinOmegaOneCenter T).trans hNZ.le)

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique
open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3 D2Amb3)

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.false_of_two_escapes_of_esc
    [D2Amb3 G]
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (Q : Subgroup G → Prop)
    (hescQ : ∀ {N X : Subgroup G}, IsTwoLocal N → ¬ N ≤ M → X ≤ N → X ≤ M → IsPGroup 3 X →
      ¬ IsCyclic X → Q X → ∃ N₁ E₀ : Subgroup G, N ≤ N₁ ∧ X ≤ E₀ ∧ D2Escape 3 P M E₀ N₁ E₀ ∧
        D2EscapeMax 3 P M E₀ ∧ Nat.card E₀ = 9)
    (hAll : ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' →
      D2EscapeMax 3 P M R' → ∃ (d' : TauCeti.ValidLieTypeIndex)
        (Rbar' : Sylow 3 (H' ⧸ primeComplementCore (G := H') 3))
        (K' : Subgroup (H' ⧸ primeComplementCore (G := H') 3)),
        D2L34BetaConf3 d' P M A' H' R' Rbar' K')
    (heq : ∀ {d' : TauCeti.ValidLieTypeIndex} {A' H' R' : Subgroup G}
      {Rbar' : Sylow 3 (H' ⧸ primeComplementCore (G := H') 3)}
      {K' : Subgroup (H' ⧸ primeComplementCore (G := H') 3)},
      D2L34BetaConf3 d' P M A' H' R' Rbar' K' → Nat.card R' = 9 → ∀ C : Subgroup G,
      (∀ k ∈ K', ∃ a ∈ H' ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H',
        QuotientGroup.mk' (primeComplementCore (G := H') 3) ⟨a, ha⟩ = k) →
      ∀ N : Subgroup G, GLBIsMaxTwoLocal N → Subgroup.normalizer (C : Set G) ≤ N → N = H')
    {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) {X₁ X₂ W₁ W₂ : Subgroup G}
    (hX₁ : X₁ ≠ ⊥) (hX₁2 : IsPGroup 2 X₁)
    (hX₁T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₁ : Set G))
    (hX₂ : X₂ ≠ ⊥) (hX₂2 : IsPGroup 2 X₂)
    (hX₂T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₂ : Set G))
    (hW₁ : W₁ ≤ M ⊓ Subgroup.normalizer (X₁ : Set G))
    (hW₂ : W₂ ≤ M ⊓ Subgroup.normalizer (X₂ : Set G))
    (hW₁p : IsPGroup 3 W₁) (hW₂p : IsPGroup 3 W₂) (hW₁c : ¬ IsCyclic W₁) (hW₂c : ¬ IsCyclic W₂)
    (hQ₁ : Q W₁) (hQ₂ : Q W₂) (hQ : Q (W₁ ⊔ W₂))
    (hW : IsPGroup 3 (W₁ ⊔ W₂ : Subgroup G)) (h9 : 9 < Nat.card (W₁ ⊔ W₂ : Subgroup G)) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Zc := (CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype with hZc
  set Jc := (CFSG.higherElemThompson ↥T 0).map T.subtype with hJc
  set Ec := (CFSG.higherElemThompsonOmega ↥T 1).map T.subtype with hEc
  have hZcT :=
    OrdinaryProofs.normalizer_le_normalizer_omegaOneCenter_top T
  have hJcT :=
    OrdinaryProofs.normalizer_le_normalizer_higherElemThompson T 0
  have hEcT :=
    OrdinaryProofs.normalizer_le_normalizer_higherElemThompsonOmega T 1
  let good : Subgroup G → Subgroup G → Prop := fun N C =>
    ∀ N' : Subgroup G, GLBIsMaxTwoLocal N' → Subgroup.normalizer (C : Set G) ≤ N' → N' = N
  have step : ∀ X W : Subgroup G, X ≠ ⊥ → IsPGroup 2 X →
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
      W ≤ M ⊓ Subgroup.normalizer (X : Set G) → IsPGroup 3 W → ¬ IsCyclic W →
      Q W → ∃ N : Subgroup G, IsTwoLocal N ∧ ¬ N ≤ M ∧ W ≤ N ∧
        ((good N Zc ∧ good N Jc) ∨ (good N Zc ∧ good N Ec) ∨ (good N Jc ∧ good N Ec)) := by
    intro X W hX hX2 hXT hW hWp hWc hgW
    have hXloc : IsTwoLocal (Subgroup.normalizer (X : Set G)) := ⟨X, hX, hX2, rfl⟩
    have hXM : ¬ Subgroup.normalizer (X : Set G) ≤ M := fun h => hNT (hXT.trans h)
    obtain ⟨N₁, E₀, hNN₁, -, hesc, hmax, hE₀9⟩ :=
      hescQ hXloc hXM (hW.trans inf_le_right) (hW.trans inf_le_left) hWp hWc hgW
    obtain ⟨d₁, Rbar₁, K₁, hc₁⟩ := hAll E₀ N₁ E₀ hesc hmax
    have hTN₁ : T ≤ N₁ := (Subgroup.le_normalizer.trans hXT).trans hNN₁
    have hT₁ : IsSylowTwoOf T (N₁ ⊓ M) := by
      refine ⟨le_inf hTN₁ hT.1, hT.2.1, fun h => hT.2.2 ?_⟩
      have := Subgroup.relIndex_mul_relIndex T (N₁ ⊓ M) M (le_inf hTN₁ hT.1) inf_le_right
      exact h.trans ⟨_, this.symm⟩
    obtain ⟨B, hBHM, hBel, hB9, hBU, hTBU⟩ := D2L34BetaConf3.exists_permuting_elemAbelian hc₁ hT₁
    have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
    have h3 := D2L34BetaConf3.two_of_three_normalized_of_nine hc₁ hE₀9 hT₁ hBHM hBel hB9 hBU hTBU
    have huniq : ∀ C : Subgroup G,
        Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) →
        B ≤ Subgroup.normalizer (C : Set G) → good N₁ C := by
      intro C hCT hBC N' hN' hCN'
      have hcov := D2L34BetaConf3.cover_of_isSylowTwoOf_of_nine hc₁ hE₀9 hT₁ hBHM hBp hB9
        (Y := N₁ ⊓ Subgroup.normalizer (C : Set G))
        (le_inf hTN₁ (Subgroup.le_normalizer.trans hCT))
        (le_inf (hBHM.trans inf_le_left) hBC) (inf_le_inf_left N₁ hCT)
      exact heq hc₁ hE₀9 _ hcov _ hN' hCN'
    refine ⟨N₁, hesc.maxTwoLocal_H.1, hesc.not_le, (hW.trans inf_le_right).trans hNN₁, ?_⟩
    rcases h3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨huniq _ hZcT h1, huniq _ hJcT h2⟩
    · exact Or.inr (Or.inl ⟨huniq _ hZcT h1, huniq _ hEcT h2⟩)
    · exact Or.inr (Or.inr ⟨huniq _ hJcT h1, huniq _ hEcT h2⟩)
  obtain ⟨N₁, hN₁, hN₁M, hW₁N, hU₁⟩ := step X₁ W₁ hX₁ hX₁2 hX₁T hW₁ hW₁p hW₁c hQ₁
  obtain ⟨N₂, -, -, hW₂N, hU₂⟩ := step X₂ W₂ hX₂ hX₂2 hX₂T hW₂ hW₂p hW₂c hQ₂
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hne : ∀ C : Subgroup G, (C = Zc ∨ C = Jc ∨ C = Ec) → C ≠ ⊥ ∧ IsPGroup 2 C := by
    rintro C (rfl | rfl | rfl)
    · refine ⟨fun h => ?_, hT.2.1.to_le (Subgroup.map_subtype_le _)⟩
      rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
      exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.omegaOneCenter_top_ne_bot hT2 h
    · refine ⟨fun h => ?_, hT.2.1.to_le (Subgroup.map_subtype_le _)⟩
      rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
      exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.higherElemThompson_zero_ne_bot hT2 h
    · refine ⟨fun h => ?_, hT.2.1.to_le (Subgroup.map_subtype_le _)⟩
      rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
      exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.higherElemThompsonOmega_one_ne_bot hT2
        (D2L34BetaConf3.two_le_pRank_of_isSylowTwoOf hc hT hNT) h
  have hcommon : ∃ C : Subgroup G, (C = Zc ∨ C = Jc ∨ C = Ec) ∧ good N₁ C ∧ good N₂ C := by
    rcases hU₁ with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
      rcases hU₂ with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
      first
        | exact ⟨Zc, Or.inl rfl, ‹good N₁ Zc›, ‹good N₂ Zc›⟩
        | exact ⟨Jc, Or.inr (Or.inl rfl), ‹good N₁ Jc›, ‹good N₂ Jc›⟩
        | exact ⟨Ec, Or.inr (Or.inr rfl), ‹good N₁ Ec›, ‹good N₂ Ec›⟩
  obtain ⟨C, hC, hC₁, hC₂⟩ := hcommon
  obtain ⟨hC1, hC2⟩ := hne C hC
  obtain ⟨N, hNC, hN⟩ := exists_maximal_twoLocal (⟨C, hC1, hC2, rfl⟩ :
    IsTwoLocal (Subgroup.normalizer (C : Set G)))
  have h12 : N₁ = N₂ := (hC₁ N hN hNC).symm.trans (hC₂ N hN hNC)
  have hWN : W₁ ⊔ W₂ ≤ N₁ := sup_le hW₁N (h12 ▸ hW₂N)
  have hWM : W₁ ⊔ W₂ ≤ M := sup_le (hW₁.trans inf_le_left) (hW₂.trans inf_le_left)
  have hWc : ¬ IsCyclic (W₁ ⊔ W₂ : Subgroup G) := fun hcyc =>
    hW₁c (Subgroup.isCyclic_of_le (H' := W₁ ⊔ W₂) le_sup_left)
  have : Nat.card (W₁ ⊔ W₂ : Subgroup G) ≤ 9 := by
    obtain ⟨_, E₀, -, hXE₀, -, -, hE₀9⟩ := hescQ hN₁ hN₁M hWN hWM hW hWc hQ
    exact hE₀9 ▸ Subgroup.card_le_of_le hXE₀
  omega

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.false_of_two_escapes_of_residue
    [D2Amb3 G]
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hAll : ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' →
      D2EscapeMax 3 P M R' → ∃ (d' : TauCeti.ValidLieTypeIndex)
        (Rbar' : Sylow 3 (H' ⧸ primeComplementCore (G := H') 3))
        (K' : Subgroup (H' ⧸ primeComplementCore (G := H') 3)),
        D2L34BetaConf3 d' P M A' H' R' Rbar' K')
    (hOnly : D2OnlyL34At P M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) {X₁ X₂ W₁ W₂ : Subgroup G}
    (hX₁ : X₁ ≠ ⊥) (hX₁2 : IsPGroup 2 X₁)
    (hX₁T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₁ : Set G))
    (hX₂ : X₂ ≠ ⊥) (hX₂2 : IsPGroup 2 X₂)
    (hX₂T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₂ : Set G))
    (hW₁ : W₁ ≤ M ⊓ Subgroup.normalizer (X₁ : Set G))
    (hW₂ : W₂ ≤ M ⊓ Subgroup.normalizer (X₂ : Set G))
    (hW₁p : IsPGroup 3 W₁) (hW₂p : IsPGroup 3 W₂) (hW₁c : ¬ IsCyclic W₁) (hW₂c : ¬ IsCyclic W₂)
    (hW : IsPGroup 3 (W₁ ⊔ W₂ : Subgroup G)) (h9 : 9 < Nat.card (W₁ ⊔ W₂ : Subgroup G)) :
    False :=
  D2L34BetaConf3.false_of_two_escapes_of_esc hc (fun _ => True)
    (fun hN hNM hXN hXM hX hXc _ =>
      D2L34BetaConf3.exists_escape_of_not_isCyclic hc hstr hN hNM hXN hXM hX hXc) hAll
    (fun hc' _ _ hcov _ hN hNC =>
      D2L34BetaConf3.eq_of_maxTwoLocal_of_normalizer_cover hc' hstr hOnly hcov hN hNC)
    hT hNT hX₁ hX₁2 hX₁T hX₂ hX₂2 hX₂T hW₁ hW₂ hW₁p hW₂p hW₁c hW₂c trivial trivial trivial hW h9

theorem D2L34BetaConf.false_of_two_escapes
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hAll : D2L34AllResidue P M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) {X₁ X₂ W₁ W₂ : Subgroup G}
    (hX₁ : X₁ ≠ ⊥) (hX₁2 : IsPGroup 2 X₁)
    (hX₁T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₁ : Set G))
    (hX₂ : X₂ ≠ ⊥) (hX₂2 : IsPGroup 2 X₂)
    (hX₂T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₂ : Set G))
    (hW₁ : W₁ ≤ M ⊓ Subgroup.normalizer (X₁ : Set G))
    (hW₂ : W₂ ≤ M ⊓ Subgroup.normalizer (X₂ : Set G))
    (hW₁p : IsPGroup 3 W₁) (hW₂p : IsPGroup 3 W₂) (hW₁c : ¬ IsCyclic W₁) (hW₂c : ¬ IsCyclic W₂)
    (hW : IsPGroup 3 (W₁ ⊔ W₂ : Subgroup G)) (h9 : 9 < Nat.card (W₁ ⊔ W₂ : Subgroup G)) :
    False := by
  have := hc.amb3
  exact hc.toConf3.false_of_two_escapes_of_residue hstr
    (fun A' H' R' he hm => let ⟨d', Rbar', K', hc'⟩ := hAll A' H' R' he hm
      ⟨d', Rbar', K', hc'.toConf3⟩)
    hAll.onlyL34At hT hNT hX₁ hX₁2 hX₁T hX₂ hX₂2 hX₂T hW₁ hW₂ hW₁p hW₂p hW₁c hW₂c hW h9

theorem D2L34BetaConf.thompsonJ_not_le_centralizer
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hAll : D2L34AllResidue P M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) :
    ¬ CFSG.Quasithin.thompsonJ T ≤ Subgroup.centralizer
      (CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter T) M : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hJ
  obtain ⟨W₁, W₂, hW₁, hW₂, hW₁c, hW₂c, -, hWel, hWc, -⟩ :=
    D2L34BetaConf.exists_elemAbelian_of_thompsonJ_le hc hstr hT hNT hJ
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hZ1 : quasithinOmegaOneCenter T ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
  have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter T) :=
    hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
  have hJ1 : CFSG.Quasithin.thompsonJ T ≠ ⊥ := Setup.thompsonJ_ne_bot hT.2.1 hT1
  have hJ2 : IsPGroup 2 (CFSG.Quasithin.thompsonJ T) :=
    hT.2.1.to_le (CFSG.Quasithin.B6.thompsonJ_le T)
  have hWp : IsPGroup 3 (W₁ ⊔ W₂ : Subgroup G) :=
    IsPGroup.of_card (n := 4) (by rw [hWc]; norm_num)
  exact D2L34BetaConf.false_of_two_escapes hc hstr hAll hT hNT hZ1 hZ2
    (normalizer_le_normalizer_quasithinOmegaOneCenter T) hJ1 hJ2
    (GammaExtra.normalizer_le_normalizer_thompsonJ T) hW₁ hW₂
    (hWp.to_le le_sup_left) (hWp.to_le le_sup_right)
    (not_isCyclic_of_isElemAbelian (isElemAbelian_of_le hWel le_sup_left)
      (by rw [hW₁c]; norm_num))
    (not_isCyclic_of_isElemAbelian (isElemAbelian_of_le hWel le_sup_right)
      (by rw [hW₂c]; norm_num))
    hWp (by rw [hWc]; norm_num)

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
