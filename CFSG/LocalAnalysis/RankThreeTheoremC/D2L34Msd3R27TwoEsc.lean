module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Escape
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Kmax
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Escape
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNoncycA
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TailInv
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.E81
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Lift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}

private theorem isSylowTwoOf_inf_of_le {N : Subgroup G} (hT : IsSylowTwoOf T M) (hTN : T ≤ N) :
    IsSylowTwoOf T (N ⊓ M) := by
  refine ⟨le_inf hTN hT.1, hT.2.1, fun h => hT.2.2 ?_⟩
  have := Subgroup.relIndex_mul_relIndex T (N ⊓ M) M (le_inf hTN hT.1) inf_le_right
  exact h.trans ⟨_, this.symm⟩

private theorem D2L34R27.exists_conf_of_normalizer (c : D2L34R27 G d P M A H R Rbar K T)
    {X W E : Subgroup G} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hXT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hW : W ≤ M ⊓ Subgroup.normalizer (X : Set G)) (hWp : IsPGroup 3 W) (hEW : E ≤ W)
    (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hEcore : GLBCore 3 1 E ≤ M) :
    ∃ (N₁ E₀ : Subgroup G) (d₁ : TauCeti.ValidLieTypeIndex)
      (Rbar₁ : Sylow 3 (N₁ ⧸ primeComplementCore (G := N₁) 3))
      (K₁ : Subgroup (N₁ ⧸ primeComplementCore (G := N₁) 3)),
      Subgroup.normalizer (X : Set G) ≤ N₁ ∧ W ≤ N₁ ∧ IsSylowTwoOf T (N₁ ⊓ M) ∧
        D2L34BetaConf3 d₁ P M E N₁ E₀ Rbar₁ K₁ := by
  have hXloc : IsTwoLocal (Subgroup.normalizer (X : Set G)) := ⟨X, hX, hX2, rfl⟩
  have hXM : ¬ Subgroup.normalizer (X : Set G) ≤ M := fun h => c.not_normalizer_le (hXT.trans h)
  obtain ⟨N₁, E₀, d₁, Rbar₁, K₁, hNN₁, -, -, hc₁⟩ :=
    c.exists_conf_of_good hXloc hXT hXM (hW.trans inf_le_right) (hW.trans inf_le_left) hWp hEW
      hEel hE9 hEcore
  have hTN₁ : T ≤ N₁ := (Subgroup.le_normalizer.trans hXT).trans hNN₁
  exact ⟨N₁, E₀, d₁, Rbar₁, K₁, hNN₁, (hW.trans inf_le_right).trans hNN₁,
    isSylowTwoOf_inf_of_le c.sylow hTN₁, hc₁⟩

theorem D2L34R27.false_of_two_escapes
    (c : D2L34R27 G d P M A H R Rbar K T) {X₁ X₂ W₁ W₂ : Subgroup G}
    (hX₁ : X₁ ≠ ⊥) (hX₁2 : IsPGroup 2 X₁)
    (hX₁T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₁ : Set G))
    (hX₂ : X₂ ≠ ⊥) (hX₂2 : IsPGroup 2 X₂)
    (hX₂T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₂ : Set G))
    (hW₁ : W₁ ≤ M ⊓ Subgroup.normalizer (X₁ : Set G))
    (hW₂ : W₂ ≤ M ⊓ Subgroup.normalizer (X₂ : Set G))
    (hW₁p : IsPGroup 3 W₁) (hW₂p : IsPGroup 3 W₂) (hg₁ : HasGoodE9 M W₁)
    (hg₂ : HasGoodE9 M W₂) (hW : IsPGroup 3 (W₁ ⊔ W₂ : Subgroup G))
    (h3 : 3 ≤ CFSG.Open.pRank 3 (W₁ ⊔ W₂ : Subgroup G)) : False := by
  haveI := c.amb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf T M := c.sylow
  have hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M := c.not_normalizer_le
  set Zc := (CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype with hZc
  set Jc := (CFSG.higherElemThompson ↥T 0).map T.subtype with hJc
  set Ec := (CFSG.higherElemThompsonOmega ↥T 1).map T.subtype with hEc
  have hZcT := OrdinaryProofs.normalizer_le_normalizer_omegaOneCenter_top T
  have hJcT := OrdinaryProofs.normalizer_le_normalizer_higherElemThompson T 0
  have hEcT := OrdinaryProofs.normalizer_le_normalizer_higherElemThompsonOmega T 1
  let good : Subgroup G → Subgroup G → Prop := fun N C =>
    ∀ N' : Subgroup G, GLBIsMaxTwoLocal N' → Subgroup.normalizer (C : Set G) ≤ N' → N' = N
  have step : ∀ X W : Subgroup G, X ≠ ⊥ → IsPGroup 2 X →
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
      W ≤ M ⊓ Subgroup.normalizer (X : Set G) → IsPGroup 3 W → HasGoodE9 M W →
      ∃ N : Subgroup G, IsTwoLocal N ∧ ¬ N ≤ M ∧ W ≤ N ∧
        ((good N Zc ∧ good N Jc) ∨ (good N Zc ∧ good N Ec) ∨ (good N Jc ∧ good N Ec)) := by
    intro X W hX hX2 hXT hW hWp ⟨E, hEW, hEel, hE9, hEcore⟩
    obtain ⟨N₁, E₀, d₁, Rbar₁, K₁, -, hWN₁, hT₁, hc₁⟩ :=
      c.exists_conf_of_normalizer hX hX2 hXT hW hWp hEW hEel hE9 hEcore
    have hTN₁ : T ≤ N₁ := hT₁.1.trans inf_le_left
    obtain ⟨B, hBg, hBHM, -, -, hBU, hTBU⟩ :=
      D2L34BetaConf3.exists_permuting_elemAbelian_conj hc₁ hT₁
    have huniq : ∀ C : Subgroup G,
        Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) →
        B ≤ Subgroup.normalizer (C : Set G) → good N₁ C := by
      intro C hCT hBC N' hN' hCN'
      have hcov := hc₁.cover_of_isSylowTwoOf_of_conj hT₁ hBg
        (Y := N₁ ⊓ Subgroup.normalizer (C : Set G))
        (le_inf hTN₁ (Subgroup.le_normalizer.trans hCT))
        (le_inf (hBHM.trans inf_le_left) hBC) (inf_le_inf_left N₁ hCT)
      exact hc₁.toWeak.eq_of_maxTwoLocal_of_normalizer_cover27 c.ctx.normRankTwo
        c.ctx.allResidue (c.ctx.conf.card_le_27 c.card_R) hc₁.pCoreOf_two_le
        c.noNonExtremal.nonExtremalL34At hcov hN' hCN' (hCT.trans hCN')
    refine ⟨N₁, hc₁.esc.maxTwoLocal_H.1, hc₁.esc.not_le, hWN₁, ?_⟩
    rcases hc₁.two_of_three_normalized_of_conj hT₁ hBg hBU hTBU with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨huniq _ hZcT h1, huniq _ hJcT h2⟩
    · exact Or.inr (Or.inl ⟨huniq _ hZcT h1, huniq _ hEcT h2⟩)
    · exact Or.inr (Or.inr ⟨huniq _ hJcT h1, huniq _ hEcT h2⟩)
  obtain ⟨N₁, hN₁, hN₁M, hW₁N, hU₁⟩ := step X₁ W₁ hX₁ hX₁2 hX₁T hW₁ hW₁p hg₁
  obtain ⟨N₂, -, -, hW₂N, hU₂⟩ := step X₂ W₂ hX₂ hX₂2 hX₂T hW₂ hW₂p hg₂
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot c.ctx.conf.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hne : ∀ C : Subgroup G, (C = Zc ∨ C = Jc ∨ C = Ec) → C ≠ ⊥ ∧ IsPGroup 2 C := by
    rintro C (rfl | rfl | rfl)
    · refine ⟨fun h => ?_, hT.2.1.to_le (Subgroup.map_subtype_le _)⟩
      rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
      exact OrdinaryProofs.omegaOneCenter_top_ne_bot hT2 h
    · refine ⟨fun h => ?_, hT.2.1.to_le (Subgroup.map_subtype_le _)⟩
      rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
      exact OrdinaryProofs.higherElemThompson_zero_ne_bot hT2 h
    · refine ⟨fun h => ?_, hT.2.1.to_le (Subgroup.map_subtype_le _)⟩
      rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
      exact OrdinaryProofs.higherElemThompsonOmega_one_ne_bot hT2
        (D2L34BetaConf3.two_le_pRank_of_isSylowTwoOf c.ctx.conf hT hNT) h
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
  have hWNM : W₁ ⊔ W₂ ≤ N₁ ⊓ M :=
    le_inf (sup_le hW₁N (h12 ▸ hW₂N)) (sup_le (hW₁.trans inf_le_left) (hW₂.trans inf_le_left))
  have := (pRank_mono 3 Nat.prime_three hWNM).trans (c.ctx.pRank_inf_le_two hN₁ hN₁M)
  omega

theorem D2L34R27.exists_inverting_square
    (c : D2L34R27 G d P M A H R Rbar K T) {C₁ : Subgroup G} (hC₁ : C₁ ≠ ⊥)
    (hC₁2 : IsPGroup 2 C₁)
    (hT₁ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₁ : Set G))
    {D : Subgroup G} (hDM : D ≤ M) (hDN : D ≤ Subgroup.normalizer (C₁ : Set G))
    (hDel : IsElemAbelian 3 D) (hD9 : Nat.card D = 9) (hDcore : GLBCore 3 1 D ≤ M) :
    ∃ s ∈ M, (∀ x ∈ D, s * x * s⁻¹ ∈ D) ∧ ∀ x ∈ D, s ^ 2 * x * (s ^ 2)⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 2) (by rw [hD9]; norm_num)
  obtain ⟨N₁, E₀, d₁, Rbar₁, K₁, -, -, hT₁', hc₁⟩ :=
    c.exists_conf_of_normalizer hC₁ hC₁2 hT₁ (le_inf hDM hDN) hDp le_rfl hDel hD9 hDcore
  obtain ⟨B, ⟨g, hg, hBg⟩, -, hBel, hB9, hBU, hTBU⟩ :=
    D2L34BetaConf3.exists_permuting_elemAbelian_conj hc₁ hT₁'
  obtain ⟨Q, hQT, ⟨eQ⟩⟩ := hc₁.exists_quaternion_le_autIn_of_conj hT₁' ⟨g, hg, hBg⟩ hBU hTBU
  set q : ↥Q := eQ.symm (QuaternionGroup.xa 0) with hq
  have hq4 : orderOf (q : MulAut B) = 4 := by
    rw [Subgroup.orderOf_coe, hq, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]
  obtain ⟨t', ht'T, ht'q⟩ := hQT q.2
  have htT : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'T
  have htB : ∀ e ∈ B, (t' : G) * e * (t' : G)⁻¹ ∈ B := fun e he =>
    (Subgroup.mem_normalizer_iff.1 t'.2 e).1 he
  have hact : ∀ (k : ℕ) (b : B),
      (((B.normalizerMonoidHom t') ^ k) b : G) = (t' : G) ^ k * b * ((t' : G) ^ k)⁻¹ := by
    intro k b
    rw [← map_pow]
    rfl
  have hq1 : (q : MulAut B) ^ 4 = 1 := by
    have := pow_orderOf_eq_one (q : MulAut B)
    rwa [hq4] at this
  have h4 : ∀ e ∈ B, (t' : G) ^ 4 * e * ((t' : G) ^ 4)⁻¹ = e := by
    intro e he
    have h := hact 4 ⟨e, he⟩
    rw [ht'q, hq1, MulAut.one_apply] at h
    exact h.symm
  have h2 : ∃ e ∈ B, (t' : G) ^ 2 * e * ((t' : G) ^ 2)⁻¹ ≠ e := by
    have hne : (q : MulAut B) ^ 2 ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hq4]; norm_num)
    by_contra hcon
    push Not at hcon
    apply hne
    refine MulEquiv.ext fun b => Subtype.ext ?_
    have h := hact 2 b
    rw [ht'q] at h
    rw [h]
    exact hcon b.1 b.2
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hinv := sq_eq_inv_of_order_four (E := B) hBab hBel.2 hB9 htB h4 h2
  have hBmem : ∀ y, y ∈ B ↔ y ∈ D.map (MulAut.conj g).toMonoidHom := fun y => by rw [hBg]
  have hgM : g ∈ M := hg.2
  have hTM : T ≤ M := c.sylow.1
  refine ⟨g⁻¹ * (t' : G) * g, M.mul_mem (M.mul_mem (M.inv_mem hgM) (hTM htT)) hgM, ?_, ?_⟩
  · intro x hx
    have hgx : g * x * g⁻¹ ∈ B := (hBmem _).2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := (hBmem _).1 (htB _ hgx)
    have hyeq' : g * y * g⁻¹ = (t' : G) * (g * x * g⁻¹) * (t' : G)⁻¹ := hyeq
    have hsx : g⁻¹ * (t' : G) * g * x * (g⁻¹ * (t' : G) * g)⁻¹ = y := by
      have e1 : g⁻¹ * (t' : G) * g * x * (g⁻¹ * (t' : G) * g)⁻¹ =
          g⁻¹ * ((t' : G) * (g * x * g⁻¹) * (t' : G)⁻¹) * g := by group
      rw [e1, ← hyeq']
      group
    rw [hsx]
    exact hy
  · intro x hx
    have hgx : g * x * g⁻¹ ∈ B := (hBmem _).2 ⟨x, hx, rfl⟩
    have h1 := hinv _ hgx
    have hs2eq : (g⁻¹ * (t' : G) * g) ^ 2 = g⁻¹ * (t' : G) ^ 2 * g := by
      rw [sq, sq]
      group
    have e1 : (g⁻¹ * (t' : G) * g) ^ 2 * x * ((g⁻¹ * (t' : G) * g) ^ 2)⁻¹ =
        g⁻¹ * ((t' : G) ^ 2 * (g * x * g⁻¹) * ((t' : G) ^ 2)⁻¹) * g := by
      rw [hs2eq]
      group
    rw [e1, h1]
    group

theorem D2L34R27.false_of_two_factors_in_normalizer
    (c : D2L34R27 G d P M A H R Rbar K T) {V : Subgroup G} {hU : IsElemAbelian 2 V}
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) {X : Subgroup G} (hX1 : X ≠ ⊥)
    (hXp : IsPGroup 2 X)
    (hXT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G))
    {Y : Subgroup G} (hYM : Y ≤ M) (hYN : Y ≤ Subgroup.normalizer (X : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6) {L₁ L₂ : Subgroup (MulAut (IntMod V hU))} (h₁ : L₁ ∈ I)
    (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂) (hL₁ : L₁ ≤ autI hU Y) (hL₂ : L₂ ≤ autI hU Y)
    (hgood : ∀ x₁ x₂ : G, x₁ ∈ Y → x₂ ∈ Y → x₁ * x₂ = x₂ * x₁ → x₁ ^ 3 = 1 → x₂ ^ 3 = 1 →
      ∀ (hx₁M : x₁ ∈ M) (hx₂M : x₂ ∈ M), actM hU hMN ⟨x₁, hx₁M⟩ ∈ L₁ →
        actM hU hMN ⟨x₂, hx₂M⟩ ∈ L₂ → actM hU hMN ⟨x₁, hx₁M⟩ ≠ 1 → actM hU hMN ⟨x₂, hx₂M⟩ ≠ 1 →
        HasGoodE9 M (Subgroup.closure {x₁, x₂})) : False := by
  have hN2 : IsTwoLocal (Subgroup.normalizer (X : Set G)) := ⟨X, hX1, hXp, rfl⟩
  have hNM : ¬ Subgroup.normalizer (X : Set G) ≤ M := fun h => c.not_normalizer_le (hXT.trans h)
  refine false_of_two_factors_of_pair hMN hYM hC3 hI hcard h₁ h₂ hne hL₁ hL₂
    fun x₁ x₂ hx₁ hx₂ hcomm hx₁3 hx₂3 hx₁M hx₂M he₁ he₂ hn₁ hn₂ =>
      false_of_same_side_pair3_of_conj hU hMN hI h₁ h₂ hne hx₁M hx₂M (hYN hx₁) (hYN hx₂) hcomm
        hx₁3 hx₂3 he₁ he₂ hn₁ hn₂ fun X' hX' hX'N hX'M hX'p _ => ?_
  subst hX'
  obtain ⟨E, hEX, hEel, hE9, hEcore⟩ :=
    hgood x₁ x₂ hx₁ hx₂ hcomm hx₁3 hx₂3 hx₁M hx₂M he₁ he₂ hn₁ hn₂
  have hcommX : IsMulCommutative (Subgroup.closure ({x₁, x₂} : Set G)) :=
    Subgroup.isMulCommutative_closure (Set.pairwise_pair.mpr fun _ => ⟨hcomm, hcomm.symm⟩)
  have hXE : Subgroup.closure ({x₁, x₂} : Set G) = E := by
    rcases c.eq_or_extraspecial_of_good hN2 hNM hX'N hX'M hX'p hEX hEel hE9 hEcore with
      h | ⟨h27, hes⟩
    · exact h
    · exfalso
      have htop : Subgroup.center (Subgroup.closure ({x₁, x₂} : Set G)) = ⊤ := by
        rw [eq_top_iff]
        intro z _
        rw [Subgroup.mem_center_iff]
        intro w
        exact hcommX.is_comm.comm w z
      have h3 := hes.2.2.2
      rw [htop, Subgroup.card_top, h27] at h3
      omega
  subst hXE
  exact ⟨hEel, hE9, c.exists_conj_eq_of_good hN2 hXT hNM hX'N hX'M hEel hE9 hEcore⟩

theorem D2L34SideCtx3.false_of_thompsonJ_le_of_coprime'
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K)
    (h3 : 3 ≤ Open.pRank 3 M) (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(ffC M T)) : False := by
  have := ctx.amb
  exact ctx.conf.false_of_thompsonJ_le_of_coprime_of_card h3 hT hNT hJ hC3
    fun E hJ1 hJ2 hNJ hE hEel hEc _ _ => by
      have hrk := ctx.pRank_inf_le_two
        (⟨_, hJ1, hJ2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (thompsonJ T : Set G))) hNJ
      have h3' : 3 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (thompsonJ T : Set G) ⊓ M) :=
        CFSG.SectionRank.le_pRank Nat.prime_three.one_lt
          (le_inf (hE.trans inf_le_right) (hE.trans inf_le_left)) hEel hEc
      omega

end CFSG.LocalAnalysis.RankThreeTheoremC
