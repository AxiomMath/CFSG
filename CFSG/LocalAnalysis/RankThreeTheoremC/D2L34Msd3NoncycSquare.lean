module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TailInv
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Escape9
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PermuteNine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.QuaternionEscape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_map_le_of_isPGroup {M W E : Subgroup G} (hWM : W ≤ M) (hWp : IsPGroup 3 W)
    (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (hEM : E ≤ M) (hEp : IsPGroup 3 E) :
    ∃ g ∈ M, E.map (MulAut.conj g).toMonoidHom ≤ W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp' : IsPGroup 3 (E.subgroupOf M) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEM).symm
  obtain ⟨S', hS'⟩ := hEp'.exists_le_sylow
  have hWp' : IsPGroup 3 (W.subgroupOf M) :=
    hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWM).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S' (hWp'.toSylow hWidx)
  have hgcoe : MulAut.conj g • (S' : Subgroup M) = W.subgroupOf M := by
    have := congrArg (fun S : Sylow 3 M => (S : Subgroup M)) hg
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxS : (⟨x, hEM hx⟩ : M) ∈ (S' : Subgroup M) := hS' (Subgroup.mem_subgroupOf.mpr hx)
  have hmem : MulAut.conj g • (⟨x, hEM hx⟩ : M) ∈ MulAut.conj g • (S' : Subgroup M) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hxS
  rw [hgcoe, Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.smul_def] using hmem

theorem card_le_of_isElemAbelian_of_pRank {M P A : Subgroup G} (hPM : P ≤ M) (hPp : IsPGroup 3 P)
    (hPidx : ¬ 3 ∣ (P.subgroupOf M).index) (hP3 : Open.pRank 3 P = 3) (hAM : A ≤ M)
    (hA : IsElemAbelian 3 A) : Nat.card A ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨g, -, hgA⟩ := exists_conj_map_le_of_isPGroup hPM hPp hPidx hAM hAp
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  have hmapel : IsElemAbelian 3 (A.map (MulAut.conj g).toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hA _
  have hmapc : Nat.card (A.map (MulAut.conj g).toMonoidHom) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hk]
  have hkle : k ≤ Open.pRank 3 P :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three P)
      ⟨_, hgA, hmapel, hmapc⟩
  rw [hP3] at hkle
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hkle
    _ = 27 := by norm_num

variable [D2Amb3 G]

omit [D2Amb3 G] in
theorem exists_inverting_square3_of_escape {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K)
    {T : Subgroup G} (hT : IsSylowTwoOf T M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    {C₁ : Subgroup G} (hC₁ : C₁ ≠ ⊥) (hC₁2 : IsPGroup 2 C₁)
    (hT₁ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₁ : Set G))
    {D : Subgroup G} (hDN : D ≤ Subgroup.normalizer (C₁ : Set G))
    (hD9 : Nat.card D = 9)
    (hesc : ∀ N : Subgroup G, IsTwoLocal N → ¬ N ≤ M → D ≤ N →
      ∃ N₁ E₀ : Subgroup G, N ≤ N₁ ∧ D ≤ E₀ ∧ D2Escape 3 P M E₀ N₁ E₀ ∧
        D2EscapeMax 3 P M E₀ ∧ Nat.card E₀ = 9) :
    ∃ s ∈ M, (∀ x ∈ D, s * x * s⁻¹ ∈ D) ∧ ∀ x ∈ D, s ^ 2 * x * (s ^ 2)⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXloc : IsTwoLocal (Subgroup.normalizer (C₁ : Set G)) := ⟨C₁, hC₁, hC₁2, rfl⟩
  have hXM : ¬ Subgroup.normalizer (C₁ : Set G) ≤ M := fun h => hNT (hT₁.trans h)
  obtain ⟨N₁, E₀, hNN₁, hDE₀, hesc, hmax, hE₀9⟩ :=
    hesc _ hXloc hXM hDN
  have hE₀D : E₀ = D := (Subgroup.eq_of_le_of_card_ge hDE₀ (by rw [hE₀9, hD9])).symm
  obtain ⟨d₁, Rbar₁, K₁, hc₁⟩ := ctx.allResidue E₀ N₁ E₀ hesc hmax
  have hTN₁ : T ≤ N₁ := (Subgroup.le_normalizer.trans hT₁).trans hNN₁
  have hT₁' : IsSylowTwoOf T (N₁ ⊓ M) := by
    refine ⟨le_inf hTN₁ hT.1, hT.2.1, fun h => hT.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex T (N₁ ⊓ M) M (le_inf hTN₁ hT.1) inf_le_right
    exact h.trans ⟨_, this.symm⟩
  obtain ⟨B, ⟨g, hg, hBg⟩, hBHM, hBel, hB9, hBU, hTBU⟩ :=
    D2L34BetaConf3.exists_permuting_elemAbelian_conj hc₁ hT₁'
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  obtain ⟨Q, hQT, ⟨eQ⟩⟩ :=
    D2L34BetaConf3.exists_quaternion_le_autIn_of_nine hc₁ hE₀9 hT₁' hBHM hBp hB9 hBU hTBU
  rw [hE₀D] at hBg
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
  have hTM : T ≤ M := hT.1
  refine ⟨g⁻¹ * (t' : G) * g, M.mul_mem (M.mul_mem (M.inv_mem hgM) (hTM htT)) hgM, ?_, ?_⟩
  · intro x hx
    have hgx : g * x * g⁻¹ ∈ B := (hBmem _).2 ⟨x, hx, rfl⟩
    have h1 := (hBmem _).1 (htB _ hgx)
    obtain ⟨y, hy, hyeq⟩ := h1
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

theorem exists_inverting_square3 {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    {T : Subgroup G} (hT : IsSylowTwoOf T M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    {C₁ : Subgroup G} (hC₁ : C₁ ≠ ⊥) (hC₁2 : IsPGroup 2 C₁)
    (hT₁ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₁ : Set G))
    {D : Subgroup G} (hDM : D ≤ M) (hDN : D ≤ Subgroup.normalizer (C₁ : Set G))
    (hDp : IsPGroup 3 D) (hDc : ¬ IsCyclic D) (hD9 : Nat.card D = 9) :
    ∃ s ∈ M, (∀ x ∈ D, s * x * s⁻¹ ∈ D) ∧ ∀ x ∈ D, s ^ 2 * x * (s ^ 2)⁻¹ = x⁻¹ :=
  exists_inverting_square3_of_escape ctx hT hNT hC₁ hC₁2 hT₁ hDN hD9
    fun _ hN hNM hDN =>
      D2L34BetaConf3.exists_escape_of_not_isCyclic ctx.conf hstr hN hNM hDN hDM hDp hDc

end CFSG.LocalAnalysis.RankThreeTheoremC
