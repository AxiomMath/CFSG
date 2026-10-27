module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WEscape
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Card
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Good

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}

private theorem card_eq_nine_or_27_of_isPGroup {Y : Subgroup G} (hY : IsPGroup 3 Y)
    (h9 : 9 ≤ Nat.card Y) (h27 : Nat.card Y ≤ 27) : Nat.card Y = 9 ∨ Nat.card Y = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hY
  rw [hn] at h9 h27 ⊢
  obtain rfl | rfl : n = 2 ∨ n = 3 := by
    have hn2 : 2 ≤ n := by
      by_contra h
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) (show n ≤ 1 by omega)
      exact absurd (h9.trans this) (by norm_num)
    have hn3 : n ≤ 3 := by
      by_contra h
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) (show 4 ≤ n by omega)
      exact absurd (this.trans h27) (by norm_num)
    omega
  · left
    norm_num
  · right
    norm_num

private theorem D2L34R27.exists_escape_aux (c : D2L34R27 G d P M A H R Rbar K T)
    {N : Subgroup G} (hN2 : IsTwoLocal N) (hNM : ¬ N ≤ M) {X E : Subgroup G} (hXN : X ≤ N)
    (hXM : X ≤ M) (hX : IsPGroup 3 X) (hEX : E ≤ X) (hEel : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hEcore : GLBCore 3 1 E ≤ M) :
    ∃ N₁ E₀ : Subgroup G, N ≤ N₁ ∧ X ≤ E₀ ∧ D2Escape 3 P M E N₁ E₀ ∧
      (E₀ = E ∨ (Nat.card E₀ = 27 ∧ ∃ (d₁ : TauCeti.ValidLieTypeIndex)
        (Rbar₁ : Sylow 3 (N₁ ⧸ primeComplementCore (G := N₁) 3))
        (K₁ : Subgroup (N₁ ⧸ primeComplementCore (G := N₁) 3)),
        D2L34BetaConf3 d₁ P M E N₁ E₀ Rbar₁ K₁)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := c.amb
  have hc := c.ctx.conf
  have hEc : Nat.card E = 3 ^ 2 := by rw [hE9]; norm_num
  obtain ⟨N₁, hNN₁, hN₁⟩ := exists_maximal_twoLocal hN2
  have hN₁M : ¬ N₁ ≤ M := fun h => hNM (hNN₁.trans h)
  have hXN₁ : X ≤ N₁ := hXN.trans hNN₁
  have hXp : IsPGroup 3 (X.subgroupOf N₁) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXN₁).symm
  obtain ⟨S, hXS⟩ := hXp.exists_le_sylow
  set E₀ : Subgroup G := (S : Subgroup N₁).map N₁.subtype
  have hXE₀ : X ≤ E₀ := fun x hx => ⟨⟨x, hXN₁ hx⟩, hXS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hE₀p : IsPGroup 3 E₀ := S.isPGroup'.map N₁.subtype
  have hErank : 2 ≤ Open.pRank 3 E := le_pRank_of_isElemAbelian Nat.prime_three hEel hEc
  have hX2 : 2 ≤ Open.pRank 3 X := hErank.trans (pRank_mono 3 Nat.prime_three hEX)
  have hE₀M : E₀ ≤ M := le_of_pGroup_of_normRankTwo c.ctx.normRankTwo hE₀p hXE₀ hXM hX2
  have hE₀N₁ : E₀ ≤ N₁ := Subgroup.map_subtype_le _
  have hEE₀ : E ≤ E₀ := hEX.trans hXE₀
  have hrank₀ : Open.pRank 3 (N₁ ⊓ M) ≤ 2 := by
    by_contra hlt
    exact hN₁M (D2Amb3.d1 (G := G) P M hc.esc.maxTwoLocal_M
      ((weakCore_le_fullCore 3 (P : Subgroup G)).trans hc.esc.core_le) N₁ hN₁.1 (by omega))
  have hesc : D2Escape 3 P M E N₁ E₀ :=
    { prime := Nat.prime_three
      ne_two := by norm_num
      sylow_le := hc.esc.sylow_le
      core_le := hc.esc.core_le
      maxTwoLocal_M := hc.esc.maxTwoLocal_M
      maxTwoLocal_H := hN₁
      elem := hEel
      card_A := hEc
      core_A := hEcore
      A_le := hEE₀
      le_H := hE₀N₁
      le_M := hE₀M
      isSylow := ⟨S, rfl⟩
      pRank_eq := le_antisymm
        ((pRank_mono 3 Nat.prime_three (le_inf hE₀N₁ hE₀M)).trans hrank₀)
        (hErank.trans (pRank_mono 3 Nat.prime_three hEE₀))
      not_le := hN₁M }
  refine ⟨N₁, E₀, hNN₁, hXE₀, hesc, ?_⟩
  rcases card_eq_nine_or_27_of_isPGroup hE₀p (hE9 ▸ Subgroup.card_le_of_le hEE₀)
      (hc.card_le_27 c.card_R E N₁ E₀ hesc) with h9 | h27
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hEE₀ (by rw [h9, hE9])).symm
  · have hmax : D2EscapeMax 3 P M E₀ := fun A' H' R' h' =>
      (hc.card_le_27 c.card_R A' H' R' h').trans h27.ge
    exact Or.inr ⟨h27, c.ctx.allResidue E N₁ E₀ hesc hmax⟩

theorem D2L34R27.exists_conf_of_good (c : D2L34R27 G d P M A H R Rbar K T) {N : Subgroup G}
    (hN2 : IsTwoLocal N) (hNT : Subgroup.normalizer (T : Set G) ≤ N) (hNM : ¬ N ≤ M)
    {X E : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M) (hX : IsPGroup 3 X) (hEX : E ≤ X)
    (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hEcore : GLBCore 3 1 E ≤ M) :
    ∃ (N₁ E₀ : Subgroup G) (d₁ : TauCeti.ValidLieTypeIndex)
      (Rbar₁ : Sylow 3 (N₁ ⧸ primeComplementCore (G := N₁) 3))
      (K₁ : Subgroup (N₁ ⧸ primeComplementCore (G := N₁) 3)),
      N ≤ N₁ ∧ X ≤ E₀ ∧ Nat.card E₀ = 27 ∧ D2L34BetaConf3 d₁ P M E N₁ E₀ Rbar₁ K₁ := by
  obtain ⟨N₁, E₀, hNN₁, hXE₀, hesc, hE₀ | ⟨h27, d₁, Rbar₁, K₁, hconf⟩⟩ :=
    D2L34R27.exists_escape_aux c hN2 hNM hXN hXM hX hEX hEel hE9 hEcore
  · rw [hE₀] at hesc
    exact (c.noNonExtremal E N₁ hesc (hNT.trans hNN₁)).elim
  · exact ⟨N₁, E₀, d₁, Rbar₁, K₁, hNN₁, hXE₀, h27, hconf⟩

theorem D2L34R27.eq_of_good
    (c : D2L34R27 G d P M A H R Rbar K T) {N : Subgroup G}
    (hN2 : IsTwoLocal N) (hNM : ¬ N ≤ M) {X E E' : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M)
    (hX : IsPGroup 3 X) (hEX : E ≤ X) (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEcore : GLBCore 3 1 E ≤ M) (hE'X : E' ≤ X) (hE'el : IsElemAbelian 3 E')
    (hE'9 : Nat.card E' = 9) (hE'core : GLBCore 3 1 E' ≤ M) : E' = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N₁, E₀, -, hXE₀, hesc, hE₀ | ⟨-, d₁, Rbar₁, K₁, hconf⟩⟩ :=
    D2L34R27.exists_escape_aux c hN2 hNM hXN hXM hX hEX hEel hE9 hEcore
  · have hE'E : E' ≤ E := by
      rw [← hE₀]
      exact hE'X.trans hXE₀
    exact Subgroup.eq_of_le_of_card_ge hE'E (by rw [hE9, hE'9])
  ·
    have hE'E₀ : E' ≤ E₀ := hE'X.trans hXE₀
    have hmap := hconf.map_eq_of_good (le_inf (hE'E₀.trans hesc.le_H) (hE'E₀.trans hesc.le_M))
      hE'el hE'9 hE'core
    have hE'E : E' ≤ E := le_of_map_mk_le hesc.le_H hesc.isPGroup hE'E₀ hesc.A_le hmap.le
    exact Subgroup.eq_of_le_of_card_ge hE'E (by rw [hE9, hE'9])

theorem D2L34R27.eq_or_extraspecial_of_good (c : D2L34R27 G d P M A H R Rbar K T)
    {N : Subgroup G} (hN2 : IsTwoLocal N) (hNM : ¬ N ≤ M) {X E : Subgroup G} (hXN : X ≤ N)
    (hXM : X ≤ M) (hX : IsPGroup 3 X) (hEX : E ≤ X) (hEel : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hEcore : GLBCore 3 1 E ≤ M) :
    X = E ∨ (Nat.card X = 27 ∧ CFSG.IsExtraspecialPGroup 3 X) := by
  obtain ⟨N₁, E₀, -, hXE₀, -, hE₀ | ⟨h27, d₁, Rbar₁, K₁, hconf⟩⟩ :=
    D2L34R27.exists_escape_aux c hN2 hNM hXN hXM hX hEX hEel hE9 hEcore
  · refine Or.inl (le_antisymm ?_ hEX)
    rw [← hE₀]
    exact hXE₀
  ·
    rcases card_eq_nine_or_27_of_isPGroup hX (hE9 ▸ Subgroup.card_le_of_le hEX)
        (h27 ▸ Subgroup.card_le_of_le hXE₀) with h9 | h27X
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hEX (by rw [h9, hE9])).symm
    · have hXeq : X = E₀ := Subgroup.eq_of_le_of_card_ge hXE₀ (by rw [h27, h27X])
      subst hXeq
      exact Or.inr ⟨h27X, hconf.isExtraspecialPGroup_of_card_R_eq_27 h27⟩

theorem D2L34R27.exists_conj_eq_of_good
    (c : D2L34R27 G d P M A H R Rbar K T) {N : Subgroup G} (hN2 : IsTwoLocal N)
    (hNT : Subgroup.normalizer (T : Set G) ≤ N) (hNM : ¬ N ≤ M) {E : Subgroup G} (hEN : E ≤ N)
    (hEM : E ≤ M) (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEcore : GLBCore 3 1 E ≤ M) :
    ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
      ∃ n ∈ M ⊓ Subgroup.normalizer (E : Set G), n * x * n⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx hx1 y hy hy1
  have hEc : Nat.card E = 3 ^ 2 := by rw [hE9]; norm_num
  have hEp : IsPGroup 3 E := IsPGroup.of_card hEc
  obtain ⟨N₁, E₀, d₁, Rbar₁, K₁, -, -, -, hconf⟩ :=
    c.exists_conf_of_good hN2 hNT hNM hEN hEM hEp le_rfl hEel hE9 hEcore
  obtain ⟨g, hg, hgxy⟩ := hconf.esc.exists_mem_normalizer_conj_eq_of_l34
    (isLinThreeFour_of_l34Index hconf.l34 hconf.iso) hconf.le_K hx hx1 hy hy1
  have hNE : Subgroup.normalizer (E : Set G) ≤ M := c.ctx.normRankTwo E hEM hEp
    (le_pRank_of_isElemAbelian Nat.prime_three hEel hEc)
  exact ⟨g, Subgroup.mem_inf.mpr ⟨hNE (Subgroup.mem_inf.mp hg).2, (Subgroup.mem_inf.mp hg).2⟩,
    hgxy⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
