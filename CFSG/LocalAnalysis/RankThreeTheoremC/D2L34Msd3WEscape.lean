module

import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycSquare
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Escape9
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section Rank

variable {G : Type} [Group G] [Finite G]

@[expose] def D2NormRankTwo (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ S : Subgroup G, S ≤ M → IsPGroup 3 S → 2 ≤ CFSG.Open.pRank 3 S →
    Subgroup.normalizer (S : Set G) ≤ M

theorem D2L34SideCtx3.normRankTwo {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) : D2NormRankTwo G M :=
  fun _ hSM hSp hS2 =>
    normalizer_le_of_gamma_two h.setting h.sigma h.core (h.fullCore 3 h.sigma P h.core) hSp hSM
      hS2

theorem le_of_pGroup_of_normRankTwo {M : Subgroup G} (hN : D2NormRankTwo G M)
    {X E₀ : Subgroup G} (hE₀ : IsPGroup 3 E₀) (hXE : X ≤ E₀) (hXM : X ≤ M)
    (hX2 : 2 ≤ CFSG.Open.pRank 3 X) : E₀ ≤ M := by
  induction' hd : Nat.card E₀ - Nat.card X using Nat.strong_induction_on with d ih generalizing X
  by_cases hXeq : X = E₀
  · exact hXeq ▸ hXM
  · have hlt : X < E₀ := lt_of_le_of_ne hXE hXeq
    have hgrow : X < E₀ ⊓ Subgroup.normalizer (X : Set G) :=
      pGroup_proper_subgroup_lt_internal_normalizer 3 Nat.prime_three E₀ X hE₀ hlt
    have hXp : IsPGroup 3 X := hE₀.to_le hXE
    have hX'M : E₀ ⊓ Subgroup.normalizer (X : Set G) ≤ M := inf_le_right.trans (hN X hXM hXp hX2)
    have hcard : Nat.card X < Nat.card (E₀ ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) := by
      by_contra hle
      exact hgrow.ne (Subgroup.eq_of_le_of_card_ge hgrow.le (not_lt.mp hle))
    have hcardE : Nat.card (E₀ ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) ≤ Nat.card E₀ :=
      Subgroup.card_le_of_le inf_le_left
    refine ih (Nat.card E₀ - Nat.card (E₀ ⊓ Subgroup.normalizer (X : Set G) : Subgroup G))
      (by omega) inf_le_left hX'M (hX2.trans (pRank_mono 3 Nat.prime_three hgrow.le)) rfl

@[expose] def HasGoodE9 (M X : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ GLBCore 3 1 E ≤ M

theorem HasGoodE9.mono {M X Y : Subgroup G} (h : HasGoodE9 M X) (hXY : X ≤ Y) :
    HasGoodE9 M Y :=
  let ⟨E, hEX, hEel, hE9, hcore⟩ := h
  ⟨E, hEX.trans hXY, hEel, hE9, hcore⟩

omit [Finite G] in
theorem mem_map_conj_iff (A : Subgroup G) (y w : G) :
    w ∈ A.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * w * y ∈ A := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem glbCore_one_map_conj_le {A M : Subgroup G} {y : G} (hy : y ∈ M)
    (h : GLBCore 3 1 A ≤ M) : GLBCore 3 1 (A.map (MulAut.conj y).toMonoidHom) ≤ M := by
  refine (fullCore_le_iff 3 1 _ M).mpr fun Q hQA hrank => ?_
  set Q' : Subgroup G := Q.map (MulAut.conj y⁻¹).toMonoidHom with hQ'
  have key : ∀ w : G, w ∈ Q' ↔ y * w * y⁻¹ ∈ Q := by
    intro w
    rw [hQ', mem_map_conj_iff, inv_inv]
  have hQ'A : Q' ≤ A := by
    intro w hw
    have h1 := hQA ((key w).mp hw)
    rw [mem_map_conj_iff] at h1
    have e : y⁻¹ * (y * w * y⁻¹) * y = w := by group
    rwa [e] at h1
  have hQ'rank : 1 ≤ CFSG.Open.pRank 3 Q' := by
    rw [hQ', CFSG.RankThreeCoreUniqueness.Helpers.pRank_map_automorphism 3 Nat.prime_three.one_lt]
    exact hrank
  have hN := (fullCore_le_iff 3 1 A M).mp h Q' hQ'A hQ'rank
  intro g hg
  have hgm : y⁻¹ * g * y ∈ Subgroup.normalizer (Q' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [key, key]
    have := (Subgroup.mem_normalizer_iff.mp hg) (y * z * y⁻¹)
    have e : y * (y⁻¹ * g * y * z * (y⁻¹ * g * y)⁻¹) * y⁻¹ = g * (y * z * y⁻¹) * g⁻¹ := by group
    rw [e]
    exact this
  have hM := hN hgm
  have : g = y * (y⁻¹ * g * y) * y⁻¹ := by group
  rw [this]
  exact M.mul_mem (M.mul_mem hy hM) (M.inv_mem hy)

end Rank

section Conf

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

omit [D2Amb3 G] in
theorem D2L34BetaConf3.core_one_le_of_le_sup (hc : D2L34BetaConf3 d P M A H R Rbar K)
    {E : Subgroup G} (hE : E ≤ A ⊔ GLBPrimeCore 3 H) (hEp : IsPGroup 3 E)
    (hE9 : Nat.card E = 3 ^ 2) : GLBCore 3 1 E ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := GLBPrimeCore 3 H with hW
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAM : A ≤ M := hc.esc.A_le.trans hc.esc.le_M
  have hWM : W ≤ M := hc.esc.primeCore_le
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := hAH.trans (le_normalizer_glbPrimeCore 3 H)
  have hSM : A ⊔ W ≤ M := sup_le hAM hWM
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 2) hc.esc.card_A
  have hWcop : Nat.Coprime 3 (Nat.card W) := glbPrimeCore_coprime 3 H
  have hW3 : ¬ 3 ∣ Nat.card W := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hWcop
  have hAWbot : A ⊓ W = ⊥ := (Subgroup.disjoint_of_coprime_natCard
    (by rw [hc.esc.card_A]; exact Nat.Coprime.pow_left 2 hWcop)).eq_bot
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hAW
  rw [sup_comm, inf_comm, hAWbot, Subgroup.card_bot, mul_one, hc.esc.card_A] at hcard
  have hAidx : ¬ 3 ∣ (A.subgroupOf (A ⊔ W)).index := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf (A ⊔ W))
    have h2 : Nat.card (A.subgroupOf (A ⊔ W)) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [h2, hc.esc.card_A, hcard] at h1
    have h3 : (A.subgroupOf (A ⊔ W)).index = Nat.card W := by
      rw [mul_comm (Nat.card W)] at h1
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3 ^ 2) h1
    rw [h3]
    exact hW3
  obtain ⟨g, hgS, hgE⟩ := exists_conj_map_le_of_isPGroup (le_sup_left : A ≤ A ⊔ W) hAp hAidx hE
    hEp
  have hEA : E.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hgE (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9, hc.esc.card_A])
  have hE' : E = A.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hEA, Subgroup.map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  rw [hE']
  exact glbCore_one_map_conj_le (M.inv_mem (hSM hgS)) hc.esc.core_A

theorem D2L34BetaConf3.exists_escape_of_good (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hR9 : Nat.card R = 9) (hN : D2NormRankTwo G M) {N : Subgroup G} (hN2 : IsTwoLocal N)
    (hNM : ¬ N ≤ M) {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M) (hX : IsPGroup 3 X)
    (hXc : ¬ IsCyclic X) (hgood : HasGoodE9 M X) :
    ∃ N₁ E₀ : Subgroup G, N ≤ N₁ ∧ X ≤ E₀ ∧ D2Escape 3 P M E₀ N₁ E₀ ∧
      D2EscapeMax 3 P M E₀ ∧ Nat.card E₀ = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E', hE'X, hE'el, hE'c9, hE'core⟩ := hgood
  have hE'c : Nat.card E' = 3 ^ 2 := by rw [hE'c9]; norm_num
  obtain ⟨N₁, hNN₁, hN₁⟩ := exists_maximal_twoLocal hN2
  have hN₁M : ¬ N₁ ≤ M := fun h => hNM (hNN₁.trans h)
  have hXN₁ : X ≤ N₁ := hXN.trans hNN₁
  have hXp : IsPGroup 3 (X.subgroupOf N₁) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXN₁).symm
  obtain ⟨T, hXT⟩ := hXp.exists_le_sylow
  set E₀ : Subgroup G := (T : Subgroup N₁).map N₁.subtype with hE₀
  have hXE₀ : X ≤ E₀ := fun x hx => ⟨⟨x, hXN₁ hx⟩, hXT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hE₀p : IsPGroup 3 E₀ := T.isPGroup'.map N₁.subtype
  have hX2 : 2 ≤ CFSG.Open.pRank 3 X :=
    two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hX hXc
  have hE₀M : E₀ ≤ M := le_of_pGroup_of_normRankTwo hN hE₀p hXE₀ hXM hX2
  have hE₀N₁ : E₀ ≤ N₁ := Subgroup.map_subtype_le _
  have hE'E₀ : E' ≤ E₀ := hE'X.trans hXE₀
  have hrank₀ : Open.pRank 3 (N₁ ⊓ M) ≤ 2 := by
    by_contra hlt
    exact hN₁M (D2Amb3.d1 (G := G) P M hc.esc.maxTwoLocal_M
      ((weakCore_le_fullCore 3 (P : Subgroup G)).trans hc.esc.core_le) N₁ hN₁.1 (by omega))
  have hE'rank : 2 ≤ Open.pRank 3 E' := le_pRank_of_isElemAbelian Nat.prime_three hE'el hE'c
  have hesc' : D2Escape 3 P M E' N₁ E₀ :=
    { prime := Nat.prime_three
      ne_two := by norm_num
      sylow_le := hc.esc.sylow_le
      core_le := hc.esc.core_le
      maxTwoLocal_M := hc.esc.maxTwoLocal_M
      maxTwoLocal_H := hN₁
      elem := hE'el
      card_A := hE'c
      core_A := hE'core
      A_le := hE'E₀
      le_H := hE₀N₁
      le_M := hE₀M
      isSylow := ⟨T, rfl⟩
      pRank_eq := le_antisymm
        ((pRank_mono 3 Nat.prime_three (le_inf hE₀N₁ hE₀M)).trans hrank₀)
        (hE'rank.trans (pRank_mono 3 Nat.prime_three hE'E₀))
      not_le := hN₁M }
  have hE₀9 : Nat.card E₀ = 9 := by
    refine le_antisymm (hR9 ▸ hc.max E' N₁ E₀ hesc') ?_
    have := Subgroup.card_le_of_le hE'E₀
    rw [hE'c] at this
    omega
  have hE'eq : E' = E₀ := Subgroup.eq_of_le_of_card_ge hE'E₀ (by rw [hE₀9, hE'c]; norm_num)
  have hmax₀ : D2EscapeMax 3 P M E₀ := fun A' H' R' h' =>
    (hc.max A' H' R' h').trans (by rw [hR9, hE₀9])
  refine ⟨N₁, E₀, hNN₁, hXE₀, ?_, hmax₀, hE₀9⟩
  rw [← hE'eq] at hesc' ⊢
  exact hesc'

theorem D2L34BetaConf3.card_le_nine_of_good (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hR9 : Nat.card R = 9) (hN : D2NormRankTwo G M) {N : Subgroup G} (hN2 : IsTwoLocal N)
    (hNM : ¬ N ≤ M) {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M) (hX : IsPGroup 3 X)
    (hXc : ¬ IsCyclic X) (hgood : HasGoodE9 M X) : Nat.card X ≤ 9 := by
  obtain ⟨N₁, E₀, -, hXE₀, -, -, hE₀9⟩ :=
    D2L34BetaConf3.exists_escape_of_good hc hR9 hN hN2 hNM hXN hXM hX hXc hgood
  exact hE₀9 ▸ Subgroup.card_le_of_le hXE₀

theorem D2L34BetaConf3.exists_conj_eq_of_good (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hR9 : Nat.card R = 9) (hN : D2NormRankTwo G M) (hOnly : D2OnlyL34At P M) {N : Subgroup G}
    (hN2 : IsTwoLocal N) (hNM : ¬ N ≤ M) {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M)
    (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X) (hgood : HasGoodE9 M X) :
    IsElemAbelian 3 X ∧ Nat.card X = 9 ∧ ∀ x ∈ X, x ≠ 1 → ∀ y ∈ X, y ≠ 1 →
      ∃ n ∈ M ⊓ Subgroup.normalizer (X : Set G), n * x * n⁻¹ = y :=
  exists_conj_eq_of_escape hOnly hX hXc
    (D2L34BetaConf3.exists_escape_of_good hc hR9 hN hN2 hNM hXN hXM hX hXc hgood)
    fun _ hn => hN X hXM hX (two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hX hXc) hn

end Conf

end CFSG.LocalAnalysis.RankThreeTheoremC
