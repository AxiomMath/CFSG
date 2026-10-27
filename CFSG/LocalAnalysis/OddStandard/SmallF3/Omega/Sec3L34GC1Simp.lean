module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GFacts
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Transport
import CFSG.GH74.Orders.LieType
import CFSG.LieType.Simplicity.Classical
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.Open (StatedLieTag ordA ordTwistedA ordBC ordD ordTwistedD)

private theorem exists_noncomm_of_simple_of_four_dvd {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (h : 2 ^ 2 ∣ Nat.card G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative G := ⟨⟨fun a b => hcon a b⟩⟩
  have hprime : (Nat.card G).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  have hpd : 2 ∣ Nat.card G := (dvd_pow_self 2 (by norm_num)).trans h
  rcases (Nat.dvd_prime hprime).1 hpd with h1 | h1
  · exact one_lt_two.ne' h1
  · rw [← h1] at h
    have h2 := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega

private theorem center_eq_bot_of_simple' {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (mem_center_iff.mp (h ▸ mem_top b) a)

private theorem simple_centerless_of_lieModel {Y : Type} [Group Y] {t : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (h : LieModel Y t n p f) (h4 : 4 ∣ Nat.card Y) :
    IsSimpleGroup Y ∧ center Y = ⊥ := by
  obtain ⟨hfin, -, hsimp⟩ :=
    CFSG.LieType.Simplicity.fam_classical_converse Y
      ⟨t, n, p, f, GH74.statedClassicalModel_of_lieModel hn h⟩
  haveI : Finite Y := hfin
  haveI : IsSimpleGroup Y := hsimp
  refine ⟨hsimp, ?_⟩
  exact center_eq_bot_of_simple'
    (exists_noncomm_of_simple_of_four_dvd (by simpa using h4))

theorem l34g_simpleFStar_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : SimpleFStarQuotient Y) : SimpleFStarQuotient Z := by
  unfold SimpleFStarQuotient at h ⊢
  rcases h with h | h
  · exact Or.inl (smallF3OmegaQuotient_of_mulEquiv e h)
  · unfold SmallF3StarQuotient at h ⊢
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h))
    · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (LieModel.of_mulEquiv e h))))

theorem l34g_simple_of_simpleFStar {Y : Type} [Group Y] [Finite Y] (h : SimpleFStarQuotient Y) :
    IsSimpleGroup Y ∧ center Y = ⊥ := by
  unfold SimpleFStarQuotient at h
  rcases h with h | h
  · unfold SmallF3OmegaQuotient at h
    rcases h with h | h | h | h | h | h
    · have h4 : 4 ∣ Nat.card Y := by
        rw [GH74.card_of_lieModel_PSp (G := Y) (n := 2) (p := 3) (f := 1) (by norm_num)
          (by norm_num) h]
        decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4
    · have h4 : 4 ∣ Nat.card Y := by
        rw [GH74.card_of_lieModel_PSL (G := Y) (n := 4) (p := 3) (f := 1) (by norm_num) h]
        decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4
    · have h4 : 4 ∣ Nat.card Y := by
        rw [GH74.card_of_lieModel_PSU (G := Y) (n := 4) (p := 3) (f := 1) (by norm_num)
          (by norm_num) h]
        decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4
    · have hcard : Nat.card Y = ordBC 3 (3 ^ 1) :=
        (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y) (t := .POmegaOdd)
          (n := 3) (p := 3) (f := 1) (by norm_num)
          (GH74.statedClassicalModel_of_lieModel (G := Y) (t := .POmegaOdd) (n := 3) (p := 3)
            (f := 1) (by norm_num) h)).2.2.2.1 rfl
      have h4 : 4 ∣ Nat.card Y := by rw [hcard]; decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4
    · have hcard : Nat.card Y = ordD 4 (3 ^ 1) :=
        (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y) (t := .POmegaPlus)
          (n := 4) (p := 3) (f := 1) (by norm_num)
          (GH74.statedClassicalModel_of_lieModel (G := Y) (t := .POmegaPlus) (n := 4) (p := 3)
            (f := 1) (by norm_num) h)).2.2.2.2.1 rfl
      have h4 : 4 ∣ Nat.card Y := by rw [hcard]; decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4
    · have hcard : Nat.card Y = ordTwistedD 4 (3 ^ 1) :=
        (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y) (t := .POmegaMinus)
          (n := 4) (p := 3) (f := 1) (by norm_num)
          (GH74.statedClassicalModel_of_lieModel (G := Y) (t := .POmegaMinus) (n := 4) (p := 3)
            (f := 1) (by norm_num) h)).2.2.2.2.2 rfl
      have h4 : 4 ∣ Nat.card Y := by rw [hcard]; decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4
  · unfold SmallF3StarQuotient at h
    rcases h with h | h | h | h
    · have h4 : 4 ∣ Nat.card Y := by
        rw [GH74.card_of_lieModel_PSL (G := Y) (n := 2) (p := 3) (f := 2) (by norm_num) h]
        decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4
    · have h4 : 4 ∣ Nat.card Y := by
        rw [GH74.card_of_lieModel_PSL (G := Y) (n := 2) (p := 3) (f := 4) (by norm_num) h]
        decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4
    · have h4 : 4 ∣ Nat.card Y := by
        rw [GH74.card_of_lieModel_PSL (G := Y) (n := 3) (p := 3) (f := 1) (by norm_num) h]
        decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4
    · have h4 : 4 ∣ Nat.card Y := by
        rw [GH74.card_of_lieModel_PSU (G := Y) (n := 3) (p := 3) (f := 1) (by norm_num)
          (by norm_num) h]
        decide
      exact simple_centerless_of_lieModel (hn := by norm_num) h h4

theorem l34g_pGroup_normal_bot {Y : Type} [Group Y] [Finite Y] (h : SimpleFStarQuotient Y)
    {p : ℕ} [Fact p.Prime] {N : Subgroup Y} [N.Normal] (hN : IsPGroup p ↥N) : N = ⊥ := by
  obtain ⟨hsimp, hcent⟩ := l34g_simple_of_simpleFStar h
  haveI : IsSimpleGroup Y := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exact hbot
  · exfalso
    have hNtop : IsPGroup p (⊤ : Subgroup Y) := htop ▸ hN
    have hYp : IsPGroup p Y := hNtop.of_equiv Subgroup.topEquiv
    haveI : Nontrivial Y := hsimp.toNontrivial
    have hlt : (⊥ : Subgroup Y) < center Y := hYp.bot_lt_center
    rw [hcent] at hlt
    exact (lt_irrefl (⊥ : Subgroup Y)) hlt

theorem l34g_closure_odd_eq_top {Y : Type} [Group Y] [Finite Y] (h : SimpleFStarQuotient Y) :
    Subgroup.closure {y : Y | Odd (orderOf y)} = ⊤ := by
  obtain ⟨hsimp, hcent⟩ := l34g_simple_of_simpleFStar h
  haveI : IsSimpleGroup Y := hsimp
  haveI : Nontrivial Y := hsimp.toNontrivial
  have hMnorm : (Subgroup.closure {y : Y | Odd (orderOf y)}).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show Odd (orderOf ((MulAut.conj g) x))
      rw [MulEquiv.orderOf_eq]
      exact hx
    · intro hy
      refine ⟨(MulAut.conj g).symm y, ?_, ?_⟩
      · show Odd (orderOf ((MulAut.conj g).symm y))
        rw [MulEquiv.orderOf_eq]
        exact hy
      · exact MulEquiv.apply_symm_apply (MulAut.conj g) y
  haveI : (Subgroup.closure {y : Y | Odd (orderOf y)}).Normal := hMnorm
  have hMne : Subgroup.closure {y : Y | Odd (orderOf y)} ≠ ⊥ := by
    have hnot2 : ¬ IsPGroup 2 Y := by
      intro h2
      have hlt : (⊥ : Subgroup Y) < center Y := h2.bot_lt_center
      rw [hcent] at hlt
      exact (lt_irrefl (⊥ : Subgroup Y)) hlt
    have hcard_ne0 : Nat.card Y ≠ 0 := (Nat.card_pos (α := Y)).ne'
    have hoddprime : ∃ q, q.Prime ∧ q ∣ Nat.card Y ∧ q ≠ 2 := by
      by_contra hcon
      push Not at hcon
      have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hcard_ne0
        (fun {d} hd hdvd => hcon d hd hdvd)
      exact hnot2 (IsPGroup.of_card hpow)
    obtain ⟨q, hqprime, hqdvd, hqne2⟩ := hoddprime
    haveI : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hqdvd
    have hyodd : Odd (orderOf y) := by
      rw [hy]
      exact hqprime.odd_of_ne_two hqne2
    have hyM : y ∈ Subgroup.closure {y : Y | Odd (orderOf y)} := Subgroup.subset_closure hyodd
    intro hbot
    have hy1 : y = 1 := by
      have : y ∈ (⊥ : Subgroup Y) := hbot ▸ hyM
      simpa using this
    have hq1 : q = 1 := by
      rw [hy1, orderOf_one] at hy
      exact hy.symm
    exact hqprime.ne_one hq1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.closure {y : Y | Odd (orderOf y)}) with hbot | htop
  · exact absurd hbot hMne
  · exact htop

end CFSG.OddStandard.SmallF3.Omega
