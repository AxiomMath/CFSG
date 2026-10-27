module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA

variable {G : Type} [Group G] [Finite G]

theorem u6_card_center (K : Subgroup G) :
    ∃ k : ℕ, Nat.card (Subgroup.center (PQuot 3 K)) = 3 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.iff_card.mp (I2611.isPGroup_center_pQuot' Nat.prime_three K)

theorem lieIndex_isG2n {S : Type} [Group S] {n : ℕ} (h : catalogIs S (S10.isG2n n)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 ∧ q.exponent = n ∧
      Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | G2 q => exact ⟨q, hv, hi.1, hi.2, ⟨e⟩⟩
    | _ => exact hi.elim

theorem G2_card_ge_three {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid) :
    3 ≤ q.card :=
  (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1

theorem exc_G2_dvd {n c d : ℕ}
    (h : CFSG.Blueprint.Multiplier.exceptionalOrders .G2 0 2 n = (c, d)) :
    c * d ∣ 2 ∧ (n ≠ 2 → c * d = 1) := by
  by_cases hn : n = 2
  · subst hn
    have h2 : (c, d) = (2, 1) := h.symm.trans rfl
    rw [Prod.mk.injEq] at h2
    rw [h2.1, h2.2]
    exact ⟨by norm_num, fun h' => absurd rfl h'⟩
  · have he : CFSG.Blueprint.Multiplier.exceptionalOrders .G2 0 2 n = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    have h1 : (c, d) = (1, 1) := h.symm.trans he
    rw [Prod.mk.injEq] at h1
    rw [h1.1, h1.2]
    exact ⟨by norm_num, fun _ => rfl⟩

theorem card_center_dvd_G2 (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {n : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.G2 q).Valid} (hq2 : q.p = 2) (hqn : q.exponent = n)
    (e : Q ⧸ Subgroup.center Q ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    Nat.card (Subgroup.center Q) ∣ 2 ∧ (n ≠ 2 → Nat.card (Subgroup.center Q) ∣ 1) := by
  have h3 : 3 ≤ 2 ^ n := by
    have := G2_card_ge_three hv
    rwa [TauCeti.PrimePower.card_def, hq2, hqn] at this
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num at h3
    · exact h
  have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .G2 0 2 n :=
    CFSG.Models.lieModel_of_namesTag (t := .G2) (p := 2) (f := n)
      ⟨Nat.prime_two, hn1, rfl, h3⟩ ⟨_, hv⟩ ⟨hq2, hqn⟩ e
  have hg : CFSG.Blueprint.Multiplier.genericOrders .G2 0 2 n = (1, 1) := rfl
  obtain ⟨c, d, hcd⟩ : ∃ c d : ℕ, CFSG.Blueprint.Multiplier.exceptionalOrders .G2 0 2 n = (c, d) :=
    ⟨_, _, rfl⟩
  obtain ⟨hdiv, hone⟩ := exc_G2_dvd hcd
  have hne : 1 * 1 * (c * d) ≠ 0 := by
    rw [one_mul, one_mul]
    intro h0
    rw [h0, zero_dvd_iff] at hdiv
    norm_num at hdiv
  have hd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := c) (d := d) hg hcd hne
  rw [one_mul, one_mul] at hd
  refine ⟨hd.trans hdiv, fun hn2 => ?_⟩
  rw [hone hn2] at hd
  exact hd

theorem center_eq_bot_of_dvd_two {Q : Type} [Group Q] [Finite Q]
    (hZ : IsPGroup 3 (Subgroup.center Q)) (hd : Nat.card (Subgroup.center Q) ∣ 2) :
    Subgroup.center Q = ⊥ := by
  by_contra hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact false_of_pGroup_dvd Nat.prime_three hZ hd (by norm_num)

theorem center_pQuot_eq_bot_G2 (hGA : CFSG.Open.GriessAllModelsStatement) {X L : Subgroup G} {n : ℕ}
    (hL : GLAPComponent 3 X L) (hcat : catalogIs (PSimple 3 L) (S10.isG2n n)) :
    Subgroup.center (PQuot 3 L) = ⊥ := by
  obtain ⟨q, hv, hp, hf, ⟨e⟩⟩ := lieIndex_isG2n hcat
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 L) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  obtain ⟨hd2, -⟩ := card_center_dvd_G2 hGA hQ hp hf e
  exact center_eq_bot_of_dvd_two (I2611.isPGroup_center_pQuot' Nat.prime_three L) hd2

end CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1

end
