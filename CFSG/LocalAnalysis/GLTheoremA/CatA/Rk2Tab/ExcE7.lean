module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.SeitzGeneration
open CFSG.StandardType.PRankBounds
open CFSG.RankThree.PartOne.KE CFSG.LieType.Chevalley

private lemma countP_map_prod_true (l : List ℕ) (m : ℕ) :
    (l.map (fun d => (d, true))).countP
      (fun f => if f.2 then decide (m ∣ f.1) else decide (m ∣ 2 * f.1 ∧ ¬ m ∣ f.1)) =
    l.countP (fun d => decide (m ∣ d)) := by
  rw [List.countP_map]
  exact List.countP_congr fun d _ => by simp

theorem rk2Mult_E7_eq_degCount (l n m : ℕ) :
    rk2Mult ⟨.E7, l, n⟩ m = degCount Tag.E7 m := by
  simp only [rk2Mult, rk2Cnt, degCount, degreesW, degreesE]
  rw [← List.countP_eq_length_filter]
  rw [show ([(2, true), (6, true), (8, true), (10, true), (12, true), (14, true), (18, true)] :
      List (ℕ × Bool)) =
      ([2, 6, 8, 10, 12, 14, 18] : List ℕ).map (fun d => (d, true)) from rfl]
  exact countP_map_prod_true _ m

theorem rk2Mult_eq_degCount_E7 {lab : GLALabel} (htag : lab.tag = .E7) (m : ℕ) :
    rk2Mult lab m = degCount Tag.E7 m := by
  obtain ⟨t, l, n⟩ := lab
  simp only at htag
  rw [htag]
  exact rk2Mult_E7_eq_degCount l n m

section Carrier


theorem pRank_adjointGroup_E7_le_seven_of_dvd_sub_one
    (F : Type) [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 F)) ≤ 7 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hV : Nat.card (CFSG.StandardType.TableBExc.torusPow Tag.E7 F p) = p ^ Tag.E7.rank :=
    CFSG.StandardType.TableBExc.card_torusPow_E7 hp hpq
  have hT : CFSG.StandardType.GGExcToralRankInput Tag.E7 F p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact CFSG.StandardType.ggE7ThreeToralRankInput_holds (K := F) hpq
    · exact CFSG.StandardType.ggExcToralRankInput_E7_of_ne_three hp hp2 hp3 hpq
  refine CFSG.SectionRank.pRank_le hp.one_lt (H := ⊤) ?_
  intro E _ hE
  have h := hT.card_le (τ := Tag.E7) (K := F) hV hE
  have hrank : Tag.E7.rank = 7 := by decide
  rwa [hrank] at h

theorem pRank_adjointGroup_E7_le_seven_of_dvd_add_one
    (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hFcard : Nat.card F = 2 ^ n)
    (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 F)) ≤ 7 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  let F' := GaloisField 2 (2 * n)
  haveI : Field F' := inferInstance
  haveI : Finite F' := inferInstance
  haveI : Fintype F' := Fintype.ofFinite F'
  have hF'pow : Nat.card F' = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
  have hF'card : Nat.card F' = (2 ^ n) ^ 2 := by
    rw [hF'pow, ← pow_mul]
    ring_nf
  have hF'rew : Nat.card F' = (Nat.card F) ^ 2 := by
    rw [hF'card, ← hFcard]
  haveI : CharP F' 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega : 1 ≤ 2 * n) hF'pow
  obtain ⟨φ⟩ := CFSG.HardMathSupport.Lang.AnisoE6.nonempty_ringHom_of_card_sq
    (ℓ := 2) (f := n) hFcard hF'card
  have hq1 : ((Nat.card F : ℕ) : ZMod p) = -1 := by
    have h0 : (((Nat.card F + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hpq' : p ∣ Nat.card F' - 1 := by
    have hsq : ((Nat.card F' : ℕ) : ZMod p) = 1 := by
      rw [hF'rew, Nat.cast_pow, hq1]
      ring
    rw [← ZMod.natCast_eq_zero_iff (Nat.card F' - 1) p, Nat.cast_sub Nat.card_pos,
      hsq, Nat.cast_one, sub_self]
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 F)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 F')) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt _
      (CFSG.StandardType.TableBExcTwo.adjointMap_injective (τ := Tag.E7) φ)
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 F')) ≤ 7 :=
    pRank_adjointGroup_E7_le_seven_of_dvd_sub_one F' hp hp2 hpq'
  exact h1.trans h2

private lemma degCount_E7_pos_values {e : ℕ} (he0 : e ≠ 0) (h : 0 < degCount Tag.E7 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨
      e = 10 ∨ e = 12 ∨ e = 14 ∨ e = 18 := by
  have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
  have h2 : e ≤ 30 := le_thirty_of_degCount_pos (Or.inr (Or.inr (Or.inl rfl))) h
  interval_cases e <;> simp_all [degCount, degreesW, degreesE]

private theorem pRank_adjointGroup_E7_le_degCount (F : Type) [Field F] [Finite F] (n : ℕ)
    (hFcard : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = e) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 F)) ≤ degCount Tag.E7 e := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn hFcard
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hFcard]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hq0 : ((Nat.card F : ℕ) : ZMod p) ≠ 0 := fun hz =>
    hpF ((ZMod.natCast_eq_zero_iff _ _).1 hz)
  have hdvd : orderOf ((Nat.card F : ℕ) : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one hq0
  have he0 : e ≠ 0 := he ▸ (Nat.pos_of_dvd_of_pos hdvd (by have := hp.two_le; omega)).ne'
  by_cases h0 : degCount Tag.E7 e = 0
  · have hp3 : 3 < p := by
      by_contra hle
      have hp2le : 2 ≤ p := hp.two_le
      have hple : p ≤ 3 := by omega
      interval_cases p
      · exact hp2 rfl
      · exfalso
        have hq03 : ((Nat.card F : ℕ) : ZMod 3) ≠ 0 := fun hz =>
          hpF ((ZMod.natCast_eq_zero_iff _ _).1 hz)
        have hdvd3 : e ∣ 3 - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq03
        have he12 : e = 1 ∨ e = 2 := by
          have := Nat.le_of_dvd (by norm_num) hdvd3
          omega
        rcases he12 with h1 | h2
        · rw [h1] at h0; exact absurd h0 (by decide)
        · rw [h2] at h0; exact absurd h0 (by decide)
    rw [h0]
    refine CFSG.SectionRank.pRank_le hp.one_lt ?_
    intro E _ hE
    rw [elemAbelian_card_eq_one_of_degCount_zero (Or.inr (Or.inl rfl)) F hp hp3 hpF he h0 hE]
    simp
  · have hpos : 0 < degCount Tag.E7 e := Nat.pos_of_ne_zero h0
    rcases degCount_E7_pos_values he0 hpos with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · have hpq : p ∣ Nat.card F - 1 := by
        have hq1 : ((Nat.card F : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.mp he
        rw [← ZMod.natCast_eq_zero_iff (Nat.card F - 1) p, Nat.cast_sub Nat.card_pos, hq1,
          Nat.cast_one, sub_self]
      have := pRank_adjointGroup_E7_le_seven_of_dvd_sub_one F hp hp2 hpq
      simpa [degCount, degreesW, degreesE] using this
    · have hpq : p ∣ Nat.card F + 1 := by
        have hcast : ((2 : ZMod p) ^ n) = ((Nat.card F : ℕ) : ZMod p) := by
          rw [hFcard]
          exact (Nat.cast_pow (α := ZMod p) 2 n).symm
        have hrn : rk2Ord p n = 2 := by
          rw [rk2Ord, hcast, he]
        simpa [hFcard] using (rk2Ord_eq_two_iff hp hp2).1 hrn
      have := pRank_adjointGroup_E7_le_seven_of_dvd_add_one F n hFcard hn hp hp2 hpq
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 3 := sylowTorus_E7_three' F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 2 := sylowTorus_E7_four F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 1 := sylowTorus_E7_five F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 3 := sylowTorus_E7_six' F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 1 := sylowTorus_E7_seven F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 1 := sylowTorus_E7_eight F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 1 := sylowTorus_E7_nine F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 1 := sylowTorus_E7_ten F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 1 := sylowTorus_E7_twelve F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 1 := sylowTorus_E7_fourteen F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this
    · have hS : SylowTorus (adjointGroup Tag.E7 F) p 1 := sylowTorus_E7_eighteen F hp he
      have := pRank_le_of_sylowTorusDatum hS hp
      simpa [degCount, degreesW, degreesE] using this

end Carrier

section Main


theorem rk2_pRank_le_E7 {K : Type} [Group K] [Finite K] (lab : GLALabel) (p : ℕ)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E7) (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 lab.n :=
    lieModel_of_markedModel_E7 htag hM
  obtain ⟨-, F, hF, hFin, hFcard, ⟨φ⟩⟩ := hM'.chevalleyExceptionalModel
    (by decide : StatedLieTag.E7 ∈ chevalleyExceptionalTags)
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7 hQ' hl.1 hFcard φ
  let χ : AdjointQuotient .E7 F ≃* adjointGroup Tag.E7 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := Tag.E7) (K := F))).trans
      QuotientGroup.quotientBot
  haveI : Fact p.Prime := ⟨hp⟩
  have he : orderOf ((Nat.card F : ℕ) : ZMod p) = rk2Ord p lab.n := by
    rw [hFcard, rk2Ord, Nat.cast_pow]
    norm_num
  have hbound : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 F)) ≤
      rk2Mult lab (rk2Ord p lab.n) := by
    rw [rk2Mult_eq_degCount_E7 htag]
    exact pRank_adjointGroup_E7_le_degCount F lab.n hFcard hl.1 hp hp2 he
  have hZcop : ¬ p ∣ Nat.card (Subgroup.center K) := by
    rw [hZ, Subgroup.card_bot, Nat.dvd_one]
    exact hp.ne_one
  calc CFSG.Open.pRank p (⊤ : Subgroup K)
      = CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) :=
        (CFSG.SectionRank.pRank_quotient_eq (p := p) (G := K) (Subgroup.center K) hZcop).symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 F)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (φ.trans χ)
    _ ≤ rk2Mult lab (rk2Ord p lab.n) := hbound

end Main

end CFSG.LocalAnalysis.GLTheoremA
