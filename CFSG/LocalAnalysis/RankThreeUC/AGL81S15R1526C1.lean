module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair

section SevenElementAux

variable {X : Type} [Group X]

theorem exists_sevenElement_centralizing_aux_conj_mul (g h : X) (H : Subgroup X) :
    conjSub g (conjSub h H) = conjSub (g * h) H := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [mul_assoc]

theorem exists_sevenElement_centralizing_aux_mem {N : Subgroup X} {e : X} (he : orderOf e = 7)
    {d : ℕ} (hd : ¬ 7 ∣ d) (hN : e ^ d ∈ N) : e ∈ N := by
  have hcop : Nat.Coprime d (orderOf e) := by
    rw [he]
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hd).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact N.pow_mem hN m

theorem exists_sevenElement_centralizing_aux_inj {I : Subgroup X} {e : X} (he : orderOf e = 7)
    (hne : e ∉ Subgroup.normalizer (I : Set X)) :
    Function.Injective (fun i : Fin 7 => conjSub (e ^ (i : ℕ)) I) := by
  have key : ∀ i j : Fin 7, i < j →
      conjSub (e ^ (i : ℕ)) I = conjSub (e ^ (j : ℕ)) I → False := by
    intro i j hij hEq
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have hj7 : (j : ℕ) < 7 := j.isLt
    have hd : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) := by omega
    have h1 : conjSub (e ^ (j : ℕ)) I =
        conjSub (e ^ (i : ℕ)) (conjSub (e ^ ((j : ℕ) - (i : ℕ))) I) := by
      rw [exists_sevenElement_centralizing_aux_conj_mul, ← pow_add, ← hd]
    have h3 : conjSub (e ^ (i : ℕ)) (conjSub (e ^ ((j : ℕ) - (i : ℕ))) I) =
        conjSub (e ^ (i : ℕ)) I := by
      rw [← h1, hEq]
    have h2 : conjSub (e ^ ((j : ℕ) - (i : ℕ))) I = I :=
      Subgroup.map_injective (MulAut.conj (e ^ (i : ℕ))).injective h3
    have h4 : e ^ ((j : ℕ) - (i : ℕ)) ∈ Subgroup.normalizer (I : Set X) := by
      rw [mem_normalizer_iff_map_conj_eq]
      exact h2
    exact hne (exists_sevenElement_centralizing_aux_mem he (d := (j : ℕ) - (i : ℕ))
      (by omega) h4)
  intro i j hij
  have hij' : conjSub (e ^ (i : ℕ)) I = conjSub (e ^ (j : ℕ)) I := hij
  rcases lt_trichotomy i j with h | h | h
  · exact (key i j h hij').elim
  · exact h
  · exact (key j i h hij'.symm).elim

theorem exists_sevenElement_centralizing_aux_outList {S : Type} [Group S]
    (h : IsLThreeOfExp 1 S) : IsOutTwoGroupList S := by
  rcases h with ⟨-, d, q, hq, hd, he⟩ | ⟨h, -⟩
  · exact Or.inr (Or.inr ⟨d, Or.inr (Or.inr ⟨q, hq, hd⟩), he⟩)
  · omega

theorem exists_sevenElement_centralizing_aux_kernel (hKOut : KOut) {Y : Type} [Group Y]
    [Finite Y] (f : X →* Y) {Is : Subgroup Y} (h3 : IsLThreeOfExp 1 ↥Is) {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian 7 E) (hEcard : Nat.card ↥E = 7 ^ 2)
    (hEN : ∀ e ∈ E, f e ∈ Subgroup.normalizer (Is : Set Y)) :
    ∃ x ∈ E, x ≠ 1 ∧ f x ∈ Subgroup.centralizer (Is : Set Y) := by
  classical
  by_contra hcon
  push Not at hcon
  let ρ0 : ↥E →* ↥(Subgroup.normalizer (Is : Set Y)) :=
    (f.comp E.subtype).codRestrict (Subgroup.normalizer (Is : Set Y)) (fun e => hEN e e.2)
  let ρ : ↥E →* MulAut ↥Is := Is.normalizerMonoidHom.comp ρ0
  have hρ : ∀ (e : ↥E) (s : ↥Is), ((ρ e) s : Y) = f e * s * (f e)⁻¹ := fun e s =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Is (ρ0 e) s
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    have hne' : (e : X) ≠ 1 := fun h => hne (Subtype.ext h)
    refine hcon e e.2 hne' ?_
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := hρ e ⟨s, hs⟩
    rw [he] at h1
    have h2 : s = f e * s * (f e)⁻¹ := h1
    calc s * f e = (f e * s * (f e)⁻¹) * f e := by rw [← h2]
      _ = f e * s := by group
  have hrange : ∀ e : ↥E, ρ e ∈ (MulAut.conj : ↥Is →* MulAut ↥Is).range := by
    intro e
    have h7 : (ρ e) ^ 7 = 1 := by
      rw [← map_pow]
      have h8 : e ^ 7 = 1 := Subtype.ext (by simpa using hE.2 e e.2)
      rw [h8, map_one]
    obtain ⟨k, hk⟩ := hKOut ↥Is (exists_sevenElement_centralizing_aux_outList h3) (ρ e)
    have hcop : Nat.Coprime (2 ^ k) (orderOf (ρ e)) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h7)
        (Nat.Coprime.pow_left k (by norm_num))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ hk m
  let ρ' : ↥E →* ↥(MulAut.conj : ↥Is →* MulAut ↥Is).range := ρ.codRestrict _ hrange
  have hinj' : Function.Injective ρ' := fun a b h => hinj (congrArg Subtype.val h)
  have d1 : Nat.card ↥E ∣ Nat.card ↥(MulAut.conj : ↥Is →* MulAut ↥Is).range :=
    Subgroup.card_dvd_of_injective ρ' hinj'
  have d2 : Nat.card ↥(MulAut.conj : ↥Is →* MulAut ↥Is).range ∣ Nat.card ↥Is :=
    Subgroup.card_dvd_of_surjective
      (f := (MulAut.conj : ↥Is →* MulAut ↥Is).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  rw [hEcard] at d1
  rw [card_eq_of_isLThreeOfExp_one h3] at d2
  have h49 := d1.trans d2
  norm_num at h49

variable [Finite X]

theorem exists_sevenElement_centralizing_aux_normalizes_gen {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h6 : CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 6) {I : Subgroup X} (hI : IsC2 I)
    (hrk : CFSG.Open.pRank q I = 1) (hZ : Nat.card (Subgroup.center ↥(barO2 I)) = 1) {e : X}
    (he : orderOf e = 7) : e ∈ Subgroup.normalizer (I : Set X) := by
  classical
  by_contra hne
  set S : Finset (Subgroup X) :=
    Finset.univ.image (fun i : Fin 7 => conjSub (e ^ (i : ℕ)) I) with hS
  have hcard : S.card = 7 := by
    rw [hS, Finset.card_image_of_injective _
      (exists_sevenElement_centralizing_aux_inj he hne)]
    simp
  have hbot : KFactsPair.centerIn (barO2 I) = ⊥ := by
    unfold KFactsPair.centerIn
    rw [Subgroup.eq_bot_of_card_eq _ hZ, Subgroup.map_bot]
  have hC2 : ∀ L ∈ S, IsC2 L := by
    intro L hL
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hL
    exact liftOf_conj_aux4 hI _
  have hs : ∀ L ∈ S, CFSG.Open.pRank q (KFactsPair.centerIn (barO2 L)) ≤ 0 := by
    intro L hL
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hL
    have h0 : KFactsPair.centerIn (barO2 (conjSub (e ^ (i : ℕ)) I)) = ⊥ := by
      unfold conjSub
      rw [barO2_map_conj, centerIn_map_conj, hbot, Subgroup.map_bot]
    rw [h0]
    exact (pRank_eq_zero_of_not_dvd_s15 hq
      (by rw [Subgroup.card_bot]; exact fun h => hq.ne_one (Nat.dvd_one.1 h))).le
  have key := pRank_sum_le_pRank_sup S hC2 (q := q) hq hq2 hs
  have hsum : ∑ L ∈ S, CFSG.Open.pRank q L = 7 := by
    have h1 : ∀ L ∈ S, CFSG.Open.pRank q L = 1 := by
      intro L hL
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hL
      unfold conjSub
      rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective q
        (f := (MulAut.conj (e ^ (i : ℕ))).toMonoidHom) (MulAut.conj _).injective I]
      exact hrk
    rw [Finset.sum_congr rfl h1]
    simp [hcard]
  have hsup : CFSG.Open.pRank q (S.sup id) ≤ 6 :=
    (CFSG.SectionRank.pRank_mono hq.one_lt le_top).trans h6
  omega

end SevenElementAux

theorem exists_sevenElement_centralizing_gen {X : Type} [Group X] [Finite X]
    (hKOut : KOut) (hKSML3 : KSML3)
    {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (h6 : CFSG.Open.pRank 7 (⊤ : Subgroup X) ≤ 6 ∨
      CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 6)
    (hL3 : ∀ (Ls : Subgroup (X ⧸ gnC T)) (L : Subgroup X), GNYComponent T T₁ T₂ Ls →
      LiftOf T L Ls → IsLThreeOfExp 1 ↥Ls)
    {Is Is' : Subgroup (X ⧸ gnC T)} {I I' : Subgroup X} (hIs : GNYComponent T T₁ T₂ Is)
    (hI : LiftOf T I Is) (hIs' : GNYComponent T T₁ T₂ Is') (hI' : LiftOf T I' Is')
    (hrank : 2 ≤ CFSG.Open.pRank 7 (pElementSubgroup 7 (cMLStar T Is))) :
    ∃ x : X, orderOf x = 7 ∧ x ∈ cMLStar T Is ∧ x ∈ cMLStar T Is' := by
  have _ := hIs
  have _ := hI
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨E, hEle, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 7) hrank
  have hL3' := hL3 Is' I' hIs' hI'
  obtain ⟨h3b, hZ⟩ := barO2_isLThree_of_lift hKSML3 hX hIs'.1 hI' hL3'
  obtain ⟨hrk3, hrk7⟩ := pRank_eq_one_of_isLThree hI'.1 h3b
  have hEN : ∀ e ∈ E, toStar T e ∈ Subgroup.normalizer (Is' : Set (X ⧸ gnC T)) := by
    intro e he
    by_cases h1 : e = 1
    · rw [h1, map_one]
      exact Subgroup.one_mem _
    · have he7 : orderOf e = 7 := orderOf_eq_prime (hE.2 e he) h1
      have hn : e ∈ Subgroup.normalizer (I' : Set X) := by
        rcases h6 with h6 | h6
        · exact exists_sevenElement_centralizing_aux_normalizes_gen (q := 7) (by norm_num)
            (by norm_num) h6 hI'.1 hrk7 hZ he7
        · exact exists_sevenElement_centralizing_aux_normalizes_gen (q := 3)
            Nat.prime_three (by norm_num) h6 hI'.1 hrk3 hZ he7
      have hn' : I'.map (MulAut.conj e).toMonoidHom = I' :=
        mem_normalizer_iff_map_conj_eq.1 hn
      have hcomp : (toStar T).comp (MulAut.conj e).toMonoidHom =
          (MulAut.conj (toStar T e)).toMonoidHom.comp (toStar T) := by
        ext a
        simp [MulAut.conj_apply]
      rw [mem_normalizer_iff_map_conj_eq]
      show Is'.map (MulAut.conj (toStar T e)).toMonoidHom = Is'
      rw [← hI'.2, Subgroup.map_map, ← hcomp, ← Subgroup.map_map, hn']
  obtain ⟨x, hxE, hx1, hxc⟩ :=
    exists_sevenElement_centralizing_aux_kernel hKOut (toStar T) hL3' hE hEcard hEN
  exact ⟨x, orderOf_eq_prime (hE.2 x hxE) hx1, (pElementSubgroup_le _) (hEle hxE), hxc⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
