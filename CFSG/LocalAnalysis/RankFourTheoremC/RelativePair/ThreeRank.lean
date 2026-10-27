module

import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_RankAux
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_RankAuxComm
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup
open scoped commutatorElement

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem zjr_exists_card_inf_centralizer_ge {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type*}
    [Group Y] [Finite Y] {D V : Subgroup Y} (hDp : ∀ d ∈ D, d ^ p = 1)
    (hDc : Nat.card D = p ^ 2) (hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hV : IsPGroup 3 V)
    (hDV : D ≤ normalizer (V : Set Y)) (hfaith : D ⊓ centralizer (V : Set Y) = ⊥) :
    ∃ d ∈ D, d ≠ 1 ∧ 27 ≤ Nat.card (V ⊓ centralizer ({d} : Set Y) : Subgroup Y) := by
  by_contra hcon
  have hlt : ∀ d ∈ D, d ≠ 1 → Nat.card (V ⊓ centralizer ({d} : Set Y) : Subgroup Y) < 27 := by
    intro d hd hd1
    by_contra hge
    exact hcon ⟨d, hd, hd1, not_lt.1 hge⟩
  have hCV : ∀ a ∈ D, a ≠ 1 → V ⊓ centralizer ({a} : Set Y) ≤ centralizer (D : Set Y) := by
    intro a ha ha1 x hx
    rw [mem_centralizer_iff]
    intro b hb
    by_contra hbx
    have hbN : b ∈ normalizer ((V ⊓ centralizer ({a} : Set Y) : Subgroup Y) : Set Y) :=
      zjr_mem_normalizer_inf_centralizer (hDV hb) (hDcomm b hb a ha)
    have hnc : ¬ (V ⊓ centralizer ({a} : Set Y) : Subgroup Y) ≤ centralizer ({b} : Set Y) :=
      fun h => hbx (zjr_mem_centralizer_singleton.1 (h hx))
    have h27 := zjr_card_fixed_mul_le hp hp5 (hV.to_le inf_le_left) (hDp b hb) hbN hnc
    have hpos : 0 < Nat.card ((V ⊓ centralizer ({a} : Set Y) : Subgroup Y) ⊓
        centralizer ({b} : Set Y) : Subgroup Y) := Nat.card_pos
    have := hlt a ha ha1
    omega
  have hDe : IsElemAbelian p D := ⟨⟨⟨fun a b => Subtype.ext (hDcomm a a.2 b b.2)⟩⟩, hDp⟩
  obtain ⟨e, he, heD⟩ := elementary_rank_two_has_coordinate_embedding p hp D hDe 2 hDc le_rfl
  have hVD : V ≤ centralizer (D : Set Y) := by
    refine embedded_rank_two_signalizer_le_of_line_centralizers p hp e V _ (heD.trans hDV) ?_ ?_
    · obtain ⟨k, hk⟩ := hV.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_three).2 (by omega))
    · intro v hv
      set w := e (Multiplicative.ofAdd v) with hw
      have hwmem : w ∈ (e.comp (coordinatePairLineHom v)).range := by
        refine ⟨Multiplicative.ofAdd 1, ?_⟩
        rw [MonoidHom.comp_apply, hw]
        congr 1
        change Multiplicative.ofAdd ((1 : ZMod p) • v) = Multiplicative.ofAdd v
        rw [one_smul]
      have hwD : w ∈ D := heD ⟨_, rfl⟩
      have hw1 : w ≠ 1 := by
        intro h
        have h' : Multiplicative.ofAdd v = 1 := he (by rw [map_one]; exact h)
        exact hv (by simpa using congrArg Multiplicative.toAdd h')
      exact (inf_le_inf_left V (centralizer_le (Set.singleton_subset_iff.mpr hwmem))).trans
        (hCV w hwD hw1)
  have hDC : D ≤ centralizer (V : Set Y) := fun d hd => by
    rw [mem_centralizer_iff]
    intro v hv
    exact (mem_centralizer_iff.1 (hVD hv) d hd).symm
  have hDbot : D = ⊥ := by
    rw [← inf_eq_left.2 hDC]
    exact hfaith
  rw [hDbot, Subgroup.card_bot] at hDc
  have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  omega

theorem zjr_main_centralizer {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type*} [Group Y]
    [Finite Y] {D R : Subgroup Y} (hDp : ∀ d ∈ D, d ^ p = 1) (hDc : Nat.card D = p ^ 2)
    (hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDR : D ≤ normalizer (R : Set Y))
    (hfaith : D ⊓ centralizer (R : Set Y) = ⊥) (hexp : ∀ x ∈ R, x ^ 3 = 1)
    (hcl : ⁅R, R⁆ ≤ centralizer (R : Set Y)) :
    ∃ d ∈ D, d ≠ 1 ∧ ∃ A : Subgroup Y, A ≤ R ⊓ centralizer ({d} : Set Y) ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ x ∈ A, x ^ 3 = 1) ∧ 27 ≤ Nat.card A := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : p ≠ 3 := by omega
  have hR3 : IsPGroup 3 R := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  by_cases hab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a
  · obtain ⟨d, hdD, hd1, hd27⟩ :=
      zjr_exists_card_inf_centralizer_ge hp hp5 hDp hDc hDcomm hR3 hDR hfaith
    exact ⟨d, hdD, hd1, R ⊓ centralizer ({d} : Set Y), le_rfl,
      fun a ha b hb => hab a (mem_inf.1 ha).1 b (mem_inf.1 hb).1,
      fun x hx => hexp x (mem_inf.1 hx).1, hd27⟩
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x := by
    by_contra h
    exact hab fun a ha b hb => by
      by_contra hne
      exact h ⟨a, ha, b, hb, hne⟩
  set Z : Subgroup Y := R ⊓ centralizer (R : Set Y) with hZdef
  have hZR : Z ≤ R := inf_le_left
  have hZc : ∀ z ∈ Z, ∀ b ∈ R, z * b = b * z := fun z hz b hb =>
    (mem_centralizer_iff.1 (mem_inf.1 hz).2 b hb).symm
  have hZ3 : IsPGroup 3 Z := hR3.to_le hZR
  have hZnt : 3 ≤ Nat.card Z := by
    have hx₀1 : x₀ ≠ 1 := by
      rintro rfl
      exact hxy (by simp)
    have : Nontrivial R := ⟨⟨⟨x₀, hx₀⟩, 1, fun h => hx₀1 (congrArg Subtype.val h)⟩⟩
    have : Nontrivial (center R) := hR3.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : center R)
    have hcZ : ((c : R) : Y) ∈ Z := by
      refine mem_inf.2 ⟨(c : R).2, mem_centralizer_iff.2 fun h hh => ?_⟩
      exact congrArg Subtype.val (mem_center_iff.1 c.2 ⟨h, hh⟩)
    obtain ⟨k, hk⟩ := hZ3.exists_card_eq
    rw [hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hk
      apply hc
      apply Subtype.ext
      apply Subtype.ext
      have := hk ▸ hcZ
      simpa using this
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hk0)
  by_cases hZ27 : 27 ≤ Nat.card Z
  · have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a ha b (hZR hb)
    by_cases hZf : D ⊓ centralizer (Z : Set Y) = ⊥
    · obtain ⟨d, hdD, hd1, hd27⟩ := zjr_exists_card_inf_centralizer_ge hp hp5 hDp hDc hDcomm hZ3
        (fun d hd => zjr_mem_normalizer_center (hDR hd)) hZf
      exact ⟨d, hdD, hd1, Z ⊓ centralizer ({d} : Set Y), inf_le_inf_right _ hZR,
        fun a ha b hb => hZab a (mem_inf.1 ha).1 b (mem_inf.1 hb).1,
        fun x hx => hexp x (hZR (mem_inf.1 hx).1), hd27⟩
    · obtain ⟨⟨d, hd⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZf
      have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
      obtain ⟨hdD, hdZ⟩ := mem_inf.1 hd
      exact ⟨d, hdD, hd1, Z, le_inf hZR fun z hz =>
        zjr_mem_centralizer_singleton.2 (mem_centralizer_iff.1 hdZ z hz).symm,
        hZab, fun x hx => hexp x (hZR hx), hZ27⟩
  have hZD : ∀ a ∈ D, Z ≤ centralizer ({a} : Set Y) := by
    intro a ha
    by_contra hnc
    have h27 := zjr_card_fixed_mul_le hp hp5 hZ3 (hDp a ha) (zjr_mem_normalizer_center (hDR ha))
      hnc
    have hpos : 0 < Nat.card (Z ⊓ centralizer ({a} : Set Y) : Subgroup Y) := Nat.card_pos
    omega
  obtain ⟨a₁, ha₁D, ha₁1, a₂, ha₂D, ha₂n, h₁, -⟩ :=
    zjr_exists_pair hp hp3 hDp hDc hR3 hDR hfaith
  have ha₂p : a₂ ^ p = 1 := hDp a₂ ha₂D
  have hn₂ : a₂ ∈ normalizer (R : Set Y) := hDR ha₂D
  have h12 : a₁ * a₂ = a₂ * a₁ := hDcomm a₁ ha₁D a₂ ha₂D
  have hZa₁ := hZD a₁ ha₁D
  have hZa₂ := hZD a₂ ha₂D
  set S₁ : Subgroup Y := R ⊓ centralizer ({a₁} : Set Y) with hS₁
  set B₁ : Subgroup Y := ⁅S₁, zpowers a₂⁆ with hB₁
  have hnc₁ : ¬ B₁ ≤ centralizer ({a₂} : Set Y) :=
    zjr_B_not_centralized hp hp3 hR3 ha₂p hn₂ h12 ha₂n (h₁ a₂ ha₂D)
  have hnormS₁ : zpowers a₂ ≤ normalizer (S₁ : Set Y) := by
    rw [zpowers_le]
    exact zjr_mem_normalizer_inf_centralizer hn₂ h12.symm
  have hB₁S₁ : B₁ ≤ S₁ := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _ hnormS₁
  set U : Subgroup Y := Z ⊔ B₁ with hU
  have hUS₁ : U ≤ S₁ := sup_le (le_inf hZR hZa₁) hB₁S₁
  have hUR : U ≤ R := hUS₁.trans inf_le_left
  have hZU : Z ≤ U := le_sup_left
  have hB₁U : B₁ ≤ U := le_sup_right
  have hnormB₁ : a₂ ∈ normalizer (B₁ : Set Y) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized _ _ hnormS₁ (mem_zpowers a₂)
  have hnormU : a₂ ∈ normalizer (U : Set Y) :=
    inf_normalizer_le_normalizer_sup Z B₁ ⟨zjr_mem_normalizer_center hn₂, hnormB₁⟩
  have hnU : ¬ U ≤ centralizer ({a₂} : Set Y) := fun h => hnc₁ (hB₁U.trans h)
  have hUcard := zjr_card_fixed_mul_le hp hp5 (hR3.to_le hUR) ha₂p hnormU hnU
  have hZUc : Nat.card Z ≤ Nat.card (U ⊓ centralizer ({a₂} : Set Y) : Subgroup Y) :=
    Subgroup.card_le_of_le (le_inf hZU hZa₂)
  have hU27 : 27 * Nat.card Z ≤ Nat.card U := by omega
  obtain ⟨M, hMU, -, hMcomm, hM27⟩ := zjr_exists_abelian_ambient hZU
    (fun b hb => hexp b (hUR hb)) (fun z hz b hb => hZc z hz b (hUR hb))
    (fun b hb b' hb' => mem_inf.2 ⟨zjr_commutator_le_self R
      (commutator_mem_commutator (hUR hb) (hUR hb')),
      hcl (commutator_mem_commutator (hUR hb) (hUR hb'))⟩) hZnt hU27
  exact ⟨a₁, ha₁D, ha₁1, M, hMU.trans hUS₁, hMcomm, fun x hx => hexp x (hUR (hMU hx)), hM27⟩

open CFSG.Open Subgroup in
theorem exists_isElemAbelian_card_three_pow_three_of_faithful {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y] {D Q : Subgroup Y} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) (hQ : IsPGroup 3 Q) (hDQ : D ≤ normalizer (Q : Set Y))
    (hfaith : D ⊓ centralizer (Q : Set Y) = ⊥) :
    ∃ d ∈ D, d ≠ 1 ∧ ∃ A : Subgroup Y, A ≤ Q ⊓ centralizer ({d} : Set Y) ∧
      IsElemAbelian 3 A ∧ 3 ^ 3 ≤ Nat.card A := by
  have : IsMulCommutative D := hD.1
  obtain ⟨R, hRQ, hDR, hRfaith, hexp, hcl⟩ := zjr_exists_reduction hp hp5 hD.2 hQ hDQ hfaith
  obtain ⟨d, hdD, hd1, A, hAR, hAcomm, hAexp, hA⟩ := zjr_main_centralizer hp hp5 hD.2 hDc
    (fun a ha b hb => congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : D) ⟨b, hb⟩))
    hDR hRfaith hexp hcl
  exact ⟨d, hdD, hd1, A, hAR.trans (inf_le_inf_right _ hRQ),
    ⟨⟨⟨fun a b => Subtype.ext (hAcomm a a.2 b b.2)⟩⟩, hAexp⟩, hA⟩

end CFSG.LocalAnalysis.RankFourTheoremC
