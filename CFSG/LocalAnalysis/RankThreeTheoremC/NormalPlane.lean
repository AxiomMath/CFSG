module

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers (aschCore_normalizer_le pRank_attained
  pRank_set_bddAbove sigmaA_prime)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

private theorem le_pRank_of_isElemAbelian {p : ℕ} (hp : p.Prime) {A K : Subgroup G}
    (hAK : A ≤ K) (hA : IsElemAbelian p A) {k : ℕ} (hcard : Nat.card A = p ^ k) :
    k ≤ pRank p K := CFSG.SectionRank.le_pRank hp.one_lt hAK hA hcard

private theorem three_le_pRank_of_lt_card {p : ℕ} (hp : p.Prime) {A K : Subgroup G}
    (hAK : A ≤ K) (hA : IsElemAbelian p A) (hcard : p ^ 2 < Nat.card A) : 3 ≤ pRank p K := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
  rw [hk] at hcard
  exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 hcard |>.trans_le
    (le_pRank_of_isElemAbelian hp hAK hA hk)

omit [Finite G] in
private theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup G} (hB : IsElemAbelian p B)
    (hAB : A ≤ B) : IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB hAB

omit [Finite G] in
private theorem isElemAbelian_sup {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hAB : B ≤ centralizer (A : Set G)) : IsElemAbelian p (A ⊔ B) := by
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, Commute a a' := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, Commute b b' := fun b hb b' hb' =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hABc : ∀ a ∈ A, ∀ b ∈ B, Commute a b := fun a ha b hb =>
    mem_centralizer_iff.mp (hAB hb) a ha
  have hmem : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
    intro x hx
    have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
    rw [coe_mul_of_right_le_normalizer_left A B (hAB.trans (centralizer_le_normalizer _))] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨a, ha, b, hb, rfl⟩
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, hxe⟩ := hmem x x.2
    obtain ⟨a', ha', b', hb', hye⟩ := hmem y y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hxe, hye]
    exact ((hAc a ha a' ha').mul_right (hABc a ha b' hb')).mul_left
      ((hABc a' ha' b hb).symm.mul_right (hBc b hb b' hb')) |>.eq
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    rw [(hABc a ha b hb).mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

omit [Finite G] in
@[instance_reducible]
private def conjMulAction {E X : Subgroup G} (h : E ≤ normalizer (X : Set G)) :
    MulAction E X where
  smul e x := ⟨e * x * e⁻¹, (mem_normalizer_iff.mp (h e.2) x).mp x.2⟩
  one_smul x := Subtype.ext (by
    change ((1 : E) : G) * x * ((1 : E) : G)⁻¹ = x
    rw [Subgroup.coe_one, inv_one, one_mul, mul_one])
  mul_smul e e' x := Subtype.ext (by
    change ((e * e' : E) : G) * x * ((e * e' : E) : G)⁻¹ = e * (e' * x * (e' : G)⁻¹) * (e : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc])

private theorem card_le_mul_card_inf_centralizer {p : ℕ} (hp : p.Prime) {E X : Subgroup G}
    (hEX : E ≤ normalizer (X : Set G)) (hE : IsPGroup p E) (hX : IsElemAbelian p X)
    (hXcard : Nat.card X = p ^ 2) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ centralizer (X : Set G)) := by
  classical
  have := Fact.mk hp
  let _ : MulAction E X := conjMulAction hEX
  have hsmul : ∀ (e : E) (x : X), ((e • x : X) : G) = e * x * e⁻¹ := fun _ _ => rfl
  obtain ⟨a, haX, haE, ha1⟩ : ∃ a : G, a ∈ X ∧ (∀ e ∈ E, e * a = a * e) ∧ a ≠ 1 := by
    have hmod := hE.card_modEq_card_fixedPoints X
    rw [hXcard] at hmod
    have hdvd : p ∣ Nat.card (MulAction.fixedPoints E X) :=
      Nat.modEq_zero_iff_dvd.mp
        (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p two_ne_zero)))
    have hone : (1 : X) ∈ MulAction.fixedPoints E X := fun e =>
      Subtype.ext (by
        rw [hsmul, Subgroup.coe_one, mul_one, ← Subgroup.coe_mul, mul_inv_cancel,
          Subgroup.coe_one])
    have : Nonempty (MulAction.fixedPoints E X) := ⟨⟨1, hone⟩⟩
    have hgt : 1 < Nat.card (MulAction.fixedPoints E X) :=
      hp.one_lt.trans_le (Nat.le_of_dvd Nat.card_pos hdvd)
    have := Finite.one_lt_card_iff_nontrivial.mp hgt
    obtain ⟨y, hy⟩ := exists_ne (⟨1, hone⟩ : MulAction.fixedPoints E X)
    refine ⟨y.1.1, y.1.2, fun e he => ?_, fun h => hy (Subtype.ext (Subtype.ext h))⟩
    have h := congrArg Subtype.val (y.2 ⟨e, he⟩)
    rw [hsmul] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have haord : orderOf a = p := orderOf_eq_prime (hX.2 a haX) ha1
  obtain ⟨b, hbX, hb⟩ : ∃ b ∈ X, b ∉ zpowers a := by
    by_contra hall
    push Not at hall
    have h := Subgroup.card_le_of_le (fun x hx => hall x hx : X ≤ zpowers a)
    rw [Nat.card_zpowers, haord, hXcard] at h
    nlinarith [hp.two_le]
  have hYX : zpowers a ⊔ zpowers b = X := by
    have hle : zpowers a ⊔ zpowers b ≤ X := sup_le (zpowers_le.mpr haX) (zpowers_le.mpr hbX)
    refine eq_of_le_of_card_ge hle ?_
    have hdvd1 : p ∣ Nat.card ↥(zpowers a ⊔ zpowers b) := by
      have h := Subgroup.card_dvd_of_le (le_sup_left : zpowers a ≤ zpowers a ⊔ zpowers b)
      rwa [Nat.card_zpowers, haord] at h
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp (hXcard ▸ Subgroup.card_dvd_of_le hle)
    rw [hXcard, hk]
    interval_cases k
    · rw [hk] at hdvd1
      exact absurd (Nat.dvd_one.mp hdvd1) hp.ne_one
    · refine absurd ?_ hb
      have heq : zpowers a = zpowers a ⊔ zpowers b := eq_of_le_of_card_ge le_sup_left
        (by rw [hk, Nat.card_zpowers, haord, pow_one])
      exact heq ▸ (le_sup_right : zpowers b ≤ zpowers a ⊔ zpowers b) (mem_zpowers b)
    · exact le_rfl
  have hcentral : ∀ g : G, g * a = a * g → g * b = b * g → g ∈ centralizer (X : Set G) := by
    intro g hga hgb
    have hX' : X ≤ centralizer ({g} : Set G) := by
      rw [← hYX]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact hga
      · exact mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact hgb
    exact mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_iff.mp (hX' hx) g (Set.mem_singleton g)).symm
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  have horb_lt : (MulAction.orbit E (⟨b, hbX⟩ : X)).ncard < p ^ 2 := by
    rw [← hXcard, ← Set.ncard_univ]
    refine Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr fun h => ?_)
    obtain ⟨e, he⟩ := MulAction.mem_orbit_iff.mp (h ▸ Set.mem_univ (1 : X))
    have h1 := congrArg Subtype.val he
    rw [hsmul] at h1
    exact hb1 (by simpa using h1)
  have horb_le : (MulAction.orbit E (⟨b, hbX⟩ : X)).ncard ≤ p := by
    obtain ⟨n, hn⟩ := hE.card_orbit (⟨b, hbX⟩ : X)
    rw [← Nat.card_coe_set_eq, hn] at horb_lt ⊢
    have hn2 : n < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 horb_lt
    calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  have hstab_le : Nat.card (MulAction.stabilizer E (⟨b, hbX⟩ : X)) ≤
      Nat.card ↥(E ⊓ centralizer (X : Set G)) := by
    have hmem : ∀ s : MulAction.stabilizer E (⟨b, hbX⟩ : X),
        (s.1 : G) ∈ E ⊓ centralizer (X : Set G) := by
      intro s
      refine mem_inf.mpr ⟨s.1.2, hcentral _ (haE _ s.1.2) ?_⟩
      have h := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp s.2)
      rw [hsmul] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    refine Nat.card_le_card_of_injective (fun s => ⟨(s.1 : G), hmem s⟩) fun s t hst => ?_
    have h := congrArg Subtype.val hst
    exact Subtype.ext (Subtype.ext h)
  calc Nat.card E
      = (MulAction.stabilizer E (⟨b, hbX⟩ : X)).index *
          Nat.card (MulAction.stabilizer E (⟨b, hbX⟩ : X)) :=
        (Subgroup.index_mul_card _).symm
    _ ≤ p * Nat.card ↥(E ⊓ centralizer (X : Set G)) := by
        rw [MulAction.index_stabilizer]
        exact Nat.mul_le_mul horb_le hstab_le

theorem three_le_pRank_sup_centralizer_of_normal_elemAbelian {p : ℕ} (hp : p.Prime)
    {P X : Subgroup G} (hrank : 3 ≤ pRank p P) (hnorm : P ≤ normalizer (X : Set G))
    (hX : IsElemAbelian p X) (hXcard : Nat.card X = p ^ 2) :
    3 ≤ pRank p (X ⊔ (P ⊓ centralizer (X : Set G))) := by
  have := Fact.mk hp
  obtain ⟨E, hEP, hE, hEcard⟩ := pRank_attained p P (by omega)
  have hEcard3 : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp.pos hrank
  have hidx := card_le_mul_card_inf_centralizer hp (hEP.trans hnorm)
    (isPGroup_of_isElemAbelian hE) hX hXcard
  have hE₁ : p ^ 2 ≤ Nat.card ↥(E ⊓ centralizer (X : Set G)) := by
    have h : p * p ^ 2 ≤ p * Nat.card ↥(E ⊓ centralizer (X : Set G)) :=
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card E := hEcard3
        _ ≤ _ := hidx
    exact Nat.le_of_mul_le_mul_left h hp.pos
  by_cases hEC : E ≤ centralizer (X : Set G)
  · exact three_le_pRank_of_lt_card hp ((le_inf hEP hEC).trans le_sup_right) hE
      (lt_of_lt_of_le (Nat.pow_lt_pow_right hp.one_lt (by norm_num)) hEcard3)
  · have hE₁E : E ⊓ centralizer (X : Set G) ≤ E := inf_le_left
    have hE₁C : E ⊓ centralizer (X : Set G) ≤ centralizer (X : Set G) := inf_le_right
    refine three_le_pRank_of_lt_card hp
      (sup_le_sup_left (le_inf (hE₁E.trans hEP) hE₁C) X)
      (isElemAbelian_sup hX (isElemAbelian_of_le hE hE₁E) hE₁C) ?_
    by_contra hle
    push Not at hle
    have hXA : X = X ⊔ E ⊓ centralizer (X : Set G) :=
      eq_of_le_of_card_ge le_sup_left (by rw [hXcard]; exact hle)
    have hE₁X : E ⊓ centralizer (X : Set G) ≤ X :=
      (le_sup_right : E ⊓ centralizer (X : Set G) ≤ X ⊔ E ⊓ centralizer (X : Set G)).trans
        hXA.symm.le
    have hXE : X ≤ E ⊓ centralizer (X : Set G) :=
      (eq_of_le_of_card_ge hE₁X (by rw [hXcard]; exact hE₁)).ge
    apply hEC
    intro e he
    refine mem_centralizer_iff.mpr fun x hx => ?_
    have hxe : x ∈ E := hXE hx |>.1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hxe⟩ ⟨e, he⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
