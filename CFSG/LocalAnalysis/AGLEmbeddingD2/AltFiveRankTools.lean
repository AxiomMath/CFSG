module

import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open

namespace AltFiveRankTools

theorem pow_eq_one_of_mem_closure_of_pairwise_commute {J : Type*} [Group J] {S : Set J}
    (hS : S.Pairwise Commute) {m : ℕ} (hgen : ∀ y ∈ S, y ^ m = 1) {y : J}
    (hy : y ∈ Subgroup.closure S) : y ^ m = 1 := by
  have : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hS
  refine Subgroup.closure_induction (p := fun y _ => y ^ m = 1) hgen (by simp)
    (fun a b ha hb iha ihb => ?_) (fun a ha ih => by rw [inv_pow, ih, inv_one]) hy
  have hab : a * b = b * a :=
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure S) ⟨b, hb⟩)
  rw [Commute.mul_pow hab, iha, ihb, one_mul]

theorem le_pRank_closure_of_pairwise_commute {J : Type*} [Group J] [Finite J] {p : ℕ}
    [Fact p.Prime] {S : Set J} (hS : S.Pairwise Commute) (hgen : ∀ y ∈ S, y ^ p = 1) {k : ℕ}
    (hk : p ^ k ≤ Nat.card (Subgroup.closure S)) : k ≤ Open.pRank p (Subgroup.closure S) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hS
  have hpow : ∀ a : Subgroup.closure S, a ^ p = 1 := fun a =>
    Subtype.ext (pow_eq_one_of_mem_closure_of_pairwise_commute hS hgen a.2)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1
    (fun a : Subgroup.closure S => ⟨1, by simpa using hpow a⟩ : IsPGroup p (Subgroup.closure S))
  refine ((Nat.pow_le_pow_iff_right hp1).1 (hm ▸ hk)).trans ?_
  exact SectionRank.le_pRank_of_injective hp1 (fun a b => mul_comm' a b) hpow hm
    (Subgroup.closure S).subtype (Subgroup.closure S).subtype_injective
    (by rw [Subgroup.range_subtype])

end AltFiveRankTools

theorem pRank_succ_le_sup_zpowers {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (A : Subgroup G) {z : G} (hz : z ^ q = 1) (hz1 : z ≠ 1)
    (hzA : z ∈ Subgroup.centralizer (A : Set G)) (hdisj : Subgroup.zpowers z ⊓ A = ⊥) :
    Open.pRank q A + 1 ≤ Open.pRank q (A ⊔ Subgroup.zpowers z) := by
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  obtain ⟨E, hEA, hE, hcard⟩ := SectionRank.exists_pRank hq1 A
  have : IsMulCommutative E := hE.1
  have hZcard : Nat.card (Subgroup.zpowers z) = q := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz hz1
  have hcommute : ∀ (e : E) (w : Subgroup.zpowers z),
      Commute (E.subtype e) ((Subgroup.zpowers z).subtype w) := by
    intro e w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 w.2
    have hez : Commute (e : G) z :=
      Subgroup.mem_centralizer_iff.1 hzA (e : G) (hEA e.2)
    have : Commute (e : G) (w : G) := by
      rw [← hk]
      exact hez.zpow_right k
    exact this
  let φ : E × Subgroup.zpowers z →* G :=
    MonoidHom.noncommCoprod E.subtype (Subgroup.zpowers z).subtype hcommute
  have hφ : ∀ (e : E) (w : Subgroup.zpowers z), φ (e, w) = (e : G) * (w : G) := fun e w =>
    MonoidHom.noncommCoprod_apply _ _ _ (e, w)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨e, w⟩ h
    rw [hφ] at h
    have hew : (e : G) = (w : G)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hemem : (e : G) ∈ Subgroup.zpowers z ⊓ A :=
      ⟨hew ▸ Subgroup.inv_mem _ w.2, hEA e.2⟩
    rw [hdisj, Subgroup.mem_bot] at hemem
    have he : e = 1 := Subtype.ext hemem
    refine Prod.ext he (Subtype.ext ?_)
    rw [he] at h
    simpa using h
  have hcomm : ∀ a b : E × Subgroup.zpowers z, a * b = b * a := fun a b =>
    Prod.ext (mul_comm' a.1 b.1) (mul_comm' a.2 b.2)
  have hpow : ∀ a : E × Subgroup.zpowers z, a ^ q = 1 := by
    intro a
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using hE.2 (a.1 : G) a.1.2
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2.2
      change (a.2 : G) ^ q = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  have hA : Nat.card (E × Subgroup.zpowers z) = q ^ (Open.pRank q A + 1) := by
    rw [Nat.card_prod, hcard, hZcard, pow_succ]
  refine SectionRank.le_pRank_of_injective hq1 hcomm hpow hA φ hφinj ?_
  rintro _ ⟨⟨e, w⟩, rfl⟩
  rw [hφ]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hEA e.2)) (Subgroup.mem_sup_right w.2)

end CFSG.AGLEmbeddingD2
