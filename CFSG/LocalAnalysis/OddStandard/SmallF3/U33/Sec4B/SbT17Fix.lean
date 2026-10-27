module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private def conjN {N : Subgroup G} {t : G}
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (n : ↥N) : ↥N :=
  ⟨t * n.1 * t⁻¹, htN n.1 n.2⟩

private def cosetConj {E N : Subgroup G} {t : G}
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) :
    (↥N ⧸ E.subgroupOf N) → (↥N ⧸ E.subgroupOf N) :=
  Quotient.map' (conjN htN) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    apply Subgroup.mem_subgroupOf.mpr
    have hmem : (a : G)⁻¹ * (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hab
    have hconj : t * ((a : G)⁻¹ * (b : G)) * t⁻¹ ∈ E := htE _ hmem
    have hEq : ((conjN htN a : G)⁻¹ * (conjN htN b : G)) =
        t * ((a : G)⁻¹ * (b : G)) * t⁻¹ := by
      simp only [conjN, Subtype.coe_mk]
      push_cast
      group
    change ((conjN htN a : G)⁻¹ * (conjN htN b : G)) ∈ E
    rw [hEq]
    exact hconj

private lemma conjN_involutive {N : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (n : ↥N) :
    conjN htN (conjN htN n) = n := by
  have htinv : t⁻¹ = t := by
    calc t⁻¹ = t⁻¹ * 1 := (mul_one _).symm
      _ = t⁻¹ * (t * t) := by rw [ht2]
      _ = (t⁻¹ * t) * t := by rw [mul_assoc]
      _ = t := by rw [inv_mul_cancel, one_mul]
  apply Subtype.ext
  simp only [conjN, Subtype.coe_mk]
  calc t * (t * n.1 * t⁻¹) * t⁻¹ = (t * t) * n.1 * (t⁻¹ * t⁻¹) := by group
    _ = n.1 := by rw [ht2, htinv, ht2]; group

private lemma cosetConj_involutive {E N : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) :
    Function.Involutive (cosetConj htN htE) := by
  intro q
  induction q using Quotient.inductionOn' with
  | h n =>
    simp only [cosetConj, Quotient.map'_mk'']
    rw [conjN_involutive ht2 htN n]

theorem exists_fixed_coset {E N : Subgroup G} (hN2 : IsPGroup 2 N) (hEN : E < N) {t : G}
    (ht2 : t * t = 1) (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) :
    ∃ n ∈ N, n ∉ E ∧ n⁻¹ * (t * n * t⁻¹) ∈ E := by
  classical
  let X := ↥N ⧸ E.subgroupOf N
  haveI : Fintype ↥N := Fintype.ofFinite ↥N
  haveI : Fintype X :=
    Fintype.ofSurjective (Quotient.mk'' : ↥N → X) Quotient.mk''_surjective
  have hcardX : Fintype.card X = (E.subgroupOf N).index := by
    rw [Fintype.card_eq_nat_card, Subgroup.index_eq_card]
  have hne_index : (E.subgroupOf N).index ≠ 1 := by
    intro h
    have htop : E.subgroupOf N = ⊤ := Subgroup.index_eq_one.mp h
    exact hEN.2 (Subgroup.subgroupOf_eq_top.mp htop)
  obtain ⟨k, hk⟩ := hN2.index (E.subgroupOf N)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (hk ▸ hk0 ▸ rfl) hne_index
    · exact hk0
  have hα : 2 ∣ Fintype.card X := by
    rw [hcardX, hk]
    exact dvd_pow_self 2 hkpos.ne'
  let s : Equiv.Perm X := (cosetConj_involutive ht2 htN htE).toPerm (cosetConj htN htE)
  have hs : (s : X → X) = cosetConj htN htE := Function.Involutive.coe_toPerm _
  have hpow : s ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [hs]
    exact cosetConj_involutive ht2 htN htE x
  let oneN : ↥N := ⟨1, N.one_mem⟩
  let a : X := Quotient.mk'' oneN
  have hone : conjN htN oneN = oneN := by
    ext
    simp [conjN, oneN, ht2]
  have hfixa : s a = a := by
    rw [hs]
    change cosetConj htN htE (Quotient.mk'' oneN) = Quotient.mk'' oneN
    simp only [cosetConj, Quotient.map'_mk'']
    rw [hone]
  obtain ⟨b, hbfix, hbne⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := 1) hα hpow hfixa
  obtain ⟨x, hxb⟩ : ∃ x : ↥N, (Quotient.mk'' x : X) = b :=
    ⟨b.out, Quotient.out_eq' b⟩
  have hbfix' : s (Quotient.mk'' x) = Quotient.mk'' x := by
    rw [hxb]
    exact hbfix
  have hbne' : (Quotient.mk'' x : X) ≠ a := by
    rw [hxb]
    exact hbne
  have hfixq : cosetConj htN htE (Quotient.mk'' x) = Quotient.mk'' x := by
    rw [← hs]
    exact hbfix'
  have hmemQ : (conjN htN x)⁻¹ * x ∈ E.subgroupOf N := by
    apply QuotientGroup.eq.mp
    simpa only [cosetConj, Quotient.map'_mk''] using hfixq
  have hmemE : (conjN htN x : G)⁻¹ * x.1 ∈ E :=
    Subgroup.mem_subgroupOf.mp hmemQ
  refine ⟨x.1, x.2, ?_, ?_⟩
  · intro hxe
    apply hbne'
    rw [QuotientGroup.eq]
    apply Subgroup.mem_subgroupOf.mpr
    simpa [oneN] using E.inv_mem hxe
  · have hfin : ((conjN htN x : G)⁻¹ * x.1)⁻¹ ∈ E := E.inv_mem hmemE
    simpa [conjN, mul_inv_rev, inv_inv] using hfin

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
