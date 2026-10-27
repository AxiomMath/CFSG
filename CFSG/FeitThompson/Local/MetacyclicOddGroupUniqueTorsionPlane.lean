module

public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.CyclicIndexPGroupTorsionPlane
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p k : ℕ} {R : Type*} [Group R]

def IsMetacyclic (R : Type*) [Group R] : Prop :=
  ∃ (S : Subgroup R) (_ : S.Normal), IsCyclic S ∧ IsCyclic (R ⧸ S)

theorem isMetacyclic_iff : IsMetacyclic R ↔
    ∃ (S : Subgroup R) (_ : S.Normal), IsCyclic S ∧ IsCyclic (R ⧸ S) := Iff.rfl

theorem isMetacyclic_of_normal (S : Subgroup R) [S.Normal] (hS : IsCyclic S)
    (hQ : IsCyclic (R ⧸ S)) : IsMetacyclic R := ⟨S, ‹S.Normal›, hS, hQ⟩

theorem IsMetacyclic.of_isCyclic (R : Type*) [Group R] [IsCyclic R] : IsMetacyclic R :=
  ⟨⊤, inferInstance, inferInstance,
    @isCyclic_of_subsingleton _ _ QuotientGroup.subsingleton_quotient_top⟩

theorem mem_zpowers_pow_of_pow_eq_one {Q : Type*} [Group Q] {g : Q} (hp : p.Prime) (hk : 1 ≤ k)
    (hg : orderOf g = p ^ k) {y : Q} (hy : y ∈ zpowers g) (hyp : y ^ p = 1) :
    y ∈ zpowers (g ^ p ^ (k - 1)) := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
  have h1 : (orderOf g : ℤ) ∣ m * (p : ℤ) :=
    orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_mul, zpow_natCast, hyp])
  rw [hg, show ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ (k - 1) * (p : ℤ) by
    push_cast; rw [← pow_succ]; congr 1; omega] at h1
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨c, rfl⟩ := (mul_dvd_mul_iff_right hpne).mp h1
  refine mem_zpowers_iff.mpr ⟨c, ?_⟩
  rw [← zpow_natCast g (p ^ (k - 1)), ← zpow_mul]
  push_cast
  ring_nf

theorem exists_natCard_eq_prime_forall_pow_eq_one_mem {Q : Type*} [Group Q] [Finite Q]
    [Nontrivial Q] [IsCyclic Q] (hp : p.Prime) (hQ : IsPGroup p Q) :
    ∃ K : Subgroup Q, Nat.card K = p ∧ ∀ y : Q, y ^ p = 1 → y ∈ K := by
  have := Fact.mk hp
  obtain ⟨k, hk, hcard⟩ := hQ.nontrivial_iff_card.mp ‹Nontrivial Q›
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  have hog : orderOf g = p ^ k := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  refine ⟨zpowers (g ^ p ^ (k - 1)), ?_, fun y hy =>
    mem_zpowers_pow_of_pow_eq_one hp hk hog (hg y) hy⟩
  rw [Nat.card_zpowers,
    orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hog ▸ pow_dvd_pow p (by omega)), hog,
    show p ^ k = p ^ (k - 1) * p by rw [← pow_succ]; congr 1; omega]
  exact Nat.mul_div_cancel_left _ (pow_pos hp.pos _)

theorem index_subgroupOf_comap_mk' [Finite R] (S : Subgroup R) [S.Normal] (K : Subgroup (R ⧸ S))
    (hKcard : Nat.card K = p) :
    (S.subgroupOf (K.comap (QuotientGroup.mk' S))).index = p := by
  set T := K.comap (QuotientGroup.mk' S) with hT
  have hST : S ≤ T := fun x hx => Subgroup.mem_comap.mpr (by
    change (x : R ⧸ S) ∈ K
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact K.one_mem)
  have h1 : S.relIndex T * T.index = S.index := Subgroup.relIndex_mul_index hST
  have h2 : T.index = K.index :=
    Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective S)
  have h3 : K.index * Nat.card K = Nat.card (R ⧸ S) := Subgroup.index_mul_card K
  have h4 : S.index = Nat.card (R ⧸ S) := Subgroup.index_eq_card S
  have hKi : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact Nat.eq_of_mul_eq_mul_right hKi
    (calc S.relIndex T * K.index = S.relIndex T * T.index := by rw [h2]
      _ = Nat.card (R ⧸ S) := by rw [h1, h4]
      _ = p * K.index := by rw [← h3, hKcard]; ring)

theorem omega1_eq_map_subtype {T : Subgroup R} (hT : ∀ x : R, x ^ p = 1 → x ∈ T) :
    omega1 p R = (omega1 p T).map T.subtype := by
  refine le_antisymm (omega1_le fun x hx =>
    ⟨⟨x, hT x hx⟩, mem_omega1_of_pow_eq_one (Subtype.ext (by simpa using hx)), rfl⟩) ?_
  rw [Subgroup.map_le_iff_le_comap]
  exact omega1_le fun y hy =>
    Subgroup.mem_comap.mpr (mem_omega1_of_pow_eq_one (by simpa using congrArg T.subtype hy))

theorem natCard_omega1_eq_of_forall {T : Subgroup R} (hT : ∀ x : R, x ^ p = 1 → x ∈ T) :
    Nat.card (omega1 p R) = Nat.card (omega1 p T) := by
  rw [omega1_eq_map_subtype hT]
  exact (Nat.card_congr
    ((omega1 p T).equivMapOfInjective T.subtype T.subtype_injective).toEquiv).symm

theorem nonempty_mulEquiv_omega1_of_forall {T : Subgroup R} (hT : ∀ x : R, x ^ p = 1 → x ∈ T)
    {N : Type*} [Group N] (e : omega1 p T ≃* N) : Nonempty (omega1 p R ≃* N) := by
  rw [omega1_eq_map_subtype hT]
  exact ⟨(((omega1 p T).equivMapOfInjective T.subtype T.subtype_injective).symm).trans e⟩

theorem coe_omega1_eq_of_forall {T : Subgroup R} (hT : ∀ x : R, x ^ p = 1 → x ∈ T)
    (hcoe : (omega1 p T : Set T) = {x : T | x ^ p = 1}) :
    (omega1 p R : Set R) = {x : R | x ^ p = 1} := by
  rw [omega1_eq_map_subtype hT, Subgroup.coe_map, hcoe]
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, coe_subtype]
  refine ⟨?_, fun hx => ⟨⟨x, hT x hx⟩, Subtype.ext (by simpa using hx), rfl⟩⟩
  rintro ⟨y, hy, rfl⟩
  simpa using congrArg T.subtype hy

theorem exists_natCard_eq_prime_sq_forall_pow_eq_one [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hR : IsPGroup p R) (hnc : ¬ IsCyclic R) :
    ∃ E : Subgroup R, Nat.card E = p ^ 2 ∧ ∀ x ∈ E, x ^ p = 1 := by
  obtain ⟨E, -, -, ⟨f⟩⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hodd hR
    (⊤ : Subgroup R) (fun _ => hnc (isCyclic_of_surjective (⊤ : Subgroup R).subtype
      fun x => ⟨⟨x, trivial⟩, rfl⟩))
  refine ⟨E, by rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod], fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : E) ^ p = 1 :=
    f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
  exact congrArg E.subtype h

theorem not_isCyclic_of_natCard_eq_prime_sq_of_pow_eq_one (hp : p.Prime) {E : Subgroup R}
    (hE : Nat.card E = p ^ 2) (hEexp : ∀ x ∈ E, x ^ p = 1) {T : Subgroup R} (hET : E ≤ T) :
    ¬ IsCyclic T := by
  intro hT
  have hEcyc : IsCyclic E := Subgroup.isCyclic_of_le hET
  have hfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hE]; exact pow_ne_zero _ hp.ne_zero)
  have hexp : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hEexp g.1 g.2)
  rw [IsCyclic.exponent_eq_card, hE] at hexp
  have := Nat.le_of_dvd hp.pos hexp
  nlinarith [hp.two_le]

theorem exists_subgroup_forall_pow_eq_one_mem [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hR : IsPGroup p R) (hnc : ¬ IsCyclic R) (hm : IsMetacyclic R) :
    ∃ (T : Subgroup R) (A : Subgroup T), (∀ x : R, x ^ p = 1 → x ∈ T) ∧ IsCyclic A ∧
      A.index = p ∧ ¬ IsCyclic T := by
  obtain ⟨S, hSnorm, hScyc, hQcyc⟩ := hm
  have := hSnorm
  have := hQcyc
  have hSne : S ≠ ⊤ := by
    rintro rfl
    exact hnc (isCyclic_of_surjective (⊤ : Subgroup R).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hQnt : Nontrivial (R ⧸ S) := QuotientGroup.nontrivial_iff.mpr hSne
  obtain ⟨K, hKcard, hKmem⟩ :=
    exists_natCard_eq_prime_forall_pow_eq_one_mem hp (hR.to_quotient S)
  refine ⟨K.comap (QuotientGroup.mk' S), S.subgroupOf _, fun x hx =>
    Subgroup.mem_comap.mpr (hKmem _ (by rw [← map_pow, hx, map_one])), ?_,
    index_subgroupOf_comap_mk' S K hKcard, ?_⟩
  · have hST : S ≤ K.comap (QuotientGroup.mk' S) := fun x hx => Subgroup.mem_comap.mpr (by
      change (x : R ⧸ S) ∈ K
      rw [(QuotientGroup.eq_one_iff x).mpr hx]
      exact K.one_mem)
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hST).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hST).injective
  · obtain ⟨E, hEcard, hEexp⟩ := exists_natCard_eq_prime_sq_forall_pow_eq_one hp hodd hR hnc
    exact not_isCyclic_of_natCard_eq_prime_sq_of_pow_eq_one hp hEcard hEexp
      (fun x hx => Subgroup.mem_comap.mpr (hKmem _ (by rw [← map_pow, hEexp x hx, map_one])))

section Node

variable [Finite R] (hp : p.Prime) (hodd : Odd p) (hR : IsPGroup p R) (hnc : ¬ IsCyclic R)
  (hm : IsMetacyclic R)

include hp hodd hR hnc hm

theorem coe_omega1_of_isMetacyclic : (omega1 p R : Set R) = {x : R | x ^ p = 1} := by
  obtain ⟨T, A, hTmem, hAcyc, hidx, hTnc⟩ :=
    exists_subgroup_forall_pow_eq_one_mem hp hodd hR hnc hm
  have := hAcyc
  exact coe_omega1_eq_of_forall hTmem
    (coe_omega1_of_isCyclic_of_index_eq_prime A hp hodd (hR.to_subgroup T) hTnc hidx)

theorem natCard_omega1_of_isMetacyclic : Nat.card (omega1 p R) = p ^ 2 := by
  obtain ⟨T, A, hTmem, hAcyc, hidx, hTnc⟩ :=
    exists_subgroup_forall_pow_eq_one_mem hp hodd hR hnc hm
  have := hAcyc
  rw [natCard_omega1_eq_of_forall hTmem]
  exact natCard_omega1_of_isCyclic_of_index_eq_prime A hp hodd (hR.to_subgroup T) hTnc hidx

theorem nonempty_mulEquiv_omega1_of_isMetacyclic :
    Nonempty (omega1 p R ≃* Multiplicative (ZMod p × ZMod p)) := by
  obtain ⟨T, A, hTmem, hAcyc, hidx, hTnc⟩ :=
    exists_subgroup_forall_pow_eq_one_mem hp hodd hR hnc hm
  have := hAcyc
  obtain ⟨f⟩ :=
    nonempty_mulEquiv_omega1_of_isCyclic_of_index_eq_prime A hp hodd (hR.to_subgroup T) hTnc hidx
  exact nonempty_mulEquiv_omega1_of_forall hTmem f

theorem nonempty_mulEquiv_pi_omega1_of_isMetacyclic :
    Nonempty (omega1 p R ≃* (Fin 2 → Multiplicative (ZMod p))) := by
  obtain ⟨f⟩ := nonempty_mulEquiv_omega1_of_isMetacyclic hp hodd hR hnc hm
  exact ⟨f.trans (piMultiplicativeZModMulEquivProd p).symm⟩

theorem omega1_coe_and_natCard_and_mulEquiv_of_isMetacyclic :
    (omega1 p R : Set R) = {x : R | x ^ p = 1} ∧ Nat.card (omega1 p R) = p ^ 2 ∧
      Nonempty (omega1 p R ≃* Multiplicative (ZMod p × ZMod p)) :=
  ⟨coe_omega1_of_isMetacyclic hp hodd hR hnc hm, natCard_omega1_of_isMetacyclic hp hodd hR hnc hm,
    nonempty_mulEquiv_omega1_of_isMetacyclic hp hodd hR hnc hm⟩

theorem eq_omega1_of_natCard_eq_prime_sq_of_isMetacyclic {E : Subgroup R}
    (hE : Nat.card E = p ^ 2) (hEexp : ∀ x ∈ E, x ^ p = 1) : E = omega1 p R := by
  have hcard : Nat.card (omega1 p R) = p ^ 2 := natCard_omega1_of_isMetacyclic hp hodd hR hnc hm
  have hfin : Finite (omega1 p R) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  exact Subgroup.eq_of_le_of_card_ge (fun x hx => mem_omega1_of_pow_eq_one (hEexp x hx))
    (by rw [hcard, hE])

theorem elementaryAbelianPRank_eq_two_of_isMetacyclic : elementaryAbelianPRank p R = 2 := by
  refine le_antisymm (elementaryAbelianPRank_le fun d hd => ?_)
    (two_le_elementaryAbelianPRank_of_not_isCyclic hp hodd hR hnc)
  obtain ⟨E, ⟨f⟩⟩ := mem_elementaryAbelianRanks.mp hd
  have hEexp : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    congrArg E.subtype (f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
      : (⟨x, hx⟩ : E) ^ p = 1)
  have hcard : Nat.card (omega1 p R) = p ^ 2 := natCard_omega1_of_isMetacyclic hp hodd hR hnc hm
  have hEcard : Nat.card E = p ^ d := by
    rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]
  have hdvd : p ^ d ∣ p ^ 2 := by
    rw [← hEcard, ← hcard]
    exact Subgroup.card_dvd_of_le (fun x hx => mem_omega1_of_pow_eq_one (hEexp x hx))
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd

end Node

end

end CFSG.FeitThompson
