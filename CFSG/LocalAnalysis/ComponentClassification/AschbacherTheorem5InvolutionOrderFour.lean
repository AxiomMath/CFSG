module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupRankOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitHypothesisISupport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionTwoGroup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

open CFSG.Open
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

variable {Q : Type} [Group Q] [Finite Q]

theorem sylow_quaternion_of_unique {X P : Subgroup Q} (hXp : Group.IsPerfect X) (hX : X ≠ ⊥)
    {c : Q} (huniq : ∀ x ∈ X, orderOf x = 2 → x = c) (hP : IsSylowOf 2 P X) :
    AschbacherTheorem3.IsQuaternionTwoGroup P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : CFSG.Open.pRank 2 P ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨E, hEP, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := 2) (H := P) (k := 2) (by omega)
    have hsub : ¬ (E : Set Q) ⊆ {1, c} := by
      intro h
      have := card_le_two_of_subset h
      rw [hcard] at this
      norm_num at this
    obtain ⟨x, hx, hxne⟩ := Set.not_subset.mp hsub
    have hx1 : x ≠ 1 := fun h => hxne (Or.inl h)
    exact hxne (Or.inr (huniq x (hP.le (hEP hx)) (orderOf_eq_prime (hE.2 x hx) hx1)))
  rcases SectionSix.cyclic_or_quaternion_of_pRank_le_one hP.isPGroup hr with hc | hq
  · exact absurd hc (SectionSix.sylow_not_cyclic_of_perfect hXp hX hP)
  · exact hq

omit [Finite Q] in
theorem eight_le_card_of_quaternion {P : Subgroup Q}
    (hP : AschbacherTheorem3.IsQuaternionTwoGroup P) : 8 ≤ Nat.card P := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hP
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem exists_orderOf_four_mem {X : Subgroup Q} (hXp : Group.IsPerfect X) (hX : X ≠ ⊥) {c : Q}
    (huniq : ∀ x ∈ X, orderOf x = 2 → x = c) : ∃ x ∈ X, orderOf x = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 X
  have hq := sylow_quaternion_of_unique hXp hX huniq hP
  obtain ⟨x, hx, hx4⟩ := exists_orderOf_four hP.isPGroup
    ((by norm_num : 4 ≤ 8).trans (eight_le_card_of_quaternion hq))
    (fun x hx hx2 => huniq x (hP.le hx) hx2)
  exact ⟨x, hP.le hx, hx4⟩

theorem sq_eq_one_of_mem_centralizer {X : Subgroup Q} (hXp : Group.IsPerfect X) (hX : X ≠ ⊥)
    {c : Q} (huniq : ∀ x ∈ X, orderOf x = 2 → x = c) {y : Q} (hyX : y ∈ X)
    (hyc : y ∈ Subgroup.centralizer (X : Set Q)) (hy2 : IsPGroup 2 (Subgroup.zpowers y)) :
    y ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hyP⟩ := AschbacherTheorem3.exists_isSylowOf_le hy2
    (Subgroup.zpowers_le.mpr hyX)
  obtain ⟨n, hn, ⟨e⟩⟩ := sylow_quaternion_of_unique hXp hX huniq hP
  have h2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hyP' : y ∈ P := hyP (Subgroup.mem_zpowers y)
  have hcent : e ⟨y, hyP'⟩ ∈ Subgroup.center (QuaternionGroup (2 ^ (n - 2))) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨p, rfl⟩ := e.surjective q
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hyc p (hP.le p.2)
  have hsq : (e ⟨y, hyP'⟩) ^ 2 = 1 := by
    rcases AschbacherKnownGroup.RankOne.quaternion_central (2 ^ (n - 2)) h2 _ hcent with h | h
    · rw [h, one_pow]
    · rw [h, pow_two, QuaternionGroup.a_mul_a, ← Nat.cast_add, ← two_mul,
        ZMod.natCast_self, QuaternionGroup.one_def]
  have : (⟨y, hyP'⟩ : P) ^ 2 = 1 := by
    rw [← map_eq_one_iff e e.injective, map_pow]
    exact hsq
  have := congrArg Subtype.val this
  simpa using this

theorem not_mem_centralizer_of_orderOf_four {X : Subgroup Q} (hXp : Group.IsPerfect X)
    (hX : X ≠ ⊥) {c : Q} (huniq : ∀ x ∈ X, orderOf x = 2 → x = c) {y : Q} (hyX : y ∈ X)
    (hy4 : orderOf y = 4) : y ∉ Subgroup.centralizer (X : Set Q) := by
  intro hyc
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hy4]; norm_num)
  have hsq := sq_eq_one_of_mem_centralizer hXp hX huniq hyX hyc hy2
  have := orderOf_dvd_of_pow_eq_one hsq
  rw [hy4] at this
  norm_num at this

theorem exists_orderOf_four_fixed_or_inverted_mem {X : Subgroup Q} (hXp : Group.IsPerfect X)
    (hX : X ≠ ⊥) {c : Q} (hcX : c ∈ X) (hc2 : orderOf c = 2)
    (huniq : ∀ x ∈ X, orderOf x = 2 → x = c) (σ : MulAut Q) (hσ : ∀ q, σ (σ q) = q)
    (hσX : X.map σ.toMonoidHom = X) :
    ∃ y ∈ X, orderOf y = 4 ∧ (σ y = y ∨ σ y = y⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α : MulAut X := (MulEquiv.subgroupMap σ X).trans (MulEquiv.subgroupCongr hσX)
  have hα : α ^ 2 = 1 := by
    ext x
    change σ (σ x) = x
    exact hσ x
  obtain ⟨P0, hP0⟩ := AschbacherToolkit.exists_invariant_sylow_two α hα
  set P := (P0 : Subgroup X).map X.subtype
  have hP : IsSylowOf 2 P X := ⟨P0, rfl⟩
  have hq := sylow_quaternion_of_unique hXp hX huniq hP
  have hcP : c ∈ P := by
    have hcz : (⟨c, hcX⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact unique_involution_central hcX hc2 huniq x.2
    have hzn : (Subgroup.zpowers (⟨c, hcX⟩ : X)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcz)
    have hz2 : IsPGroup 2 (Subgroup.zpowers (⟨c, hcX⟩ : X)) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hc2, pow_one])
    exact ⟨_, hz2.le_sylow_of_normal P0 (Subgroup.mem_zpowers _), rfl⟩
  have hσP : ∀ x ∈ P, σ x ∈ P := by
    rintro _ ⟨p, hp, rfl⟩
    have hmem : α p ∈ (P0 : Subgroup X) := by
      rw [← hP0]
      exact Subgroup.mem_map_of_mem _ hp
    exact ⟨α p, hmem, rfl⟩
  obtain ⟨y, hyP, hy4, hy⟩ := exists_orderOf_four_fixed_or_inverted hP.isPGroup
    (eight_le_card_of_quaternion hq) hcP hc2 (fun x hx hx2 => huniq x (hP.le hx) hx2)
    σ.toMonoidHom hσ hσP
  exact ⟨y, hP.le hyP, hy4, hy⟩

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
