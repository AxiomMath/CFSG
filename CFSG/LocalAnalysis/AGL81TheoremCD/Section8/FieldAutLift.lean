module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K7145Comp
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.KFacts.K72List

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.ComponentClassification CFSG.RankThree.PartTwo.KFacts

theorem eq_one_of_mem_center_of_isComponent {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hr : CFSG.Open.pRank 3 L ≤ 1) {z : L}
    (hz : z ∈ Subgroup.center L) (hz3 : z ^ 3 = 1) : z = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine eq_one_of_mem_center_of_isCyclic_sylow (Group.isPerfect_def.mp hL.1.1) (fun Q => ?_) hz
    hz3
  refine CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_sylow_of_pRank_le_one
    Nat.prime_three (by norm_num) ?_ Q
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact hr

theorem not_three_dvd_card_center_of_isComponent {X : Type*} [Group X] [Finite X]
    {L : Subgroup X} (hL : CFSG.IsComponent L) (hr : CFSG.Open.pRank 3 L ≤ 1) :
    ¬ 3 ∣ Nat.card (Subgroup.center L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hz1 : z = 1 := Subtype.ext (eq_one_of_mem_center_of_isComponent hL hr z.2 (by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]))
  rw [hz1, orderOf_one] at hz
  norm_num at hz

theorem pRank_quotient_center_eq_one_of_isComponent {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hL : CFSG.IsComponent L) (hr : CFSG.Open.pRank 3 L = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) = 1 := by
  have h3 : 3 ∣ Nat.card L := CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three hr.ge
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)] at h3
  exact le_antisymm (CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.pRank_quotient_center_le_one
    Nat.prime_three (by norm_num) L hr.le) (CFSG.one_le_pRank_of_dvd_card Nat.prime_three
      (((Nat.Prime.dvd_mul Nat.prime_three).mp h3).resolve_right
        (not_three_dvd_card_center_of_isComponent hL hr.le)))

theorem not_isInnerAut_centerQuotientHom {X : Type*} [Group X] (L : Subgroup X) [L.Normal]
    [Group.IsPerfect L] {a : X} (ha : a ∉ L ⊔ Subgroup.centralizer (L : Set X)) :
    ¬ IsInnerAut (PerfectAutomorphisms.centerQuotientHom L (MulAut.conjNormal a)) := fun h =>
  ha (CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.mem_sup_centralizer_of_outerAction_eq_one L
    (x := a) ((QuotientGroup.eq_one_iff (N := OuterAutomorphisms.inner (L ⧸ Subgroup.center L))
      (PerfectAutomorphisms.centerQuotientHom L (MulAut.conjNormal a))).mpr h))

theorem exists_commute_mk_eq_of_fixed {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    [L.Normal] (hZ : ¬ 3 ∣ Nat.card (Subgroup.center L)) {a : X} (ha3 : a ^ 3 = 1) (t₀ : L)
    (ht₀ : PerfectAutomorphisms.centerQuotientHom L (MulAut.conjNormal a)
      (QuotientGroup.mk' (Subgroup.center L) t₀) = QuotientGroup.mk' (Subgroup.center L) t₀) :
    ∃ t : L, QuotientGroup.mk' (Subgroup.center L) t = QuotientGroup.mk' (Subgroup.center L) t₀ ∧
      (t : X) * a = a * t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers a) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card (Subgroup.zpowers a) ∣ 3 ^ 1 by
        rw [Nat.card_zpowers, pow_one]
        exact orderOf_dvd_of_pow_eq_one ha3)
    exact IsPGroup.of_card hk
  obtain ⟨φ, hφ⟩ : ∃ φ : Subgroup.zpowers a →* MulAut L,
      ∀ g : Subgroup.zpowers a, φ g = MulAut.conjNormal (g : X) :=
    ⟨MulAut.conjNormal.comp (Subgroup.zpowers a).subtype, fun _ => rfl⟩
  have hpow : ∀ m : ℕ, (PerfectAutomorphisms.centerQuotientHom L (MulAut.conjNormal a) ^ m)
      (QuotientGroup.mk' (Subgroup.center L) t₀) = QuotientGroup.mk' (Subgroup.center L) t₀ := by
    intro m
    induction m with
    | zero => rw [pow_zero, MulAut.one_apply]
    | succ m ih => rw [pow_succ, MulAut.mul_apply, ht₀, ih]
  have hφN : ∀ g, ∀ n ∈ Subgroup.center L, φ g n ∈ Subgroup.center L := by
    intro g n hn
    rw [Subgroup.mem_center_iff] at hn ⊢
    intro y
    obtain ⟨y', rfl⟩ := (φ g).surjective y
    rw [← map_mul, ← map_mul, hn]
  have hy : ∀ g, ((φ g t₀ : L) : L ⧸ Subgroup.center L) = (t₀ : L ⧸ Subgroup.center L) := by
    intro g
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr g.2)
    rw [hφ, ← hm, map_pow]
    have h1 := PerfectAutomorphisms.onCenterQuotient_apply_mk (MulAut.conjNormal a ^ m) t₀
    rw [show PerfectAutomorphisms.onCenterQuotient (MulAut.conjNormal a ^ m) =
      PerfectAutomorphisms.centerQuotientHom L (MulAut.conjNormal a) ^ m from
        map_pow (PerfectAutomorphisms.centerQuotientHom L) _ m, hpow m] at h1
    exact h1.symm
  obtain ⟨t, ht, hfix⟩ := exists_fixed_of_coprime hP φ (Subgroup.center L) hZ hφN t₀ hy
  refine ⟨t, ht, ?_⟩
  have h : a * (t : X) * a⁻¹ = t := by
    have h' := congrArg Subtype.val (hfix ⟨a, Subgroup.mem_zpowers a⟩)
    rwa [hφ, MulAut.conjNormal_apply] at h'
  calc (t : X) * a = a * t * a⁻¹ * a := by rw [h]
    _ = a * t := by group

theorem mul_mul_inv_eq_inv_of_mk_center {L : Type*} [Group L]
    (hZ : ∀ z ∈ Subgroup.center L, z ^ 3 = 1 → z = 1) {t u : L} (hu3 : u ^ 3 = 1)
    (h : QuotientGroup.mk' (Subgroup.center L) t * QuotientGroup.mk' (Subgroup.center L) u *
      (QuotientGroup.mk' (Subgroup.center L) t)⁻¹ = (QuotientGroup.mk' (Subgroup.center L) u)⁻¹) :
    t * u * t⁻¹ = u⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨c, hc, hc'⟩ := h
  have h1 : t * u * t⁻¹ = u⁻¹ * c⁻¹ := eq_mul_inv_of_mul_eq hc'
  have hcomm : Commute u⁻¹ c⁻¹ := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) u⁻¹
  have h2 : (t * u * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hu3, mul_one, mul_inv_cancel]
  rw [h1, hcomm.mul_pow, inv_pow, hu3, inv_one, one_mul, inv_pow, inv_eq_one] at h2
  rw [h1, hZ c hc h2, inv_one, mul_one]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
