module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem invol_orderOf_eq_two_pow {P : Subgroup K} (hP : IsPGroup 2 P) {g : K} (hg : g ∈ P) :
    ∃ k : ℕ, orderOf g = 2 ^ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨g, hg⟩
  exact ⟨k, (Subgroup.orderOf_mk g hg).symm.trans hk⟩

theorem invol_central_involution {P : Subgroup K} [Nontrivial P] (hP : IsPGroup 2 P) :
    ∃ u ∈ P, u ^ 2 = 1 ∧ u ≠ 1 ∧ ∀ g ∈ P, g * u = u * g := by
  haveI : Nontrivial (Subgroup.center ↥P) := IsPGroup.center_nontrivial hP
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
  obtain ⟨w, hwP, hw1, hwc⟩ : ∃ w ∈ P, w ≠ 1 ∧ ∀ g ∈ P, g * w = w * g := by
    refine ⟨((z : ↥P) : K), (z : ↥P).2, fun h => hz (Subtype.ext (Subtype.ext h)), ?_⟩
    intro g hg
    have hc := Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩
    exact congrArg Subtype.val hc
  obtain ⟨k, hk⟩ := invol_orderOf_eq_two_pow hP hwP
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hw1
    apply orderOf_eq_one_iff.mp
    rw [hk, pow_zero]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkey : 2 ^ j * 2 = orderOf w := by
    rw [hk]
    ring
  refine ⟨w ^ 2 ^ j, P.pow_mem hwP _, ?_, ?_, ?_⟩
  · rw [← pow_mul, hkey, pow_orderOf_eq_one]
  · apply pow_ne_one_of_lt_orderOf
    · positivity
    · rw [hk]
      have h0 : 0 < 2 ^ j := by positivity
      rw [pow_succ]
      omega
  · intro g hg
    exact (Commute.pow_right (show Commute g w from hwc g hg) _).eq

theorem exists_commuting_involutions {P : Subgroup K} (hP : IsPGroup 2 P) {e e' : K}
    (he : e ∈ P) (he' : e' ∈ P) (he2 : e ^ 2 = 1) (he'2 : e' ^ 2 = 1) (he1 : e ≠ 1)
    (he'1 : e' ≠ 1) (hne : e ≠ e') :
    ∃ e₁ ∈ P, ∃ e₂ ∈ P, e₁ ^ 2 = 1 ∧ e₂ ^ 2 = 1 ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ ∧
      e₁ * e₂ = e₂ * e₁ := by
  haveI : Nontrivial P := ⟨⟨⟨e, he⟩, 1, fun h => he1 (congrArg Subtype.val h)⟩⟩
  obtain ⟨u, huP, hu2, hu1, huc⟩ := invol_central_involution hP
  by_cases hue : u = e
  · refine ⟨e', he', e, he, he'2, he2, he'1, he1, Ne.symm hne, ?_⟩
    have h := huc e' he'
    rw [hue] at h
    exact h
  · exact ⟨e, he, u, huP, he2, hu2, he1, hu1, Ne.symm hue, huc e he⟩

theorem exists_sq_eq_of_not_isCyclic {C : Subgroup K} (hC : IsPGroup 2 C) {t : K} (ht : t ∈ C)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (huniq : ∀ e ∈ C, e ^ 2 = 1 → e = 1 ∨ e = t)
    (hnc : ¬ IsCyclic C) : ∃ c ∈ C, c ^ 2 = t := by
  obtain ⟨x, hxC, hxt⟩ : ∃ x ∈ C, x ∉ Subgroup.zpowers t := by
    by_contra hcon
    push Not at hcon
    apply hnc
    refine ⟨⟨⟨t, ht⟩, fun y => ?_⟩⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcon y.1 y.2)
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  obtain ⟨k, hk⟩ := invol_orderOf_eq_two_pow hC hxC
  have hx1 : x ≠ 1 := fun h => hxt (by rw [h]; exact Subgroup.one_mem _)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    · exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk))
    · have hx2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hk]; norm_num)
      rcases huniq x hxC hx2 with h | h
      · exact hx1 h
      · exact hxt (by rw [h]; exact Subgroup.mem_zpowers t)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hsq : (x ^ 2 ^ m) ^ 2 = x ^ 2 ^ (m + 1) := by
    rw [← pow_mul, ← pow_succ]
  have hy2 : ((x ^ 2 ^ m) ^ 2) ^ 2 = 1 := by
    have hkey : 2 ^ (m + 1) * 2 = orderOf x := by
      rw [hk]
      ring
    rw [hsq, ← pow_mul, hkey, pow_orderOf_eq_one]
  have hy1 : (x ^ 2 ^ m) ^ 2 ≠ 1 := by
    rw [hsq]
    have h0 : 0 < 2 ^ (m + 1) := by positivity
    have h1 : orderOf x = 2 ^ (m + 1) * 2 := by
      rw [hk]
      ring
    apply pow_ne_one_of_lt_orderOf
    · positivity
    · rw [h1]
      omega
  have hmem : (x ^ 2 ^ m) ^ 2 ∈ C := C.pow_mem (C.pow_mem hxC _) _
  refine ⟨x ^ 2 ^ m, C.pow_mem hxC _, ?_⟩
  rcases huniq _ hmem hy2 with h | h
  · exact absurd h hy1
  · exact h
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem exists_mem_not_mem_commutator_mem {N R Z : Subgroup K} (hN : IsPGroup 2 N) (hRN : R ≤ N)
    (hNR : N ≤ normalizer (R : Set K)) (hZR : Z ≤ R)
    (hZ : ∀ n ∈ N, ∀ y ∈ Z, n * y = y * n) (hRZ : ¬ R ≤ Z) :
    ∃ r ∈ R, r ∉ Z ∧ ∀ n ∈ N, ⁅r, n⁆ ∈ Z := by
  clear hZR
  have hZN : (Z.subgroupOf N).Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    have hc : (g : K) * (y : K) = (y : K) * (g : K) := hZ g g.2 y hy
    show (g : K) * (y : K) * (g : K)⁻¹ ∈ Z
    rw [hc, mul_inv_cancel_right]
    exact hy
  have hRnorm : (R.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hRN).mpr hNR
  haveI : (Z.subgroupOf N).Normal := hZN
  have hQnil : Group.IsNilpotent (↥N ⧸ Z.subgroupOf N) :=
    IsPGroup.isNilpotent (hN.to_quotient (Z.subgroupOf N))
  haveI : Group.IsNilpotent (↥N ⧸ Z.subgroupOf N) := hQnil
  let π : ↥N →* ↥N ⧸ Z.subgroupOf N := QuotientGroup.mk' (Z.subgroupOf N)
  have hR'norm : ((R.subgroupOf N).map π).Normal :=
    hRnorm.map π (QuotientGroup.mk'_surjective (Z.subgroupOf N))
  haveI : ((R.subgroupOf N).map π).Normal := hR'norm
  have hR'ne : (R.subgroupOf N).map π ≠ ⊥ := by
    intro h
    obtain ⟨r0, hr0R, hr0Z⟩ := SetLike.not_le_iff_exists.mp hRZ
    have hmem : π ⟨r0, hRN hr0R⟩ ∈ (R.subgroupOf N).map π :=
      Subgroup.mem_map_of_mem _ (mem_subgroupOf.mpr hr0R)
    rw [h, Subgroup.mem_bot] at hmem
    apply hr0Z
    have h1 : (⟨r0, hRN hr0R⟩ : ↥N) ∈ Z.subgroupOf N :=
      (QuotientGroup.eq_one_iff (N := Z.subgroupOf N) _).mp hmem
    exact mem_subgroupOf.mp h1
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hR'ne)
  have hx1 : (a : ↥N ⧸ Z.subgroupOf N) ≠ 1 := fun h => ha (Subtype.ext h)
  obtain ⟨hxR', hxc⟩ := Subgroup.mem_inf.mp a.2
  obtain ⟨r', hr'R, hr'x⟩ := Subgroup.mem_map.mp hxR'
  have hrZ : (r' : K) ∉ Z := by
    intro hr
    apply hx1
    rw [← hr'x]
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf N) r').mpr (mem_subgroupOf.mpr hr)
  refine ⟨(r' : K)⁻¹, R.inv_mem (mem_subgroupOf.mp hr'R), fun hr => hrZ (Z.inv_mem_iff.mp hr),
    fun n hn => ?_⟩
  obtain ⟨h, rfl⟩ : ∃ h : ↥N, (h : K) = n := ⟨⟨n, hn⟩, rfl⟩
  have hcn : ((h⁻¹ : ↥N) : ↥N ⧸ Z.subgroupOf N) * (a : ↥N ⧸ Z.subgroupOf N) =
      (a : ↥N ⧸ Z.subgroupOf N) * ((h⁻¹ : ↥N) : ↥N ⧸ Z.subgroupOf N) :=
    Subgroup.mem_center_iff.mp hxc _
  rw [← hr'x] at hcn
  have h2 : ((h⁻¹ * r' : ↥N) : ↥N ⧸ Z.subgroupOf N) = ((r' * h⁻¹ : ↥N) : ↥N ⧸ Z.subgroupOf N) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hcn
  have h3 : (h⁻¹ * r')⁻¹ * (r' * h⁻¹) ∈ Z.subgroupOf N := QuotientGroup.eq.mp h2
  have e : (h⁻¹ * r')⁻¹ * (r' * h⁻¹) = ⁅r'⁻¹, h⁆ := by
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
  rw [e] at h3
  have h5 : ((⁅r'⁻¹, h⁆ : ↥N) : K) = ⁅((r'⁻¹ : ↥N) : K), (h : K)⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  have h6 : ((⁅r'⁻¹, h⁆ : ↥N) : K) ∈ Z := mem_subgroupOf.mp h3
  rw [h5, Subgroup.coe_inv] at h6
  exact h6
end

section
open Subgroup

variable {K : Type} [Group K] [Finite K]

@[instance_reducible]
def fixedPt_conjAct (V : Subgroup K) {z : K} (hzV : zpowers z ≤ normalizer (V : Set K)) :
    MulAction ↥(zpowers z) ↥V where
  smul g v := ⟨(g : K) * v * (g : K)⁻¹, (Subgroup.mem_normalizer_iff.mp (hzV g.2) v).mp v.2⟩
  one_smul v := Subtype.ext (by
    show ((1 : ↥(zpowers z)) : K) * (v : K) * ((1 : ↥(zpowers z)) : K)⁻¹ = (v : K)
    simp)
  mul_smul g h v := Subtype.ext (by
    show ((g * h : ↥(zpowers z)) : K) * (v : K) * ((g * h : ↥(zpowers z)) : K)⁻¹
      = (g : K) * ((h : K) * (v : K) * (h : K)⁻¹) * (g : K)⁻¹
    simp [mul_assoc])

theorem card_modEq_card_inf_centralizer {V : Subgroup K} {z : K} {p : ℕ} (hp : p.Prime)
    (hz : z ^ p = 1) (hzV : z ∈ normalizer (V : Set K)) :
    Nat.card V ≡ Nat.card ↥(V ⊓ centralizer ({z} : Set K)) [MOD p] := by
  haveI hfact : Fact p.Prime := ⟨hp⟩
  have hGV : zpowers z ≤ normalizer (V : Set K) := Subgroup.zpowers_le.mpr hzV
  letI hact : MulAction ↥(zpowers z) ↥V := fixedPt_conjAct V hGV
  have hpow : ∀ n : ℤ, (z ^ n) ^ p = 1 := by
    intro n
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  have hG : IsPGroup p ↥(zpowers z) := by
    refine fun g => ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hn]
    exact hpow n
  have hfix : ∀ v : ↥V, v ∈ MulAction.fixedPoints ↥(zpowers z) ↥V ↔
      (v : K) ∈ centralizer ({z} : Set K) := by
    intro v
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      have hz' : (⟨z, Subgroup.mem_zpowers z⟩ : ↥(zpowers z)) • v = v := h _
      have hconj : z * (v : K) * z⁻¹ = v := congrArg Subtype.val hz'
      exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hconj).symm
    · intro hc g
      apply Subtype.ext
      have hzc : zpowers z ≤ centralizer ({(v : K)} : Set K) :=
        Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hc).symm)
      show (g : K) * (v : K) * (g : K)⁻¹ = (v : K)
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp (hzc g.2))
  have he : Nat.card ↥(MulAction.fixedPoints ↥(zpowers z) ↥V)
      = Nat.card ↥(V ⊓ centralizer ({z} : Set K)) :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : K), Subgroup.mem_inf.mpr ⟨x.1.2, (hfix x.1).mp x.2⟩⟩
        invFun := fun y =>
          ⟨⟨(y : K), (Subgroup.mem_inf.mp y.2).1⟩,
            (hfix ⟨(y : K), (Subgroup.mem_inf.mp y.2).1⟩).mpr (Subgroup.mem_inf.mp y.2).2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  have h1 := IsPGroup.card_modEq_card_fixedPoints hG ↥V
  rw [he] at h1
  exact h1
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
