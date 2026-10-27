module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BTClass

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

private theorem sec5c3q_conjClass_eq_of_mem {N : Subgroup G} {x x' y : G}
    (hx : y ∈ conjClassIn N x) (hx' : y ∈ conjClassIn N x') :
    conjClassIn N x = conjClassIn N x' := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hab⟩ := hx'
  have hxx : x = (a⁻¹ * b) * x' * (a⁻¹ * b)⁻¹ := by
    calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
      _ = a⁻¹ * (b * x' * b⁻¹) * a := by rw [hab]
      _ = (a⁻¹ * b) * x' * (a⁻¹ * b)⁻¹ := by group
  have hx'x : x' = (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ := by
    calc x' = b⁻¹ * (b * x' * b⁻¹) * b := by group
      _ = b⁻¹ * (a * x * a⁻¹) * b := by rw [← hab]
      _ = (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ := by group
  ext w
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n * (a⁻¹ * b), N.mul_mem hn (N.mul_mem (N.inv_mem ha) hb), ?_⟩
    rw [hxx]
    group
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n * (b⁻¹ * a), N.mul_mem hn (N.mul_mem (N.inv_mem hb) ha), ?_⟩
    rw [hx'x]
    group

private theorem sec5c3q_conjClass_subset {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1) :
    conjClassIn (normalizer (A : Set G)) x ⊆ (A : Set G) \ {1} := by
  rintro y ⟨m, hmM, rfl⟩
  refine ⟨(Subgroup.mem_normalizer_iff.mp hmM x).mp hxA, ?_⟩
  intro h1
  rw [Set.mem_singleton_iff] at h1
  apply hx1
  calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
    _ = 1 := by rw [h1]; group

theorem sec5c3q_s59_tzM_bounds (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ)
    (h7 : (conjClassIn (normalizer (A : Set G)) t).ncard = 7) {g₀ : G}
    (hg₀ : g₀⁻¹ * t * g₀ = t * z) :
    15 ≤ (conjClassIn (normalizer (A : Set G)) (t * z)).ncard ∧
      (conjClassIn (normalizer (A : Set G)) (t * z)).ncard ≤ 21 := by
  have hnt := sec5_t_not_conj_z hy.h37 hR.toSec5Ctx
  have ht2 : orderOf t = 2 := hR.involution
  have hz2 : orderOf z = 2 := hR.pocket.1
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have htz1 : t * z ≠ 1 := by
    intro h
    have hzt : z = t := by
      calc z = t * (t * z) := by rw [← mul_assoc, htt, one_mul]
        _ = t := by rw [h, mul_one]
    exact hnt 1 (by rw [hzt]; group)
  have htA := hm.mem_A.1
  have hzA := hm.mem_A.2.2
  have htzA : t * z ∈ A := A.mul_mem htA hzA
  have hW2 : wclass φ 2 ⊆ conjClassIn (normalizer (A : Set G)) (t * z) :=
    hm.perm.wclass_subset_of_inter
      (fun a ha x hx => by
        obtain ⟨n, hn, rfl⟩ := hx
        exact ⟨(a : G) * n, (normalizer (A : Set G)).mul_mem (Subgroup.mem_inf.mp ha).2 hn,
          by group⟩)
      ⟨t * z, ⟨1, one_mem _, by group⟩, hm.tz_mem_wclass⟩
  have h15 : 15 ≤ (conjClassIn (normalizer (A : Set G)) (t * z)).ncard := by
    have h := Set.ncard_le_ncard hW2 (Set.toFinite _)
    rw [hm.perm.ncard_wclass 2] at h
    simpa [Nat.choose] using h
  refine ⟨h15, ?_⟩
  have hTU : Disjoint (conjClassIn (normalizer (A : Set G)) (t * z))
      (conjClassIn (normalizer (A : Set G)) t) := by
    rw [Set.disjoint_left]
    intro y hyT hyU
    have heq := sec5c3q_conjClass_eq_of_mem hyT hyU
    rw [heq, h7] at h15
    omega
  have hTZ : Disjoint (conjClassIn (normalizer (A : Set G)) (t * z))
      (conjClassIn (normalizer (A : Set G)) z) := by
    rw [Set.disjoint_left]
    rintro y ⟨m, -, hm1⟩ ⟨m', -, hm2⟩
    refine hnt (g₀ * m⁻¹ * m')⁻¹ ?_
    rw [inv_inv]
    calc (g₀ * m⁻¹ * m') * z * (g₀ * m⁻¹ * m')⁻¹
        = g₀ * m⁻¹ * (m' * z * m'⁻¹) * m * g₀⁻¹ := by group
      _ = g₀ * m⁻¹ * (m * (t * z) * m⁻¹) * m * g₀⁻¹ := by rw [← hm2, hm1]
      _ = g₀ * (g₀⁻¹ * t * g₀) * g₀⁻¹ := by rw [hg₀]; group
      _ = t := by group
  have hUZ : Disjoint (conjClassIn (normalizer (A : Set G)) t)
      (conjClassIn (normalizer (A : Set G)) z) := by
    rw [Set.disjoint_left]
    rintro y ⟨m, -, hm1⟩ ⟨m', -, hm2⟩
    refine hnt (m⁻¹ * m')⁻¹ ?_
    rw [inv_inv]
    calc (m⁻¹ * m') * z * (m⁻¹ * m')⁻¹ = m⁻¹ * (m' * z * m'⁻¹) * m := by group
      _ = m⁻¹ * (m * t * m⁻¹) * m := by rw [← hm2, hm1]
      _ = t := by group
  have hsub : conjClassIn (normalizer (A : Set G)) (t * z) ∪
      conjClassIn (normalizer (A : Set G)) t ∪ conjClassIn (normalizer (A : Set G)) z ⊆
        (A : Set G) \ {1} :=
    Set.union_subset (Set.union_subset (sec5c3q_conjClass_subset htzA htz1)
      (sec5c3q_conjClass_subset htA ht1)) (sec5c3q_conjClass_subset hzA hz1)
  have hA63 : ((A : Set G) \ {1}).ncard = 63 := by
    have hA64 : (A : Set G).ncard = 64 := by
      rw [← Nat.card_coe_set_eq]
      exact hm.perm.card_A
    rw [Set.ncard_diff_singleton_of_mem A.one_mem, hA64]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hTZ, hUZ⟩), Set.ncard_union_eq hTU,
    sec5b_zM_ncard hy hR hm, h7, hA63] at hle
  omega

theorem sec5c3q_s59_card_cases (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) :
    (conjClassIn (normalizer (A : Set G)) t).ncard = 28 ∨
      (conjClassIn (normalizer (A : Set G)) t).ncard = 7 ∨
      (conjClassIn (normalizer (A : Set G)) t).ncard = 13 ∨
      (conjClassIn (normalizer (A : Set G)) t).ncard = 22 := by
  rcases sec5b_tM_cases hy hR hm with h | h | h | h
  · left
    rw [h]
    have hd12 : Disjoint (wclass φ 1) (wclass φ 2) := hm.perm.disjoint_wclass (by norm_num)
    have hd15 : Disjoint (wclass φ 1) (wclass φ 5) := hm.perm.disjoint_wclass (by norm_num)
    have hd16 : Disjoint (wclass φ 1) (wclass φ 6) := hm.perm.disjoint_wclass (by norm_num)
    have hd25 : Disjoint (wclass φ 2) (wclass φ 5) := hm.perm.disjoint_wclass (by norm_num)
    have hd26 : Disjoint (wclass φ 2) (wclass φ 6) := hm.perm.disjoint_wclass (by norm_num)
    have hd56 : Disjoint (wclass φ 5) (wclass φ 6) := hm.perm.disjoint_wclass (by norm_num)
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨hd16, hd26⟩, hd56⟩)]
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hd15, hd25⟩)]
    rw [Set.ncard_union_eq hd12]
    rw [IsPerm6.ncard_wclass hm.perm 1, IsPerm6.ncard_wclass hm.perm 2,
      IsPerm6.ncard_wclass hm.perm 5, IsPerm6.ncard_wclass hm.perm 6]
    norm_num [Nat.choose]
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem sec5c3q_s59_orbit_contra (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ)
    (h7 : (conjClassIn (normalizer (A : Set G)) t).ncard = 7) {g₀ : G}
    (hg₀ : g₀⁻¹ * t * g₀ = t * z) {L' S' : Subgroup G} {z' a : G} {B' : Subgroup G}
    {φ' : (Fin 6 → ZMod 2) → G} (hR' : Sec5RCtx G (t * z) L' S' z' a B' A)
    (hm' : Sec5Model58 (t * z) L' z' a A φ') : False := by
  obtain ⟨h15, h21⟩ := sec5c3q_s59_tzM_bounds hy hR hm h7 hg₀
  rcases sec5c3q_s59_card_cases hy hR' hm' with h | h | h | h <;> omega

end CFSG.OddStandard.SmallF3.Omega
