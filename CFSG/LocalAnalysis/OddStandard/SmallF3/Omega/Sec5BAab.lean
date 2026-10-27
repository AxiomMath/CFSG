module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem sec5b_orderOf_conj_inv (x g : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
  simpa [MulAut.conj_apply] using h

private lemma sec5b_mem_sup_zpowers {r : G} {B : Subgroup G}
    (hrN : zpowers r ≤ Subgroup.normalizer (B : Set G)) {x : G}
    (hx : x ∈ zpowers r ⊔ B) : ∃ n : ℤ, ∃ b ∈ B, x = r ^ n * b := by
  have hx' : x ∈ (zpowers r : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (zpowers r) B hrN]
    exact hx
  rw [Set.mem_mul] at hx'
  obtain ⟨y, hy, b, hb, hyb⟩ := hx'
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨n, b, hb, by rw [← hyb, ← hn]⟩

private lemma sec5b_elemAbelian_sup_zpowers {r : G} {B : Subgroup G}
    (hr2 : r * r = 1) (hBr : ∀ b ∈ B, r * b = b * r)
    (hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBsq : ∀ b ∈ B, b * b = 1) :
    (∀ a ∈ (zpowers r ⊔ B : Subgroup G), ∀ b ∈ (zpowers r ⊔ B : Subgroup G), a * b = b * a) ∧
      ∀ a ∈ (zpowers r ⊔ B : Subgroup G), a * a = 1 := by
  have hrc : r ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hBr b hb).symm
  have hrN : zpowers r ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hrc)
  constructor
  · intro a ha c hc
    obtain ⟨m, b, hb, rfl⟩ := sec5b_mem_sup_zpowers hrN ha
    obtain ⟨n, b', hb', rfl⟩ := sec5b_mem_sup_zpowers hrN hc
    have h1 : Commute (r ^ m) (r ^ n) := Commute.zpow_zpow_self r m n
    have h2 : Commute b (r ^ n) := (show Commute r b from hBr b hb).symm.zpow_right n
    have h3 : Commute (r ^ m) b' := (show Commute r b' from hBr b' hb').zpow_left m
    have h4 : Commute b b' := hBcomm b hb b' hb'
    exact (h1.mul_left h2).mul_right (h3.mul_left h4)
  · intro a ha
    obtain ⟨m, b, hb, rfl⟩ := sec5b_mem_sup_zpowers hrN ha
    have hc : Commute (r ^ m) b := (show Commute r b from hBr b hb).zpow_left m
    have hrm2 : r ^ m * r ^ m = 1 := by
      calc r ^ m * r ^ m = (r ^ m) ^ (2 : ℤ) := by rw [zpow_two]
        _ = r ^ (m * 2) := by rw [← zpow_mul]
        _ = r ^ (2 * m) := by rw [show m * 2 = 2 * m by ring]
        _ = (r ^ (2 : ℤ)) ^ m := by rw [zpow_mul]
        _ = 1 := by rw [show r ^ (2 : ℤ) = 1 by rw [zpow_two, hr2], one_zpow]
    calc (r ^ m * b) * (r ^ m * b)
        = r ^ m * (b * r ^ m) * b := by group
      _ = r ^ m * (r ^ m * b) * b := by rw [← hc.eq]
      _ = (r ^ m * r ^ m) * (b * b) := by group
      _ = 1 := by rw [hrm2, hBsq b hb, mul_one]

theorem sec5b_orderOf_r {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
    (h : Sec5RCtx G t L S z r B A) : orderOf r = 2 := by
  obtain ⟨g, hg⟩ := h.conj_r
  rw [← hg, sec5b_orderOf_conj_inv, h.involution]

theorem sec5b_A_elemAb {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
    (h : Sec5RCtx G t L S z r B A) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a * a = 1 := by
  have hr2 : r * r = 1 := by
    have h2 := pow_orderOf_eq_one r
    rw [sec5b_orderOf_r h] at h2
    simpa [pow_two] using h2
  have hBr : ∀ b ∈ B, r * b = b * r := fun b hb =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h.B_le hb)).2 r (Set.mem_singleton r)
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.B_E32.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsq : ∀ b ∈ B, b * b = 1 := fun b hb => by
    have h2 := h.B_E32.1.2 b hb
    rwa [pow_two] at h2
  obtain ⟨hcomm, hsq⟩ := sec5b_elemAbelian_sup_zpowers hr2 hBr hBcomm hBsq
  have hle : A ≤ zpowers r ⊔ B := le_of_eq h.A_eq
  exact ⟨fun a ha b hb => hcomm a (hle ha) b (hle hb), fun a ha => hsq a (hle ha)⟩

theorem sec5b_card_t_mem {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
    (h : Sec5RCtx G t L S z r B A) : 32 ≤ Nat.card A ∧ t ∈ A := by
  have hBcard : Nat.card B = 32 := by
    rw [h.B_E32.2]
    norm_num
  have hBA : B ≤ A := by
    rw [h.A_eq]
    exact le_sup_right
  exact ⟨hBcard ▸ Subgroup.card_le_of_le hBA, hBA h.B_split.1⟩

theorem sec5b_z_mem_A {t z : G} {A : Subgroup G} (hcard : 32 ≤ Nat.card A)
    (h : Case59Two t z A) : z ∈ A := by
  by_contra hz
  unfold Case59Two at h
  obtain ⟨hc1, _, hc3, _⟩ := h
  have hmiss : conjClassIn (normalizer (A : Set G)) z ∩ (A : Set G) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxC, hxA⟩
    obtain ⟨n, hn, rfl⟩ := hxC
    exact hz ((Subgroup.mem_normalizer_iff.mp hn z).mpr hxA)
  have hdisj : Disjoint (A : Set G) (conjClassIn (normalizer (A : Set G)) z) := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
    exact hmiss
  have hmain : ((A : Set G) \ {1}) \ conjClassIn (normalizer (A : Set G)) z =
      (A : Set G) \ {1} :=
    (hdisj.mono_left Set.sdiff_subset).sdiff_eq_left
  have hcard28 : Set.ncard ((A : Set G) \ {1}) = 28 := by
    rw [← hmain, ← hc1, hc3]
  have hval : Set.ncard ((A : Set G) \ {1}) = Nat.card A - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem A.one_mem]
    rfl
  omega

end CFSG.OddStandard.SmallF3.Omega
