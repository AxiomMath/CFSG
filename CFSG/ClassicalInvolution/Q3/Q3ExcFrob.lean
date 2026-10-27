module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ClassicalInvolution.Q3

open scoped Pointwise
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Torus

variable {τ : Tag} {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

theorem exc3_entrywiseFrob_of_mem_torus (e : ℕ) {t : ModGL τ k} (ht : t ∈ torusGroup τ k) :
    entrywiseFrobGL τ k p e t = t ^ (p ^ e) := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [entrywiseFrobGL_rootDiagUnit_eq_map]
  have h : (rootDiagUnit τ a) ^ (p ^ e) = rootDiagUnit τ (a ^ (p ^ e)) :=
    (map_pow (rootDiagUnitHom τ k) a (p ^ e)).symm
  rw [h]
  congr 1

variable {p}

theorem exc3_frobTwist_sq_of_mem_torus (e : ℕ) {c : ModGL τ k}
    (hcT : c ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hc2 : c * c ∈ torusGroup τ k) {t : ModGL τ k} (ht : t ∈ torusGroup τ k) :
    frobTwistGL τ k p e c (frobTwistGL τ k p e c t) = t ^ ((p ^ e) ^ 2) := by
  have hu : c * t * c⁻¹ ∈ torusGroup τ k := (Subgroup.mem_normalizer_iff.1 hcT t).1 ht
  have h1 : frobTwistGL τ k p e c t = (c * t * c⁻¹) ^ (p ^ e) := by
    rw [frobTwistGL_apply, exc3_entrywiseFrob_of_mem_torus p e ht, conj_pow]
  have huq : (c * t * c⁻¹) ^ (p ^ e) ∈ torusGroup τ k := pow_mem hu _
  rw [h1, frobTwistGL_apply, exc3_entrywiseFrob_of_mem_torus p e huq, ← pow_mul, ← sq]
  have hcomm : c * c * t = t * (c * c) :=
    mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hc2)
      (torusGroup_le_diagonalGroup ht)
  have : c * (c * t * c⁻¹) * c⁻¹ = t := by
    calc c * (c * t * c⁻¹) * c⁻¹ = (c * c) * t * (c * c)⁻¹ := by group
      _ = t := by rw [hcomm]; group
  rw [← conj_pow, this]

theorem exc3_pow_eq_one_of_fixed_torus (e : ℕ) {c : ModGL τ k}
    (hcT : c ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hc2 : c * c ∈ torusGroup τ k) {t : ModGL τ k} (ht : t ∈ torusGroup τ k)
    (hF : frobTwistGL τ k p e c t = t) : t ^ ((p ^ e) ^ 2 - 1) = 1 := by
  have h := exc3_frobTwist_sq_of_mem_torus e hcT hc2 ht
  rw [hF, hF] at h
  have hq : 1 ≤ (p ^ e) ^ 2 := Nat.one_le_pow 2 (p ^ e) (pow_pos (Fact.out : p.Prime).pos e)
  have : t ^ ((p ^ e) ^ 2) = t * t ^ ((p ^ e) ^ 2 - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hq]
  rw [this] at h
  exact (mul_eq_left.mp h.symm)

end Torus

section Product

variable {τ : Tag} {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]

omit [Fact p.Prime] [CharP k p] in
theorem exc3_pow_mul_mem {G : Type*} [Group G] {S T : Subgroup G}
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) {s : G} (hs : s ∈ S) {t : G} (ht : t ∈ T)
    (n : ℕ) : ∃ s' ∈ S, (s * t) ^ n = s' * t ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨s', hs', h⟩ := ih
    have hc : t ^ n * s * (t ^ n)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.1 (hTS (T.pow_mem ht n)) s).1 hs
    refine ⟨s' * (t ^ n * s * (t ^ n)⁻¹), S.mul_mem hs' hc, ?_⟩
    rw [pow_succ, h]
    group

theorem exc3_pow_mem_rootSpan_of_fixed (e : ℕ) {c : ModGL τ k}
    (hcT : c ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hc2 : c * c ∈ torusGroup τ k) {S : Subgroup (ModGL τ k)}
    (hTS : torusGroup τ k ≤ Subgroup.normalizer (S : Set (ModGL τ k)))
    (hFS : ∀ s ∈ S, frobTwistGL τ k p e c s ∈ S) {x : ModGL τ k}
    (hx : x ∈ torusGroup τ k ⊔ S) (hxF : frobTwistGL τ k p e c x = x) :
    x ^ ((p ^ e) ^ 2 - 1) ∈ S := by
  rw [sup_comm] at hx
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left S (torusGroup τ k) hTS
  have hx' : x ∈ (S : Set (ModGL τ k)) * (torusGroup τ k : Set (ModGL τ k)) := by
    rw [← hmul]
    exact hx
  obtain ⟨s, hs, t, ht, hxst⟩ := hx'
  subst hxst
  set F := frobTwistGL τ k p e c with hF
  have hs2 : F (F s) ∈ S := hFS _ (hFS s hs)
  have h1 : F (F (s * t)) = s * t := by rw [hxF, hxF]
  rw [map_mul, map_mul, exc3_frobTwist_sq_of_mem_torus e hcT hc2 ht] at h1
  have hq : 1 ≤ (p ^ e) ^ 2 := Nat.one_le_pow 2 (p ^ e) (pow_pos (Fact.out : p.Prime).pos e)
  have ht1 : t ^ ((p ^ e) ^ 2 - 1) ∈ S := by
    have h2 : t ^ ((p ^ e) ^ 2 - 1) * t = (F (F s))⁻¹ * s * t := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
      have : F (F s) * t ^ ((p ^ e) ^ 2) = s * t := h1
      calc t ^ ((p ^ e) ^ 2) = (F (F s))⁻¹ * (F (F s) * t ^ ((p ^ e) ^ 2)) := by group
        _ = (F (F s))⁻¹ * (s * t) := by rw [this]
        _ = (F (F s))⁻¹ * s * t := by group
    have h3 := mul_right_cancel h2
    rw [h3]
    exact S.mul_mem (S.inv_mem hs2) hs
  obtain ⟨s', hs', h⟩ := exc3_pow_mul_mem hTS hs ht ((p ^ e) ^ 2 - 1)
  rw [h]
  exact S.mul_mem hs' ht1

end Product

end CFSG.ClassicalInvolution.Q3
