module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathEnd
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.ABGLocalTools

variable {Y : Type} [Group Y]

@[expose] def projSub (A B T : Subgroup Y) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Subgroup Y where
  carrier := {a | a ∈ A ∧ ∃ b ∈ B, a * b ∈ T}
  mul_mem' := by
    rintro a₁ a₂ ⟨ha₁, b₁, hb₁, h₁⟩ ⟨ha₂, b₂, hb₂, h₂⟩
    refine ⟨mul_mem ha₁ ha₂, b₁ * b₂, mul_mem hb₁ hb₂, ?_⟩
    have : a₁ * a₂ * (b₁ * b₂) = a₁ * b₁ * (a₂ * b₂) := by
      rw [mul_assoc, ← mul_assoc a₂, hcomm a₂ ha₂ b₁ hb₁]
      group
    rw [this]
    exact mul_mem h₁ h₂
  one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, b, hb, h⟩
    refine ⟨inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
    rw [hcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb), ← mul_inv_rev]
    exact inv_mem h

theorem projSub_le {A B T : Subgroup Y} {hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a} :
    projSub A B T hcomm ≤ A := fun _ h => h.1

theorem isPGroup_projSub {A B T : Subgroup Y} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : Disjoint A B) (hT : IsPGroup 2 T) : IsPGroup 2 (projSub A B T hcomm) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨a, hmem⟩
  obtain ⟨ha, b, hb, hab⟩ := id hmem
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨a * b, hab⟩
  have h1 : (a * b) ^ (2 ^ k) = 1 := by
    have h := pow_orderOf_eq_one (⟨a * b, hab⟩ : T)
    rw [hk] at h
    simpa using congrArg Subtype.val h
  have h2 : a ^ (2 ^ k) * b ^ (2 ^ k) = 1 := by
    rw [← (show Commute a b from hcomm a ha b hb).mul_pow]
    exact h1
  have h3 : a ^ (2 ^ k) = 1 := by
    refine Subgroup.disjoint_def.1 hdisj (pow_mem ha _) ?_
    rw [eq_inv_of_mul_eq_one_left h2]
    exact inv_mem (pow_mem hb _)
  have hdvd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h3
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨j, by rw [Subgroup.orderOf_mk]; exact hj⟩

theorem exists_mul_mem_of_isSylowOf_sup [Finite Y] {A B T : Subgroup Y}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : Disjoint A B)
    (hT : IsSylowOf 2 T (A ⊔ B)) {t : Y} (ht : t ∈ T) :
    ∃ a ∈ T ⊓ A, ∃ b ∈ T ⊓ B, t = a * b := by
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hAB : B ≤ centralizer (A : Set Y) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hcomm a ha b hb
  set TA := projSub A B T hcomm with hTA
  set TB := projSub B A T hcomm' with hTB
  have hpA : IsPGroup 2 TA := isPGroup_projSub hcomm hdisj hT.isPGroup
  have hpB : IsPGroup 2 TB := isPGroup_projSub hcomm' hdisj.symm hT.isPGroup
  have hTAC : TA ≤ centralizer (TB : Set Y) := fun a ha =>
    mem_centralizer_iff.2 fun h hh => (hcomm a (projSub_le ha) h (projSub_le hh)).symm
  have hP : IsPGroup 2 (TA ⊔ TB : Subgroup Y) :=
    hpA.to_sup_of_normal_right' hpB (hTAC.trans (Subgroup.centralizer_le_normalizer _))
  have hmemA : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ T → a ∈ TA := fun a ha b hb h => ⟨ha, b, hb, h⟩
  have hmemB : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ T → b ∈ TB := fun a ha b hb h =>
    ⟨hb, a, ha, by rw [hcomm' b hb a ha]; exact h⟩
  have hle : T ≤ TA ⊔ TB := by
    intro t ht'
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hAB (hT.le ht')
    exact mul_mem (mem_sup_left (hmemA a ha b hb ht')) (mem_sup_right (hmemB a ha b hb ht'))
  have heq : TA ⊔ TB = T :=
    hT.eq_of_le hle (sup_le_sup projSub_le projSub_le) hP
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hAB (hT.le ht)
  exact ⟨a, mem_inf.2 ⟨heq.le (mem_sup_left (hmemA a ha b hb ht)), ha⟩, b,
    mem_inf.2 ⟨heq.le (mem_sup_right (hmemB a ha b hb ht)), hb⟩, rfl⟩

theorem exists_mem_conj_of_wreath_sylow [Finite Y] {N1 N2 T : Subgroup Y} {zb x : Y}
    (hSyl : IsSylowOf 2 T ⊤) (hnorm : (N1 ⊔ N2).Normal) (hdisj : Disjoint N1 N2)
    (hcomm : ∀ a ∈ N1, ∀ b ∈ N2, a * b = b * a) (hz2 : zb * zb = 1)
    (hz1 : ∀ a ∈ N1, zb * a * zb ∈ N2) (hz2' : ∀ b ∈ N2, zb * b * zb ∈ N1)
    (hzT : zb ∈ T) (hxT : x ∈ T) (hx2 : x * x = 1) (hzx : zb * x ∈ N1 ⊔ N2) :
    ∃ b ∈ T, x = b⁻¹ * zb * b := by
  have hS : IsSylowOf 2 (T ⊓ (N1 ⊔ N2)) (N1 ⊔ N2) :=
    hSyl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.2 hnorm])
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_mem_of_isSylowOf_sup hcomm hdisj hS
    (t := zb * x) (mem_inf.2 ⟨T.mul_mem hzT hxT, hzx⟩)
  have ha' := mem_inf.1 ha
  have hb' := mem_inf.1 hb
  have hx : zb * x ∈ (T ⊓ N1) ⊔ (T ⊓ N2) := by
    rw [hab]
    exact mul_mem (mem_sup_left (mem_inf.2 ⟨(mem_inf.1 ha'.1).1, ha'.2⟩))
      (mem_sup_right (mem_inf.2 ⟨(mem_inf.1 hb'.1).1, hb'.2⟩))
  obtain ⟨c, hc, hxc⟩ := involution_conj_of_wreath (S1 := T ⊓ N1) (S2 := T ⊓ N2)
    (hdisj.mono inf_le_right inf_le_right)
    (fun a ha b hb => hcomm a (mem_inf.1 ha).2 b (mem_inf.1 hb).2) hz2
    (fun a ha => mem_inf.2 ⟨T.mul_mem (T.mul_mem hzT (mem_inf.1 ha).1) hzT,
      hz1 a (mem_inf.1 ha).2⟩)
    (fun b hb => mem_inf.2 ⟨T.mul_mem (T.mul_mem hzT (mem_inf.1 hb).1) hzT,
      hz2' b (mem_inf.1 hb).2⟩) hx hx2
  exact ⟨c, (mem_inf.1 hc).1, hxc⟩

end CFSG.EvenSporadicStandard.M23Std
