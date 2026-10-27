module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallVerdictSound
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import Certificates.Certificate9743
public import Certificates.Certificate9744

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 Check

theorem u33_check_9743 :
    goodCheck 100 (elemsT QP) = true :=
  Certificates.certificate9743

theorem u33_check_9744 :
    verdictCheck 100 (elemsT QP) (elemsT QA) false (pickReps (elemsT QA)) = true :=
  Certificates.certificate9744

theorem concreteLeaf_u33 :
    ConcreteLeaf (Equiv.Perm (Fin 28)) QP.originalSubgroup QA.originalSubgroup := by
  intro X hPX hXA R S t hd hc hE2
  have hP : Nat.card QP.originalSubgroup = 6048 := by rw [card_group QP QP_ok, QP_valid.2]
  have hA : Nat.card QA.originalSubgroup = 12096 := by rw [card_group QA QA_ok, QA_valid.2]
  obtain ⟨k, hk⟩ : 6048 ∣ Nat.card X := hP ▸ Subgroup.card_dvd_of_le hPX
  have h2 : Nat.card X ∣ 12096 := hA ▸ Subgroup.card_dvd_of_le hXA
  have hk2 : k ∣ 2 := by
    rw [hk] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 6048) (by simpa using h2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
  ·
    have hXP : QP.originalSubgroup = X :=
      Subgroup.eq_of_le_of_card_ge hPX (by rw [hk, hP])
    subst hXP
    refine Or.inr (good_of_goodCheck (ι := QP.originalSubgroup.subtype) Subtype.val_injective
      (fun m => ?_) u33_check_9743 hd hc.1)
    rw [mem_elemsT QP QP_ok m]
    exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  ·
    have hXA' : X = QA.originalSubgroup :=
      Subgroup.eq_of_le_of_card_ge hXA (by rw [hk, hA])
    subst hXA'
    set N : Subgroup QA.originalSubgroup := QP.originalSubgroup.subgroupOf QA.originalSubgroup
      with hNdef
    have hNcard : Nat.card N = 6048 := by
      rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hP]
    have hidx : N.index = 2 := by
      have h := Subgroup.card_mul_index N
      rw [hNcard, hA] at h
      omega
    have hN : N.Normal := Subgroup.normal_of_index_eq_two hidx
    have hNtop : N ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hidx
      omega
    exact phi_all_of_verdictCheck (ι := QA.originalSubgroup.subtype) Subtype.val_injective
      (fun m => by
        rw [mem_elemsT QA QA_ok m]
        exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
      (by norm_num) (N := N) (LN := elemsT QP)
      (fun y => by rw [mem_elemsT QP QP_ok, hNdef, Subgroup.mem_subgroupOf]; rfl) hN hNtop
      (fun h => absurd h (by decide)) u33_check_9744 hd.order R S hd hc hE2

section Leaf


theorem smallSimpleLeaf_u33_of_check :
    SmallSimpleLeaf fun F _ => CFSG.Blueprint.LieModel F .PSU 3 3 1 :=
  smallSimpleLeaf_u33 concreteLeaf_u33

end Leaf

end CFSG.ClassicalInvolution.Q3.TA3
