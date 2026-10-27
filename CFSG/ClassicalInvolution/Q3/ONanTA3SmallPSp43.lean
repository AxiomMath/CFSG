module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallVerdictSound
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import Certificates.Certificate9745
public import Certificates.Certificate9746

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43 Check

theorem psp43_check_9745 :
    verdictCheck 100 [(1 : Equiv.Perm (Fin 45))] (elemsT QP45) false (pickReps (elemsT QP45)) =
      true :=
  Certificates.certificate9745

theorem psp43_check_9746 :
    verdictCheck 100 (elemsT QP45) (elemsT QA45) false (pickReps (elemsT QA45)) = true :=
  Certificates.certificate9746

theorem concreteLeaf_psp43 :
    ConcreteLeaf (Equiv.Perm (Fin 45)) QP45.originalSubgroup QA45.originalSubgroup := by
  intro X hPX hXA R S t hd hc hE2
  have hP : Nat.card QP45.originalSubgroup = 25920 := by
    rw [card_group QP45 QP45_ok, QP45_valid.2]
  have hA : Nat.card QA45.originalSubgroup = 51840 := by
    rw [card_group QA45 QA45_ok, QA45_valid.2]
  obtain ⟨k, hk⟩ : 25920 ∣ Nat.card X := hP ▸ Subgroup.card_dvd_of_le hPX
  have h2 : Nat.card X ∣ 51840 := hA ▸ Subgroup.card_dvd_of_le hXA
  have hk2 : k ∣ 2 := by
    rw [hk] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 25920) (by simpa using h2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
  ·
    have hXP : QP45.originalSubgroup = X :=
      Subgroup.eq_of_le_of_card_ge hPX (by rw [hk, hP])
    subst hXP
    have ht1 : t ≠ 1 := fun h => by
      have := hd.order
      rw [h, orderOf_one] at this
      omega
    have hNtop : (⊥ : Subgroup QP45.originalSubgroup) ≠ ⊤ := fun h =>
      ht1 (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_top t))
    exact phi_all_of_verdictCheck (ι := QP45.originalSubgroup.subtype) Subtype.val_injective
      (fun m => by
        rw [mem_elemsT QP45 QP45_ok m]
        exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
      (by norm_num) (N := ⊥) (LN := [1])
      (fun y => by
        rw [List.mem_singleton, Subgroup.mem_bot]
        exact ⟨fun h => Subtype.val_injective (by simpa using h), fun h => by simp [h]⟩)
      Subgroup.normal_bot hNtop (fun h => absurd h (by decide)) psp43_check_9745 hd.order R S hd
      hc hE2
  ·
    have hXA' : X = QA45.originalSubgroup :=
      Subgroup.eq_of_le_of_card_ge hXA (by rw [hk, hA])
    subst hXA'
    set N : Subgroup QA45.originalSubgroup := QP45.originalSubgroup.subgroupOf QA45.originalSubgroup
      with hNdef
    have hNcard : Nat.card N = 25920 := by
      rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hP]
    have hidx : N.index = 2 := by
      have h := Subgroup.card_mul_index N
      rw [hNcard, hA] at h
      omega
    have hN : N.Normal := Subgroup.normal_of_index_eq_two hidx
    have hNtop : N ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hidx
      omega
    exact phi_all_of_verdictCheck (ι := QA45.originalSubgroup.subtype) Subtype.val_injective
      (fun m => by
        rw [mem_elemsT QA45 QA45_ok m]
        exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
      (by norm_num) (N := N) (LN := elemsT QP45)
      (fun y => by rw [mem_elemsT QP45 QP45_ok, hNdef, Subgroup.mem_subgroupOf]; rfl) hN hNtop
      (fun h => absurd h (by decide)) psp43_check_9746 hd.order R S hd hc hE2

section Leaf


theorem smallSimpleLeaf_psp43_of_check :
    SmallSimpleLeaf fun F _ => CFSG.Blueprint.LieModel F .PSp 2 3 1 :=
  smallSimpleLeaf_psp43 concreteLeaf_psp43

end Leaf

end CFSG.ClassicalInvolution.Q3.TA3
