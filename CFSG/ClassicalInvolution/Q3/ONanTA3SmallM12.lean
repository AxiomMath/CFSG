module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallVerdictSound
public import CFSG.ClassicalInvolution.Q3.TA3SmallModelM12
public import Certificates.Certificate9747
public import Certificates.Certificate9748

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG.GH74.KGroups CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover Check

theorem m12_check_9747 :
    verdictCheck 100 [(1 : Equiv.Perm (Fin 24))] (elemsT m12D) true (pickReps (elemsT m12D)) =
      true :=
  Certificates.certificate9747

theorem m12_check_9748 :
    verdictCheck 100 (elemsT m12D) (elemsT m12D ++ (elemsT m12D).map (fun d => m12Sigma * d))
      false (pickReps (elemsT m12D ++ (elemsT m12D).map (fun d => m12Sigma * d))) = true :=
  Certificates.certificate9748

theorem concreteLeaf_m12 :
    ConcreteLeaf (Equiv.Perm (Fin 24)) blockGroup autModel := by
  intro X hPX hXA R S t hd hc hE2
  have hP : Nat.card blockGroup = 95040 := by
    rw [blockGroup, ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]
  have hA : Nat.card autModel = 190080 := card_autModel
  obtain ⟨k, hk⟩ : 95040 ∣ Nat.card X := hP ▸ Subgroup.card_dvd_of_le hPX
  have h2 : Nat.card X ∣ 190080 := hA ▸ Subgroup.card_dvd_of_le hXA
  have hk2 : k ∣ 2 := by
    rw [hk] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 95040) (by simpa using h2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
  ·
    have hXP : blockGroup = X := Subgroup.eq_of_le_of_card_ge hPX (by rw [hk, hP])
    subst hXP
    have ht1 : t ≠ 1 := fun h => by
      have := hd.order
      rw [h, orderOf_one] at this
      omega
    have hNtop : (⊥ : Subgroup blockGroup) ≠ ⊤ := fun h =>
      ht1 (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_top t))
    have hE3b : (true = true) → ∃ f : blockGroup →* CFSG.Blueprint.NativeSporadic.Carrier .M12,
        Function.Surjective f ∧ IsPGroup 2 ↥f.ker := fun _ => by
      let f : blockGroup →* CFSG.Blueprint.NativeSporadic.Carrier .M12 :=
        m12EquivD.symm.toMonoidHom
      have hker : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff f).2 m12EquivD.symm.injective
      have hbot : IsPGroup 2 (⊥ : Subgroup ↥blockGroup) := IsPGroup.of_card (n := 0) (by simp)
      exact ⟨f, m12EquivD.symm.surjective, by rw [hker]; exact hbot⟩
    exact phi_all_of_verdictCheck (ι := blockGroup.subtype) Subtype.val_injective
      (fun m => by
        rw [mem_elemsT m12D m12D_check.1 m]
        exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
      (by norm_num) (N := ⊥) (LN := [1])
      (fun y => by
        rw [List.mem_singleton, Subgroup.mem_bot]
        exact ⟨fun h => Subtype.val_injective (by simpa using h), fun h => by simp [h]⟩)
      Subgroup.normal_bot hNtop hE3b m12_check_9747 hd.order R S hd hc hE2
  ·
    have hXA' : X = autModel := Subgroup.eq_of_le_of_card_ge hXA (by rw [hk, hA])
    subst hXA'
    set N : Subgroup autModel := blockGroup.subgroupOf autModel with hNdef
    have hidx : N.index = 2 := index_blockGroup
    have hN : N.Normal := Subgroup.normal_of_index_eq_two hidx
    have hNtop : N ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hidx
      omega
    exact phi_all_of_verdictCheck (ι := autModel.subtype) Subtype.val_injective
      (L := elemsT m12D ++ (elemsT m12D).map (fun d => m12Sigma * d))
      (fun m => by
        rw [List.mem_append, List.mem_map, mem_elemsT m12D m12D_check.1 m]
        constructor
        · rintro (hm | ⟨d, hd', rfl⟩)
          · exact ⟨⟨m, mem_autModel.2 (Or.inl hm)⟩, rfl⟩
          · refine ⟨⟨m12Sigma * d, mem_autModel.2 (Or.inr ?_)⟩, rfl⟩
            rw [← mul_assoc, CFSG.ComponentClassification.M12Cover.sigma_mul_self, one_mul]
            exact (mem_elemsT m12D m12D_check.1 d).1 hd'
        · rintro ⟨⟨y, hy⟩, rfl⟩
          rcases mem_autModel.1 hy with hy' | hy'
          · exact Or.inl hy'
          · exact Or.inr ⟨m12Sigma * y, (mem_elemsT m12D m12D_check.1 _).2 hy',
              by rw [← mul_assoc, CFSG.ComponentClassification.M12Cover.sigma_mul_self, one_mul]
                 rfl⟩)
      (by norm_num) (N := N) (LN := elemsT m12D)
      (fun y => by rw [mem_elemsT m12D m12D_check.1, hNdef, Subgroup.mem_subgroupOf]; rfl) hN
      hNtop (fun h => absurd h (by decide)) m12_check_9748 hd.order R S hd hc hE2

section Leaf


theorem smallSimpleLeaf_m12_of_check :
    SmallSimpleLeaf SmallM12 :=
  smallSimpleLeaf_m12 concreteLeaf_m12

end Leaf

end CFSG.ClassicalInvolution.Q3.TA3
