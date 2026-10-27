module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupActions

theorem solvable_of_card_five_mul_two_pow {T : Type*} [Group T] [Finite T] {j : ℕ} (hj : j ≤ 3)
    (hT : Nat.card T = 5 * 2 ^ j) : Group.IsSolvable T := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F⟩ : Nonempty (Sylow 5 T) := inferInstance
  have hn1 : Nat.card (Sylow 5 T) % 5 = 1 := card_sylow_modEq_one 5 T
  have hndvd : Nat.card (Sylow 5 T) ∣ 5 * 2 ^ j := by
    rw [← hT, Sylow.card_eq_index_normalizer F]
    exact Subgroup.index_dvd_card _
  have hcop : Nat.Coprime 5 (Nat.card (Sylow 5 T)) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    rintro ⟨c, hc⟩
    omega
  have hn2 : Nat.card (Sylow 5 T) ∣ 2 ^ j := hcop.symm.dvd_of_dvd_mul_left hndvd
  obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hn2
  have hi3 : i ≤ 3 := hi.trans hj
  have hn : Nat.card (Sylow 5 T) = 1 := by
    rw [hni] at hn1 ⊢
    interval_cases i <;> simp_all
  have : Subsingleton (Sylow 5 T) := (Finite.card_le_one_iff_subsingleton).1 hn.le
  have hFn : (F : Subgroup T).Normal := Sylow.normal_of_subsingleton F
  have : Group.IsSolvable (F : Subgroup T) :=
    @IsNilpotent.to_isSolvable _ _ (F.isPGroup').isNilpotent
  have hidx : ¬ 5 ∣ (F : Subgroup T).index := F.not_dvd_index
  have hidx2 : (F : Subgroup T).index ∣ 2 ^ j := by
    have h1 : (F : Subgroup T).index ∣ 5 * 2 ^ j := hT ▸ Subgroup.index_dvd_card _
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hidx).symm.dvd_of_dvd_mul_left h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidx2
  have hQ : IsPGroup 2 (T ⧸ (F : Subgroup T)) :=
    IsPGroup.of_card (n := k) (by rw [← Subgroup.index_eq_card, hk])
  have : Group.IsSolvable (T ⧸ (F : Subgroup T)) := @IsNilpotent.to_isSolvable _ _ hQ.isNilpotent
  exact Group.isSolvable_of_ker_le_range (F : Subgroup T).subtype
    (QuotientGroup.mk' (F : Subgroup T)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem index_five_two_subgroup_solvable {P : Type*} [Group P] [Finite P] (Q : Subgroup P)
    (hQ : IsPGroup 2 Q) (hidx : Q.index = 5) : Group.IsSolvable P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := MulAction.toPermHom P (P ⧸ Q) with hφ
  have hker : φ.ker ≤ Q := by
    rw [hφ, ← Subgroup.normalCore_eq_ker]
    exact Subgroup.normalCore_le Q
  have hK2 : IsPGroup 2 φ.ker := hQ.to_le hker
  have : Group.IsSolvable φ.ker := @IsNilpotent.to_isSolvable _ _ hK2.isNilpotent
  have hcardQ : Nat.card (P ⧸ Q) = 5 := by rw [← Subgroup.index_eq_card, hidx]
  have hperm : Nat.card (Equiv.Perm (P ⧸ Q)) = 120 := by
    rw [Nat.card_perm, hcardQ]
    rfl
  have hTdvd : Nat.card φ.range ∣ 120 := hperm ▸ Subgroup.card_subgroup_dvd_card φ.range
  have hTcard : Nat.card φ.range = φ.ker.relIndex Q * 5 := by
    rw [← Subgroup.index_ker, ← Subgroup.relIndex_mul_index hker, hidx]
  have hrel : φ.ker.relIndex Q ∣ Nat.card Q := Subgroup.relIndex_dvd_card _ _
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hQ
  rw [ha] at hrel
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hrel
  rw [hi] at hTcard
  have hi3 : i ≤ 3 := by
    rw [hTcard] at hTdvd
    by_contra h
    push Not at h
    have h16 : 2 ^ 4 ∣ 2 ^ i := pow_dvd_pow 2 h
    have : 2 ^ 4 * 5 ∣ 120 := (Nat.mul_dvd_mul_right h16 5).trans hTdvd
    norm_num at this
  have : Group.IsSolvable φ.range :=
    solvable_of_card_five_mul_two_pow hi3 (by rw [hTcard, mul_comm])
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

end CFSG.GroupActions
