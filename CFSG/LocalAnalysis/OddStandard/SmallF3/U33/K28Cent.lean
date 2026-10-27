module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.K28Invol

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.K28

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates

private abbrev D8 : Subgroup Pm := Subgroup.closure ({fy, fz, flam} : Set Pm)

private theorem fy_mul_self : fy * fy = 1 := by
  rw [fy_def, ← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, fx₁_pow.1]

private theorem fz_mul_self : fz * fz = 1 := by
  have h4 : (fx₁ * fx₂) ^ 4 = 1 := by
    rw [Commute.mul_pow fx₁_fx₂_comm 4, fx₁_pow.1, fx₂_pow.1, one_mul]
  rw [fz, ← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, h4]

private theorem flam_mul_self : flam * flam = 1 := flam_pow.1

private theorem d8_gen_inv : fy⁻¹ = fy ∧ fz⁻¹ = fz ∧ flam⁻¹ = flam :=
  ⟨inv_eq_of_mul_eq_one_right fy_mul_self,
   inv_eq_of_mul_eq_one_right fz_mul_self,
   inv_eq_of_mul_eq_one_right flam_mul_self⟩

private theorem d8List_mem_D8 : ∀ g ∈ d8List, g ∈ D8 := by
  intro g hg
  simp only [d8List, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact D8.one_mem
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact Subgroup.subset_closure (by simp)
  · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact mul_mem (mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))

private theorem mem_d8List_of_mem_D8 : ∀ g ∈ D8, g ∈ d8List := by
  intro g hg
  induction hg using Subgroup.closure_induction_right with
  | one => simp [d8List]
  | mul_right a _ b hb ih =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl
      · exact (d8List_closed a ih).1
      · exact (d8List_closed a ih).2.1
      · exact (d8List_closed a ih).2.2
  | mul_inv_cancel a _ b hb ih =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl
      · rw [d8_gen_inv.1]; exact (d8List_closed a ih).1
      · rw [d8_gen_inv.2.1]; exact (d8List_closed a ih).2.1
      · rw [d8_gen_inv.2.2]; exact (d8List_closed a ih).2.2

private theorem card_D8 : Nat.card D8 = 8 := by
  have hle : Nat.card D8 ≤ 8 := by
    have hsub : (D8 : Set Pm) ⊆ (d8List.toFinset : Set Pm) := by
      intro x hx
      rw [Finset.mem_coe, List.mem_toFinset]
      exact mem_d8List_of_mem_D8 x hx
    have h := Set.ncard_le_ncard hsub (d8List.toFinset.finite_toSet)
    have hcard : Nat.card D8 = (D8 : Set Pm).ncard := by
      simpa using Nat.card_coe_set_eq (D8 : Set Pm)
    rw [hcard]
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup d8List_nodup] at h
    simpa [d8List] using h
  have hge : 8 ≤ Nat.card D8 := by
    have h := length_le_card_of_nodup D8 d8List d8List_mem_D8 d8List_nodup
    simpa [d8List] using h
  exact le_antisymm hle hge

theorem card_cent_fz :
    Nat.card ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({fz} : Set Pm)) = 96 := by
  let C : Subgroup Pm := QP.originalSubgroup ⊓ Subgroup.centralizer ({fz} : Set Pm)
  change Nat.card ↥C = 96
  haveI : Finite ↥(QP.originalSubgroup) :=
    Finite.of_injective (fun x : ↥(QP.originalSubgroup) => (x : Pm)) Subtype.coe_injective
  have hle : Nat.card ↥C ≤ 96 := by
    have h := card_inf_centralizer_mul_le QP.originalSubgroup fz (zConjWords.map wordP)
      (by
        intro w hw
        rw [List.mem_map] at hw
        obtain ⟨v, -, rfl⟩ := hw
        exact wordP_mem v)
      zConjWords_nodup
    change (zConjWords.map wordP).length * Nat.card ↥C ≤ Nat.card QP.originalSubgroup at h
    rw [List.length_map, zConjWords_length, card_P] at h
    omega
  have hge : 96 ≤ Nat.card ↥C := by
    have hT : wreathGrp fx₁ fx₂ flam ≤ C := by
      refine le_inf T_le_P ?_
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr frame_comm_fz.1
      · exact Subgroup.mem_centralizer_singleton_iff.mpr frame_comm_fz.2.1
      · exact Subgroup.mem_centralizer_singleton_iff.mpr frame_comm_fz.2.2
    have h32 : 32 ∣ Nat.card ↥C := by
      have h := Subgroup.card_dvd_of_le hT
      rwa [card_T] at h
    have h3 : 3 ∣ Nat.card ↥C := by
      have hle' : Subgroup.zpowers fg3 ≤ C := by
        refine le_inf ?_ ?_
        · rw [Subgroup.zpowers_le]; exact fg3_mem
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.mpr fg3_pow.2.2
      have h := Subgroup.card_dvd_of_le hle'
      rwa [Nat.card_zpowers, orderOf_eq_prime fg3_pow.1 fg3_pow.2.1] at h
    have h96 : 96 ∣ Nat.card ↥C := by
      have h := Nat.lcm_dvd h32 h3
      rw [Nat.Coprime.lcm_eq_mul (by decide : Nat.Coprime 32 3)] at h
      norm_num at h
      exact h
    haveI : Nonempty ↥C := ⟨1, C.one_mem⟩
    exact Nat.le_of_dvd Nat.card_pos h96
  exact le_antisymm hle hge

theorem card_cent_ftau :
    Nat.card ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({ftau} : Set Pm)) = 24 := by
  let C : Subgroup Pm := QP.originalSubgroup ⊓ Subgroup.centralizer ({ftau} : Set Pm)
  change Nat.card ↥C = 24
  haveI : Finite ↥(QP.originalSubgroup) :=
    Finite.of_injective (fun x : ↥(QP.originalSubgroup) => (x : Pm)) Subtype.coe_injective
  have hle : Nat.card ↥C ≤ 24 := by
    have h := card_inf_centralizer_mul_le QP.originalSubgroup ftau (tauConjWords.map wordP)
      (by
        intro w hw
        rw [List.mem_map] at hw
        obtain ⟨v, -, rfl⟩ := hw
        exact wordP_mem v)
      tauConjWords_nodup
    change (tauConjWords.map wordP).length * Nat.card ↥C ≤ Nat.card QP.originalSubgroup at h
    rw [List.length_map, tauConjWords_length, card_P] at h
    omega
  have hge : 24 ≤ Nat.card ↥C := by
    have hDle : D8 ≤ C := by
      refine le_inf ?_ ?_
      · refine (Subgroup.closure_le _).mpr ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · rw [fy_def]; exact Subgroup.pow_mem _ fx₁_mem 2
        · rw [fz_eq.1]
          exact mul_mem (Subgroup.pow_mem _ fx₁_mem 2) (Subgroup.pow_mem _ fx₂_mem 2)
        · exact flam_mem
      · refine (Subgroup.closure_le _).mpr ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact Subgroup.mem_centralizer_singleton_iff.mpr d8_comm_ftau.1
        · exact Subgroup.mem_centralizer_singleton_iff.mpr d8_comm_ftau.2.1
        · exact Subgroup.mem_centralizer_singleton_iff.mpr d8_comm_ftau.2.2
    have h8 : 8 ∣ Nat.card ↥C := by
      have h := Subgroup.card_dvd_of_le hDle
      rwa [card_D8] at h
    have h3 : 3 ∣ Nat.card ↥C := by
      have hle' : Subgroup.zpowers frho ≤ C := by
        refine le_inf ?_ ?_
        · rw [Subgroup.zpowers_le]; exact frho_mem
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.mpr ftau_frho.symm
      have h := Subgroup.card_dvd_of_le hle'
      rwa [Nat.card_zpowers, frho_ord] at h
    have h24 : 24 ∣ Nat.card ↥C := by
      have h := Nat.lcm_dvd h8 h3
      rw [Nat.Coprime.lcm_eq_mul (by decide : Nat.Coprime 8 3)] at h
      norm_num at h
      exact h
    haveI : Nonempty ↥C := ⟨1, C.one_mem⟩
    exact Nat.le_of_dvd Nat.card_pos h24
  exact le_antisymm hle hge

theorem cent_ftau_eq : QP.originalSubgroup ⊓ Subgroup.centralizer ({ftau} : Set Pm) =
    Subgroup.closure {fy, fz, frho, flam} := by
  let Ct : Subgroup Pm := QP.originalSubgroup ⊓ Subgroup.centralizer ({ftau} : Set Pm)
  let K : Subgroup Pm := Subgroup.closure ({fy, fz, frho, flam} : Set Pm)
  change Ct = K
  have hKle : K ≤ Ct := by
    refine le_inf ?_ ?_
    · refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [fy_def]; exact Subgroup.pow_mem _ fx₁_mem 2
      · rw [fz_eq.1]
        exact mul_mem (Subgroup.pow_mem _ fx₁_mem 2) (Subgroup.pow_mem _ fx₂_mem 2)
      · exact frho_mem
      · exact flam_mem
    · refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr d8_comm_ftau.1
      · exact Subgroup.mem_centralizer_singleton_iff.mpr d8_comm_ftau.2.1
      · exact Subgroup.mem_centralizer_singleton_iff.mpr ftau_frho.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr d8_comm_ftau.2.2
  have hDleK : D8 ≤ K := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have h8 : 8 ∣ Nat.card K := by
    have h := Subgroup.card_dvd_of_le hDleK
    rwa [card_D8] at h
  have h3 : 3 ∣ Nat.card K := by
    have hle : Subgroup.zpowers frho ≤ K := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, frho_ord] at h
  have h24 : 24 ∣ Nat.card K := by
    have h := Nat.lcm_dvd h8 h3
    rw [Nat.Coprime.lcm_eq_mul (by decide : Nat.Coprime 8 3)] at h
    norm_num at h
    exact h
  have hcardCt : Nat.card Ct = 24 := card_cent_ftau
  have hKdvd : Nat.card K ∣ 24 := by
    have h := Subgroup.card_dvd_of_le hKle
    rwa [hcardCt] at h
  have hKcard : Nat.card K = 24 := (Nat.dvd_antisymm h24 hKdvd).symm
  have hcardle : Nat.card Ct ≤ Nat.card K := by
    omega
  have heq : K = Ct := Subgroup.eq_of_le_of_card_ge hKle hcardle
  exact heq.symm

end CFSG.OddStandard.SmallF3.HarrisU33.K28
