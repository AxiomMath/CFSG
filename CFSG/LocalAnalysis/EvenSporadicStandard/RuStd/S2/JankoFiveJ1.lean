module

public import CFSG.Walter.J1Props.Facts

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1Recog CFSG.Open Word

theorem elt_eq_one_of_mem_p1Raw {w : Word 5} (hw : w ∈ p1Raw) : elt w = 1 := by
  have hmem : FreeGroup.reduce w ∈ rels .O1a :=
    List.mem_map_of_mem (List.mem_append_left _ (List.mem_append_left _ hw))
  exact Subtype.ext ((ev_reduce unit w).symm.trans (ev_unit_rels _ hmem))

theorem elt_word_comm (x y : Word 5) :
    elt (Word.comm x y) = (elt x)⁻¹ * (elt y)⁻¹ * elt x * elt y := by
  simp only [Word.comm, elt_append, elt_inv, mul_assoc]

theorem sJ_mul_mJ : sJ * mJ = mJ * sJ := by
  have h := elt_eq_one_of_mem_p1Raw (w := Word.comm ws wm) (by simp [p1Raw])
  rw [elt_word_comm] at h
  calc sJ * mJ = mJ * sJ * (sJ⁻¹ * mJ⁻¹ * sJ * mJ) := by group
    _ = mJ * sJ := by rw [h, mul_one]

theorem tJ_mul_sJ_pow_five : (tJ * sJ) ^ 5 = 1 := by
  have h := elt_eq_one_of_mem_p1Raw (w := Word.pow (wt ++ ws) 5) (by simp [p1Raw])
  rwa [elt_pow, elt_append] at h

theorem tJ_ne_sJ : tJ ≠ sJ := by
  intro h
  have h1 := congrArg CFSG.Walter.J1Props.mat h
  rw [mat_tJ, mat_sJ] at h1
  have h2 := congrFun (congrFun h1 0) 1
  revert h2
  decide

theorem orderOf_tJ_mul_sJ : orderOf (tJ * sJ) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime tJ_mul_sJ_pow_five fun h1 => tJ_ne_sJ ?_
  rw [eq_inv_of_mul_eq_one_right h1, tJ_inv]

theorem tJ_mul_sJ_comm_mJ : tJ * sJ * mJ = mJ * (tJ * sJ) :=
  calc tJ * sJ * mJ = tJ * (sJ * mJ) := mul_assoc _ _ _
    _ = tJ * (mJ * sJ) := by rw [sJ_mul_mJ]
    _ = tJ * mJ * sJ := (mul_assoc _ _ _).symm
    _ = mJ * tJ * sJ := by rw [four_data.2.1]
    _ = mJ * (tJ * sJ) := mul_assoc _ _ _

end CFSG.Walter.J1Props

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.Walter.J1Props CFSG.Open

theorem walterJ1_three_five (s : walterJ1) (hs : orderOf s = 3) :
    5 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set walterJ1)) := by
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card (Subgroup.zpowers s) = 3 := by rw [Nat.card_zpowers, hs]
  let P : Sylow 3 walterJ1 :=
    (IsPGroup.of_card (n := 1) (by rw [hcard, pow_one]) :
      IsPGroup 3 (Subgroup.zpowers s)).toSylow (not_dvd_index_of_card (Or.inl rfl) hcard)
  have hP : (P : Subgroup walterJ1) = Subgroup.zpowers s := rfl
  obtain ⟨g, hg⟩ := exists_eq_zpowers_conj (Or.inl rfl) P
  rw [hP] at hg
  have hsmem : s ∈ Subgroup.zpowers (g * mJ * g⁻¹) := hg ▸ Subgroup.mem_zpowers s
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hsmem
  have hcomm : Commute (g * (tJ * sJ) * g⁻¹) (g * mJ * g⁻¹) := by
    change g * (tJ * sJ) * g⁻¹ * (g * mJ * g⁻¹) = g * mJ * g⁻¹ * (g * (tJ * sJ) * g⁻¹)
    calc g * (tJ * sJ) * g⁻¹ * (g * mJ * g⁻¹) = g * (tJ * sJ * mJ) * g⁻¹ := by group
      _ = g * (mJ * (tJ * sJ)) * g⁻¹ := by rw [tJ_mul_sJ_comm_mJ]
      _ = g * mJ * g⁻¹ * (g * (tJ * sJ) * g⁻¹) := by group
  have hcs : g * (tJ * sJ) * g⁻¹ ∈ Subgroup.centralizer ({s} : Set walterJ1) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
    exact (hcomm.zpow_right k).eq
  have hc5 : orderOf (g * (tJ * sJ) * g⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_tJ_mul_sJ]
  rw [← hc5]
  exact Subgroup.orderOf_dvd_natCard _ hcs

end CFSG.EvenSporadicStandard.RuStd.S2
