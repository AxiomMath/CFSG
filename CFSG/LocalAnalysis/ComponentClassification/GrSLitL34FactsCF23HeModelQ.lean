module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeModelJ
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEights

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts


@[expose] def hjL : Cover →* ↥hjJ := hjLam.rangeRestrict

theorem hjL_surjective : Function.Surjective hjL := MonoidHom.rangeRestrict_surjective _

theorem coe_hjL (c : Cover) : (hjL c : Equiv.Perm (Fin 8330)) = hjLam c := rfl

@[expose] def hjQ : ↥hjJ →* Equiv.Perm (Fin 42) :=
  (QuotientGroup.lift hjLam.ker sigma ker_hjLam_le_ker_sigma).comp
    (QuotientGroup.quotientKerEquivRange hjLam).symm.toMonoidHom

theorem hjQ_hjL (c : Cover) : hjQ (hjL c) = sigma c := by
  have : (QuotientGroup.quotientKerEquivRange hjLam).symm (hjL c) =
      (c : Cover ⧸ hjLam.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [hjQ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk]

theorem hjQ_mem_S (e : ↥hjJ) : hjQ e ∈ PSL3Four.S := by
  obtain ⟨c, rfl⟩ := hjL_surjective e
  rw [hjQ_hjL]
  exact sigma_mem_S c

theorem hjQ_surj : ∀ s ∈ PSL3Four.S, ∃ e, hjQ e = s := by
  intro s hs
  rw [← range_sigma] at hs
  obtain ⟨c, rfl⟩ := hs
  exact ⟨hjL c, hjQ_hjL c⟩

theorem ker_hjQ_le_center : hjQ.ker ≤ center ↥hjJ := by
  intro e he
  obtain ⟨c, rfl⟩ := hjL_surjective e
  rw [MonoidHom.mem_ker, hjQ_hjL] at he
  have hc := ker_sigma_le_center he
  rw [mem_center_iff] at hc ⊢
  intro e'
  obtain ⟨c', rfl⟩ := hjL_surjective e'
  rw [← map_mul, ← map_mul, hc c']

theorem center_S_eq_bot : center ↥PSL3Four.S = ⊥ := by
  have hS := hj_isSimpleGroup_S
  have : Group.IsPerfect Cover := Group.isPerfect_def.2 commutator_cover
  have hsurj : Function.Surjective (sigma.codRestrict PSL3Four.S sigma_mem_S) := by
    intro s
    have hs : (s : Equiv.Perm (Fin 42)) ∈ sigma.range := by
      rw [range_sigma]
      exact s.2
    obtain ⟨c, hc⟩ := hs
    exact ⟨c, Subtype.ext hc⟩
  have : Group.IsPerfect ↥PSL3Four.S := Group.IsPerfect.ofSurjective hsurj
  have : Nontrivial ↥PSL3Four.S := by
    rw [← Finite.one_lt_card_iff_nontrivial, PSL3Four.card_S]
    norm_num
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥PSL3Four.S) with hbot | htop
  · exact hbot
  · exact absurd (Subgroup.center_eq_top_iff.mp htop) (Group.IsPerfect.not_isMulCommutative _)

theorem center_le_ker_hjQ : center ↥hjJ ≤ hjQ.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have h1 : (⟨hjQ z, hjQ_mem_S z⟩ : ↥PSL3Four.S) ∈ center ↥PSL3Four.S := by
    rw [mem_center_iff]
    intro s
    obtain ⟨e, he⟩ := hjQ_surj s s.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← he, ← map_mul, ← map_mul, (mem_center_iff.1 hz e)]
  rw [center_S_eq_bot, mem_bot] at h1
  exact congrArg Subtype.val h1

theorem ker_hjQ : hjQ.ker = center ↥hjJ := le_antisymm ker_hjQ_le_center center_le_ker_hjQ


theorem hjZP_mul_t_sq : (hjZP * heGenPerm 0) * (hjZP * heGenPerm 0) = 1 := by
  have ht : heGenPerm 0 * heGenPerm 0 = 1 := by rw [← sq]; exact heGen0_sq
  calc (hjZP * heGenPerm 0) * (hjZP * heGenPerm 0) =
      hjZP * (heGenPerm 0 * hjZP) * heGenPerm 0 := by group
    _ = hjZP * (hjZP * heGenPerm 0) * heGenPerm 0 := by rw [hjZP_comm_t]
    _ = (hjZP * hjZP) * (heGenPerm 0 * heGenPerm 0) := by group
    _ = 1 := by rw [hjZP_mul_self, ht, one_mul]

theorem ker_hjQ_cases {e : ↥hjJ} (he : e ∈ hjQ.ker) :
    (e : Equiv.Perm (Fin 8330)) = 1 ∨ (e : Equiv.Perm (Fin 8330)) = hjZP ∨
      (e : Equiv.Perm (Fin 8330)) = heGenPerm 0 ∨
        (e : Equiv.Perm (Fin 8330)) = hjZP * heGenPerm 0 := by
  have ht : heGenPerm 0 * heGenPerm 0 = 1 := by rw [← sq]; exact heGen0_sq
  obtain ⟨c, rfl⟩ := hjL_surjective e
  rw [MonoidHom.mem_ker, hjQ_hjL] at he
  have he' : c ∈ zHom.range := by
    rw [range_zHom, MonoidHom.mem_ker]
    exact he
  obtain ⟨d, rfl⟩ := he'
  rw [coe_hjL, hjLam_zHom, pow_eq_pow_mod_two hjZP_mul_self, pow_eq_pow_mod_two ht]
  rcases Nat.mod_two_eq_zero_or_one d.1.toAdd.val with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one d.2.1.toAdd.val with h2 | h2 <;>
    simp only [h1, h2, pow_zero, pow_one, one_mul, mul_one, true_or, or_true]

theorem mul_self_of_mem_ker {e : ↥hjJ} (he : e ∈ hjQ.ker) :
    (e : Equiv.Perm (Fin 8330)) * e = 1 := by
  have ht : heGenPerm 0 * heGenPerm 0 = 1 := by rw [← sq]; exact heGen0_sq
  rcases ker_hjQ_cases he with h | h | h | h <;> rw [h]
  · exact one_mul 1
  · exact hjZP_mul_self
  · exact ht
  · exact hjZP_mul_t_sq

theorem isQSetting_hj : IsQSetting hjQ hjL where
  qS := hjQ_mem_S
  qsurj := hjQ_surj
  ker := ker_hjQ
  three := by
    intro e he h3
    apply Subtype.ext
    have h2 := mul_self_of_mem_ker he
    have h3' : (e : Equiv.Perm (Fin 8330)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
    calc (e : Equiv.Perm (Fin 8330)) = (e : Equiv.Perm (Fin 8330)) ^ 3 *
        ((e : Equiv.Perm (Fin 8330)) * e)⁻¹ := by group
      _ = 1 := by rw [h3', h2]; group
  ql := MonoidHom.ext hjQ_hjL
  lsurj := hjL_surjective

end CFSG.ComponentClassification.GSThmB.CF23L34
