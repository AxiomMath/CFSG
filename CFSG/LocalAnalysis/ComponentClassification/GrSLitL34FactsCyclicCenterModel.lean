
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModelBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModelBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem mem_sqData_of_mul_self {k : ℕ} (hk : k < 64)
    (h2 : wordPerm (tg k) * wordPerm (tg k) = 1) : k = 0 ∨ ∃ d ∈ sqData, d.1 = k := by
  have hinv := coverParts.invols k hk
  have h1 : comp 42 (wordTab (tg k)) (wordTab (tg k)) = idTab 42 :=
    ((tabRep_wordTab _).comp (tabRep_wordTab _)).tab_eq (h2 ▸ TabRep.idTab)
  rw [h1, beq_self_eq_true] at hinv
  have := hinv.symm
  simp only [Bool.or_eq_true, beq_iff_eq, List.elem_iff, List.mem_map] at this
  exact this

theorem involution_mem_U
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0)
    (h2 : t * t = 1) : t ∈ U1 ∨ t ∈ U2 := by
  obtain ⟨k, hk, rfl⟩ := exists_tg ht
  have hmem : k ∈ 0 :: sqData.map (·.1) := by
    rcases mem_sqData_of_mul_self hk h2 with rfl | ⟨d, hd, rfl⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hd)
  rcases sqData_U k hmem with h | ⟨h4, h64⟩
  · exact Or.inl (tg_mem_U1 h)
  · right
    have e : k = 4 * (k / 4) := by omega
    rw [e]
    exact tg_mem_U2 (by omega)

theorem U1_mul_self
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ U1) : t * t = 1 := by
  obtain ⟨k, hk, rfl⟩ := mem_U1_iff.1 ht
  have hinv := coverParts.invols k (by omega)
  have hmem : (k == 0 || (sqData.map (·.1)).contains k) = true := by
    have : k ∈ 0 :: sqData.map (·.1) := U1_idx k hk
    simp only [List.mem_cons, List.mem_map] at this
    rcases this with rfl | ⟨d, hd, rfl⟩
    · rfl
    · simp only [Bool.or_eq_true, beq_iff_eq, List.elem_iff, List.mem_map]
      exact Or.inr ⟨d, hd, rfl⟩
  rw [hmem, beq_iff_eq] at hinv
  exact ((tabRep_wordTab _).comp (tabRep_wordTab _)).perm_eq (hinv ▸ TabRep.idTab)

theorem U2_mul_self
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ U2) : t * t = 1 := by
  obtain ⟨k, hk, rfl⟩ := mem_U2_iff.1 ht
  have hinv := coverParts.invols (4 * k) (by omega)
  have hmem : (4 * k == 0 || (sqData.map (·.1)).contains (4 * k)) = true := by
    have : 4 * k ∈ 0 :: sqData.map (·.1) := U2_idx k hk
    simp only [List.mem_cons, List.mem_map] at this
    rcases this with h | ⟨d, hd, hdk⟩
    · rw [h]; rfl
    · simp only [Bool.or_eq_true, beq_iff_eq, List.elem_iff, List.mem_map]
      exact Or.inr ⟨d, hd, hdk⟩
  rw [hmem, beq_iff_eq] at hinv
  exact ((tabRep_wordTab _).comp (tabRep_wordTab _)).perm_eq (hinv ▸ TabRep.idTab)

theorem Z0_le_U1 :
    Z0 ≤ U1 := fun t ht => by
  obtain ⟨k, hk, rfl⟩ := mem_Z0.1 ht
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  exact tg_mem_U1 (by omega)

theorem Z0_le_U2 :
    Z0 ≤ U2 := fun t ht => by
  obtain ⟨k, hk, rfl⟩ := mem_Z0.1 ht
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  have e : k = 4 * (k / 4) := by omega
  rw [e]
  exact tg_mem_U2 (by omega)

namespace IsQSetting

theorem exists_sq_eq (h : IsQSetting q l) {e : E} (he : q e ∈ T0)
    (h2 : q e * q e = 1) : ∃ w ∈ q.ker, e * e = w * w := by
  obtain ⟨k, hk, hke⟩ := exists_tg he
  rcases mem_sqData_of_mul_self hk (hke ▸ h2) with rfl | ⟨d, hd, rfl⟩
  · refine ⟨e, ?_, rfl⟩
    rw [MonoidHom.mem_ker, ← hke, wordPerm_tg_zero]
  · have hz : (l (cv (tw d.1)))⁻¹ * e ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h.q_lift hk, hke, inv_mul_cancel]
    have hs := congrArg l (sq_spec hd)
    rw [map_pow, map_mul, map_mul, map_pow, map_pow, map_pow, h.lz₃, one_pow, mul_one] at hs
    have hv : l z₁ ^ d.2.1 * l z₂ ^ d.2.2.1 ∈ q.ker :=
      mul_mem (pow_mem (h.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₁)) _)
        (pow_mem (h.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₂)) _)
    refine ⟨l z₁ ^ d.2.1 * l z₂ ^ d.2.2.1 * ((l (cv (tw d.1)))⁻¹ * e), mul_mem hv hz, ?_⟩
    have hzc := mem_center_iff.mp (h.ker_le hz)
    have hvc := mem_center_iff.mp (h.ker_le hv)
    have h2c : ∀ g : E, g * l z₂ ^ d.2.2.1 = l z₂ ^ d.2.2.1 * g := fun g =>
      mem_center_iff.mp (h.ker_le (pow_mem (h.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₂)) _)) g
    have hvv : (l z₁ ^ d.2.1 * l z₂ ^ d.2.2.1) * (l z₁ ^ d.2.1 * l z₂ ^ d.2.2.1) =
        l (cv (tw d.1)) ^ 2 := by
      rw [hs]
      calc l z₁ ^ d.2.1 * l z₂ ^ d.2.2.1 * (l z₁ ^ d.2.1 * l z₂ ^ d.2.2.1) =
          l z₁ ^ d.2.1 * (l z₂ ^ d.2.2.1 * l z₁ ^ d.2.1) * l z₂ ^ d.2.2.1 := by group
        _ = l z₁ ^ d.2.1 * (l z₁ ^ d.2.1 * l z₂ ^ d.2.2.1) * l z₂ ^ d.2.2.1 := by
          rw [← h2c]
        _ = l z₁ ^ (2 * d.2.1) * l z₂ ^ (2 * d.2.2.1) := by
          rw [two_mul, two_mul, pow_add, pow_add]
          group
    have he' : e = l (cv (tw d.1)) * ((l (cv (tw d.1)))⁻¹ * e) := by group
    generalize (l (cv (tw d.1)))⁻¹ * e = z at hz hzc he' ⊢
    generalize l z₁ ^ d.2.1 * l z₂ ^ d.2.2.1 = v at hv hvc hvv ⊢
    generalize l (cv (tw d.1)) = p at hvv he' ⊢
    rw [he']
    calc p * z * (p * z) = p * (z * p) * z := by group
      _ = p * (p * z) * z := by rw [hzc p]
      _ = p ^ 2 * (z * z) := by rw [pow_two]; group
      _ = v * v * (z * z) := by rw [hvv]
      _ = v * (v * z) * z := by group
      _ = v * (z * v) * z := by rw [hzc v]
      _ = v * z * (v * z) := by group

theorem exists_A0
    [Finite E] (h : IsQSetting q l) {ζ : E} (hζk : ζ ∈ q.ker)
    (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1) :
    IsEightGroup (zpowers (ilift l (8, 1, 0, 0)) ⊔ (zpowers (ilift l (4, 1, 1, 1)) ⊔ zpowers ζ)) ∧
      zpowers (ilift l (8, 1, 0, 0)) ⊔ (zpowers (ilift l (4, 1, 1, 1)) ⊔ zpowers ζ) ≤
        Z0.comap q := by
  have hq4 : q (ilift l (4, 1, 1, 1)) = wordPerm (tg 4) := h.q_ilift (by norm_num)
  have hq8 : q (ilift l (8, 1, 0, 0)) = wordPerm (tg 8) := h.q_ilift (by norm_num)
  have h4sq := h.ilift_mul_self (d := (4, 1, 1, 1)) (by decide)
  have h8sq := h.ilift_mul_self (d := (8, 1, 0, 0)) (by decide)
  have ht4 := h.tg_mul_self_of_ilift (d := (4, 1, 1, 1)) (by decide) (by norm_num)
  have hc48 : ilift l (4, 1, 1, 1) * ilift l (8, 1, 0, 0) =
      ilift l (8, 1, 0, 0) * ilift l (4, 1, 1, 1) :=
    h.ilift_comm (by
      rw [← map_mul, cv_comm_of_commData (d := (4, 8, 0, 0, 0)) (by decide) rfl, map_mul])
  have hζc : ∀ x : E, ζ * x = x * ζ := fun x => (mem_center_iff.mp (h.ker_le hζk) x).symm
  have hζq : q ζ = 1 := hζk
  refine ⟨isEightGroup_of_three hζ2 h4sq h8sq (hζc _) (hζc _) hc48 hζ1 ?_ ?_, ?_⟩
  · intro hmem
    have := map_mem_zpowers q hmem
    rw [hq4, hζq, zpowers_one_eq_bot, mem_bot, ← wordPerm_tg_zero] at this
    exact absurd (tg_injective (by norm_num) (by norm_num) this) (by norm_num)
  · intro hmem
    have hle : zpowers (ilift l (4, 1, 1, 1)) ⊔ zpowers ζ ≤ (zpowers (wordPerm (tg 4))).comap q :=
      sup_le (zpowers_le.2 (by rw [mem_comap, hq4]; exact mem_zpowers _))
        (zpowers_le.2 (by rw [mem_comap, hζq]; exact one_mem _))
    have := hle hmem
    rw [mem_comap, hq8] at this
    exact not_mem_zpowers_tg (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht4 this
  · refine sup_le (zpowers_le.2 ?_) (sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_))
    · rw [mem_comap, hq8]
      exact mem_Z0.2 ⟨8, by decide, rfl⟩
    · rw [mem_comap, hq4]
      exact mem_Z0.2 ⟨4, by decide, rfl⟩
    · rw [mem_comap, hζq]
      exact one_mem _

end IsQSetting

end CFSG.ComponentClassification.GrSLit.L34Facts
