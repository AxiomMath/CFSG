module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SD2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SD3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SDInputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t z g : G} {L S B : Subgroup G}

theorem sec9d_B_le_conj (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h66 : Asc82Lemma66)
    (h82 : Asc82Lemma82) (hT6 : Asc82Tab6M) (hB8 : Asc82Sec8B) (hE : Asc82E16Inner)
    (h : Sec8Base G t L S z g B) : B ≤ CFSG.conjugate L g := by
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1]
    exact one_mem _
  have hzB : z ∈ B := (hB8 G t L S z g B h).1
  have hww : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    rw [h.tz]
    calc (t * z) * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [← sec9d_t_B h hzB]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [sec9d_t_sq h, sec9d_z_sq h, one_mul]
  have hb2 : orderOf b = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact sec9d_B_sq h hb) hb1
  have hLgM : IsOm6M (CFSG.conjugate L g) := sec9d_isOm6M_conj h
  have hnorm : B ≤ normalizer (CFSG.conjugate L g : Set G) :=
    sec9d_B_le_normalizer h36 hB8 h
  have hinf : B ⊓ centralizer (CFSG.conjugate L g : Set G) = ⊥ :=
    sec9d_B_inf_cent_conj h82 hB8 h
  have hlayer : ∀ f ∈ B, orderOf f = 2 → layerCent (CFSG.conjugate L g) f = ⊥ :=
    sec9d_layerCent_conj_eq_bot h37 hB8 h
  have hin : InnerOn (CFSG.conjugate L g) b :=
    hE G (CFSG.conjugate L g) B hLgM hnorm h.B_e16 hinf hlayer b hb
  have hsetting : Sec3SettingLB G (g⁻¹ * t * g) (CFSG.conjugate L g) :=
    sec9d_setting_conj h
  have hbC : b ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (sec9d_B_comm_tg hB8 h hb)
  have hbne : b ≠ g⁻¹ * t * g :=
    fun heq => sec9d_tg_not_mem_B hB8 h (heq ▸ hb)
  obtain ⟨v, hvL, _hv2, hcase⟩ :=
    sec66_inner_decomp h82 hsetting hLgM.2 hb2 hbC hbne hin
  rcases hcase with hbv | hbv
  · rw [hbv]
    exact hvL
  · exfalso
    have hwb : v = b * (g⁻¹ * t * g) := by
      rw [hbv, mul_assoc, hww, mul_one]
    have hv_eq : v = t * (b * z) := by
      rw [hwb, h.tz]
      calc b * (t * z) = (b * t) * z := by rw [mul_assoc]
        _ = (t * b) * z := by rw [← sec9d_t_B h hb]
        _ = t * (b * z) := by rw [mul_assoc]
    have hdisj : t * (b * z) ∉ CFSG.conjugate L g :=
      sec9d_coset_disjoint_conj h37 h66 hT6 hB8 h (b * z) (B.mul_mem hb hzB)
    exact hdisj (hv_eq ▸ hvL)

end CFSG.OddStandard.SmallF3.Omega
