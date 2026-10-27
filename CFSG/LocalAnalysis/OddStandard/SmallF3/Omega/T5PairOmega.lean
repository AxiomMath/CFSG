module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma conj_mul_self_eq_one {G : Type*} [Group G] {t g : G} (ht : t * t = 1) :
    (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
  rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht, mul_one,
    mul_inv_cancel]

theorem t5_omega_pair (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hs : quadSign Q = -1) {z : OGroup Q} (hzz : z * z = 1) (hz : invType z = (4, 1)) :
    ∃ w : OGroup Q, w ∈ omegaGroup hQ ∧ w * w = 1 ∧ invType w = (4, 1) ∧ w * z = z * w ∧
      (piOrth Q * z * w) * (piOrth Q * z * w) = 1 ∧ invType (piOrth Q * z * w) = (4, 1) := by
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hs
  let J₁ : Finset (Fin 6) := {0, 1, 2, 3}
  let J₂ : Finset (Fin 6) := {0, 1, 2, 4}
  let J₃ : Finset (Fin 6) := {3, 4}
  let z₀ : OGroup Q := fr.signChange J₁
  let w₀ : OGroup Q := fr.signChange J₂
  have hJ₁card : J₁.card = 4 := by decide
  have hJ₂card : J₂.card = 4 := by decide
  have hJ₃card : J₃.card = 2 := by decide
  have hJdiff : symmDiff J₁ J₂ = J₃ := by decide
  have hd4 : (4 : ℕ) / 2 = 2 := by norm_num
  have hd2 : (2 : ℕ) / 2 = 1 := by norm_num
  have hz0sq : z₀ * z₀ = 1 := fr.signChange_mul_self J₁
  have hw0sq : w₀ * w₀ = 1 := fr.signChange_mul_self J₂
  have hcomm0 : z₀ * w₀ = w₀ * z₀ := fr.signChange_comm J₁ J₂
  have hw0mem : w₀ ∈ omegaGroup hQ :=
    fr.signChange_mem_omegaGroup hQ J₂ (by rw [hJ₂card]; decide)
  have hz0w0 : z₀ * w₀ = fr.signChange J₃ := by
    rw [show z₀ * w₀ = fr.signChange (symmDiff J₁ J₂) from fr.signChange_mul J₁ J₂, hJdiff]
  have hdiffinv : (z₀ * w₀) * (z₀ * w₀) = 1 := by
    rw [hz0w0]
    exact fr.signChange_mul_self J₃
  have hz0type : invType z₀ = (4, 1) := by
    have h := fr.invType_signChange hQ J₁ (by rw [hJ₁card]; decide)
    rw [hJ₁card, hd4] at h
    rw [h]
    exact Prod.ext rfl (by decide)
  have hw0type : invType w₀ = (4, 1) := by
    have h := fr.invType_signChange hQ J₂ (by rw [hJ₂card]; decide)
    rw [hJ₂card, hd4] at h
    rw [h]
    exact Prod.ext rfl (by decide)
  have hz0w0type : invType (z₀ * w₀) = (2, -1) := by
    rw [hz0w0]
    have h := fr.invType_signChange hQ J₃ (by rw [hJ₃card]; decide)
    rw [hJ₃card, hd2] at h
    rw [h]
    exact Prod.ext rfl (by decide)
  have hdim2 : invDim (z₀ * w₀) = 2 := congrArg Prod.fst hz0w0type
  have hsign2 : invSign (z₀ * w₀) = -1 := congrArg Prod.snd hz0w0type
  let A : OGroup Q := piOrth Q * (z₀ * w₀)
  have hA2 : A * A = 1 := piOrth_mul_mul_self hdiffinv
  have hAtype : invType A = (4, 1) := by
    change invType (piOrth Q * (z₀ * w₀)) = (4, 1)
    have hEvenV : Even (Module.finrank (ZMod 3) V) := by rw [hdim]; decide
    have h := invType_piOrth_mul_of_even_minus hQ hdiffinv hEvenV hs
    rw [hdim, hdim2, hsign2] at h
    rw [h]
    refine Prod.ext (by norm_num) ?_
    have hpow : ((-1 : ℤˣ)) ^ (2 + 1) = -1 := by decide
    rw [hpow, neg_mul_neg, one_mul]
  obtain ⟨g, hg⟩ :=
    isConj_iff.mp (isConj_of_invType_eq hQ hz0sq hzz (by rw [hz0type, hz]))
  let w : OGroup Q := g * w₀ * g⁻¹
  have hwmem : w ∈ omegaGroup hQ := (omegaGroup_normal hQ).conj_mem w₀ hw0mem g
  have hw2 : w * w = 1 := conj_mul_self_eq_one hw0sq
  have hwtype : invType w = (4, 1) := by
    change invType (g * w₀ * g⁻¹) = (4, 1)
    rw [invType_conj hQ hw0sq g, hw0type]
  have hwz : w * z = z * w := by
    change (g * w₀ * g⁻¹) * z = z * (g * w₀ * g⁻¹)
    rw [← hg]
    calc (g * w₀ * g⁻¹) * (g * z₀ * g⁻¹)
        = g * (w₀ * z₀) * g⁻¹ := by group
      _ = g * (z₀ * w₀) * g⁻¹ := by rw [← hcomm0]
      _ = (g * z₀ * g⁻¹) * (g * w₀ * g⁻¹) := by group
  have hconj : piOrth Q * z * w = g * A * g⁻¹ := by
    change piOrth Q * z * (g * w₀ * g⁻¹) = g * A * g⁻¹
    rw [← hg]
    have hc : piOrth Q * g = g * piOrth Q :=
      (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) g).symm
    calc piOrth Q * (g * z₀ * g⁻¹) * (g * w₀ * g⁻¹)
        = piOrth Q * g * z₀ * w₀ * g⁻¹ := by group
      _ = g * piOrth Q * z₀ * w₀ * g⁻¹ := by rw [hc]
      _ = g * (piOrth Q * (z₀ * w₀)) * g⁻¹ := by group
  have hA2' : (piOrth Q * z * w) * (piOrth Q * z * w) = 1 := by
    rw [hconj]
    exact conj_mul_self_eq_one hA2
  have hAtype' : invType (piOrth Q * z * w) = (4, 1) := by
    rw [hconj, invType_conj hQ hA2 g, hAtype]
  exact ⟨w, hwmem, hw2, hwtype, hwz, hA2', hAtype'⟩

end CFSG.OddStandard.SmallF3.Omega
