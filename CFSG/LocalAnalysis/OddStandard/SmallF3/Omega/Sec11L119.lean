module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L119B

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma119_of (hp : Asc82Pre11) (r : Asc82Res11a) (h117 : Asc82Lemma117)
    (h118 : Asc82Lemma118) : Asc82Lemma119 := by
  intro G _ _ t L S z K1 K2 T R hctx
  have hRH : R ≤ centralizer ({z} : Set G) :=
    hctx.sylowR.1.trans (sec11_normalizer_Q_le_centralizer_z hp hctx.toSec10Ctx)
  obtain ⟨R', hR', hRR'⟩ := exists_isSylow2Of_ge hctx.sylowR.2.1 hRH
  have hEq : R' = R := by
    by_contra hne
    obtain ⟨y, hyR', hyR, hyN⟩ := sec11_exists_normalizing_of_lt hR'.2.1 hRR' (Ne.symm hne)
    have hyH : y ∈ centralizer ({z} : Set G) := hR'.1 hyR'
    have hyz0 : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyH
    have hyz : y * z * y⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hyz0
    have hyz' : y⁻¹ * z * y⁻¹⁻¹ = z := by
      have e : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
      rwa [hyz] at e
    have hJ := (h117 G t L S z K1 K2 T R hctx).2.2
    have hyDQ : y ∈ normalizer ((secD K1 K2 R ⊔ secQ K1 K2 : Subgroup G) : Set G) := by
      rw [← hJ]
      refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · exact sec11_JMod_conj hyz hyN hx
      · have h := sec11_JMod_conj hyz' (inv_mem hyN) hx
        have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
        rwa [e] at h
    have hyQ : y ∈ normalizer (secQ K1 K2 : Set G) :=
      sec11_N_DQ_le_N_Q hp r.l115c h118 hctx hyH hyDQ
    have hle : R ⊔ zpowers y ≤ normalizer (secQ K1 K2 : Set G) :=
      sup_le hctx.sylowR.1 ((Subgroup.zpowers_le).mpr hyQ)
    have h2 : IsPGroup 2 ↥(R ⊔ zpowers y) :=
      IsPGroup.to_le hR'.2.1 (sup_le hRR' ((Subgroup.zpowers_le).mpr hyR'))
    have hEq' := IsSylow2Of.eq_of_le hctx.sylowR hle h2 le_sup_left
    apply hyR
    rw [← hEq']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  rw [← hEq]
  exact hR'

end CFSG.OddStandard.SmallF3.Omega
