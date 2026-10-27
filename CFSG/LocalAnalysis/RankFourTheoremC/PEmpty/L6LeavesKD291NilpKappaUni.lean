module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofBSU
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAMat

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N

open Subgroup Matrix CFSG.Open
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr conjTr_mul SUid mem_SUid)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LocalAnalysis.RankFourTheoremC (l212in_suConj l212in_suConj_coe l212in_suPhi
  l212in_suPhi_mk l212in_detU l212in_conj_scalar_su l212in_aut_su l212in_exists_zpow_units
  l212in_conj_mem_statedSU l212in_scalar_unitary l212in_det_scalar l212in_glAut_mem_Uid
  l212in_det_glAut l212in_glAut_scalar l212in_conj_scalar l212in_dvd_of_pow_mem
  scalar_mem_statedSU_iff)

section Unitary

variable {p r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

theorem detU_eq_pow_of_suPhi_eq_one (hp5 : 5 ≤ p) (hK : Nat.card K = (r ^ f) ^ 2)
    (B : Uid (unitaryInvolution K r f) p) (hB : l212in_suPhi hK B = 1) :
    ∃ c : rootsOfUnity (r ^ f + 1) K, l212in_detU B = c ^ p := by
  have hconj : ∀ g : StatedSU p (r ^ f) K,
      ∃ hg : (B : GL (Fin p) K) * (g : GL (Fin p) K) * (B : GL (Fin p) K)⁻¹ ∈
        StatedSU p (r ^ f) K,
      (QuotientGroup.mk ⟨_, hg⟩ : StatedProj (StatedSU p (r ^ f) K)) = QuotientGroup.mk g := by
    intro g
    refine ⟨l212in_conj_mem_statedSU hK B.2 g.2, ?_⟩
    have h1 : l212in_suPhi hK B (QuotientGroup.mk g) =
        (1 : MulAut (StatedProj (StatedSU p (r ^ f) K))) (QuotientGroup.mk g) := by rw [hB]
    rw [l212in_suPhi_mk, MulAut.one_apply] at h1
    exact h1
  obtain ⟨z, hz⟩ := l212in_conj_scalar_su hp5 hK B ((mem_Uid_iff _ _ _).1 B.2) hconj
  have hzu : z ^ (r ^ f + 1) = 1 := by
    refine l212in_scalar_unitary (n := p) (by omega) ?_
    rw [← hz]
    exact B.2
  refine ⟨⟨z, (mem_rootsOfUnity _ _).2 hzu⟩, ?_⟩
  apply Subtype.ext
  show GeneralLinearGroup.det (B : GL (Fin p) K) = z ^ p
  rw [hz, l212in_det_scalar]

theorem lift_data_uni (hp5 : 5 ≤ p) (hK : Nat.card K = (r ^ f) ^ 2)
    (γ : MulAut (StatedProj (StatedSU p (r ^ f) K))) :
    ∃ (κ : ℤ) (Ã : StatedSU p (r ^ f) K →* StatedSU p (r ^ f) K)
      (t : Uid (unitaryInvolution K r f) p → Uid (unitaryInvolution K r f) p),
      (∀ s, QuotientGroup.mk' ((StatedScalars (Fin p) K).subgroupOf (StatedSU p (r ^ f) K))
          (Ã s) = γ (QuotientGroup.mk' ((StatedScalars (Fin p) K).subgroupOf
            (StatedSU p (r ^ f) K)) s)) ∧
      (∀ s ∈ (QuotientGroup.mk' ((StatedScalars (Fin p) K).subgroupOf
          (StatedSU p (r ^ f) K))).ker, Ã s = s ^ κ) ∧
      (∀ B, γ * l212in_suPhi hK B * γ⁻¹ = l212in_suPhi hK (t B)) ∧
      (∀ B, l212in_detU (t B) = l212in_detU B ^ κ) := by
  obtain ⟨σ, B, hB, hg⟩ := l212in_aut_su hp5 hK γ
  choose hmem hγ using hg
  obtain ⟨ρ, hρ⟩ := l212in_exists_zpow_units σ
  have hBU : B ∈ Uid (unitaryInvolution K r f) p := (mem_Uid_iff _ _ _).2 hB
  let Ã : StatedSU p (r ^ f) K →* StatedSU p (r ^ f) K :=
    { toFun := fun g => ⟨B * glAut σ (g : GL (Fin p) K) * B⁻¹, hmem g⟩
      map_one' := Subtype.ext (by
        show B * glAut σ (1 : GL (Fin p) K) * B⁻¹ = 1
        rw [map_one, mul_one, mul_inv_cancel])
      map_mul' := fun g h => Subtype.ext (by
        show B * glAut σ ((g : GL (Fin p) K) * (h : GL (Fin p) K)) * B⁻¹ =
          (B * glAut σ (g : GL (Fin p) K) * B⁻¹) * (B * glAut σ (h : GL (Fin p) K) * B⁻¹)
        rw [map_mul]
        group) }
  let t : Uid (unitaryInvolution K r f) p → Uid (unitaryInvolution K r f) p := fun B' =>
    ⟨B * glAut σ (B' : GL (Fin p) K) * B⁻¹,
      mul_mem (mul_mem hBU (l212in_glAut_mem_Uid σ B'.2)) (inv_mem hBU)⟩
  refine ⟨ρ, Ã, t, ?_, ?_, ?_, ?_⟩
  · intro s
    exact (hγ s).symm
  · intro s hs
    rw [QuotientGroup.ker_mk'] at hs
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hs
    apply Subtype.ext
    show B * glAut σ (s : GL (Fin p) K) * B⁻¹ = ((s ^ ρ : StatedSU p (r ^ f) K) : GL (Fin p) K)
    rw [Subgroup.coe_zpow, ← hc, l212in_glAut_scalar, l212in_conj_scalar, hρ,
      ← map_zpow (GeneralLinearGroup.scalar (Fin p) : Kˣ →* GL (Fin p) K) c ρ]
  · intro B'
    have key : γ * l212in_suPhi hK B' = l212in_suPhi hK (t B') * γ := by
      ext z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
      rw [MulAut.mul_apply, MulAut.mul_apply, l212in_suPhi_mk, hγ, hγ g, l212in_suPhi_mk]
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      show B * glAut σ ((B' : GL (Fin p) K) * (g : GL (Fin p) K) * (B' : GL (Fin p) K)⁻¹) * B⁻¹ =
        (B * glAut σ (B' : GL (Fin p) K) * B⁻¹) * (B * glAut σ (g : GL (Fin p) K) * B⁻¹) *
          (B * glAut σ (B' : GL (Fin p) K) * B⁻¹)⁻¹
      simp only [map_mul, map_inv]
      group
    exact mul_inv_eq_iff_eq_mul.2 key
  · intro B'
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    change GeneralLinearGroup.det (B * glAut σ (B' : GL (Fin p) K) * B⁻¹) =
      (GeneralLinearGroup.det (B' : GL (Fin p) K)) ^ ρ
    rw [map_mul, map_mul, map_inv, l212in_det_glAut, hρ, mul_right_comm, mul_inv_cancel,
      one_mul]

theorem lift_kappa_uni [hpp : Fact p.Prime] (hp5 : 5 ≤ p) (hK : Nat.card K = (r ^ f) ^ 2)
    {ŷ : Uid (unitaryInvolution K r f) p} {ω : K}
    (hŷ : ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω)
    (hω : ∀ b : K, b ^ p ≠ ω) (α : MulAut (StatedProj (StatedSU p (r ^ f) K)))
    (hα : α * l212in_suPhi hK ŷ = l212in_suPhi hK ŷ * α) :
    ∃ Ã : StatedSU p (r ^ f) K →* StatedSU p (r ^ f) K,
      (∀ s, QuotientGroup.mk' ((StatedScalars (Fin p) K).subgroupOf (StatedSU p (r ^ f) K))
          (Ã s) = α (QuotientGroup.mk' ((StatedScalars (Fin p) K).subgroupOf
            (StatedSU p (r ^ f) K)) s)) ∧
      ∀ z ∈ (StatedScalars (Fin p) K).subgroupOf (StatedSU p (r ^ f) K), Ã z = z := by
  have hp : p.Prime := hpp.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨κ, Ã, t, hπÃ, hÃker, hΦt, hdet⟩ := lift_data_uni hp5 hK α
  refine ⟨Ã, hπÃ, fun z hz => ?_⟩
  have hz' : z ∈ (QuotientGroup.mk' ((StatedScalars (Fin p) K).subgroupOf
      (StatedSU p (r ^ f) K))).ker := by rw [QuotientGroup.ker_mk']; exact hz
  rw [hÃker z hz']
  have h1 : l212in_suPhi hK (t ŷ) = l212in_suPhi hK ŷ := by
    rw [← hΦt, hα, mul_inv_cancel_right]
  have h2 : l212in_suPhi hK (ŷ⁻¹ * t ŷ) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨c, hc⟩ := detU_eq_pow_of_suPhi_eq_one hp5 hK _ h2
  have hnotpow : ¬ ∃ c : rootsOfUnity (r ^ f + 1) K, l212in_detU ŷ = c ^ p := by
    rintro ⟨c, hc'⟩
    refine I292CaseA.not_pow_det hp hp2 hŷ hω ((c : Kˣ) : K) ?_
    have := congrArg (fun u : rootsOfUnity (r ^ f + 1) K => ((u : Kˣ) : K)) hc'
    simpa [l212in_detU, GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val] using
      this.symm
  have hBb : ∃ c' : rootsOfUnity (r ^ f + 1) K, l212in_detU ŷ ^ (κ - 1) = c' ^ p := by
    refine ⟨c, ?_⟩
    have h3 : l212in_detU ŷ ^ κ = l212in_detU ŷ * c ^ p := by
      rw [← hdet ŷ, ← hc, map_mul, map_inv]
      group
    calc l212in_detU ŷ ^ (κ - 1) = l212in_detU ŷ ^ κ * (l212in_detU ŷ)⁻¹ := zpow_sub_one _ _
      _ = l212in_detU ŷ * c ^ p * (l212in_detU ŷ)⁻¹ := by rw [h3]
      _ = c ^ p := by rw [mul_right_comm, mul_inv_cancel, one_mul]
  have hpdvd : (p : ℤ) ∣ κ - 1 :=
    l212in_dvd_of_pow_mem hp hnotpow ⟨l212in_detU ŷ, rfl⟩ hBb
  obtain ⟨m, hm⟩ := hpdvd
  have hκ1 : κ = 1 + (p : ℤ) * m := by omega
  have hzp : z ^ p = 1 := by
    obtain ⟨c0, hc0⟩ := Subgroup.mem_subgroupOf.1 hz
    have hzc : (z : GL (Fin p) K) = GeneralLinearGroup.scalar (Fin p) c0 := hc0.symm
    have hsc : GeneralLinearGroup.scalar (Fin p) c0 ∈ StatedSU p (r ^ f) K := by
      rw [← hzc]; exact z.2
    have hc0p : c0 ^ p = 1 := ((scalar_mem_statedSU_iff hK (by omega) c0).1 hsc).1
    apply Subtype.ext
    rw [Subgroup.coe_pow, hzc, ← map_pow, hc0p, map_one]
    rfl
  rw [hκ1, _root_.zpow_add, _root_.zpow_one, _root_.zpow_mul, _root_.zpow_natCast, hzp,
    _root_.one_zpow, mul_one]

end Unitary

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N
