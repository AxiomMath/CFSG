module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOrth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma aux_commSp_le {τ u : OGroup Q} (hτ : τ * τ = 1) (hu : u * u = 1)
    (hcomm : τ * u = u * τ) (hfix : fixSp τ ≤ fixSp u) : commSp u ≤ commSp τ := by
  intro v hv
  have hcompl := isCompl_fixSp_commSp (Q := Q) hτ
  obtain ⟨w, hw, c, hc, hwc⟩ := Submodule.mem_sup.mp (show v ∈ fixSp τ ⊔ commSp τ by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top)
  rw [← hwc] at hv ⊢
  have hcomm' : (τ : V ≃ₗ[ZMod 3] V) * (u : V ≃ₗ[ZMod 3] V) =
      (u : V ≃ₗ[ZMod 3] V) * (τ : V ≃ₗ[ZMod 3] V) := by
    simpa only [Subgroup.coe_mul] using
      congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) hcomm
  have huc : (u : V ≃ₗ[ZMod 3] V) c ∈ commSp τ := by
    rw [mem_commSp_iff hτ]
    calc (τ : V ≃ₗ[ZMod 3] V) ((u : V ≃ₗ[ZMod 3] V) c)
        = ((τ : V ≃ₗ[ZMod 3] V) * (u : V ≃ₗ[ZMod 3] V)) c :=
          (LinearEquiv.mul_apply _ _ _).symm
      _ = ((u : V ≃ₗ[ZMod 3] V) * (τ : V ≃ₗ[ZMod 3] V)) c := by rw [hcomm']
      _ = (u : V ≃ₗ[ZMod 3] V) ((τ : V ≃ₗ[ZMod 3] V) c) := LinearEquiv.mul_apply _ _ _
      _ = (u : V ≃ₗ[ZMod 3] V) (-c) := by rw [(mem_commSp_iff hτ).mp hc]
      _ = -(u : V ≃ₗ[ZMod 3] V) c := map_neg _ _
  have hwc : (u : V ≃ₗ[ZMod 3] V) w = w := mem_fixSp_iff.mp (hfix hw)
  have hkey : (w + (u : V ≃ₗ[ZMod 3] V) c) + (w + c) = 0 := by
    have h : w + (u : V ≃ₗ[ZMod 3] V) c = -(w + c) := by
      simpa only [map_add, hwc] using (mem_commSp_iff hu).mp hv
    rw [h, neg_add_cancel]
  have h2w : (2 : ZMod 3) • w = -(c + (u : V ≃ₗ[ZMod 3] V) c) := by
    have hkey' : (w + w) + (c + (u : V ≃ₗ[ZMod 3] V) c) = 0 := by
      rw [← hkey]; abel
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mpr hkey'
  have hmem_w : (2 : ZMod 3) • w ∈ fixSp τ := (fixSp τ).smul_mem (2 : ZMod 3) hw
  have hmem_c : (2 : ZMod 3) • w ∈ commSp τ := by
    rw [h2w]
    exact (commSp τ).neg_mem ((commSp τ).add_mem hc huc)
  have hinf : fixSp τ ⊓ commSp τ = ⊥ := disjoint_iff.mp hcompl.disjoint
  have hzero : (2 : ZMod 3) • w = 0 := by
    have hmem : (2 : ZMod 3) • w ∈ fixSp τ ⊓ commSp τ := ⟨hmem_w, hmem_c⟩
    rwa [hinf, Submodule.mem_bot] at hmem
  have hw0 : w = 0 := (isUnit_of_invertible (2 : ZMod 3)).smul_eq_zero.mp hzero
  rw [hw0, zero_add]
  exact hc

private lemma aux_mul_self_of_comm {τ u : OGroup Q} (hτ : τ * τ = 1) (hu : u * u = 1)
    (hcomm : τ * u = u * τ) : (u * τ) * (u * τ) = 1 := by
  calc (u * τ) * (u * τ) = u * (τ * u) * τ := by group
    _ = u * (u * τ) * τ := by rw [hcomm]
    _ = (u * u) * (τ * τ) := by group
    _ = 1 := by rw [hu, hτ, mul_one]

theorem t5_k1_finrank_fixSp (hdim : Module.finrank (ZMod 3) V = 6) {τ : OGroup Q}
    (hty : invType τ = (4, -1)) : Module.finrank (ZMod 3) (fixSp τ) = 2 := by
  have hd : invDim τ = 4 := by simpa only [invType] using congrArg Prod.fst hty
  simp only [invDim] at hd
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) τ
  omega

theorem t5_k1_invType_layer (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {τ u : OGroup Q} (hτ : τ * τ = 1) (hty : invType τ = (4, -1)) (hu : u * u = 1) (hu1 : u ≠ 1)
    (huΩ : u ∈ omegaGroup hQ) (hcomm : τ * u = u * τ) (hfix : fixSp τ ≤ fixSp u) :
    invType u = (2, -1) := by
  have hle : commSp u ≤ commSp τ := aux_commSp_le hτ hu hcomm hfix
  rcases t5_omega_involution_type (Q := Q) hdim hu huΩ with h | h | h | h
  · have h0 : invDim u = 0 := by simpa only [invType] using congrArg Prod.fst h
    exact absurd ((invDim_eq_zero_iff hu).mp h0) hu1
  · exact h
  · exfalso
    have hd : invDim u = 4 := by simpa only [invType] using congrArg Prod.fst h
    have hsu : invSign u = 1 := by simpa only [invType] using congrArg Prod.snd h
    have hdτ : invDim τ = 4 := by simpa only [invType] using congrArg Prod.fst hty
    have hfin : Module.finrank (ZMod 3) (commSp u) =
        Module.finrank (ZMod 3) (commSp τ) := by
      simp only [invDim] at hd hdτ
      omega
    have heq : commSp u = commSp τ := Submodule.eq_of_le_of_finrank_eq hle hfin
    have hsτ : invSign τ = -1 := by simpa only [invType] using congrArg Prod.snd hty
    have hsuτ : invSign u = invSign τ := by rw [eq_of_commSp_eq hQ hu hτ heq]
    rw [hsu, hsτ] at hsuτ
    exact absurd hsuτ (by decide)
  · exfalso
    have hd6 : invDim u = 6 := by simpa only [invType] using congrArg Prod.fst h
    have hdτ : invDim τ = 4 := by simpa only [invType] using congrArg Prod.fst hty
    have hle' : Module.finrank (ZMod 3) (commSp u) ≤ Module.finrank (ZMod 3) (commSp τ) :=
      Submodule.finrank_mono hle
    simp only [invDim] at hd6 hdτ
    omega

theorem t5_k1_invType_prod (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {τ u : OGroup Q} (hτ : τ * τ = 1) (hty : invType τ = (4, -1))
    (hu : u * u = 1) (hcomm : τ * u = u * τ) (hfix : fixSp τ ≤ fixSp u)
    (hu2 : invType u = (2, -1)) :
    invType (u * τ) = (2, 1) ∧ invType (piOrth Q * (u * τ)) = (4, -1) := by
  have huτ : (u * τ) * (u * τ) = 1 := aux_mul_self_of_comm hτ hu hcomm
  have hle : commSp u ≤ commSp τ := aux_commSp_le hτ hu hcomm hfix
  have hle_fix : commSp u ≤ fixSp (u * τ) := by
    intro v hv
    rw [mem_fixSp_iff]
    have hvτ : (τ : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff hτ).mp (hle hv)
    have hvu : (u : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff hu).mp hv
    change ((u : V ≃ₗ[ZMod 3] V) * (τ : V ≃ₗ[ZMod 3] V)) v = v
    rw [LinearEquiv.mul_apply, hvτ, map_neg, hvu, neg_neg]
  have horth : ∀ v ∈ commSp u, ∀ w ∈ commSp (u * τ), QuadraticMap.polar Q v w = 0 :=
    fun v hv w hw => polar_fixSp_commSp huτ (hle_fix hv) hw
  have hinv := invType_mul_of_orth hQ hu huτ horth
  have huprod : u * (u * τ) = τ := by rw [← mul_assoc, hu, one_mul]
  rw [huprod, hty] at hinv
  have hdu : invDim u = 2 := by simpa only [invType] using congrArg Prod.fst hu2
  have hsu : invSign u = -1 := by simpa only [invType] using congrArg Prod.snd hu2
  have hfst : (4 : ℕ) = invDim u + invDim (u * τ) := by
    simpa using congrArg Prod.fst hinv
  have hd : invDim (u * τ) = 2 := by omega
  have hsnd : (-1 : ℤˣ) = invSign u * invSign (u * τ) *
      (-1) ^ (invDim u * invDim (u * τ)) := by
    simpa using congrArg Prod.snd hinv
  have hs : invSign (u * τ) = 1 := by
    have h := hsnd
    rw [hdu, hd, hsu] at h
    have hpow : ((-1 : ℤˣ) ^ (2 * 2)) = 1 := by decide
    rw [hpow, mul_one] at h
    have hneg : ((-1 : ℤˣ) * (-1 : ℤˣ)) = 1 := by decide
    have hm := congrArg (fun x : ℤˣ => (-1 : ℤˣ) * x) h
    rw [hneg, ← mul_assoc, hneg, one_mul] at hm
    exact hm.symm
  have htu : invType (u * τ) = (2, 1) := by
    simp only [invType]
    rw [hd, hs]
  have hpi : invType (piOrth Q * (u * τ)) = (4, -1) := by
    have h := invType_piOrth_mul hQ huτ
    rw [hd, hs, hdim, hsgn] at h
    have hpow : ((-1 : ℤˣ) ^ (2 * (6 - 2))) = 1 := by decide
    rw [hpow] at h
    simpa using h
  exact ⟨htu, hpi⟩

theorem t5_k1_hasType_prod (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {τ u : OGroup Q} (hτ : τ * τ = 1) (hty : invType τ = (4, -1))
    (hu : u * u = 1) (hcomm : τ * u = u * τ) (hfix : fixSp τ ≤ fixSp u)
    (hu2 : invType u = (2, -1)) : HasType (toProj Q (u * τ)) 4 (-1) := by
  have huτ : (u * τ) * (u * τ) = 1 := aux_mul_self_of_comm hτ hu hcomm
  have hprod := t5_k1_invType_prod hQ hdim hsgn hτ hty hu hcomm hfix hu2
  have hd : invDim (u * τ) = 2 := by
    have := congrArg Prod.fst hprod.1
    simpa only [invType] using this
  unfold HasType
  refine ⟨?_, piOrth Q * (u * τ), piOrth_mul_mul_self huτ, hprod.2, ?_⟩
  · intro h1
    have hmem : u * τ ∈ piGroup Q := by
      have h' : (u * τ : OGroup Q ⧸ piGroup Q) = 1 := by simpa [toProj] using h1
      exact (QuotientGroup.eq_one_iff (u * τ)).mp h'
    rcases mem_piGroup_iff.mp hmem with h1 | h1
    · have h0 : invDim (u * τ) = 0 := (invDim_eq_zero_iff huτ).mpr h1
      omega
    · have h6 : invDim (u * τ) = Module.finrank (ZMod 3) V :=
        (invDim_eq_finrank_iff huτ).mpr h1
      omega
  · rw [map_mul, toProj_piOrth, one_mul]

end CFSG.OddStandard.SmallF3.Omega
