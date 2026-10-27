module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma toProj_eq_or_eq_piOrth {a b : OGroup Q} (h : toProj Q a = toProj Q b) :
    a = b ∨ a = piOrth Q * b := by
  have hmem : a / b ∈ piGroup Q := by
    refine (QuotientGroup.eq_iff_div_mem (N := piGroup Q)).mp ?_
    change toProj Q a = toProj Q b
    exact h
  rcases mem_piGroup_iff.mp hmem with h1 | h1
  · left
    rw [div_eq_mul_inv] at h1
    exact mul_inv_eq_one.mp h1
  · right
    rw [div_eq_mul_inv] at h1
    rw [← h1]
    group

private lemma invDim_piOrth_mul (hQ : Q.Nondegenerate) {u : OGroup Q} (huu : u * u = 1) :
    invDim (piOrth Q * u) = Module.finrank (ZMod 3) V - invDim u := by
  simpa only [invType] using congrArg Prod.fst (invType_piOrth_mul hQ huu)

private lemma invDim_mul_le_two {s t : OGroup Q} (hss : s * s = 1) (htt : t * t = 1)
    (hs : invDim s = 6) (ht : invDim t = 6) (hdim : Module.finrank (ZMod 3) V = 7) :
    invDim (s * t) ≤ 2 := by
  have hle : commSp s ⊓ commSp t ≤ fixSp (s * t) := by
    intro v hv
    rw [Submodule.mem_inf] at hv
    rw [mem_fixSp_iff]
    have hsv : (s : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff hss).mp hv.1
    have htv : (t : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff htt).mp hv.2
    change ((s : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V)) v = v
    rw [LinearEquiv.mul_apply, htv, map_neg, hsv, neg_neg]
  have hmono := Submodule.finrank_mono hle
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (commSp s) (commSp t)
  have hleV := Submodule.finrank_le (commSp s ⊔ commSp t)
  have hsum := finrank_fixSp_add_finrank_commSp (s * t)
  simp only [invDim] at hs ht ⊢
  omega

private lemma mul_comm_of_toProj_mul_comm (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) {s t : OGroup Q} (hss : s * s = 1) (htt : t * t = 1)
    (hs : invDim s = 6) (ht : invDim t = 6) (h : toProj Q (s * t) = toProj Q (t * s)) :
    s * t = t * s := by
  rcases toProj_eq_or_eq_piOrth h with h1 | h1
  · exact h1
  · exfalso
    have heq : s * t * s⁻¹ = piOrth Q * t := by
      rw [h1]
      group
    have h6 : invDim (s * t * s⁻¹) = 6 := by
      have hconj : invDim (s * t * s⁻¹) = invDim t := by
        simpa only [invType] using congrArg Prod.fst (invType_conj hQ htt s)
      rw [hconj, ht]
    have h1' : invDim (piOrth Q * t) = 1 := by
      rw [invDim_piOrth_mul hQ htt, ht, hdim]
    rw [heq] at h6
    omega

theorem sec4F_sixsix_proj (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    {x y : ProjOrth Q} {α β : ℤˣ} (hxy : x * y = y * x) (hx : HasType x 6 α)
    (hy : HasType y 6 β) : ¬ HasType (x * y) 4 1 := by
  obtain ⟨-, s, hss, hs, rfl⟩ := hx
  obtain ⟨-, t, htt, ht, rfl⟩ := hy
  have hsd : invDim s = 6 := congrArg Prod.fst hs
  have htd : invDim t = 6 := congrArg Prod.fst ht
  have hcomm_proj : toProj Q (s * t) = toProj Q (t * s) := by
    rw [map_mul, map_mul, hxy]
  have hcomm : s * t = t * s :=
    mul_comm_of_toProj_mul_comm hQ hdim hss htt hsd htd hcomm_proj
  have hst : (s * t) * (s * t) = 1 := by
    have h : (s * t) * (s * t) = (s * s) * (t * t) := by
      calc (s * t) * (s * t) = s * (t * s) * t := by group
        _ = s * (s * t) * t := by rw [← hcomm]
        _ = (s * s) * (t * t) := by group
    rw [h, hss, htt, mul_one]
  have hle2 : invDim (s * t) ≤ 2 := invDim_mul_le_two hss htt hsd htd hdim
  intro hc
  obtain ⟨-, u, huu, hu, hu'⟩ := hc
  have hud : invDim u = 4 := congrArg Prod.fst hu
  have hproj : toProj Q u = toProj Q (s * t) := by
    rw [hu', map_mul]
  rcases toProj_eq_or_eq_piOrth hproj with hu1 | hu1
  · rw [hu1] at hud
    omega
  · have h5 : 5 ≤ invDim u := by
      rw [hu1, invDim_piOrth_mul hQ hst, hdim]
      omega
    omega

end CFSG.OddStandard.SmallF3.Omega
