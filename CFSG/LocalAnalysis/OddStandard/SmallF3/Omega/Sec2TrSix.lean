module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2BlockInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def omegaInr (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp s)) :
    omegaGroup (nondegenerate_restrict_commSp hQ hs) →* omegaGroup hQ :=
  ((blockInr hs).comp (omegaGroup (nondegenerate_restrict_commSp hQ hs)).subtype).codRestrict
    (omegaGroup hQ) (fun b => blockInr_mem_omegaGroup hQ hs hU b.2)

theorem coe_omegaInr (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp s))
    (b : omegaGroup (nondegenerate_restrict_commSp hQ hs)) :
    ((omegaInr hQ hs hU b : omegaGroup hQ) : OGroup Q) = blockInr hs (b : OGroup _) := rfl

@[expose] noncomputable def omegaProjInr (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp s)) :
    omegaGroup (nondegenerate_restrict_commSp hQ hs) →* omegaProj hQ :=
  (omegaToProj hQ).comp (omegaInr hQ hs hU)

theorem omegaProjInr_injective (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp s))
    (hW : 0 < Module.finrank (ZMod 3) (fixSp s)) :
    Function.Injective (omegaProjInr hQ hs hU) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  rcases (omegaToProj_eq_one_iff hQ (omegaInr hQ hs hU b)).mp hb with h | h
  · apply Subtype.ext
    exact blockInr_injective hs (h.trans (map_one (blockInr hs)).symm)
  · exfalso
    obtain ⟨w, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hW
    have happ := blockHom_apply hs (1, (b : OGroup _)) w 0
    have h1 : ((blockInr hs (b : OGroup _) : OGroup Q) : V ≃ₗ[ZMod 3] V) (w : V) = (w : V) := by
      have h0 : (w : V) + ((0 : commSp s) : V) = (w : V) := by simp
      rw [blockInr_apply, ← h0, happ]
      simp
    have h2 : ((piOrth Q : OGroup Q) : V ≃ₗ[ZMod 3] V) (w : V) = -(w : V) :=
      coe_piOrth_apply (w : V)
    rw [coe_omegaInr] at h
    rw [h, h2] at h1
    have h3 : (2 : ZMod 3) • (w : V) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      exact neg_add_cancel _
    have h4 : (w : V) = 0 := (smul_eq_zero.mp h3).resolve_left (by decide)
    exact hw0 (Subtype.ext h4)

theorem omegaProjInr_range_normal (hQ : Q.Nondegenerate) {y : omegaGroup hQ}
    (hyy : (y : OGroup Q) * y = 1) (hU : 2 ≤ Module.finrank (ZMod 3) (commSp (y : OGroup Q)))
    (hne : Module.finrank (ZMod 3) (commSp (y : OGroup Q)) * 2 ≠ Module.finrank (ZMod 3) V) :
    (((omegaProjInr hQ hyy hU).range).subgroupOf
        (Subgroup.centralizer ({omegaToProj hQ y} : Set (omegaProj hQ)))).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hn
  obtain ⟨c, hc⟩ := omegaToProj_surjective hQ (g : omegaProj hQ)
  have hg : (g : omegaProj hQ) * omegaToProj hQ y = omegaToProj hQ y * (g : omegaProj hQ) :=
    Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hcy : omegaToProj hQ (c * y * c⁻¹) = omegaToProj hQ y := by
    rw [map_mul, map_mul, map_inv, hc]
    exact mul_inv_eq_iff_eq_mul.mpr hg
  rcases omegaToProj_eq_iff hQ hcy.symm with h | h
  · have h' : (c : OGroup Q) * (y : OGroup Q) * (c : OGroup Q)⁻¹ = (y : OGroup Q) := h
    have hcc : (c : OGroup Q) ∈ Subgroup.centralizer ({(y : OGroup Q)} : Set (OGroup Q)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h')
    obtain ⟨c₂, hc₂⟩ := blockInr_conj hQ hyy hcc (b : OGroup _)
    have hmem : c₂ * (b : OGroup _) * c₂⁻¹ ∈ omegaGroup (nondegenerate_restrict_commSp hQ hyy) :=
      (omegaGroup_normal _).conj_mem _ b.2 c₂
    refine ⟨⟨c₂ * (b : OGroup _) * c₂⁻¹, hmem⟩, ?_⟩
    have hcb : c * omegaInr hQ hyy hU b * c⁻¹ = omegaInr hQ hyy hU ⟨_, hmem⟩ :=
      Subtype.ext hc₂
    calc omegaProjInr hQ hyy hU ⟨c₂ * (b : OGroup _) * c₂⁻¹, hmem⟩
        = omegaToProj hQ (c * omegaInr hQ hyy hU b * c⁻¹) := by rw [hcb]; rfl
      _ = (g : omegaProj hQ) * (n : omegaProj hQ) * (g : omegaProj hQ)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hc, ← hb]
          rfl
  · exfalso
    have h' : (c : OGroup Q) * (y : OGroup Q) * (c : OGroup Q)⁻¹ = piOrth Q * (y : OGroup Q) := h
    have h1 := congrArg (fun t => (invType t).1) h'
    rw [invType_conj hQ hyy (c : OGroup Q), invType_piOrth_mul hQ hyy] at h1
    have h2 := invDim_le (y : OGroup Q)
    simp only [invType, invDim] at h1 h2 hne
    omega

end CFSG.OddStandard.SmallF3.Omega
