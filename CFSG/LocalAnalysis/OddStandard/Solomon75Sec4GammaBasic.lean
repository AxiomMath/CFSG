module

public import CFSG.Open.AschbacherProperTwoGeneratedCoreMilestoneDefs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Subgroup CFSG.Open
open scoped Pointwise

section Basic

variable {K K' : Type*} [Group K] [Group K'] [Finite K] [Finite K']

theorem normalizer_le_gamma {S Q : Subgroup K} (hQS : Q ≤ S) (hQ : 2 ≤ Open.pRank 2 Q) :
    normalizer (Q : Set K) ≤ properTwoGenCoreGamma S 2 := by
  unfold properTwoGenCoreGamma
  exact le_iSup₂_of_le Q hQS (le_iSup_of_le hQ le_rfl)

theorem center_le_gamma {S Q : Subgroup K} (hQS : Q ≤ S) (hQ : 2 ≤ Open.pRank 2 Q) :
    center K ≤ properTwoGenCoreGamma S 2 :=
  (Subgroup.center_le_normalizer (s := (Q : Set K))).trans (normalizer_le_gamma hQS hQ)

theorem pRank_map_mulEquiv (φ : K ≃* K') (H : Subgroup K) :
    Open.pRank 2 (H.map φ.toMonoidHom) = Open.pRank 2 H := by
  refine le_antisymm ?_ (CFSG.SectionRank.pRank_le_map (by norm_num) φ.toMonoidHom φ.injective H)
  have h := CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) φ.symm.toMonoidHom
    φ.symm.injective (H.map φ.toMonoidHom)
  have e : (H.map φ.toMonoidHom).map φ.symm.toMonoidHom = H := by
    rw [Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id K := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  rwa [e] at h

theorem gamma_map_equiv (φ : K ≃* K') (S : Subgroup K) :
    properTwoGenCoreGamma (S.map φ.toMonoidHom) 2 =
      (properTwoGenCoreGamma S 2).map φ.toMonoidHom := by
  apply le_antisymm
  · unfold properTwoGenCoreGamma
    refine iSup_le fun Q' => iSup_le fun hQ'S => iSup_le fun hQ' => ?_
    set Q : Subgroup K := Q'.comap φ.toMonoidHom with hQdef
    have hQmap : Q.map φ.toMonoidHom = Q' :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective Q'
    have hQS : Q ≤ S := by
      rw [hQdef, ← Subgroup.comap_map_eq_self_of_injective
        (show Function.Injective φ.toMonoidHom from φ.injective) S]
      exact Subgroup.comap_mono hQ'S
    have hr : 2 ≤ Open.pRank 2 Q := by
      rw [← pRank_map_mulEquiv φ Q, hQmap]
      exact hQ'
    have h1 := normalizer_le_gamma hQS hr
    have h2 : (normalizer (Q : Set K)).map φ.toMonoidHom ≤
        (properTwoGenCoreGamma S 2).map φ.toMonoidHom := Subgroup.map_mono h1
    rwa [Subgroup.map_equiv_normalizer_eq, hQmap] at h2
  · rw [Subgroup.map_le_iff_le_comap]
    unfold properTwoGenCoreGamma
    refine iSup_le fun Q => iSup_le fun hQS => iSup_le fun hQ => ?_
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_equiv_normalizer_eq]
    exact normalizer_le_gamma (Subgroup.map_mono hQS)
      (by rwa [pRank_map_mulEquiv φ Q])

theorem gamma_conj (g : K) (S : Subgroup K) :
    properTwoGenCoreGamma (S.map (MulAut.conj g).toMonoidHom) 2 =
      (properTwoGenCoreGamma S 2).map (MulAut.conj g).toMonoidHom :=
  gamma_map_equiv (MulAut.conj g) S

theorem exists_sylow_map_conj_eq (S₀ S : Sylow 2 K) :
    ∃ g : K, (S : Subgroup K) = (S₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S₀ S
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map_equiv]
  simp [MulAut.smul_def, mul_assoc]

theorem gamma_eq_top_of_sylow {S₀ : Sylow 2 K} (S : Sylow 2 K)
    (h : properTwoGenCoreGamma (S₀ : Subgroup K) 2 = ⊤) :
    properTwoGenCoreGamma (S : Subgroup K) 2 = ⊤ := by
  obtain ⟨g, hg⟩ := exists_sylow_map_conj_eq S₀ S
  rw [hg, gamma_conj, h]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

theorem gamma_map_subtype_le {L : Subgroup K} {Q : Subgroup ↥L} {S : Subgroup K}
    (hQ : Q.map L.subtype ≤ S) :
    (properTwoGenCoreGamma Q 2).map L.subtype ≤ properTwoGenCoreGamma S 2 := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold properTwoGenCoreGamma
  refine iSup_le fun T => iSup_le fun hTQ => iSup_le fun hT => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine (Subgroup.le_normalizer_map L.subtype).trans ?_
  exact normalizer_le_gamma ((Subgroup.map_mono hTQ).trans hQ)
    (hT.trans (CFSG.SectionRank.pRank_le_map (by norm_num) L.subtype L.subtype_injective T))

end Basic

theorem conj_smul_subgroup_eq_map {K : Type*} [Group K] (g : K) (H : Subgroup K) :
    (MulAut.conj g) • H = H.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map_equiv]
  simp [MulAut.smul_def, mul_assoc]

section Frattini

variable {X : Type*} [Group X]

@[expose] def normalizerConjEquiv (A : Subgroup X) (g : X) (hg : g ∈ normalizer (A : Set X)) :
    ↥A ≃* ↥A where
  toFun a := ⟨g * a * g⁻¹, (mem_normalizer_iff.1 hg a).1 a.2⟩
  invFun a := ⟨g⁻¹ * a * g, (mem_normalizer_iff.1 hg (g⁻¹ * a * g)).2 (by
    have : g * (g⁻¹ * (a : X) * g) * g⁻¹ = a := by group
    rw [this]
    exact a.2)⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem normalizerConjEquiv_apply (A : Subgroup X) (g : X) (hg : g ∈ normalizer (A : Set X))
    (a : ↥A) : ((normalizerConjEquiv A g hg a : ↥A) : X) = g * a * g⁻¹ := by
  simp [normalizerConjEquiv]

theorem gamma_frattini (A : Subgroup X) [Finite A] (S : Sylow 2 ↥A) :
    ∀ g ∈ normalizer (A : Set X), ∃ a ∈ A, ∃ b ∈ normalizer
      (((properTwoGenCoreGamma (S : Subgroup ↥A) 2).map A.subtype : Subgroup X) : Set X),
      g = a * b := by
  intro g hg
  set σ := normalizerConjEquiv A g hg with hσ
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥A
    (Sylow.mapSurjective (show Function.Surjective σ.toMonoidHom from σ.surjective) S) S
  set τ : ↥A ≃* ↥A := σ.trans (MulAut.conj k) with hτ
  have h1 : ((S : Subgroup ↥A).map σ.toMonoidHom).map (MulAut.conj k).toMonoidHom =
      (S : Subgroup ↥A) := by
    have := congrArg (fun P : Sylow 2 ↥A => (P : Subgroup ↥A)) hk
    simp only [Sylow.coe_subgroup_smul, Sylow.coe_mapSurjective] at this
    rwa [conj_smul_subgroup_eq_map] at this
  have hSτ : (S : Subgroup ↥A).map τ.toMonoidHom = (S : Subgroup ↥A) := by
    calc (S : Subgroup ↥A).map τ.toMonoidHom
        = ((S : Subgroup ↥A).map σ.toMonoidHom).map (MulAut.conj k).toMonoidHom := by
          rw [Subgroup.map_map]; rfl
      _ = S := h1
  have hΓτ : (properTwoGenCoreGamma (S : Subgroup ↥A) 2).map τ.toMonoidHom =
      properTwoGenCoreGamma (S : Subgroup ↥A) 2 := by
    rw [← gamma_map_equiv, hSτ]
  refine ⟨(k : X)⁻¹, (k⁻¹).2, (k : X) * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : (MulAut.conj ((k : X) * g)).toMonoidHom.comp A.subtype =
        A.subtype.comp τ.toMonoidHom := by
      ext a
      simp [hτ, hσ, normalizerConjEquiv_apply, mul_assoc]
    rw [Subgroup.map_map]
    show Subgroup.map ((MulAut.conj ((k : X) * g)).toMonoidHom.comp A.subtype) _ = _
    rw [hcomp, ← Subgroup.map_map, hΓτ]
  · group

end Frattini

end CFSG.OddStandard.Solomon75.AhatData
