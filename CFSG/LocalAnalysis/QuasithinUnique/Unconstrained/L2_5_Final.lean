module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalSC

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

@[expose] def Lemma25FinalBadCaseExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2527 N t zK →
      T ≤ Subgroup.normalizer (N.S : Set G) →
        ∀ E : Subgroup G, E ≤ N.SK → IsFourSubgroup E →
          N.x ^ 2 ∉ Subgroup.normalizer (E : Set G) → False

section Final

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Lv2527.isUStarPair (h : Lv2527 N t zK) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) :
    IsUStarPair M N.H (N.S ⊓ Subgroup.normalizer (E : Set G))
      (N.H ⊓ Subgroup.normalizer (E : Set G)) := by
  obtain ⟨E₁, E₂, -, -, -, -, -, hall, -, hstars⟩ := h.concl2523
  have hmem : E ∈ ({E₁, E₂} : Set (Subgroup G)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hall E hEK hE4
  exact (hstars E hmem).1

theorem final_contra_of_sq (h : Lv2527 N t zK)
    (hsq : ∀ E : Subgroup G, E ≤ N.SK → IsFourSubgroup E →
      N.x ^ 2 ∈ Subgroup.normalizer (E : Set G)) : False := by
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  obtain ⟨D⟩ := exists_a6Datum N hKH h.facts258 h.concl2521
  obtain ⟨E, e, C, hE, hE4, hpair⟩ := FinalCtx.exists_E h D
  have hx2 : N.x ^ 2 ∈ Subgroup.normalizer (E : Set G) := hsq E hE.hEK hE4
  have hxx : N.x * N.x ∈ Subgroup.normalizer (E : Set G) := by rw [← sq]; exact hx2
  have hxxS : N.x * N.x ∈ N.S := by rw [← sq]; exact N.x_sq
  have hsupL : E ≤ E ⊔ CFSG.conjugate E N.x := le_sup_left
  have hsupR : CFSG.conjugate E N.x ≤ E ⊔ CFSG.conjugate E N.x := le_sup_right
  have hxN : N.x ∈ Subgroup.normalizer ((E ⊔ CFSG.conjugate E N.x : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_mem
    apply closed_sup_of
    · intro y hy
      have hw : N.x⁻¹ * y * N.x ∈ CFSG.conjugate E N.x := by
        rw [BenderBranch.mem_conjugate_iff]
        have : N.x * (N.x⁻¹ * y * N.x) * N.x⁻¹ = y := by group
        rw [this]; exact hy
      have h1 := C.normS_conj hE hxxS hxx _ hw
      have e1 : N.x * y * N.x⁻¹ = (N.x * N.x) * (N.x⁻¹ * y * N.x) * (N.x * N.x)⁻¹ := by group
      rw [e1]
      exact hsupR h1
    · intro y hy
      exact hsupL (BenderBranch.mem_conjugate_iff.mp hy)
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  have hAS : E ⊔ CFSG.conjugate E N.x ≤ N.S := by
    refine sup_le (fun y hy => N.SK_le_S (hE.hEK hy)) (fun g hg => ?_)
    have h1 : N.x * g * N.x⁻¹ ∈ E := BenderBranch.mem_conjugate_iff.mp hg
    have h2 := N.x_conj_S' (N.SK_le_S (hE.hEK h1))
    simpa [mul_assoc] using h2
  have hA2 : IsPGroup 2 ↥(E ⊔ CFSG.conjugate E N.x) := hS2.to_le hAS
  have hc := ((h.concl2512 hKH).1 _ _ hpair inf_le_left).2
  have hres := hc (E ⊔ CFSG.conjugate E N.x) hA2 (C.z_mem_A hE) (C.A_le hE) (C.norm_H_le hE)
  have hxS : N.x ∈ N.S :=
    cp_contra hs.setting.sylow.isPGroup (inf_le_left : N.S ⊓ Subgroup.normalizer (E : Set G) ≤ N.S)
      N.S_le_T hres.2 N.x_mem.1 hxN
  exact N.x_not_mem hxS

end Final

theorem lemma25Final (hbad : Lemma25FinalBadCaseExcluded) : Lemma25Final := by
  intro G _ _ T M hs N t zK h
  by_cases hsq : ∀ E : Subgroup G, E ≤ N.SK → IsFourSubgroup E →
      N.x ^ 2 ∈ Subgroup.normalizer (E : Set G)
  · exact final_contra_of_sq h hsq
  · push Not at hsq
    obtain ⟨E, hEK, hE4, hxE⟩ := hsq
    have hK0 : N.K0 = N.K := h.concl2520
    have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
      rw [← hK0]; exact N.H_le_normalizer_K0
    obtain ⟨D⟩ := exists_a6Datum N hKH h.facts258 h.concl2521
    have C : FinalCtx N t zK D := FinalCtx.of_lv h D
    obtain ⟨e, hE⟩ := C.exists_finalE hEK hE4
    have hT : T ≤ Subgroup.normalizer (N.S : Set G) :=
      bad_case_T_le h D C hE hE4 (h.isUStarPair hEK hE4) (fun hmem => hxE (by rw [sq]; exact hmem))
    exact hbad G T M hs N t zK h hT E hEK hE4 hxE

end CFSG.QuasithinUnique
