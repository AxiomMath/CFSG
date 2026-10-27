module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.Gen

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem conj_mem_M2_of_commute (hgam : gam * jInv * gam⁻¹ = z0) {t : J}
    (ht : t ∈ Subgroup.centralizer ({jInv} : Set J)) : gam * t * gam⁻¹ ∈ M2 := by
  have hc : Commute jInv t := (Subgroup.mem_centralizer_singleton_iff.1 ht).symm
  have hc' := hc.map (MulAut.conj gam).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc'
  rw [hgam] at hc'
  exact Subgroup.mem_centralizer_singleton_iff.2 hc'.eq.symm

theorem hover_of_WA
    (hgam : gam * jInv * gam⁻¹ = z0)
    (hgens : c1j ∈ Subgroup.normalizer (Q11 : Set J) ⊓ Subgroup.centralizer ({jInv} : Set J) ∧
      nrm₂ ∈ Subgroup.normalizer (Q11 : Set J) ⊓ Subgroup.centralizer ({jInv} : Set J) ∧
      qz ∈ Subgroup.normalizer (Q11 : Set J) ⊓ Subgroup.centralizer ({jInv} : Set J))
    (hWA : ∀ T' : Subgroup J, C0p ≤ T' → T' ≤ M2 → ¬ T' ≤ C0p →
      (∃ i : Fin 7, rRep i ∈ T') ∨ mElt ∈ T') :
    ∀ T : Subgroup J, Subgroup.normalizer (Q11 : Set J) ⊓ Subgroup.centralizer ({jInv} : Set J) < T →
      T ≤ Subgroup.centralizer ({jInv} : Set J) → Subgroup.normalizer (Q11 : Set J) ⊔ T = ⊤ := by
  intro T hCT hTW
  obtain ⟨h1, h2, h3⟩ := hgens
  set f : J →* J := (MulAut.conj gam).toMonoidHom with hf
  have hfx : ∀ x, f x = gam * x * gam⁻¹ := fun x => rfl
  set T' := T.map f with hT'
  have hT'M : T' ≤ M2 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hfx]
    exact conj_mem_M2_of_commute hgam (hTW ht)
  have hle : Subgroup.normalizer (Q11 : Set J) ⊓ Subgroup.centralizer ({jInv} : Set J) ≤ T :=
    hCT.le
  have hCT' : C0p ≤ T' := by
    unfold C0p
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨c1j, hle h1, rfl⟩
    · exact ⟨nrm₂, hle h2, rfl⟩
    · exact ⟨qz, hle h3, rfl⟩
  have hTC' : ¬ T' ≤ C0p := by
    intro hTC
    apply (lt_iff_le_not_ge.1 hCT).2
    intro t ht
    have hft : f t ∈ C0p := hTC ⟨t, ht, rfl⟩
    have hpre : C0p ≤ (Subgroup.normalizer (Q11 : Set J) ⊓
        Subgroup.centralizer ({jInv} : Set J)).map f := by
      unfold C0p
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl | rfl)
      · exact ⟨c1j, h1, rfl⟩
      · exact ⟨nrm₂, h2, rfl⟩
      · exact ⟨qz, h3, rfl⟩
    obtain ⟨s, hs, hst⟩ := hpre hft
    have hinj : Function.Injective f := (MulAut.conj gam).injective
    rw [hinj hst] at hs
    exact hs
  have hgen : ∀ i, i < 8 → gam⁻¹ * xElt i * gam ∈ T →
      Subgroup.normalizer (Q11 : Set J) ⊔ T = ⊤ := by
    intro i hi hx
    rw [eq_top_iff, ← normalizer_sup_closure_eq_top i hi]
    exact sup_le_sup_left ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hx)) _
  have hback : ∀ x, x ∈ T' → gam⁻¹ * x * gam ∈ T := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hfx]
    have e : gam⁻¹ * (gam * t * gam⁻¹) * gam = t := by group
    rw [e]
    exact ht
  rcases hWA T' hCT' hT'M hTC' with ⟨i, hi⟩ | hm
  · refine hgen i (by omega) ?_
    have e : xElt i = rRep i := by
      simp [xElt]
    rw [e]
    exact hback _ hi
  · refine hgen 7 (by norm_num) ?_
    have e : xElt 7 = mElt := by
      simp [xElt]
    rw [e]
    exact hback _ hm

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
