module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCentFix

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (commutatorElement_mul_mem_center)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem false_of_k2_isoCent [Finite K] (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {M : Subgroup (GL (Fin d) K)} (hd : K2Data R M)
    {gs : similarityPairs (oQ R)} (hσ : gs.val.right = 1)
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ gs))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ gs))))
    (hN : Group.IsSolvable (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ :
        Subgroup (GL (Fin d) K)) ∨
      IsQuasisimple (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin d) K)))
    {u : GL (Fin d) K}
    (hu : u ∈ (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin d) K)))
    (huu : u * u = 1) (hu1 : u ≠ 1) (hun : u ≠ -1) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set H := matrixDerived (oQ R) with hH
  set S := gs.val.left with hSdef
  set N : Subgroup (GL (Fin d) K) := ⁅isoCent R S, isoCent R S⁆ with hNdef
  set Qb := (M.subgroupOf H).map (projH H) with hQb
  have hperfH : ⁅M.subgroupOf H, M.subgroupOf H⁆ = M.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hd.le, hd.perf]
  have hfixP : ∀ X ∈ M.subgroupOf H, oκ _ gs (projH H X) = projH H X :=
    fun X hX => hQs ⟨X, hX, rfl⟩
  have hSM : ∀ X ∈ M, X * S = S * X := by
    intro X hX
    have e := kappa_eq_of_fix gs hperfH hfixP (X := ⟨X, hd.le hX⟩) (mem_subgroupOf.2 hX)
    rw [hσ] at e
    have e2 : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map ⇑(1 : K ≃+* K) = X := by
      ext
      rfl
    change (S : Matrix (Fin d) (Fin d) K) * ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map
      ⇑(1 : K ≃+* K) * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = X at e
    rw [e2] at e
    have e' : S * X * S⁻¹ = X := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact e)
    calc X * S = S * X * S⁻¹ * S := by rw [e']
      _ = S * X := by group
  have hiso : ∀ X ∈ M, X ∈ CatalogueBGraphForm.isometryGroup d K R := fun X hX =>
    (mem_matrixIsometries_oQ h2 R hR X).1 (matrixDerived_le_isometries _ (hd.le hX))
  have hMC : M ≤ isoCent R S := fun X hX =>
    ⟨hiso X hX, mem_centralizer_singleton_iff.2 (hSM X hX)⟩
  have hMN : M ≤ N := by
    rw [← hd.perf]
    exact commutator_mono hMC hMC
  have hNH : N ≤ H := by
    rw [hH, matrixDerived_oQ h2 R hR]
    exact commutator_mono inf_le_left inf_le_left
  set Pn := (N.subgroupOf H).map (projH H) with hPn
  have hQP : Qb ≤ Pn := map_mono fun g hg => mem_subgroupOf.2 (hMN (mem_subgroupOf.1 hg))
  have hPs : Pn ≤ autFixed (oκ _ gs) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Burgoyne.DX.mem_autFixed_iff, kappa_proj]
    congr 1
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, hσ, map_one, MulAut.one_apply]
    have hgC : (g : GL (Fin d) K) ∈ isoCent R S := commutator_le_self _ (mem_subgroupOf.1 hg)
    have hc := mem_centralizer_singleton_iff.1 (mem_inf.1 hgC).2
    change S * (g : GL (Fin d) K) * S⁻¹ = g
    rw [← hc, mul_inv_cancel_right]
  have hQc' := C.isPComponent_subgroupOf_of_le hQP hPs hQc
  set φ := (projH H).comp ((N.subgroupOf H).subtype.comp
    (subgroupOfEquivOfLe hNH).symm.toMonoidHom) with hφ
  have hφr : φ.range = Pn := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (subgroupOfEquivOfLe hNH).symm.surjective, Subgroup.map_top, Subgroup.range_subtype]
  rcases hN with hsol | hqs
  · have : Group.IsSolvable φ.range := Group.isSolvable_of_surjective φ.rangeRestrict_surjective
    rw [hφr] at this
    exact C.not_le_of_isSolvable hQP hQc' this hQP
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hqs φ with hb | hqr
  · rw [hφr] at hb
    rw [hb] at hQP
    exact C.ne_bot_of_isPComponent hQs hQc (le_bot_iff.1 hQP)
  rw [hφr] at hqr
  have heq := C.eq_of_le_of_isQuasisimple hQP le_rfl hQc' hqr
  have hlift : ∀ g (hg : g ∈ N), ∃ m ∈ M.subgroupOf H, ∃ z ∈ center H,
      (⟨g, hNH hg⟩ : H) = m * z := by
    intro g hg
    have hgP : projH H ⟨g, hNH hg⟩ ∈ Qb := by
      rw [heq]
      exact ⟨⟨g, hNH hg⟩, mem_subgroupOf.2 hg, rfl⟩
    obtain ⟨m, hm, hmg⟩ := hgP
    exact ⟨m, hm, m⁻¹ * ⟨g, hNH hg⟩,
      scalars_subgroupOf_le_center ((projH_eq_projH_iff).1 hmg), by group⟩
  have hperfN : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.1 hqs.1
  have hNM : N ≤ M := by
    rw [← hperfN, commutator_le]
    intro a ha b hb
    obtain ⟨m₁, hm₁, z₁, hz₁, e₁⟩ := hlift a ha
    obtain ⟨m₂, hm₂, z₂, hz₂, e₂⟩ := hlift b hb
    have e : ⁅(⟨a, hNH ha⟩ : H), ⟨b, hNH hb⟩⁆ = ⁅m₁, m₂⁆ := by
      rw [e₁, e₂, commutatorElement_mul_mem_center m₁ m₂ hz₁ hz₂]
    have e' := congrArg Subtype.val e
    change ⁅a, b⁆ = ⁅(m₁ : GL (Fin d) K), (m₂ : GL (Fin d) K)⁆ at e'
    rw [e', ← hd.perf]
    exact commutator_mem_commutator (mem_subgroupOf.1 hm₁) (mem_subgroupOf.1 hm₂)
  rcases hd.inv u (hNM hu) huu with h | h
  · exact hu1 h
  · exact hun h

end CFSG.ComponentClassification.Burgoyne.DX.Kl
