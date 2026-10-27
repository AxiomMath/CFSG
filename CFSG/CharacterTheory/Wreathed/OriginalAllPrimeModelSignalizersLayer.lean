module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersLayerElements

public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.CentralSL2 CFSG.ABGTheoremB
open scoped Pointwise

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem toGL_commute_weyl_of_mem {t : SpecialLinearGroup (Fin 2) F}
    (ht : t ∈ Subgroup.centralizer {weyl F}) :
    SpecialLinearGroup.toGL t * SpecialLinearGroup.toGL (weyl F) =
      SpecialLinearGroup.toGL (weyl F) * SpecialLinearGroup.toGL t := by
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp ht]

theorem rootGroup_mem_signalizers [Fintype F] (h2 : (2 : F) ≠ 0) (hd : Odd (Nat.card Sigma))
    {p f : ℕ} (hcard : Nat.card F = p ^ f) {i : F} (hi : i * i = -1) :
    rootGroup b m hm heven Sigma hSigma i hi ∈
      signalizers (modelLayer b m hm heven Sigma hSigma) (modelC b m hm heven Sigma hSigma) p := by
  refine ⟨rootGroup_le_modelLayer hi, IsPGroup.of_card (by rw [card_rootGroup, hcard]), ?_, ?_⟩
  · apply le_normalizer_of_forall_conj_mem
    intro c hc x hx
    obtain ⟨l, rfl⟩ := mem_rootGroup_iff.mp hx
    obtain ⟨G, hG⟩ := exists_projectiveMap_eq c.left
    have hGc := (mem_modelC_iff_commute hG).mp hc
    rw [conj_inl_specialInclusion hG, fieldSL_rootSL hd h2,
      matrixConjugation_rootSL_of_commute hi hGc]
    exact inl_rootSL_mem_rootGroup hi _
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨l, rfl⟩ := mem_rootGroup_iff.mp hxQ
    rw [inl_specialInclusion_mem_modelC_iff, rootSL_mem_torus_iff h2] at hxC
    subst hxC
    rw [rootSL_zero, map_one, map_one]
    exact Subgroup.one_mem _

theorem rootGroup_ne_rootGroup_neg (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) :
    rootGroup b m hm heven Sigma hSigma i hi ≠
      rootGroup b m hm heven Sigma hSigma (-i) (neg_mul_neg_eq_neg_one hi) := by
  intro h
  have hmem := inl_rootSL_mem_rootGroup (b := b) (m := m) (hm := hm) (heven := heven)
    (Sigma := Sigma) (hSigma := hSigma) hi 1
  rw [h] at hmem
  obtain ⟨l, hl⟩ := mem_rootGroup_iff.mp hmem
  have hZ := inl_specialInclusion_injective hl
  have e01 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => X 0 1) hZ
  have e00 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => X 0 0) hZ
  change l = 1 at e01
  change 1 + l * -i = 1 + 1 * i at e00
  rw [e01] at e00
  have hi0 : i = 0 := by
    have h2i : (2 : F) * i = 0 := by linear_combination -e00
    exact (mul_eq_zero.mp h2i).resolve_left h2
  rw [hi0, mul_zero] at hi
  exact one_ne_zero (neg_eq_zero.mp hi.symm)

theorem modelLayer_eq_rootGroup_sup (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) :
    modelLayer b m hm heven Sigma hSigma =
      rootGroup b m hm heven Sigma hSigma i hi ⊔
        rootGroup b m hm heven Sigma hSigma (-i) (neg_mul_neg_eq_neg_one hi) := by
  apply le_antisymm
  · rw [modelLayer_eq_matrixLayer, matrixLayer, MonoidHom.range_eq_map, ← closure_rootSL h2 hi,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨Z, hZ, rfl⟩
    rcases hZ with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · exact Subgroup.mem_sup_left (inl_rootSL_mem_rootGroup hi l)
    · exact Subgroup.mem_sup_right (inl_rootSL_mem_rootGroup _ l)
  · exact sup_le (rootGroup_le_modelLayer hi) (rootGroup_le_modelLayer _)

theorem conjSub_rootGroup_of_conj_modelY [Fintype F] (h2 : (2 : F) ≠ 0)
    (hd : Odd (Nat.card Sigma)) {i : F} (hi : i * i = -1)
    {h : SemilinearExtension F b m hm heven Sigma hSigma}
    (hh : h * modelY b m hm heven Sigma hSigma * h⁻¹ =
      modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma) :
    TotallyInverted.conjSub h (rootGroup b m hm heven Sigma hSigma i hi) =
      rootGroup b m hm heven Sigma hSigma (-i) (neg_mul_neg_eq_neg_one hi) := by
  obtain ⟨G, hG⟩ := exists_projectiveMap_eq h.left
  have hGJ := (conj_modelY_eq_modelX_mul_iff hG).mp hh
  set μ := -(G.val 0 0 - G.val 1 0 * i) / (G.val 0 0 + G.val 1 0 * i) with hμ
  have hconj : ∀ l, h * SemidirectProduct.inl (specialInclusion F b m hm heven
      (rootSL i hi l)) * h⁻¹ = SemidirectProduct.inl (specialInclusion F b m hm heven
        (rootSL (-i) (neg_mul_neg_eq_neg_one hi) ((h.right : F ≃+* F) l * μ))) := by
    intro l
    rw [conj_inl_specialInclusion hG, fieldSL_rootSL hd h2,
      matrixConjugation_rootSL_of_conj_eq_inv hi hGJ]
  have hμ0 : μ ≠ 0 := by
    obtain ⟨h11, h01⟩ := entries_of_conj_weyl_eq_inv hGJ
    have hdet := GeneralLinearGroup.det_ne_zero G
    rw [det_fin_two] at hdet
    have hprod : (G.val 0 0 - G.val 1 0 * i) * (G.val 0 0 + G.val 1 0 * i) ≠ 0 := by
      intro h0
      apply hdet
      change G.val 0 0 * G.val 1 1 - G.val 0 1 * G.val 1 0 = 0
      rw [h11, h01]
      linear_combination -h0 - G.val 1 0 ^ 2 * hi
    rw [hμ]
    exact div_ne_zero (neg_ne_zero.mpr (left_ne_zero_of_mul hprod))
      (right_ne_zero_of_mul hprod)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨l, rfl⟩ := mem_rootGroup_iff.mp hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj]
    exact inl_rootSL_mem_rootGroup _ _
  · intro y hy
    obtain ⟨l', rfl⟩ := mem_rootGroup_iff.mp hy
    refine ⟨SemidirectProduct.inl (specialInclusion F b m hm heven
      (rootSL i hi ((h.right : F ≃+* F).symm (l' / μ)))), inl_rootSL_mem_rootGroup hi _, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj, RingEquiv.apply_symm_apply,
      div_mul_cancel₀ _ hμ0]

theorem signalizer_le_rootGroup_or [Fintype F] (h2 : (2 : F) ≠ 0) (hq : 5 < Nat.card F)
    (h4 : 4 ∣ m) {i : F} (hi : i * i = -1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hX : X ∈ signalizers (modelLayer b m hm heven Sigma hSigma)
      (modelC b m hm heven Sigma hSigma) r) :
    X ≤ rootGroup b m hm heven Sigma hSigma i hi ∨
      X ≤ rootGroup b m hm heven Sigma hSigma (-i) (neg_mul_neg_eq_neg_one hi) :=
  le_or_le_of_forall_mem_or_mem fun _ hx =>
    mem_rootGroup_of_mem_signalizer h2 hq h4 hi hr hr2 hX hx

theorem eq_bot_or_eq_rootGroup [Fintype F] (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1)
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hXQ : X ≤ rootGroup b m hm heven Sigma hSigma i hi)
    (hXC : modelC b m hm heven Sigma hSigma ≤ Subgroup.normalizer (X : Set _)) :
    X = ⊥ ∨ X = rootGroup b m hm heven Sigma hSigma i hi := by
  by_cases hX : X = ⊥
  · exact Or.inl hX
  right
  have hadd : ∀ l l' : F,
      (SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL i hi l)) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ X →
      (SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL i hi l')) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ X →
      (SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL i hi (l + l'))) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ X := by
    intro l l' h h'
    rw [rootSL_add, ← inl_specialInclusion_mul]
    exact X.mul_mem h h'
  have hsq : ∀ (μ l : F),
      (SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL i hi l)) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ X →
      (SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL i hi (l * μ ^ 2))) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ X := by
    intro μ l hl
    by_cases hμ : μ = 0
    · rw [hμ, zero_pow two_ne_zero, mul_zero, rootSL_zero, map_one, map_one]
      exact X.one_mem
    obtain ⟨t, ht⟩ :=
      (CFSG.Wreathed.OddFieldTorus.torusToUnits_bijective h2 i hi).2 (Units.mk0 μ hμ)
    have hμt : (t : SpecialLinearGroup (Fin 2) F) 0 0 +
        i * (t : SpecialLinearGroup (Fin 2) F) 1 0 = μ := congrArg Units.val ht
    have htT : (t : SpecialLinearGroup (Fin 2) F) ∈ Subgroup.centralizer {weyl F} := t.2
    have hc : (SemidirectProduct.inl (specialInclusion F b m hm heven
        (t : SpecialLinearGroup (Fin 2) F)) : SemilinearExtension F b m hm heven Sigma hSigma) ∈
          modelC b m hm heven Sigma hSigma :=
      (inl_specialInclusion_mem_modelC_iff _).mpr htT
    have hmem := (Subgroup.mem_normalizer_iff.mp (hXC hc) _).mp hl
    have hG : projectiveMap F b m hm heven
        (SemidirectProduct.inl (specialInclusion F b m hm heven
          (t : SpecialLinearGroup (Fin 2) F)) :
            SemilinearExtension F b m hm heven Sigma hSigma).left =
          ProjGenLinGroup.mk (SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 2) F)) :=
      projectiveMap_specialInclusion F b m hm heven _
    rw [conj_inl_specialInclusion hG] at hmem
    simp only [SemidirectProduct.right_inl, OneMemClass.coe_one, fieldSL_one,
      MulAut.one_apply] at hmem
    rw [matrixConjugation_rootSL_of_commute hi (toGL_commute_weyl_of_mem htT)] at hmem
    have hsum := CFSG.Wreathed.OddFieldTorus.torus_sq_add_sq (L := F) htT
    have hD := sub_mul_ne_zero_of_commute_weyl hi (toGL_commute_weyl_of_mem htT)
    have hκ : ((SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 2) F)).val 0 0 +
        (SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 2) F)).val 1 0 * i) /
        ((SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 2) F)).val 0 0 -
          (SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 2) F)).val 1 0 * i) = μ ^ 2 := by
      rw [div_eq_iff hD]
      change (t : SpecialLinearGroup (Fin 2) F) 0 0 + (t : SpecialLinearGroup (Fin 2) F) 1 0 * i =
        μ ^ 2 * ((t : SpecialLinearGroup (Fin 2) F) 0 0 -
          (t : SpecialLinearGroup (Fin 2) F) 1 0 * i)
      rw [← hμt]
      linear_combination
        -((t : SpecialLinearGroup (Fin 2) F) 0 0 + (t : SpecialLinearGroup (Fin 2) F) 1 0 * i) *
          hsum +
        ((t : SpecialLinearGroup (Fin 2) F) 0 0 + (t : SpecialLinearGroup (Fin 2) F) 1 0 * i) *
          (t : SpecialLinearGroup (Fin 2) F) 1 0 ^ 2 * hi
    rw [hκ] at hmem
    exact hmem
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX
  obtain ⟨l₀, rfl⟩ := mem_rootGroup_iff.mp (hXQ hx)
  have hl₀ : l₀ ≠ 0 := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    change SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL i hi 0)) = 1
    rw [rootSL_zero, map_one, map_one]
  apply le_antisymm hXQ
  intro y hy
  obtain ⟨l, rfl⟩ := mem_rootGroup_iff.mp hy
  obtain ⟨a, c, hac⟩ := CFSG.Wreathed.OddFieldTorus.exists_sq_add_sq h2 (l / l₀)
  have hl : l = l₀ * a ^ 2 + l₀ * c ^ 2 := by
    rw [← mul_add, hac, mul_div_cancel₀ _ hl₀]
  rw [hl]
  exact hadd _ _ (hsq a l₀ hx) (hsq c l₀ hx)

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
