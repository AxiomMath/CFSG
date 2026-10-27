module

public import CFSG.Fischer.Classification.PartIII.U.SixAdm

public section

namespace CFSG.Fischer.Classification.LocalU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification LocalR3 F3

theorem ncard_D3_restrict_six_one {v : Fin 6 → ZMod 3} (hv : diagF3 6 1 v v = 1)
    {f' : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hf' : IsF3Form f')
    (e : perpOne (diagF3 6 1) v ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (he : ∀ a b : perpOne (diagF3 6 1) v, f' (e a) (e b) = diagF3 6 1 a b) :
    (D3 f').ncard = 45 := by
  obtain ⟨e', he'⟩ := exists_isometry_restrict_diagF3 (n := 5) (by norm_num) (δ := 1)
    (by decide) hv hf' e he
  exact (ncard_D3_of_isometry e' he').trans ncard_D3_diagF3_five_one

theorem eq_sPt_of_isAdm_of_compl {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}
    (hf : IsF3Form f)
    (hC : ∀ {w z n : Fin 6 → ZMod 3}, f w w = 1 → z ≠ 0 → f z z = 0 → f z w = 0 → f n n = 0 →
      f n w = 0 → f z n = 0 → (∀ a : ZMod 3, n ≠ a • z) →
        ∃ t, f t t = 1 ∧ f t w = 0 ∧ f t z = 0 ∧ f t n = 0)
    {S : Set (R3 f)} (hS : IsAdm (D3 f) S) {w₀ z₀ : Fin 6 → ZMod 3} (hw₀ : f w₀ w₀ = 1)
    (hg₀ : reflBar f w₀ ∈ S) (hz₀ : IsIsoPt f w₀ z₀)
    (hS₀ : S ∩ LocalClass (D3 f) (reflBar f w₀) = muPt f w₀ z₀) : S = sPt f z₀ := by
  have hm4 : 4 ≤ 6 := by norm_num
  refine (subset_sPt_of_isAdm hf (by norm_num) hS hw₀ hg₀ hz₀ hS₀).antisymm ?_
  rintro _ ⟨y, hy, hyz, rfl⟩
  by_cases hyw : f y w₀ = 0
  · exact (hS₀.symm ▸ (⟨y, hy, hyw, hyz, rfl⟩ : reflBar f y ∈ muPt f w₀ z₀) :
      reflBar f y ∈ S ∩ LocalClass (D3 f) (reflBar f w₀)).1
  obtain ⟨y₁, hy₁, hy₁w, hreq, hy₁x⟩ := exists_normalize hy hyw
  rw [← hreq]
  obtain ⟨hnn, hnw⟩ := isotropic_sub hf hy₁ hw₀ hy₁w
  have hz₀w₀ : f w₀ z₀ = 0 := by rw [hf.symm]; exact hz₀.2.2
  have hy₁z : f y₁ z₀ = 0 := (hy₁x z₀).2 hyz
  have hnz : f z₀ (y₁ - w₀) = 0 := by
    rw [hf.symm, LinearMap.BilinForm.sub_left, hy₁z, hz₀w₀, sub_zero]
  obtain ⟨t, htt, htw, htz, htn⟩ : ∃ t, f t t = 1 ∧ f t w₀ = 0 ∧ f t z₀ = 0 ∧
      f t (y₁ - w₀) = 0 := by
    by_cases hind : ∃ a : ZMod 3, y₁ - w₀ = a • z₀
    · obtain ⟨a, ha⟩ := hind
      obtain ⟨t, htt, htw, htz⟩ :=
        exists_norm_one_perp_isotropic hf (by norm_num) hw₀ hz₀.1 hz₀.2.1 hz₀.2.2
      exact ⟨t, htt, htw, htz, by rw [ha, LinearMap.BilinForm.smul_right, htz, mul_zero]⟩
    · exact hC hw₀ hz₀.1 hz₀.2.1 hz₀.2.2 hnn hnw hnz fun a ha => hind ⟨a, ha⟩
  have htS : reflBar f t ∈ S ∩ LocalClass (D3 f) (reflBar f w₀) :=
    hS₀.symm ▸ (⟨t, htt, htw, htz, rfl⟩ : reflBar f t ∈ muPt f w₀ z₀)
  obtain ⟨zt, hzt, hSt⟩ := exists_isIsoPt_of_isAdm hf hm4 hS htt htS.1
  obtain ⟨γ, hγ⟩ :=
    exists_smul_eq_of_commute hf (by norm_num) hw₀ htt hg₀ htS.1 htS.2 hz₀ hS₀ hzt hSt
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hγ
    exact hzt.1 hγ
  rw [hγ, muPt_smul hγ0] at hSt
  have hy₁t : f y₁ t = 0 := by
    have : y₁ = (y₁ - w₀) + w₀ := by abel
    rw [hf.symm, this, LinearMap.BilinForm.add_right, htn, htw, add_zero]
  exact (hSt.symm ▸ (⟨y₁, hy₁, hy₁t, hy₁z, rfl⟩ : reflBar f y₁ ∈ muPt f t z₀) :
    reflBar f y₁ ∈ S ∩ LocalClass (D3 f) (reflBar f t)).1

end CFSG.Fischer.Classification.LocalU

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer LocalR3 F3 LocalU

theorem classicalConclusion_of_localR3_diagF3_six_one
    (hIC : Comparison fun f' : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3) =>
      (D3 f').ncard = 45) {G : Type} [Group G] {D : Set G}
    (hH : Hyp G D) (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    (φ : LocalQuotient D d ≃* R3 (diagF3 6 1)) (hφ : φ '' LocalImages D d = D3 (diagF3 6 1)) :
    ClassicalConclusion G D := by
  have hf : IsF3Form (diagF3 6 1) := isF3Form_diagF3 (by decide)
  have hH' := hH
  obtain ⟨hP, hZ, hS⟩ := hH'
  have hna : ∃ a b : commutator G, a * b ≠ b * a := hnab
  obtain ⟨x, hx, hxd⟩ : ∃ x ∈ D, x * d ≠ d * x := by
    by_contra! h
    have hdZ : d ∈ Subgroup.center G := (Pair.mem_center_iff hP).2 h
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  have hadm := isAdm_image_muSet_six hP hZ hS hd hf
    (Good := fun f' : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3) => (D3 f').ncard = 45)
    (fun v hv f' hf' e he => ncard_D3_restrict_six_one hv hf' e he) hIC φ hφ hx hxd
  obtain ⟨f₀, hf₀⟩ := Pair.muSet_nonempty hP (Pair.connected_of_nonabelian hP hS hna) hd hx hxd
  obtain ⟨w₀, hw₀, hwg⟩ := mem_D3_iff.1 (hι.mem hf₀.1)
  have hg₀ : reflBar (diagF3 6 1) w₀ ∈ (φ ∘ lqMap D d) '' muSet D d x := by
    rw [hwg]
    exact ⟨f₀, hf₀, rfl⟩
  obtain ⟨z₀, hz₀, hS₀⟩ := exists_isIsoPt_of_isAdm hf (by norm_num) hadm hw₀ hg₀
  have hM := eq_sPt_of_isAdm_of_compl hf
    (fun hw hz0 hzz hzw hnn hnw hzn hind =>
      exists_norm_one_perp_iso_two_six hw hz0 hzz hzw hnn hnw hzn hind) hadm hw₀ hg₀ hz₀ hS₀
  refine classicalConclusion_of_localR3_of_muSet hH hnab hd (by norm_num) hf φ hφ hx hxd hz₀.1
    hz₀.2.1 ?_
  rw [← hM, Set.image_comp, lqMap_image (muSet_subset_localClass d x)]

end CFSG.Fischer.Classification
