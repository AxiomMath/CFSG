module

public import CFSG.Fischer.Classification.PartIII.R3.Chart
public import CFSG.Fischer.Classification.PartIII.R3.Forms
public import CFSG.Fischer.Classification.Orthogonal3.Mu

public section

namespace CFSG.Fischer.Classification.LocalR3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

variable (f) in
@[expose] def sPt (z : Fin m → ZMod 3) : Set (R3 f) :=
  {q | ∃ w, f w w = 1 ∧ f w z = 0 ∧ reflBar f w = q}

theorem sPt_subset_D3 (z : Fin m → ZMod 3) : sPt f z ⊆ D3 f := by
  rintro _ ⟨w, hw, -, rfl⟩
  exact reflBar_mem_D3 hw

theorem reflBar_mem_sPt_iff (hf : IsF3Form f) (hm : 4 ≤ m) {w z : Fin m → ZMod 3}
    (hw : f w w = 1) : reflBar f w ∈ sPt f z ↔ f w z = 0 := by
  constructor
  · rintro ⟨w', hw', hw'z, h⟩
    exact pair_eq_zero_of_reflBar_eq hf hm hw hw' h hw'z
  · intro h
    exact ⟨w, hw, h, rfl⟩

theorem sPt_inter_localClass (hf : IsF3Form f) (hm : 4 ≤ m) {w z : Fin m → ZMod 3}
    (hw : f w w = 1) : sPt f z ∩ LocalClass (D3 f) (reflBar f w) = muPt f w z := by
  ext q
  constructor
  · rintro ⟨⟨y, hy, hyz, rfl⟩, hq⟩
    exact ⟨y, hy, (reflBar_mem_localClass_iff hf hm hw hy).1 hq, hyz, rfl⟩
  · rintro ⟨y, hy, hyw, hyz, rfl⟩
    exact ⟨⟨y, hy, hyz, rfl⟩, reflBar_mem_localClass hf hm hw hy hyw⟩

theorem sPt_nonempty (hf : IsF3Form f) (hm : 5 ≤ m) {v z : Fin m → ZMod 3} (hv : f v v = 1)
    (hz : IsIsoPt f v z) : (sPt f z).Nonempty := by
  obtain ⟨w, hw, -, hwz⟩ := exists_norm_one_perp_isotropic hf hm hv hz.1 hz.2.1 hz.2.2
  exact ⟨_, w, hw, hwz, rfl⟩

theorem isAdm_sPt (hf : IsF3Form f) (hm : 4 ≤ m) {z : Fin m → ZMod 3} (hz0 : z ≠ 0)
    (hzz : f z z = 0) : IsAdm (D3 f) (sPt f z) := by
  refine ⟨sPt_subset_D3 z, ?_⟩
  rintro _ ⟨w, hw, hwz, rfl⟩
  have hzw : f z w = 0 := by rw [hf.symm]; exact hwz
  have hu : f (w + z) (w + z) = 1 := by rw [norm_add hf, hw, hwz, hzz]; ring
  refine ⟨reflBar f (w + z), reflBar_mem_D3 hu,
    reflBar_add_not_commute hf hm hw ⟨hz0, hzz, hzw⟩, ?_⟩
  rw [sPt_inter_localClass hf hm hw, muSet_eq_muPt hf hm hw hu, add_sub_cancel_left]

theorem exists_isIsoPt_of_isAdm (hf : IsF3Form f) (hm : 4 ≤ m) {S : Set (R3 f)}
    (hS : IsAdm (D3 f) S) {w : Fin m → ZMod 3} (hw : f w w = 1) (hg : reflBar f w ∈ S) :
    ∃ z, IsIsoPt f w z ∧ S ∩ LocalClass (D3 f) (reflBar f w) = muPt f w z := by
  obtain ⟨q, hq, hqg, hμ⟩ := hS.2 _ hg
  have hfam : muSet (D3 f) (reflBar f w) q ∈ muFamily (D3 f) (reflBar f w) := ⟨q, hq, hqg, rfl⟩
  rw [muFamily_D3 hf hm hw] at hfam
  obtain ⟨z, hz, hzq⟩ := hfam
  exact ⟨z, hz, hμ.trans hzq.symm⟩

theorem reflBar_mem_localClass_comm (hf : IsF3Form f) (hm : 4 ≤ m) {w w' : Fin m → ZMod 3}
    (hw : f w w = 1) (hw' : f w' w' = 1)
    (h : reflBar f w' ∈ LocalClass (D3 f) (reflBar f w)) :
    reflBar f w ∈ LocalClass (D3 f) (reflBar f w') := by
  have h1 := (reflBar_mem_localClass_iff hf hm hw hw').1 h
  exact reflBar_mem_localClass hf hm hw' hw (by rw [hf.symm]; exact h1)

theorem exists_smul_eq_of_commute (hf : IsF3Form f) (hm : 6 ≤ m) {S : Set (R3 f)}
    {w w' z z' : Fin m → ZMod 3} (hw : f w w = 1) (hw' : f w' w' = 1)
    (hg : reflBar f w ∈ S) (hh : reflBar f w' ∈ S)
    (hc : reflBar f w' ∈ LocalClass (D3 f) (reflBar f w)) (hz : IsIsoPt f w z)
    (hSz : S ∩ LocalClass (D3 f) (reflBar f w) = muPt f w z) (hz' : IsIsoPt f w' z')
    (hSz' : S ∩ LocalClass (D3 f) (reflBar f w') = muPt f w' z') : ∃ γ : ZMod 3, z' = γ • z := by
  have hm4 : 4 ≤ m := by omega
  have hw'w : f w' w = 0 := (reflBar_mem_localClass_iff hf hm4 hw hw').1 hc
  have hw'z : f w' z = 0 := by
    have : reflBar f w' ∈ muPt f w z := hSz ▸ ⟨hh, hc⟩
    exact ((reflBar_mem_muPt_iff hf hm4 hw').1 this).2
  have hwz' : f w z' = 0 := by
    have : reflBar f w ∈ muPt f w' z' :=
      hSz' ▸ ⟨hg, reflBar_mem_localClass_comm hf hm4 hw hw' hc⟩
    exact ((reflBar_mem_muPt_iff hf hm4 hw).1 this).2
  refine exists_smul_eq_of_perp_two hf hm hw hw' hw'w hz.1 hz.2.1 hz.2.2
    (by rw [hf.symm]; exact hw'z) (by rw [hf.symm]; exact hwz') hz'.2.2
    (fun y hy hyw hyw' hyz => ?_) (Or.inl hz'.2.1)
  have hyS : reflBar f y ∈ S := (hSz.symm ▸ (⟨y, hy, hyw, hyz, rfl⟩ : reflBar f y ∈ muPt f w z) :
    reflBar f y ∈ S ∩ LocalClass (D3 f) (reflBar f w)).1
  have : reflBar f y ∈ muPt f w' z' := hSz' ▸ ⟨hyS, reflBar_mem_localClass hf hm4 hw' hy hyw'⟩
  rw [hf.symm]
  exact ((reflBar_mem_muPt_iff hf hm4 hy).1 this).2

theorem exists_normalize {u w : Fin m → ZMod 3} (hu : f u u = 1)
    (huw : f u w ≠ 0) : ∃ u₁, f u₁ u₁ = 1 ∧ f u₁ w = 1 ∧ reflBar f u₁ = reflBar f u ∧
      ∀ x, f u₁ x = 0 ↔ f u x = 0 := by
  refine ⟨f u w • u, by rw [norm_smul, mul_self_of_ne_zero huw, hu, one_mul],
    by rw [LinearMap.BilinForm.smul_left, mul_self_of_ne_zero huw], reflBar_smul huw u,
    fun x => ?_⟩
  rw [LinearMap.BilinForm.smul_left]
  exact ⟨fun h => (mul_eq_zero.1 h).resolve_left huw, fun h => by rw [h, mul_zero]⟩

theorem isotropic_sub (hf : IsF3Form f) {u w : Fin m → ZMod 3} (hu : f u u = 1)
    (hw : f w w = 1) (huw : f u w = 1) : f (u - w) (u - w) = 0 ∧ f (u - w) w = 0 := by
  have hwu : f w u = 1 := by rw [hf.symm]; exact huw
  refine ⟨?_, by rw [LinearMap.BilinForm.sub_left, huw, hw, sub_self]⟩
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hu, huw, hwu, hw]
  ring

theorem subset_sPt_of_isAdm (hf : IsF3Form f) (hm : 6 ≤ m) {S : Set (R3 f)}
    (hS : IsAdm (D3 f) S) {w₀ z₀ : Fin m → ZMod 3} (hw₀ : f w₀ w₀ = 1)
    (hg₀ : reflBar f w₀ ∈ S) (hz₀ : IsIsoPt f w₀ z₀)
    (hS₀ : S ∩ LocalClass (D3 f) (reflBar f w₀) = muPt f w₀ z₀) : S ⊆ sPt f z₀ := by
  have hm4 : 4 ≤ m := by omega
  intro h hhS
  obtain ⟨u, hu, rfl⟩ := mem_D3_iff.1 (hS.1 hhS)
  rw [reflBar_mem_sPt_iff hf hm4 hu]
  by_contra huz
  have hz₀w₀ : f w₀ z₀ = 0 := by rw [hf.symm]; exact hz₀.2.2
  by_cases huw : f u w₀ = 0
  ·
    have hmem : reflBar f u ∈ muPt f w₀ z₀ :=
      hS₀ ▸ ⟨hhS, reflBar_mem_localClass hf hm4 hw₀ hu huw⟩
    exact huz ((reflBar_mem_muPt_iff hf hm4 hu).1 hmem).2
  obtain ⟨u₁, hu₁, hu₁w, hreq, hu₁x⟩ := exists_normalize hu huw
  obtain ⟨hnn, hnw⟩ := isotropic_sub hf hu₁ hw₀ hu₁w
  have hnz : f (u₁ - w₀) z₀ ≠ 0 := by
    rw [LinearMap.BilinForm.sub_left, hz₀w₀, sub_zero]
    exact fun h => huz ((hu₁x z₀).1 h)
  obtain ⟨t, htt, htw, htn, htz⟩ :=
    exists_norm_one_perp_of_ne_zero hf (by omega) hw₀ hnn hnw hz₀.2.1 hz₀.2.2 hnz
  have htu : f t u₁ = 0 := by
    have : u₁ = (u₁ - w₀) + w₀ := by abel
    rw [this, LinearMap.BilinForm.add_right, htn, htw, add_zero]
  have htS : reflBar f t ∈ S ∩ LocalClass (D3 f) (reflBar f w₀) :=
    hS₀.symm ▸ (⟨t, htt, htw, htz, rfl⟩ : reflBar f t ∈ muPt f w₀ z₀)
  have hu₁S : reflBar f u₁ ∈ S := hreq ▸ hhS
  have hu₁t : reflBar f u₁ ∈ LocalClass (D3 f) (reflBar f t) :=
    reflBar_mem_localClass hf hm4 htt hu₁ (by rw [hf.symm]; exact htu)
  obtain ⟨zt, hzt, hSt⟩ := exists_isIsoPt_of_isAdm hf hm4 hS htt htS.1
  obtain ⟨zh, hzh, hSh⟩ := exists_isIsoPt_of_isAdm hf hm4 hS hu₁ hu₁S
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_commute hf hm hw₀ htt hg₀ htS.1 htS.2 hz₀ hS₀ hzt hSt
  obtain ⟨γ', hγ'⟩ := exists_smul_eq_of_commute hf hm htt hu₁ htS.1 hu₁S hu₁t hzt hSt hzh hSh
  have h1 : f zh u₁ = 0 := hzh.2.2
  rw [hγ', hγ, smul_smul, LinearMap.BilinForm.smul_left] at h1
  have hc : γ' * γ ≠ 0 := by
    rintro hc
    apply hzh.1
    rw [hγ', hγ, smul_smul, hc, zero_smul]
  have h2 : f z₀ u₁ = 0 := (mul_eq_zero.1 h1).resolve_left hc
  apply huz
  rw [← hu₁x, hf.symm]
  exact h2

theorem eq_sPt_of_subset_of_isAdm (hf : IsF3Form f) (hm : 6 ≤ m) {S : Set (R3 f)}
    (hS : IsAdm (D3 f) S) {z : Fin m → ZMod 3} (hz0 : z ≠ 0) (hzz : f z z = 0)
    (hsub : sPt f z ⊆ S) (hne : (sPt f z).Nonempty) : S = sPt f z := by
  have hm4 : 4 ≤ m := by omega
  obtain ⟨_, ⟨w, hw, hwz, rfl⟩⟩ := hne
  have hzw : f z w = 0 := by rw [hf.symm]; exact hwz
  obtain ⟨zg, hzg, hSg⟩ := exists_isIsoPt_of_isAdm hf hm4 hS hw (hsub ⟨w, hw, hwz, rfl⟩)
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_perp hf (by omega) hw hz0 hzz hzw hzg.2.2
    (fun y hy hyw hyz => by
      have hmem : reflBar f y ∈ S ∩ LocalClass (D3 f) (reflBar f w) :=
        ⟨hsub ⟨y, hy, hyz, rfl⟩, reflBar_mem_localClass hf hm4 hw hy hyw⟩
      rw [hSg] at hmem
      rw [hf.symm]
      exact ((reflBar_mem_muPt_iff hf hm4 hy).1 hmem).2)
    (Or.inl hzg.2.1)
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hγ
    exact hzg.1 hγ
  rw [hγ, muPt_smul hγ0] at hSg
  exact (subset_sPt_of_isAdm hf hm hS hw (hsub ⟨w, hw, hwz, rfl⟩) ⟨hz0, hzz, hzw⟩ hSg).antisymm
    hsub

theorem eq_sPt_of_isAdm (hf : IsF3Form f) (hm : 7 ≤ m) {S : Set (R3 f)}
    (hS : IsAdm (D3 f) S) {w₀ z₀ : Fin m → ZMod 3} (hw₀ : f w₀ w₀ = 1)
    (hg₀ : reflBar f w₀ ∈ S) (hz₀ : IsIsoPt f w₀ z₀)
    (hS₀ : S ∩ LocalClass (D3 f) (reflBar f w₀) = muPt f w₀ z₀) : S = sPt f z₀ := by
  have hm4 : 4 ≤ m := by omega
  refine (subset_sPt_of_isAdm hf (by omega) hS hw₀ hg₀ hz₀ hS₀).antisymm ?_
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
        exists_norm_one_perp_isotropic hf (by omega) hw₀ hz₀.1 hz₀.2.1 hz₀.2.2
      exact ⟨t, htt, htw, htz, by rw [ha, LinearMap.BilinForm.smul_right, htz, mul_zero]⟩
    · exact exists_norm_one_perp_iso_two hf hm hw₀ hz₀.1 hz₀.2.1 hz₀.2.2 hnn hnw hnz
        fun a ha => hind ⟨a, ha⟩
  have htS : reflBar f t ∈ S ∩ LocalClass (D3 f) (reflBar f w₀) :=
    hS₀.symm ▸ (⟨t, htt, htw, htz, rfl⟩ : reflBar f t ∈ muPt f w₀ z₀)
  obtain ⟨zt, hzt, hSt⟩ := exists_isIsoPt_of_isAdm hf hm4 hS htt htS.1
  obtain ⟨γ, hγ⟩ :=
    exists_smul_eq_of_commute hf (by omega) hw₀ htt hg₀ htS.1 htS.2 hz₀ hS₀ hzt hSt
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

theorem isAdm_iff_eq_sPt (hf : IsF3Form f) (hm : 7 ≤ m) {S : Set (R3 f)} :
    IsAdm (D3 f) S ∧ S.Nonempty ↔ ∃ w z, f w w = 1 ∧ IsIsoPt f w z ∧ S = sPt f z := by
  constructor
  · rintro ⟨hS, g, hg⟩
    obtain ⟨w, hw, rfl⟩ := mem_D3_iff.1 (hS.1 hg)
    obtain ⟨z, hz, hSz⟩ := exists_isIsoPt_of_isAdm hf (by omega) hS hw hg
    exact ⟨w, z, hw, hz, eq_sPt_of_isAdm hf hm hS hw hg hz hSz⟩
  · rintro ⟨w, z, hw, hz, rfl⟩
    exact ⟨isAdm_sPt hf (by omega) hz.1 hz.2.1, sPt_nonempty hf (by omega) hw hz⟩

end CFSG.Fischer.Classification.LocalR3
