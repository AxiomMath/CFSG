module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.ModelTheta
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Restrict
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Tr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Dt

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Equiv Equiv.Perm

private theorem sixA_model_restrict {s : Sym 7} {ρ : Sym 5} (hρ : s = sixAExt ρ) :
    Nonempty (↥(Subgroup.centralizer ({sixASigma, s} : Set (Sym 7))) ≃*
      ↥(Subgroup.centralizer ({((1 : Z 2), ρ)} : Set (Z 2 × Sym 5)))) := by
  have hsθ : s = sixATheta ((1 : Z 2), ρ) := by
    rw [hρ, sixATheta_apply, sixAFlip_one, one_mul]
  obtain ⟨e⟩ := sixA_restrict_equiv sixATheta sixATheta_injective
    (D := Subgroup.centralizer ({((1 : Z 2), ρ)} : Set (Z 2 × Sym 5)))
    (C := Subgroup.centralizer ({sixASigma, s} : Set (Sym 7)))
    (fun c hc => by
      have hcσ : c ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.mp hc) sixASigma (by simp)).symm
      obtain ⟨x, hx⟩ := sixATheta_surj hcσ
      exact ⟨x, hx⟩)
    (fun x => by
      constructor
      · intro hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 := (Subgroup.mem_centralizer_iff.mp hx) s (by simp)
        rw [hsθ] at h2
        exact (sixATheta_injective (by simpa only [← map_mul] using h2)).symm
      · intro hx
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
        rcases hh with rfl | rfl
        · exact (Subgroup.mem_centralizer_singleton_iff.mp (sixATheta_mem x)).symm
        · rw [hsθ]
          rw [Subgroup.mem_centralizer_singleton_iff] at hx
          rw [← map_mul, ← map_mul, hx])
  exact ⟨e.symm⟩

theorem sixA_model_shape_A {s : Sym 7}
    (hs : s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7))) (hA : sixAIsA s) :
    Nonempty (↥(Subgroup.centralizer ({sixASigma, s} : Set (Sym 7))) ≃* Elem2 2 × Sym 3) := by
  obtain ⟨ρ, hρ | hρ⟩ := sixA_coord hs
  · have hs1 : s.cycleType = {2} := hA.1
    have hρ2 : ρ.cycleType = {2} := by
      simpa [hρ, sixA_cycleType_ext] using hs1
    obtain ⟨e1⟩ := sixA_model_restrict hρ
    obtain ⟨e2⟩ := symCent_prod (1 : Z 2) ρ
    obtain ⟨e3⟩ := symCent_tr 3 (σ := ρ) hρ2
    obtain ⟨e4⟩ := symCent_elem2 (Sym 3)
    exact ⟨e1.trans (e2.trans ((MulEquiv.prodCongr (MulEquiv.refl (Z 2)) e3).trans e4))⟩
  · exfalso
    have hs1 : s.cycleType = {2} := hA.1
    have hs2 : (sixASigma * s).cycleType = {2, 2} := hA.2
    have hρ2 : ρ.cycleType = {2, 2} := by
      have h1 : ρ.cycleType = (sixASigma * s).cycleType := by
        rw [hρ]
        rw [show sixASigma * (sixASigma * sixAExt ρ) = sixAExt ρ by
          rw [← mul_assoc, sixA_sigma_mul_self, one_mul]]
        exact (sixA_cycleType_ext ρ).symm
      rw [h1, hs2]
    have hsc : s.cycleType = {2, 2, 2} := by
      rw [hρ, sixA_cycleType_sigma_mul_ext, hρ2]
      decide
    rw [hs1] at hsc
    have hne : ({2} : Multiset ℕ) ≠ {2, 2, 2} := by decide
    exact absurd hsc hne

theorem sixA_model_shape_B {s : Sym 7}
    (hs : s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7))) (hB : sixAIsB s) :
    Nonempty (↥(Subgroup.centralizer ({sixASigma, s} : Set (Sym 7))) ≃* Z 2 × DihedralGroup 4) := by
  obtain ⟨ρ, hρ | hρ⟩ := sixA_coord hs
  · have hs1 : s.cycleType = {2, 2} := hB.1
    have hρ2 : ρ.cycleType = {2, 2} := by
      simpa [hρ, sixA_cycleType_ext] using hs1
    obtain ⟨e1⟩ := sixA_model_restrict hρ
    obtain ⟨e2⟩ := symCent_prod (1 : Z 2) ρ
    obtain ⟨e3⟩ := symCent_dt 1 (σ := ρ) hρ2
    have e4 : Z 2 × (DihedralGroup 4 × Sym 1) ≃* Z 2 × DihedralGroup 4 :=
      MulEquiv.prodCongr (MulEquiv.refl (Z 2))
        (MulEquiv.prodUnique : DihedralGroup 4 × Sym 1 ≃* DihedralGroup 4)
    exact ⟨e1.trans (e2.trans ((MulEquiv.prodCongr (MulEquiv.refl (Z 2)) e3).trans e4))⟩
  · exfalso
    have hs1 : s.cycleType = {2, 2} := hB.1
    have hs2 : (sixASigma * s).cycleType = {2, 2, 2} := hB.2
    have hρ2 : ρ.cycleType = {2, 2, 2} := by
      have h1 : ρ.cycleType = (sixASigma * s).cycleType := by
        rw [hρ]
        rw [show sixASigma * (sixASigma * sixAExt ρ) = sixAExt ρ by
          rw [← mul_assoc, sixA_sigma_mul_self, one_mul]]
        exact (sixA_cycleType_ext ρ).symm
      rw [h1, hs2]
    have hsc : s.cycleType = {2, 2, 2, 2} := by
      rw [hρ, sixA_cycleType_sigma_mul_ext, hρ2]
      decide
    rw [hs1] at hsc
    have hne : ({2, 2} : Multiset ℕ) ≠ {2, 2, 2, 2} := by decide
    exact absurd hsc hne

end CFSG.EvenSporadicStandard.HNRecog.Section3
