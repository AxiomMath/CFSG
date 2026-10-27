module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightRigidKappa
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCTwo

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem mSidePropsE (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus n K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0) :
    (∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))), M.Normal →
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ≤ M →
      M = (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ∨ M = ⊤) ∧
    SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s)))
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ∧
    ∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))), M.Normal →
      IsPGroup 2 M → M ≤ (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker := by
  have hB := (regular_coordinateQuadPlus n K hn).1
  have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
  by_cases hM : finrank K (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) = 0
  · have hsub : Subsingleton (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) :=
      Module.finrank_zero_iff.mp hM
    have htop : (kerQuotHom (exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [MonoidHom.mem_ker]
      apply LinearMap.ext
      intro p
      exact Subsingleton.elim _ _
    refine ⟨fun M _ hle => Or.inr (top_le_iff.mp (htop ▸ hle)),
      spLeviSectionE_of_eq _ fp htop.symm (spLeviSectionE_top _ fp _), fun M _ _ => ?_⟩
    rw [htop]
    exact le_top
  · have hβ := kerQuotForm_isAlt (sNil s.val) (polar_sNil_left s hss)
    have hβn := kerQuotForm_nondegenerate (sNil s.val) (polar_sNil_left s hss) hB
    obtain ⟨r, b, hdim, hb⟩ :=
      CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
    have hr : 1 ≤ r := by omega
    have hpres := kerQuotForm_map (exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega))
      (X := perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
      (polar_sNil_left s hss) (fun x hx v => projLift_sNil_of_mem_core _ s hx v)
    have hker := sympChart_ker hβ hb _ hpres
    have hρ := sympChart_surjective hβ hb _ hpres fun h hh =>
      exists_core_kerQuotHom_eq_plus hn hq4 s hss hW h hh
    obtain ⟨hq₁, hle₁⟩ := ker_props_of_surjective_sp hq4 hr _ hρ
    refine ⟨fun M hM hle => ?_, ?_, fun M hM hMp => ?_⟩
    · rw [← hker] at hle ⊢
      exact hq₁ M hM hle
    · exact spLeviSectionE_of_eq _ fp hker (spLeviSectionE_of_kerQuot
        (exists_coordinateQuadPlus_ne_zero (by omega)) fp hfp hr (sNil s.val) hNN
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v) _ hρ
        (fun x => spMatTrace_sympChart hβ hb _ hpres x))
    · rw [← hker]
      exact hle₁ M hM hMp

theorem spLeviDataE_of_wallChart (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus n K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0) {r : ℕ}
    (hr : 1 ≤ r) (ρ₁ : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))) →*
      StatedSp r K) (hρ₁ : Function.Surjective ρ₁)
    (h12 : IsPGroup 2 ↥((kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ⊓ ρ₁.ker))
    (hs₁ : SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) ρ₁.ker)
    (hinv : ∀ (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))),
      β ∈ matrixProjectiveImage (coordinateQuadPlus n K) →
      ∀ (hβ : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        β x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
      ∀ m ∈ ρ₁.ker, restrictAutOfMapsTo β _ hβ m ∈ ρ₁.ker) :
    SpLeviDataE (matrixProjectiveImage (coordinateQuadPlus n K)) fp
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  obtain ⟨hM1, hM2, -⟩ := mSidePropsE hn hq4 fp hfp s hss hW
  obtain ⟨hq₁, -⟩ := ker_props_of_surjective_sp hq4 hr ρ₁ hρ₁
  refine ⟨ρ₁.ker, (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
      (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker, ⊤, inferInstance, inferInstance,
    inferInstance, ?_, ?_, ?_, r, hr, ⟨chartOfSurjective ρ₁ hρ₁⟩, hinv⟩
  · rw [inf_top_eq, inf_comm]
    exact h12
  · intro N' hN' M hM hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN'
    rcases hN' with rfl | rfl | rfl
    · exact hq₁ M hM hle
    · exact hM1 M hM hle
    · exact Or.inr (top_le_iff.mp hle)
  · intro N' _ hN'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN'
    rcases hN' with rfl | rfl | rfl
    · exact hs₁
    · exact hM2
    · exact spLeviSectionE_top _ fp _

theorem spLeviDataE_of_kerQuotChart (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus n K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    {X : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (N : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) (hNN : ∀ v, N (N v) = 0)
    (hXN : ∀ x ∈ X, ∀ v, projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x (N v) =
      N (projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x v))
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K _
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN x))
    (N₂ : Subgroup ↥X) [N₂.Normal] (h12 : IsPGroup 2 ↥(ρ.ker ⊓ N₂))
    (hq₂ : ∀ M : Subgroup ↥X, M.Normal → N₂ ≤ M → M = N₂ ∨ M = ⊤)
    (hs₂ : SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp X N₂)
    (h₂ : IsEmpty (↥X ⧸ N₂ ≃* StatedProj (StatedSp r K))) :
    SpLeviDataE (matrixProjectiveImage (coordinateQuadPlus n K)) fp X := by
  obtain ⟨hq₁, -⟩ := ker_props_of_surjective_sp hq4 hr ρ hρ
  have hs₁ : SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp X ρ.ker :=
    spLeviSectionE_of_kerQuot (exists_coordinateQuadPlus_ne_zero (by omega)) fp hfp hr N hNN hXN
      ρ hρ htr
  exact spLeviDataE_two_of_isEmpty_mulEquiv _ fp hq4 ρ.ker N₂ h12 hq₁ hq₂ hs₁ hs₂ hr
    (chartOfSurjective ρ hρ) h₂

theorem spLeviDataE_typeBC_unequal (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus n K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0)
    (hposM : finrank K (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) ≠ 0)
    (N₂ : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) [N₂.Normal]
    (h12 : IsPGroup 2 ↥((kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ⊓ N₂))
    (hq₂ : ∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
      M.Normal → N₂ ≤ M → M = N₂ ∨ M = ⊤)
    (hs₂ : SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) N₂)
    (h₂ : ∀ r : ℕ, finrank K (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) = 2 * r →
      IsEmpty (↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))) ⧸ N₂ ≃*
        StatedProj (StatedSp r K))) :
    SpLeviDataE (matrixProjectiveImage (coordinateQuadPlus n K)) fp
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  have hB : (QuadraticMap.polarBilin (coordinateQuadPlus n K)).Nondegenerate :=
    (regular_coordinateQuadPlus n K hn).1
  have hβ := kerQuotForm_isAlt (sNil s.val) (polar_sNil_left s hss)
  have hβn := kerQuotForm_nondegenerate (sNil s.val) (polar_sNil_left s hss) hB
  obtain ⟨r, b, hdim, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  have hr : 1 ≤ r := by omega
  have hpres := kerQuotForm_map (exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega))
    (X := perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
    (polar_sNil_left s hss) (fun x hx v => projLift_sNil_of_mem_core _ s hx v)
  have hker := sympChart_ker hβ hb _ hpres
  exact spLeviDataE_of_kerQuotChart hn hq4 fp hfp (sNil s.val)
    (sNil_sNil (congrArg Subtype.val hss)) (fun x hx v => projLift_sNil_of_mem_core _ s hx v) hr
    (sympChart hβ hb _ hpres)
    (sympChart_surjective hβ hb _ hpres fun h hh =>
      exists_core_kerQuotHom_eq_plus hn hq4 s hss hW h hh)
    (fun x => spMatTrace_sympChart hβ hb _ hpres x) N₂ (by rw [hker]; exact h12) hq₂ hs₂
    (h₂ r hdim)

theorem spLeviDataE_typeC_two (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus n K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW2 : finrank K (LinearMap.range (sNil s.val)) = 2)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0) :
    SpLeviDataE (matrixProjectiveImage (coordinateQuadPlus n K)) fp
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  have hQ := exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega)
  have hB := (regular_coordinateQuadPlus n K hn).1
  have hdim := finrank_kerQuot_add (sNil s.val) (sNil_sNil (congrArg Subtype.val hss))
  have hposM : finrank K (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) ≠ 0 := by
    omega
  refine spLeviDataE_typeBC_unequal hn hq4 fp hfp s hss hW hposM ⊤ ?_ ?_
    (spLeviSectionE_top _ fp _) ?_
  · rw [inf_top_eq]
    refine (isPGroup_ker_inf_ker hQ (perfectCore (autFixSubgroup (isometryConjugationHom _ s)))
      (sNil s.val) (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).to_le fun x hx => ⟨?_, hx⟩
    refine MonoidHom.mem_ker.mpr ?_
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact core_fix_range_of_two hQ hB s hss hW2 hW x.2 w.2
  · intro M _ hle
    exact Or.inr (top_le_iff.mp hle)
  · intro r hr
    exact isEmpty_quotient_top_mulEquiv _ (by omega)

end CFSG.SeitzReduction.OmegaPilot
