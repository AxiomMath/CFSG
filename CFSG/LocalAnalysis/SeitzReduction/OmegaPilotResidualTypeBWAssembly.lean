module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCData

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] in
theorem spLeviSection_of_eq {C : Type*} [Group C] [Finite C] {fp : MulAut C →* (K ≃+* K)}
    {X : Subgroup C} {N N' : Subgroup ↥X} [N.Normal] [N'.Normal] (h : N = N')
    (hs : SpLeviSection fp X N) : SpLeviSection fp X N' := by
  subst h
  exact hs

theorem mSide_props (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0) :
    (∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))), M.Normal →
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ≤ M →
      M = (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ∨ M = ⊤) ∧
    SpLeviSection (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s)))
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ∧
    ∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))), M.Normal →
      IsPGroup 2 M → M ≤ (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker := by
  have hB := (regular_coordinateQuadPlus n K (by omega)).1
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
      spLeviSection_of_eq htop.symm (spLeviSection_top _ _), fun M _ _ => ?_⟩
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
      exists_core_kerQuotHom_eq_plus (by omega) hq4 s hss hW h hh
    obtain ⟨hq₁, hle₁⟩ := ker_props_of_surjective_sp hq4 hr _ hρ
    refine ⟨fun M hM hle => ?_, ?_, fun M hM hMp => ?_⟩
    · rw [← hker] at hle ⊢
      exact hq₁ M hM hle
    · exact spLeviSection_of_eq hker (spLeviSection_of_kerQuot_plus hf hK hn hr (sNil s.val) hNN
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v) _ hρ
        (fun x => spMatTrace_sympChart hβ hb _ hpres x))
    · rw [← hker]
      exact hle₁ M hM hMp

theorem spLeviData_of_wallChart (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0) {r : ℕ}
    (hr : 1 ≤ r) (ρ₁ : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))) →*
      StatedSp r K) (hρ₁ : Function.Surjective ρ₁)
    (h12 : IsPGroup 2 ↥((kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ⊓ ρ₁.ker))
    (hs₁ : SpLeviSection (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) ρ₁.ker)
    (hinv : ∀ (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
      (hβ : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        β x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
      ∀ m ∈ ρ₁.ker, restrictAutOfMapsTo β _ hβ m ∈ ρ₁.ker) :
    SpLeviData (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  obtain ⟨hM1, hM2, -⟩ := mSide_props hf hK hn hq4 s hss hW
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
    · exact spLeviSection_top _ _

end CFSG.SeitzReduction.OmegaPilot
