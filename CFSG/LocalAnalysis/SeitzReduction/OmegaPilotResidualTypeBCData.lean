module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCCore

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

theorem exists_core_kerQuotHom_eq_plus (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0)
    (h : (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) →ₗ[K]
      (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)))
    (hh : ∀ p q, kerQuotForm _ (polar_sNil_left s hss) (h p) (h q) =
      kerQuotForm _ (polar_sNil_left s hss) p q) :
    ∃ x, kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
      (fun _ hx v => projLift_sNil_of_mem_core _ s hx v) x = h :=
  exists_core_kerQuotHom_eq _ (regular_coordinateQuadPlus n K hn).1 hq4 s hss hW h hh

theorem spLeviData_typeBC_of_quad (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0)
    (hposM : finrank K (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) ≠ 0)
    (N₂ : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) [N₂.Normal]
    (h12 : IsPGroup 2 ↥((kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ⊓ N₂))
    (hq₂ : ∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
      M.Normal → N₂ ≤ M → M = N₂ ∨ M = ⊤)
    (hab₂ : N₂ = ⊤ ∨
      ∃ a b : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))) ⧸ N₂, a * b ≠ b * a)
    (hs₂ : SpLeviSection (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) N₂)
    (hU : ∀ v, v ∈ LinearMap.range (sNil s.val) ↔
      ∀ x ∈ (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
          (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
          (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ⊓ N₂,
        projLift (exists_coordinateQuadPlus_ne_zero (by omega))
          (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v = v) :
    SpLeviData (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) :=
  spLeviData_typeBC hf hK hn hq4 s hss hposM
    (fun h hh => exists_core_kerQuotHom_eq_plus (by omega) hq4 s hss hW h hh) N₂ h12 hq₂ hab₂ hs₂ hU

theorem spLeviData_typeBC_unequal (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0)
    (hposM : finrank K (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) ≠ 0)
    (N₂ : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) [N₂.Normal]
    (h12 : IsPGroup 2 ↥((kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega))
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
        (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).ker ⊓ N₂))
    (hq₂ : ∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
      M.Normal → N₂ ≤ M → M = N₂ ∨ M = ⊤)
    (hs₂ : SpLeviSection (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) N₂)
    (h₂ : ∀ r : ℕ, finrank K (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) = 2 * r →
      IsEmpty (↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))) ⧸ N₂ ≃*
        StatedProj (StatedSp r K))) :
    SpLeviData (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  have hB : (QuadraticMap.polarBilin (coordinateQuadPlus n K)).Nondegenerate :=
    (regular_coordinateQuadPlus n K (by omega)).1
  have hβ := kerQuotForm_isAlt (sNil s.val) (polar_sNil_left s hss)
  have hβn := kerQuotForm_nondegenerate (sNil s.val) (polar_sNil_left s hss) hB
  obtain ⟨r, b, hdim, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  have hr : 1 ≤ r := by omega
  have hpres := kerQuotForm_map (exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega))
    (X := perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sNil s.val)
    (polar_sNil_left s hss) (fun x hx v => projLift_sNil_of_mem_core _ s hx v)
  have hker := sympChart_ker hβ hb _ hpres
  exact spLeviData_of_kerQuotChart hf hK hn hq4 (sNil s.val)
    (sNil_sNil (congrArg Subtype.val hss)) (fun x hx v => projLift_sNil_of_mem_core _ s hx v) hr
    (sympChart hβ hb _ hpres)
    (sympChart_surjective hβ hb _ hpres fun h hh =>
      exists_core_kerQuotHom_eq_plus (by omega) hq4 s hss hW h hh)
    (fun x => spMatTrace_sympChart hβ hb _ hpres x) N₂ (by rw [hker]; exact h12) hq₂ hs₂
    (h₂ r hdim)

end CFSG.SeitzReduction.OmegaPilot
