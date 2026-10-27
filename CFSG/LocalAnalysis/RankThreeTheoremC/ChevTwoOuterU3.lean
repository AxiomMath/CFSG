module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterSylow
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open Matrix

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem psuConj_pow_three_mem_inner (A : unitaryIsom3 h) :
    psuConj h A ^ 3 ∈ inner (unitaryPSU h 3) :=
  CFSG.RankThree.PartTwo.KFacts.cube_mem_range_conj_of_mem_psuConj_range ⟨A, rfl⟩

variable (h) in
@[expose] noncomputable def outerDiag : Subgroup (Outer (unitaryPSU h 3)) :=
  ((QuotientGroup.mk' (inner (unitaryPSU h 3))).comp (psuConj h)).range

theorem outerDiag_normal (hq : 2 < p ^ f) : (outerDiag h).Normal where
  conj_mem n hn y := by
    obtain ⟨A, rfl⟩ := hn
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (unitaryPSU h 3)) y
    obtain ⟨B, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
    refine ⟨B * ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩ * B⁻¹, ?_⟩
    have key : (psuConj h B * psuField h σ) * psuConj h A * (psuConj h B * psuField h σ)⁻¹ =
        psuConj h (B * ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩ * B⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← psuField_mul_psuConj_mul_inv]
      group
    rw [MonoidHom.comp_apply, ← key]
    simp only [MonoidHom.comp_apply, map_mul, map_inv]

theorem isPGroup_outerDiag : IsPGroup 3 (outerDiag h) := by
  rintro ⟨n, A, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change ((QuotientGroup.mk' (inner (unitaryPSU h 3))).comp (psuConj h) A) ^ 3 = 1
  rw [MonoidHom.comp_apply, ← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (psuConj_pow_three_mem_inner A)

theorem outerDiag_commutator (hq : 2 < p ^ f) (x y : Outer (unitaryPSU h 3)) :
    x * y * x⁻¹ * y⁻¹ ∈ outerDiag h := by
  have := outerDiag_normal (h := h) hq
  have := h.finite
  let π := QuotientGroup.mk' (outerDiag h)
  let F : (K ≃+* K) →* Outer (unitaryPSU h 3) ⧸ outerDiag h :=
    π.comp ((QuotientGroup.mk' (inner (unitaryPSU h 3))).comp (psuField h))
  have hF : ∀ x : Outer (unitaryPSU h 3), ∃ σ, π x = F σ := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
    refine ⟨σ, ?_⟩
    have h1 : π (QuotientGroup.mk' (inner (unitaryPSU h 3)) (psuConj h A)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨A, rfl⟩
    simp only [F, MonoidHom.comp_apply, map_mul]
    rw [h1, one_mul]
  obtain ⟨σ, hσ⟩ := hF x
  obtain ⟨τ, hτ⟩ := hF y
  have hστ : σ * τ * σ⁻¹ * τ⁻¹ = 1 := by
    rw [ringAut_mul_comm K σ τ, mul_inv_cancel_right, mul_inv_cancel]
  refine (QuotientGroup.eq_one_iff _).mp ?_
  change π (x * y * x⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hσ, hτ, ← map_inv, ← map_inv, ← map_mul,
    ← map_mul, ← map_mul, hστ, map_one]

theorem isPByAbelian_outer_unitaryPSU_three (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    IsPByAbelian 3 (Outer (unitaryPSU h 3)) :=
  ⟨outerDiag h, outerDiag_normal hq, isPGroup_outerDiag, outerDiag_commutator hq⟩

theorem isPByAbelian_outer_twistedA_two (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hd : d.1 = .twistedA 2 q) : IsPByAbelian 3 (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.twistedA 2 q := hd
  have h3 : 3 ≤ q.card := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
  obtain ⟨p, f, hp, hf⟩ := q
  have : Fact p.Prime := ⟨hp⟩
  have hq : 2 < p ^ f := by
    simp only [TauCeti.PrimePower.card_def] at h3
    omega
  have hU : UnitaryFieldData p f (GaloisField p (2 * f)) :=
    ⟨hp, hf, GaloisField.card p (2 * f) (by omega)⟩
  let e := (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 _ hv).trans
    (unitaryPSUEquiv hU (n := 3) (by norm_num)).symm
  exact (isPByAbelian_outer_unitaryPSU_three hU hq).map_equiv (equivalence e).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter
