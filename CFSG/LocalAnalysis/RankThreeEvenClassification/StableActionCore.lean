module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticActions

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem actionPrimeCore_normal {actor : Type u} {acted : Type v} [Group actor] [Group acted]
    (prime : ℕ) (action : actor →* MulAut acted) : (actionPrimeCore prime action).Normal :=
  (pCore_normal (actor ⧸ action.ker) prime).comap (QuotientGroup.mk' action.ker)

theorem kernel_le_actionPrimeCore {actor : Type u} {acted : Type v} [Group actor] [Group acted]
    (prime : ℕ) (action : actor →* MulAut acted) : action.ker ≤ actionPrimeCore prime action := by
  intro member hmember
  have heq : QuotientGroup.mk' action.ker member = 1 := by
    apply MonoidHom.mem_ker.mp
    rwa [QuotientGroup.ker_mk']
  change QuotientGroup.mk' action.ker member ∈ pCore prime (actor ⧸ action.ker)
  rw [heq]
  exact Subgroup.one_mem _

theorem actionPrimeCore_isPGroup_of_kernel {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] (prime : ℕ) (action : actor →* MulAut acted)
    (hkernel : IsPGroup prime action.ker) : IsPGroup prime (actionPrimeCore prime action) := by
  apply (pCore_isPGroup (actor ⧸ action.ker) prime).comap_of_ker_isPGroup
  rwa [QuotientGroup.ker_mk']

theorem actionPrimeCore_eq_primeCore_of_kernel {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] (prime : ℕ) (action : actor →* MulAut acted)
    (hkernel : IsPGroup prime action.ker) : actionPrimeCore prime action = pCore prime actor := by
  apply le_antisymm
  · exact le_pCore_of_normal prime (actionPrimeCore prime action) (actionPrimeCore_normal prime action)
      (actionPrimeCore_isPGroup_of_kernel prime action hkernel)
  · have hmappedNormal : ((pCore prime actor).map (QuotientGroup.mk' action.ker)).Normal :=
      (pCore_normal actor prime).map (QuotientGroup.mk' action.ker) (QuotientGroup.mk'_surjective action.ker)
    have hmappedPGroup := (pCore_isPGroup actor prime).map (QuotientGroup.mk' action.ker)
    exact Subgroup.map_le_iff_le_comap.mp (le_pCore_of_normal prime _ hmappedNormal hmappedPGroup)

theorem primeCore_le_actionPrimeCore {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] (prime : ℕ) (action : actor →* MulAut acted) :
    pCore prime actor ≤ actionPrimeCore prime action := by
  have hmappedNormal : ((pCore prime actor).map (QuotientGroup.mk' action.ker)).Normal :=
    (pCore_normal actor prime).map (QuotientGroup.mk' action.ker) (QuotientGroup.mk'_surjective action.ker)
  exact Subgroup.map_le_iff_le_comap.mp (le_pCore_of_normal prime _ hmappedNormal
    ((pCore_isPGroup actor prime).map (QuotientGroup.mk' action.ker)))

theorem conjugation_kernel_eq_centralizer {G : Type u} [Group G]
    (normal : Subgroup G) [normal.Normal] :
    (MulAut.conjNormal : G →* MulAut normal).ker = Subgroup.centralizer (normal : Set G) := by
  ext member
  constructor
  · intro hmember
    have heq := MonoidHom.mem_ker.mp hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro element helement
    have happly := DFunLike.congr_fun heq (⟨element, helement⟩ : normal)
    have hambient := congrArg (fun value : normal => (value : G)) happly
    change member * element * member⁻¹ = element at hambient
    have hmul := congrArg (fun value : G => value * member) hambient
    have hcomm : member * element = element * member := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
    exact hcomm.symm
  · intro hmember
    apply MonoidHom.mem_ker.mpr
    ext element
    rw [MulAut.conjNormal_apply]
    have hcomm := Subgroup.mem_centralizer_iff.mp hmember element element.property
    rw [← hcomm]
    group
    rfl

theorem conjugation_actionPrimeCore_eq_primeCore {G : Type u} [Group G]
    (prime : ℕ) (hcharacteristic : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G) :
    letI := pCore_normal G prime
    actionPrimeCore prime (MulAut.conjNormal : G →* MulAut (pCore prime G)) = pCore prime G := by
  have : (pCore prime G).Normal := pCore_normal G prime
  apply actionPrimeCore_eq_primeCore_of_kernel
  rw [conjugation_kernel_eq_centralizer]
  exact (pCore_isPGroup G prime).to_le hcharacteristic

theorem PrimeStableAction.inverse_quadratic {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] (prime : ℕ) (action : actor →* MulAut acted)
    (hstable : PrimeStableAction prime action) (member : actor)
    (hquadratic : QuadraticAutomorphism (action member⁻¹)) : member ∈ actionPrimeCore prime action := by
  simpa only [inv_inv] using (actionPrimeCore prime action).inv_mem (hstable member⁻¹ hquadratic)

end CFSG.RankThreeEvenClassification.Helpers
