module

public import CFSG.LocalAnalysis.LargeEvenClassification.RankOneComparable

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem rank_one_cyclic_norm_obstruction {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    (Normal : Subgroup Ambient) [Normal.Normal] [IsCyclic Normal]
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (element : Ambient) (helementNe : element ∉ Normal) (hsquare : element ^ 2 ∈ Normal) :
    let _ : CommGroup Normal := IsCyclic.commGroup
    ∀ (_ : ∀ source : Normal, element * source.val * element⁻¹ = source.val →
      source ∈ (powMonoidHom 2 : Normal →* Normal).range)
    (_ : ∀ square : (powMonoidHom 2 : Normal →* Normal).range,
      ∃ source : Normal, source.val * (element * source.val * element⁻¹) = square.val.val), False := by
  dsimp only
  let : CommGroup Normal := IsCyclic.commGroup
  intro hcentralizer hnormSurjective
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsquareFixed : element * (element ^ 2) * element⁻¹ = element ^ 2 := by group
  have hsquareRange := hcentralizer ⟨element ^ 2, hsquare⟩ hsquareFixed
  have hinverseRange : (⟨element ^ 2, hsquare⟩ : Normal)⁻¹ ∈
      (powMonoidHom 2 : Normal →* Normal).range := Subgroup.inv_mem _ hsquareRange
  obtain ⟨source, hnorm⟩ := hnormSurjective ⟨(⟨element ^ 2, hsquare⟩ : Normal)⁻¹, hinverseRange⟩
  have hinvolutionSquare : (source.val * element) ^ 2 = 1 := by
    calc
      (source.val * element) ^ 2 =
          (source.val * (element * source.val * element⁻¹)) * element ^ 2 := by
        simp only [pow_two]
        group
      _ = (element ^ 2)⁻¹ * element ^ 2 := by rw [hnorm]; rfl
      _ = 1 := inv_mul_cancel _
  have hinvolutionNotMem : source.val * element ∉ Normal := by
    intro hmem
    apply helementNe
    have hproduct := Normal.mul_mem (Normal.inv_mem source.property) hmem
    simpa only [inv_mul_cancel_left] using hproduct
  have hinvolutionNe : source.val * element ≠ 1 := by
    intro hone
    apply hinvolutionNotMem
    rw [hone]
    exact Normal.one_mem
  have hinvolution : orderOf (source.val * element) = 2 :=
    orderOf_eq_prime_iff.mpr ⟨hinvolutionSquare, hinvolutionNe⟩
  have hcentral := rank_one_involution_central hpgroup hrank (source.val * element) hinvolution
  apply hinvolutionNotMem
  exact hselfCentralizing.le (Subgroup.center_le_centralizer _ hcentral)

end CFSG.LargeEvenClassification.Helpers
