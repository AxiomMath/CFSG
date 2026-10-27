module

public import CFSG.LocalAnalysis.LargeEvenClassification.MaximalAbelian
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalPowers

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem deep_lifts_commute_mod_squares {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) [Normal.Normal] (hcommutative : IsMulCommutative Normal)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (first second : Ambient)
    (hfirstSquare : (MulAut.conjNormal (H := Normal) first) ^ 2 = 1)
    (hactions : Commute (MulAut.conjNormal (H := Normal) first)
      (MulAut.conjNormal (H := Normal) second))
    (hfirstDeep : ∀ element : Normal,
      first * (element : Ambient) * first⁻¹ * (element : Ambient)⁻¹ ∈
        normalPowerSubgroup Normal hcommutative 4)
    (hsecondDeep : ∀ element : Normal,
      second * (element : Ambient) * second⁻¹ * (element : Ambient)⁻¹ ∈
        normalPowerSubgroup Normal hcommutative 4)
    (hroot : ∀ element : Normal,
      (element : Ambient) ^ 2 ∈ normalPowerSubgroup Normal hcommutative 4 →
        (element : Ambient) ∈ normalPowerSubgroup Normal hcommutative 2) :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    Commute ((QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) first)
      ((QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) second) := by
  dsimp only
  let Power := normalPowerSubgroup Normal hcommutative 2
  let Fourth := normalPowerSubgroup Normal hcommutative 4
  let : Power.Normal := normalPowerSubgroup_normal Normal hcommutative 2
  let action : Ambient →* MulAut Normal := MulAut.conjNormal
  have hkernel : action.ker = Normal :=
    (conjNormal_ker_eq_centralizer Normal).trans hselfCentralizing
  let commutator := first * second * first⁻¹ * second⁻¹
  have hcommutatorNormal : commutator ∈ Normal := by
    apply hkernel.le
    change action commutator = 1
    dsimp only [commutator]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    change Commute (action first) (action second) at hactions
    rw [hactions.eq]
    group
  have hfirstSquareNormal : first ^ 2 ∈ Normal := by
    apply hkernel.le
    change action (first ^ 2) = 1
    rw [map_pow]
    exact hfirstSquare
  have hsquareCommFourth : first ^ 2 * second * (first ^ 2)⁻¹ * second⁻¹ ∈ Fourth := by
    have hdeep := hsecondDeep ⟨first ^ 2, hfirstSquareNormal⟩
    have hinverse := Fourth.inv_mem hdeep
    convert hinverse using 1
    group
  have hconjugateFourth : first * commutator * first⁻¹ * commutator⁻¹ ∈ Fourth :=
    hfirstDeep ⟨commutator, hcommutatorNormal⟩
  have hconjugateNormal : first * commutator * first⁻¹ ∈ Normal :=
    Subgroup.Normal.conj_mem inferInstance commutator hcommutatorNormal first
  have hcommute : Commute (first * commutator * first⁻¹) commutator := by
    exact congrArg (fun entry : Normal => (entry : Ambient))
      (@mul_comm' Normal _ hcommutative ⟨_, hconjugateNormal⟩ ⟨_, hcommutatorNormal⟩)
  have hcommutatorSquareFourth : commutator ^ 2 ∈ Fourth := by
    have hproduct := Fourth.mul_mem hsquareCommFourth (Fourth.inv_mem hconjugateFourth)
    have hformula : first ^ 2 * second * (first ^ 2)⁻¹ * second⁻¹ =
        (first * commutator * first⁻¹) * commutator := by
      dsimp only [commutator]
      simp only [pow_two]
      group
    rw [hformula] at hproduct
    have hidentity : ∀ leftEntry rightEntry : Ambient, Commute leftEntry rightEntry →
        (leftEntry * rightEntry) * (leftEntry * rightEntry⁻¹)⁻¹ = rightEntry ^ 2 := by
      intro leftEntry rightEntry hentries
      rw [mul_inv_rev, inv_inv]
      calc
        _ = (leftEntry * rightEntry ^ 2) * leftEntry⁻¹ := by simp only [pow_two]; group
        _ = (rightEntry ^ 2 * leftEntry) * leftEntry⁻¹ := by rw [(hentries.pow_right 2).eq]
        _ = rightEntry ^ 2 := by group
    exact (hidentity _ _ hcommute) ▸ hproduct
  have hcommutatorPower : commutator ∈ Power :=
    hroot ⟨commutator, hcommutatorNormal⟩ hcommutatorSquareFourth
  let projection := QuotientGroup.mk' Power
  have hzero : projection commutator = 1 := (QuotientGroup.eq_one_iff _).mpr hcommutatorPower
  dsimp only [commutator] at hzero
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hzero
  have heq : projection first * projection second = projection second * projection first := by
    have := mul_inv_eq_iff_eq_mul.mp hzero
    have := mul_inv_eq_iff_eq_mul.mp (by simpa using this)
    simpa using this
  exact heq

end CFSG.LargeEvenClassification.Helpers
