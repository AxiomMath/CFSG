module

public import CFSG.GH74.GLS.IVK.Lifted.FCent
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

section HatCenter

theorem hat_sq_eq_one_mem_center {Q : Type} [Group Q] [Finite Q] (hOK : HatOK Q) {x : Q}
    (hx : x * x = 1) : x ∈ Subgroup.center Q := by
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  · obtain ⟨c, hc1, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q)).1 hOK.sl2.2
    have hcc : (c : Q) * c = 1 := sq_eq_one_of_card_center hOK.sl2.2 c c.2
    have hc1' : (c : Q) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
    have hco : orderOf (c : Q) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1'
    have hcomm : x * c = c * x := Subgroup.mem_center_iff.1 c.2 x
    have := noCommInv_of_pRank hOK.rank x c hxo hco hcomm
    rw [this]
    exact c.2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_cSec_iff_hatMk_central {K : Subgroup G} {a : G} (ha : a ∈ K) :
    a ∈ cSec K ↔ hatMk K ⟨a, ha⟩ ∈ Subgroup.center (Hat K) := by
  constructor
  · intro hcs
    have h1 : phi K a (le_normalizer ha) = 1 := (phi_eq_one_iff K (le_normalizer ha)).2 hcs
    rw [phi_of_mem K ha] at h1
    rw [Subgroup.mem_center_iff]
    intro g
    have := DFunLike.congr_fun h1 g
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  · intro hc
    rw [← phi_eq_one_iff K (le_normalizer ha), phi_of_mem K ha]
    exact conj_eq_one_of_mem_center hc

end HatCenter

section Kernel

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem inf_Oz_le {B : Subgroup G} (hB : IsPCompIn 2 (Cz z) B) : B ⊓ Oz z ≤ pPrimeCoreOf 2 B := by
  have hBC : B ≤ Cz z := hB.1
  refine le_pPrimeCoreOf' inf_le_left (fun x hx n hn => ⟨?_, ?_⟩) ?_
  · exact B.mul_mem (B.mul_mem hx hn.1) (B.inv_mem hx)
  · exact Oz_conj (hBC hx) hn.2
  · exact Odd.of_dvd_nat card_Oz_odd (Subgroup.card_dvd_of_le inf_le_right)

end Kernel

section Involution

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mem_cSec_other {A B : Subgroup G} (hA : IsPCompIn 2 (Cz z) A) (hB : IsPCompIn 2 (Cz z) B)
    (hBA : B ≤ cSec A) (hAB : A ≤ cSec B) (hOA : HatOK (Hat A)) (hOB : HatOK (Hat B)) {a b : G}
    (ha : a ∈ A) (hb : b ∈ B) (hu2 : (a * b) * (a * b) = 1) (huA : a * b ∈ cSec A) :
    a * b ∈ cSec B := by
  have hbA : b ∈ cSec A := hBA hb
  have haA : a ∈ cSec A := by
    have := (cSec A).mul_mem huA ((cSec A).inv_mem hbA)
    simpa using this
  have hacent : hatMk A ⟨a, ha⟩ ∈ Subgroup.center (Hat A) := (mem_cSec_iff_hatMk_central ha).1 haA
  have haa : a * a ∈ pPrimeCoreOf 2 A := by
    have h1 := sq_eq_one_of_card_center hOA.sl2.2 _ hacent
    rw [← hatMk_eq_one_iff A ⟨a * a, A.mul_mem ha ha⟩]
    have : (⟨a * a, A.mul_mem ha ha⟩ : ↥A) = ⟨a, ha⟩ * ⟨a, ha⟩ := rfl
    rw [this, map_mul]
    exact h1
  have hcomm : ⁅a⁻¹, b⁆ ∈ pPrimeCoreOf 2 A := hbA.2.2 a⁻¹ (A.inv_mem ha)
  have hbb : b * b = (a * a * ⁅a⁻¹, b⁆)⁻¹ := by
    have : a * a * ⁅a⁻¹, b⁆ * (b * b) = 1 := by
      calc a * a * ⁅a⁻¹, b⁆ * (b * b) = (a * b) * (a * b) := by
            simp only [commutatorElement_def]
            group
        _ = 1 := hu2
    exact eq_inv_of_mul_eq_one_right this
  have hbbO : b * b ∈ Oz z := by
    rw [hbb]
    exact (Oz z).inv_mem ((Oz z).mul_mem (pPrimeCoreOf_le_Oz hA haa) (pPrimeCoreOf_le_Oz hA hcomm))
  have hbbB : b * b ∈ pPrimeCoreOf 2 B := inf_Oz_le hB ⟨B.mul_mem hb hb, hbbO⟩
  have hb2 : hatMk B ⟨b, hb⟩ * hatMk B ⟨b, hb⟩ = 1 := by
    rw [← map_mul]
    exact (hatMk_eq_one_iff B (⟨b, hb⟩ * ⟨b, hb⟩)).2 hbbB
  have hbcent : hatMk B ⟨b, hb⟩ ∈ Subgroup.center (Hat B) := hat_sq_eq_one_mem_center hOB hb2
  have hbB : b ∈ cSec B := (mem_cSec_iff_hatMk_central hb).2 hbcent
  exact (cSec B).mul_mem (hAB ha) hbB

end Involution

end CFSG.GH74.GLS.IVK.Lifted
