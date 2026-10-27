module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open CFSG.Assembly
open CFSG.LieType.SemisimpleCentralizers.Held
  (heldSU hct_heldSU_eq_statedSU hct_isSolvable_of_natCard_eq)

theorem nonempty_quot_heldSU_equiv_statedProj (hScal : UniScalar) {E : Type} [Field E]
    [Finite E] {a m : ℕ} (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x)
    (hτ'm : ∀ x, τ' x = x ^ (2 ^ m)) (hE : Nat.card E = (2 ^ m) ^ 2) (ha : 3 ≤ a)
    (ham : (a, 2 ^ m) ≠ (3, 2)) :
    Nonempty (heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ') ≃*
      StatedProj (StatedSU a (2 ^ m) E)) := by
  have hH : heldSU a E τ' hτ' = StatedSU a (2 ^ m) E := hct_heldSU_eq_statedSU hτ'm
  have hZge : (StatedScalars (Fin a) E).subgroupOf (StatedSU a (2 ^ m) E) ≤
      Subgroup.center (StatedSU a (2 ^ m) E) := by
    have h := ker_projMk_uni_le_center (d := a) (K := E) (StatedSU a (2 ^ m) E)
    simpa only [LargeEvenProjMk, QuotientGroup.ker_mk'] using h
  have hZle : Subgroup.center (StatedSU a (2 ^ m) E) ≤
      (StatedScalars (Fin a) E).subgroupOf (StatedSU a (2 ^ m) E) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    have hcomm : ∀ g : GL (Fin a) E, g ∈ StatedSU a (2 ^ m) E → ∃ c : E,
        ((z : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) *
          (g : Matrix (Fin a) (Fin a) E) *
          (((z : GL (Fin a) E)⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) =
          c • (g : Matrix (Fin a) (Fin a) E) := by
      intro g hg
      refine ⟨1, ?_⟩
      have hzg : g * (z : GL (Fin a) E) = (z : GL (Fin a) E) * g := by
        simpa using congrArg (fun w : ↥(StatedSU a (2 ^ m) E) => (w : GL (Fin a) E))
          (Subgroup.mem_center_iff.mp hz (⟨g, hg⟩ : ↥(StatedSU a (2 ^ m) E)))
      have h1 : (z : GL (Fin a) E) * g * (z : GL (Fin a) E)⁻¹ = g := by
        rw [hzg.symm, mul_assoc, mul_inv_cancel, mul_one]
      have hmat := congrArg (fun w : GL (Fin a) E => (w : Matrix (Fin a) (Fin a) E)) h1
      simpa [Units.val_inv_eq_inv_val] using hmat
    obtain ⟨c, hc⟩ := hScal E (2 ^ m) a τ' hτ' hτ'm hE ha ham (z : GL (Fin a) E) hcomm
    have hzcenter : (z : GL (Fin a) E) ∈ Subgroup.center (GL (Fin a) E) := by
      rw [Subgroup.mem_center_iff]
      intro X
      apply Units.ext
      simp only [Units.val_mul]
      rw [hc, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hzcenter
    exact hzcenter
  have hZ : Subgroup.center (StatedSU a (2 ^ m) E) =
      (StatedScalars (Fin a) E).subgroupOf (StatedSU a (2 ^ m) E) := le_antisymm hZle hZge
  refine ⟨?_⟩
  rw [hH]
  exact QuotientGroup.quotientMulEquivOfEq hZ

theorem ggHasLabel_twA {X : Type} [Group X] {b m : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ m) ^ 2) (e : X ≃* StatedProj (StatedSU (b + 1) (2 ^ m) E)) :
    CFSG.StandardType.GGHasLabel ⟨.twA, b, m⟩ X := by
  refine ⟨E, inferInstance, inferInstance, hE, ?_⟩
  exact ⟨e⟩

theorem largeEvenInLambda2_twA {b m : ℕ} (hm : 1 ≤ m) (hb : 2 ≤ b) (hbm : b = 2 → 2 ≤ m) :
    LargeEvenInLambda2 ⟨.twA, b, m⟩ := by
  refine ⟨hm, hb, ?_⟩
  exact hbm

theorem isSolvable_quot_heldSU_three_two {E : Type} [Field E] [Finite E] (τ' : E ≃+* E)
    (hτ' : ∀ x, τ' (τ' x) = x) (hτ'2 : ∀ x, τ' x = x ^ 2) (hE : Nat.card E = 4) :
    Group.IsSolvable (heldSU 3 E τ' hτ' ⧸ Subgroup.center (heldSU 3 E τ' hτ')) := by
  have hH : heldSU 3 E τ' hτ' = StatedSU 3 2 E := hct_heldSU_eq_statedSU (a := 3) (Q := 2) hτ'2
  have hcard : Nat.card ↥(heldSU 3 E τ' hτ') = 2 ^ 3 * 3 ^ 3 := by
    have hc := CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two
      (F := E) (f := 1) (by rw [hE]; norm_num)
    rw [hH]
    norm_num at hc ⊢
    exact hc
  have hsol : Group.IsSolvable ↥(heldSU 3 E τ' hτ') :=
    hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 3)
      Nat.prime_two Nat.prime_three (by norm_num) hcard
  haveI := hsol
  exact Group.instIsSolvableQuotientSubgroup (Subgroup.center ↥(heldSU 3 E τ' hτ'))

theorem not_isSolvable_quot_center {J : Type} [Group J] [IsSimpleGroup (J ⧸ Subgroup.center J)] :
    ¬ Group.IsSolvable (J ⧸ Subgroup.center J) := by
  intro hsol
  have hcomm : ∀ a b : J ⧸ Subgroup.center J, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr hsol
  haveI : IsMulCommutative (J ⧸ Subgroup.center J) := ⟨⟨hcomm⟩⟩
  letI : CommGroup (J ⧸ Subgroup.center J) := IsMulCommutative.instCommGroup
  have hcyc : IsCyclic (J ⧸ Subgroup.center J) := IsSimpleGroup.isCyclic
  haveI := hcyc
  have hJcomm : ∀ a b : J, a * b = b * a :=
    commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center J))
      (by rw [QuotientGroup.ker_mk'])
  haveI : IsMulCommutative J := ⟨⟨hJcomm⟩⟩
  have htop : Subgroup.center J = ⊤ := Subgroup.center_eq_top
  exact not_subsingleton (J ⧸ Subgroup.center J)
    (QuotientGroup.subsingleton_iff.mpr htop)

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end
