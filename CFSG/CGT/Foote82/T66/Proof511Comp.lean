module

public import CFSG.CGT.Foote82.T66.Proof511Red
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2A7
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415K2
public import CFSG.GH74.E2.ComponentsShape

public section

namespace CFSG.CGT.Foote82.Proof511

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem simple_nonab_of_mulEquiv {M S : Type*} [Group M] [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) (e : M ≃* S) :
    IsSimpleGroup M ∧ (∃ a b : M, a * b ≠ b * a) ∧ center M = ⊥ := by
  haveI : IsSimpleGroup M := e.isSimpleGroup
  have hnab' : ∃ a b : M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  exact ⟨inferInstance, hnab', center_eq_bot_of_simple hnab'⟩

variable {G : Type} [Group G] [Finite G]

namespace Red

variable {J L : Subgroup G} {H : Type} [Group H] [Finite H] (r : Red J L H)
include r

theorem pPrimeCore_Lb_eq_bot (hev : 2 ∣ Nat.card ↥L) : pPrimeCore 2 ↥r.Lb = ⊥ := by
  haveI := r.simpleL
  obtain ⟨hs, -, -⟩ := simple_nonab_of_mulEquiv r.nonabL r.eL
  exact CFSG.ComponentClassification.HarrisLit.L415.pPrimeCore_eq_bot_of_simple_even hs
    (by rw [Nat.card_congr r.eL.toEquiv]; exact hev)

theorem lieModel_Lb (h6 : Nonempty (↥L ≃* alternatingGroup (Fin 6))) :
    LieModel (↥r.Lb ⧸ pPrimeCore 2 ↥r.Lb) .PSL 2 3 2 := by
  obtain ⟨e⟩ := h6
  have hev : 2 ∣ Nat.card ↥L := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hO := r.pPrimeCore_Lb_eq_bot hev
  exact CFSG.GH74.E2.lieModel_psl_two_nine_of_alt_six
    ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans
      (r.eL.trans e)⟩

theorem psl4_card (h6 : Nonempty (↥L ≃* alternatingGroup (Fin 6))) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel ↥(generalizedFitting H) .PSL 4 p f) :
    p ^ f = 3 ∨ p ^ f = 9 := by
  classical
  haveI : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨⟨-, he, -⟩, k, _, _, hk, ⟨φ₀⟩⟩ :=
    CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL
  let φ : ↥(generalizedFitting H) ≃* LinearFlag.projectiveSL 4 k :=
    φ₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 k).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 k))
  have hZP := CFSG.ComponentClassification.OddSelector.center_projectiveSL_eq_bot (k := k)
    (by norm_num : 3 ≤ 4)
  obtain ⟨ρ, hinj, hρW, -, -⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.socle_extension r.cent_eq φ hZP
  obtain ⟨-, h⟩ := CFSG.ComponentClassification.GSThmB.Catalog7L4M.psl4_component_type r.cent_eq
    hp hp2 he hk φ hinj hρW r.order r.le_F r.le_C r.pcomp Nat.prime_three (by norm_num)
    (by norm_num) (r.lieModel_Lb h6)
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · left
    rw [hk] at h
    exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h).symm
  · right
    rw [hk] at h
    exact h.symm

theorem psu4_card (h6 : Nonempty (↥L ≃* alternatingGroup (Fin 6))) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel ↥(generalizedFitting H) .PSU 4 p f) :
    p ^ f = 3 ∨ p ^ f = 9 := by
  classical
  haveI : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  haveI := r.simple
  obtain ⟨⟨-, he, -⟩, K, _, _, hK, ⟨φ₀⟩⟩ :=
    CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL
  have hud : UnitaryFieldData p f K := ⟨hp, he, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨hs, -, hZP⟩ := simple_nonab_of_mulEquiv r.nonab φ₀.symm
  obtain ⟨ρ, hinj, hρW, -, -⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.socle_extension r.cent_eq φ₀ hZP
  obtain ⟨-, -, A, ψ, -, -, h⟩ := CFSG.ComponentClassification.GSThmB.Catalog7L4EU.psu4_component_type
    hud r.cent_eq hp2 φ₀ hinj hρW hZP r.order r.le_F r.le_C r.pcomp Nat.prime_three (by norm_num)
    (by norm_num) (r.lieModel_Lb h6)
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · left
    exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h).symm
  · left
    exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h).symm
  · right
    exact h.symm

theorem false_of_alt7 (hGLS : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h7 : Nonempty (↥L ≃* alternatingGroup (Fin 7))) (hodd : OddLieType ↥(generalizedFitting H)) :
    False := by
  haveI : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  haveI := r.simpleL
  obtain ⟨hα2, hα1⟩ := CFSG.ComponentClassification.GSThmB.X10Rec.conjNormal_involutive
    r.cent_eq r.order
  have hα : orderOf (MulAut.conjNormal r.x : MulAut ↥(generalizedFitting H)) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  obtain ⟨L', hL'p, ⟨eL'⟩⟩ := CFSG.ComponentClassification.GSThmB.X10Rec.fixed_pComponent
    r.le_F r.le_C r.pcomp
  obtain ⟨e7⟩ := h7
  let e₁ : ↥L' ≃* ↥L := eL'.trans r.eL
  obtain ⟨hs', -, hZ'⟩ := simple_nonab_of_mulEquiv r.nonabL e₁
  have hq : CFSG.IsQuasisimple ↥L' :=
    (CFSG.IsQuasisimple.congr e₁).mpr (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup r.nonabL).1
  obtain ⟨-, -, hsub, -, -⟩ := hL'p
  rcases CFSG.ComponentClassification.CatFC.odd_arm hGLS hodd hα ⟨hq, hsub⟩ with h | h
  · exact CFSG.ComponentClassification.CatFC.not_oddLieType_of_alt7_iso hO
      (((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).trans
        (e₁.trans e7)) h
  · have h504 := CFSG.ComponentClassification.GSThmB.X10Rec.card_psl_two_eight hO h
    have h2520 : Nat.card ↥L' = 2520 := by
      rw [Nat.card_congr (e₁.trans e7).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    omega

end Red

end CFSG.CGT.Foote82.Proof511
