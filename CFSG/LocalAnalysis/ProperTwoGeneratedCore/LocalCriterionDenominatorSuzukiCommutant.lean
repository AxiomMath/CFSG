module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclicNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiInvolutions
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import Certificates.Certificate43
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.InvariantComplement

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII

theorem centralizer_commutative_of_rationalCommutant_isField
    {K V F : Type*} [Field K] [AddCommGroup V] [Module K V] [Group F]
    (rho : F →* LinearMap.GeneralLinearGroup K V) (hrho : Function.Injective rho)
    (x : F) (hfield : IsField (rationalCommutant (rho x : Module.End K V))) :
    IsMulCommutative (Subgroup.centralizer ({x} : Set F)) := by
  apply isMulCommutative_iff.mpr
  intro a b
  have hmem (c : Subgroup.centralizer ({x} : Set F)) :
      (rho c.val : Module.End K V) ∈ rationalCommutant (rho x : Module.End K V) := by
    apply (mem_rationalCommutant_iff _ _).mpr
    have hc := congrArg (fun y : F => (rho y : Module.End K V))
      (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm
    simpa only [map_mul, Units.val_mul] using hc
  apply Subtype.ext
  apply hrho
  change rho (a.val * b.val) = rho (b.val * a.val)
  rw [map_mul, map_mul]
  apply Units.ext
  exact congrArg Subtype.val
    (hfield.mul_comm (⟨rho a.val, hmem a⟩ : rationalCommutant (rho x : Module.End K V))
      ⟨rho b.val, hmem b⟩)

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "SzG" => SuzukiMatrixGroup m
local notation "V" => Fin 4 → K

@[expose] def suzukiNaturalRepresentation : SzG →* LinearMap.GeneralLinearGroup K V :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (SuzukiMatrixGroup m).subtype

theorem suzukiNaturalRepresentation_injective :
    Function.Injective (suzukiNaturalRepresentation m) := by
  intro x y hxy
  apply (SuzukiMatrixGroup m).subtype_injective
  exact Matrix.GeneralLinearGroup.toLin.injective hxy

theorem suzuki_degree_divisor_irreducible (x : SzG) (hx : x ≠ 1)
    (hdiv : orderOf x ∣ (2 ^ (2 * m + 1)) ^ 2 + 1)
    (U : Submodule K V)
    (hU : ∀ v ∈ U, (suzukiNaturalRepresentation m x : Module.End K V) v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  have hcardne : Nat.card (Subgroup.zpowers x) ≠ 1 := by
    rw [Nat.card_zpowers]
    exact fun h => hx (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrdiv⟩ := Nat.exists_prime_and_dvd hcardne
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.zpowers x) r hrdiv
  have hrN : r ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    rw [Nat.card_zpowers] at hrdiv
    exact hrdiv.trans hdiv
  have hNodd : Odd ((2 ^ (2 * m + 1)) ^ 2 + 1) :=
    ((even_two.pow_of_ne_zero (by omega : 2 * m + 1 ≠ 0)).pow_of_ne_zero
      (by norm_num : 2 ≠ 0)).add_one
  have hrne2 : r ≠ 2 := by
    intro h
    exact hNodd.not_two_dvd_nat (h ▸ hrN)
  apply lemma114_suzuki_zpowers_irreducible m r hr hrne2 z
    ((Subgroup.orderOf_coe z).trans hzorder) hrN U
  intro a v hv
  have haX : (a : SzG) ∈ Subgroup.zpowers x :=
    (Subgroup.zpowers_le.mpr z.property) a.property
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (a : SzG) x).mp (mem_powers_iff_mem_zpowers.mpr haX)
  change (suzukiNaturalRepresentation m (a : SzG) : Module.End K V) v ∈ U
  rw [← hn, map_pow, Units.val_pow_eq_pow_val]
  exact Module.End.pow_apply_mem_of_forall_mem n hU v hv

theorem suzuki_degree_divisor_centralizer_commutative
    (x : SzG) (hx : x ≠ 1)
    (hdiv : orderOf x ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) :
    IsMulCommutative (Subgroup.centralizer ({x} : Set SzG)) :=
  centralizer_commutative_of_rationalCommutant_isField
    (suzukiNaturalRepresentation m) (suzukiNaturalRepresentation_injective m) x
    (rationalCommutant_isField (suzukiNaturalRepresentation m x : Module.End K V)
      (suzuki_degree_divisor_irreducible m x hx hdiv))

theorem suzuki_degree_divisor_centralizer_cyclic_odd (hm : 0 < m)
    (x : SzG) (hx : x ≠ 1) (hdiv : orderOf x ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) :
    IsCyclic (Subgroup.centralizer ({x} : Set SzG)) ∧
      Odd (Nat.card (Subgroup.centralizer ({x} : Set SzG))) := by
  have hNodd : Odd ((2 ^ (2 * m + 1)) ^ 2 + 1) :=
    ((even_two.pow_of_ne_zero (by omega : 2 * m + 1 ≠ 0)).pow_of_ne_zero
      (by norm_num : 2 ≠ 0)).add_one
  have hodd := odd_element_full_centralizer_odd x hx (hNodd.of_dvd_nat hdiv)
    (suzuki_involution_centralizer_isPGroup m hm)
  exact ⟨odd_commutative_subgroup_cyclic _ hodd
    (suzuki_degree_divisor_centralizer_commutative m x hx hdiv)
    (lemma114_suzuki_oddSylow_isCyclic_of_equiv (MulEquiv.refl SzG)), hodd⟩

theorem suzuki_degree_divisor_full_normalizer_index_dvd_four
    (hm : 0 < m)
    (x : SzG) (hx : x ≠ 1) (hdiv : orderOf x ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) :
    (Subgroup.centralizer ({x} : Set SzG)).relIndex
      (Subgroup.normalizer (Subgroup.centralizer ({x} : Set SzG) : Set SzG)) ∣ 4 := by
  let : IsCyclic (Subgroup.centralizer ({x} : Set SzG)) :=
    (suzuki_degree_divisor_centralizer_cyclic_odd m hm x hx hdiv).1
  exact full_cyclic_centralizer_normalizer_index_dvd_four
    (suzukiNaturalRepresentation m) (suzukiNaturalRepresentation_injective m) _ x
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl) rfl
    (suzuki_degree_divisor_irreducible m x hx hdiv) (by simp)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
