module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_centralizer_of_conjNormal_eq_one {P : Subgroup G} [P.Normal] {x : G}
    (h : (MulAut.conjNormal x : MulAut ↥P) = 1) : x ∈ centralizer (P : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have h1 := congrArg (fun φ : MulAut ↥P => ((φ ⟨y, hy⟩ : ↥P) : G)) h
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc y * x = x * y * x⁻¹ * x := by rw [h1]
    _ = x * y := by group

theorem mem_centralizer_of_odd_of_isPGroup_mulAut [Finite G] {P : Subgroup G} [P.Normal]
    (hA : IsPGroup 2 (MulAut ↥P)) {x : G} (hx : Odd (orderOf x)) :
    x ∈ centralizer (P : Set G) := by
  refine mem_centralizer_of_conjNormal_eq_one ?_
  obtain ⟨k, hk⟩ := hA (MulAut.conjNormal x)
  have h1 : orderOf (MulAut.conjNormal x : MulAut ↥P) ∣ orderOf x := orderOf_map_dvd _ x
  have h2 : orderOf (MulAut.conjNormal x : MulAut ↥P) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hx)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem mulAut_sq_eq_one_of_kleinFour {V : Type*} [Group V] [IsKleinFour V] (ψ : MulAut V) {b : V}
    (hb : b ≠ 1) (hψb : ψ b = b) : ψ ^ 2 = 1 := by
  have hsq : ∀ x : V, x * x = 1 := fun x => by
    rw [← sq, ← IsKleinFour.exponent_two (G := V)]
    exact Monoid.pow_exponent_eq_one x
  ext y
  rw [sq, MulAut.mul_apply, MulAut.one_apply]
  by_cases hy1 : y = 1
  · rw [hy1, map_one, map_one]
  by_cases hyb : y = b
  · rw [hyb, hψb, hψb]
  have hψy1 : ψ y ≠ 1 := fun h => hy1 (ψ.injective (h.trans (map_one ψ).symm))
  have hψyb : ψ y ≠ b := fun h => hyb (ψ.injective (h.trans hψb.symm))
  by_cases hψyy : ψ y = y
  · rw [hψyy, hψyy]
  · have h1 : ψ y = y * b := IsKleinFour.eq_mul_of_ne_all hy1 hb hyb hψy1 hψyy hψyb
    rw [h1, map_mul, h1, hψb, mul_assoc, hsq b, mul_one]

theorem mem_centralizer_of_odd_of_kleinFour [Finite G] {P : Subgroup G} [P.Normal]
    [IsKleinFour ↥P] {b : G} (hbP : b ∈ P) (hb1 : b ≠ 1) (hbc : b ∈ center G) {x : G}
    (hx : Odd (orderOf x)) : x ∈ centralizer (P : Set G) := by
  refine mem_centralizer_of_conjNormal_eq_one ?_
  have hfix : (MulAut.conjNormal x : MulAut ↥P) ⟨b, hbP⟩ = ⟨b, hbP⟩ := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show x * b * x⁻¹ = b
    rw [mem_center_iff.mp hbc x, mul_inv_cancel_right]
  have h2 := mulAut_sq_eq_one_of_kleinFour (MulAut.conjNormal x : MulAut ↥P)
    (b := ⟨b, hbP⟩) (fun h => hb1 (congrArg Subtype.val h)) hfix
  have h1 : orderOf (MulAut.conjNormal x : MulAut ↥P) ∣ orderOf x := orderOf_map_dvd _ x
  have h2' : orderOf (MulAut.conjNormal x : MulAut ↥P) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hx) h1 h2')

theorem solvableRadical_le_centralizer_layer [Finite G] :
    solvableRadical G ≤ centralizer (layer G : Set G) := by
  rw [le_centralizer_iff]
  refine sSup_le fun J hJ => ?_
  have hSn : (solvableRadical G).Normal := ABGLocalTools.solvableRadical_normal
  rcases LocalCores.component_subnormal_subgroup hJ hSn.isSubnormal with hle | hcomm
  · exfalso
    obtain ⟨hperf, hsimp, a, b, hab⟩ := hJ.1
    have : Group.IsSolvable ↥(solvableRadical G) := ABGLocalTools.solvableRadical_isSolvable
    have hsolv : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have hnt : Nontrivial ↥J := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      apply hab
      exact Subsingleton.elim _ _
    exact Group.IsPerfect.not_isSolvable _ hsolv
  · intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : ⁅x, y⁆ ∈ ⁅J, solvableRadical G⁆ := commutator_mem_commutator hx hy
    rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

theorem centralizer_pCore_sup_layer_le [Finite G] (hO : pPrimeCore 2 G = ⊥) :
    centralizer ((pCore 2 G ⊔ layer G : Subgroup G) : Set G) ≤ pCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting G
  rw [← CFSG.generalizedFitting_eq_componentClassification] at h
  rw [← Fitting_eq_pcore G 2 hO]
  exact h

end CFSG.ComponentClassification.HarrisLit
