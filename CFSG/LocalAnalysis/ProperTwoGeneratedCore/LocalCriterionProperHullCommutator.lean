module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

theorem properHull_commutator_normalized (P A : Subgroup G) :
    P ⊔ A ≤ Subgroup.normalizer ((⁅P, A⁆ : Subgroup G) : Set G) := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.commutator_le_sup P A)).mp (CFSG.commutator_normal_in_sup P A)

theorem properHull_coprime_double_commutator [Finite G]
    (P A : Subgroup G)
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card P)) :
    ⁅⁅P, A⁆, A⁆ = ⁅P, A⁆ := by
  have : Subgroup.Normalizes A P := ⟨hAP⟩
  have hfirst : (CFSG.commutatorAction (A := A) (G := P)).map P.subtype = ⁅P, A⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P A hAP
  have hsecond : (CFSG.commutatorAction₂ (A := A) (G := P)).map P.subtype ≤
      ⁅⁅P, A⁆, A⁆ := by
    let C : Subgroup P := CFSG.commutatorAction (A := A) (G := P)
    let S : Set P := {x : P | ∃ a : A, ∃ h : P, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc
      (CFSG.commutatorAction₂ (A := A) (G := P)).map P.subtype =
          (Subgroup.closure S).map P.subtype := rfl
      _ = Subgroup.closure (P.subtype '' S) := MonoidHom.map_closure P.subtype S
      _ ≤ ⁅⁅P, A⁆, A⁆ := by
        apply (Subgroup.closure_le _).mpr
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨a, h, hh, rfl⟩ := hy
        have hhfirst : (h : G) ∈ ⁅P, A⁆ := by
          rw [← hfirst]
          exact Subgroup.mem_map_of_mem P.subtype hh
        have hc := Subgroup.commutator_mem_commutator
          ((⁅P, A⁆ : Subgroup G).inv_mem hhfirst) a.property
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hAP, mul_assoc] using hc
  have heq := CFSG.commutatorAction₂_eq_commutatorAction_of_coprime
    (G := P) (A := A) hcop
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (le_sup_right.trans (properHull_commutator_normalized P A))
  · calc
      ⁅P, A⁆ = (CFSG.commutatorAction (A := A) (G := P)).map P.subtype := hfirst.symm
      _ = (CFSG.commutatorAction₂ (A := A) (G := P)).map P.subtype :=
        congrArg (fun C : Subgroup P => C.map P.subtype) heq.symm
      _ ≤ ⁅⁅P, A⁆, A⁆ := hsecond

theorem properHull_odd_involution_commutator [Finite G]
    (p : ℕ) (P : Subgroup G) (z : G)
    (hP : IsPGroup p P) (hodd : Odd (Nat.card P))
    (hz : orderOf z = 2) (hzP : z ∈ Subgroup.normalizer (P : Set G))
    (hnoncentral : ¬ P ≤ Subgroup.centralizer ({z} : Set G)) :
    let X := ⁅P, Subgroup.zpowers z⁆
    X ≤ P ∧ X ≠ ⊥ ∧ IsPGroup p X ∧
      P ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (X : Set G) ∧
      ⁅X, Subgroup.zpowers z⁆ = X := by
  let A := Subgroup.zpowers z
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.mpr hzP
  have hXP : ⁅P, A⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hAP
  have hnon : ⁅P, A⁆ ≠ ⊥ := by
    intro hbot
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    apply hnoncentral
    intro x hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (hc hx z (Subgroup.mem_zpowers z)).symm
  have hpX : IsPGroup p (⁅P, A⁆ : Subgroup G) := hP.of_injective
    (Subgroup.inclusion hXP) (Subgroup.inclusion_injective hXP)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card P) := by
    rw [Nat.card_zpowers, hz]
    exact hodd.coprime_two_left
  exact ⟨hXP, hnon, hpX, properHull_commutator_normalized P A,
    properHull_coprime_double_commutator P A hAP hcop⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
