module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ConjAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.FixLarge
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open
open scoped commutatorElement

namespace CentConfig

variable {X : Type} [Group X] [Finite X] {a b : X} {E : Subgroup X} {Fus : X → Prop}

theorem no_commuting_component (h : CentConfig X a b E Fus) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKE : ⁅E, K⁆ = ⊥) (hF : FixLarge ↥K) : False := by
  have ha : orderOf a = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simpa [pow_two] using h.a_sq) h.a_ne
  have hKcE : K ≤ centralizer (E : Set X) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKE)
  by_cases hα : a ∈ Subgroup.normalizer (K : Set X)
  ·
    have hζ2 : conjAut K a hα * conjAut K a hα = 1 := conjAut_mul_self K hα h.a_sq
    have hfix := hF (conjAut K a hα) hζ2
    rw [card_fixedSubgroup_conjAut K hα] at hfix
    have hle := h.card_le_four (W := K ⊓ centralizer ({a} : Set X))
      inf_le_right (inf_le_left.trans hKcE)
    omega
  ·
    have hmoved :
        CFSG.ComponentClassification.AschbacherComponentAction.rightComponent K a ≠ K :=
      fun hK' => hα
        ((CFSG.ComponentClassification.AschbacherComponentAction.rightComponent_eq_iff_normalizer
          K a).mp hK')
    let C := Subgroup.centralizer ({a} : Set X)
    let D := ⁅⁅K, Subgroup.zpowers a⁆ ⊓ C, ⁅K, Subgroup.zpowers a⁆ ⊓ C⁆
    have hDc : IsComponentOf (D.subgroupOf C) ⊤ :=
      CFSG.ComponentClassification.AschbacherComponentInvolution.moved_derived_centralizer_component
        K a hK ha hmoved
    have hRcE :
        CFSG.ComponentClassification.AschbacherComponentAction.rightComponent K a ≤
          centralizer (E : Set X) := by
      rw [CFSG.ComponentClassification.AschbacherComponentAction.rightComponent_involution K a
        h.a_sq]
      rintro x ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hea : e * a = a * e := h.a_comm he
      have hke : e * k = k * e := Subgroup.mem_centralizer_iff.mp (hKcE hk) e he
      have haie : e * a⁻¹ = a⁻¹ * e := (show Commute e a from hea).inv_right.eq
      calc e * (a * k * a⁻¹) = (e * a) * k * a⁻¹ := by group
        _ = (a * e) * k * a⁻¹ := by rw [hea]
        _ = a * (e * k) * a⁻¹ := by group
        _ = a * (k * e) * a⁻¹ := by rw [hke]
        _ = (a * k) * (e * a⁻¹) := by group
        _ = (a * k) * (a⁻¹ * e) := by rw [haie]
        _ = (a * k * a⁻¹) * e := by group
    have hcommut : ⁅K, Subgroup.zpowers a⁆ ≤ centralizer (E : Set X) := by
      rw [CFSG.ComponentClassification.AschbacherComponentAction.moved_component_commutator
        K a hK h.a_sq hmoved]
      exact sup_le hKcE hRcE
    have hDA : D ≤ ⁅K, Subgroup.zpowers a⁆ ⊓ C := Subgroup.commutator_le_self _
    have hDE : D ≤ centralizer (E : Set X) := hDA.trans (inf_le_left.trans hcommut)
    have hDa : D ≤ centralizer ({a} : Set X) := hDA.trans inf_le_right
    have hDfour : ∀ x ∈ D, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
      intro x hx
      have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp (hDa hx)
      have hxE : ∀ e ∈ E, x * e = e * x := fun e he =>
        (Subgroup.mem_centralizer_iff.mp (hDE hx) e he).symm
      exact h.cent_cent_E hxa hxE
    have hDle : D ≤ Subgroup.closure ({a, b} : Set X) := by
      intro x hx
      rcases hDfour x hx with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.mul_mem _
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have hpair : ({a, b} : Set X).Pairwise Commute := by
      intro x hx y hy hxy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hxa | hxb
      · rcases hy with hya | hyb
        · exact absurd (hxa.trans hya.symm) hxy
        · rw [hxa, hyb]
          exact Subgroup.mem_center_iff.mp h.b_central a
      · rcases hy with hya | hyb
        · rw [hxb, hya]
          exact (Subgroup.mem_center_iff.mp h.b_central a).symm
        · exact absurd (hxb.trans hyb.symm) hxy
    haveI : IsMulCommutative (Subgroup.closure ({a, b} : Set X)) :=
      Subgroup.isMulCommutative_closure hpair
    haveI : IsMulCommutative D := isMulCommutative_anti hDle
    haveI : Group.IsPerfect ↥(D.subgroupOf C) := ⟨hDc.2.2.1⟩
    haveI : Nontrivial ↥(D.subgroupOf C) :=
      CFSG.ComponentClassification.Quasisimple.nontrivial hDc.2.2
    exact Group.IsPerfect.not_isMulCommutative ↥(D.subgroupOf C) inferInstance

theorem normal_of_fixLarge (h : CentConfig X a b E Fus) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hEL : E ≤ L) (hF : FixLarge ↥L) : L.Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  let L' := L.map (MulAut.conj g).toMonoidHom
  change L' = L
  by_contra hne
  have hL' : IsComponentOf L' ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  have hcomm : ⁅L, L'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL'
      (fun hEq => hne hEq.symm)
  have hEL' : ⁅E, L'⁆ = ⊥ := by
    have hle : ⁅E, L'⁆ ≤ ⁅L, L'⁆ := Subgroup.commutator_mono hEL le_rfl
    rw [hcomm] at hle
    exact le_bot_iff.mp hle
  have hF' : FixLarge ↥L' :=
    FixLarge.of_mulEquiv
      (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hF
  exact no_commuting_component h hL' hEL' hF'

end CentConfig

end CFSG.EvenSporadicStandard.Co3Std.CentT
