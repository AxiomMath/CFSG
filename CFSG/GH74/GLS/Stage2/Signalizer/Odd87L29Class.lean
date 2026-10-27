module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Sporadic
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Dih
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Burnside
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cHyp
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section Class

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem O2Of_mono {X X' : Subgroup G} (h : X ≤ X') : O2Of X ≤ O2Of X' := by
  unfold O2Of
  rw [Subgroup.map_le_iff_le_comap]
  unfold oResidual
  rw [Subgroup.closure_le]
  intro y hy
  have hy' : (y : G) ∈ O2Of X' :=
    mem_O2Of_of_coprime (h y.2) (by
      have := hy
      simpa [Subgroup.orderOf_coe] using this)
  exact hy'

theorem isDihedral_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsDihedral B) :
    IsDihedral A := by
  obtain ⟨m, k, hm, hk, ⟨f⟩⟩ := h
  exact ⟨m, k, hm, hk, ⟨e.trans f⟩⟩

omit [Finite G] in
theorem dihedral_or_cyclic_of_le {X X' : Subgroup G} (hX : X ≤ X')
    (hF : ∀ P : Sylow 2 ↥(O2Of X'), IsDihedral ↥P) (P' : Sylow 2 ↥(O2Of X)) :
    IsCyclic ↥P' ∨ IsDihedral ↥P' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := O2Of_mono hX
  set Pm : Subgroup G := (P' : Subgroup ↥(O2Of X)).map (O2Of X).subtype with hPm
  have hPmO : Pm ≤ O2Of X' := (Subgroup.map_subtype_le _).trans hO
  set P'' : Subgroup ↥(O2Of X') := Pm.subgroupOf (O2Of X') with hP''
  have h2 : IsPGroup 2 ↥P'' := (P'.isPGroup'.map (O2Of X).subtype).comap_subtype
  obtain ⟨S, hS⟩ := h2.exists_le_sylow
  have hdih := hF S
  let Y : Subgroup ↥(S : Subgroup ↥(O2Of X')) := P''.subgroupOf S
  let e : ↥(P' : Subgroup ↥(O2Of X)) ≃* ↥Y :=
    (Subgroup.equivMapOfInjective (P' : Subgroup ↥(O2Of X)) (O2Of X).subtype
      (O2Of X).subtype_injective).trans
      ((Subgroup.subgroupOfEquivOfLe hPmO).symm.trans (Subgroup.subgroupOfEquivOfLe hS).symm)
  rcases subgroup_of_dihedral hdih Y with h | h
  · exact Or.inl (e.isCyclic.mpr h)
  · exact Or.inr (isDihedral_congr e h)

theorem lemma29Alt_of_noncentral {z : G} {k : Kind} (hk : IsClassicalKind k) {U : Subgroup G}
    {x : G} (hxU : x ∈ U) (hF : P27.FullG x)
    (hz : (∀ u ∈ U, ¬ IsConj z u) ∨
      ∃ t g : G, SwapsComps z t ∧ conjugate (zpowers z ⊔ zpowers t) g = U) :
    Lemma29Alt z k U := by
  have hle : centralizer (U : Set G) ≤ centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxU)
  by_cases hcyc : ∃ P : Sylow 2 ↥(O2Of (centralizer (U : Set G))), IsCyclic ↥P
  · exact Or.inl (hasNormal2Compl_of_O2_cyclic _ hcyc)
  · refine Or.inr (Or.inl ⟨hk, fun P => ?_, hz⟩)
    rcases dihedral_or_cyclic_of_le hle hF P with h | h
    · exact absurd ⟨P, h⟩ hcyc
    · exact h

theorem lemma29Alt_of_no_conj {z : G} {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S)
    (hk : IsClassicalKind k) (hND : NonCentralDihedral) {U : Subgroup G}
    (hU : IVK.IsFourSubgroup U) (hz : ∀ u ∈ U, ¬ IsConj z u) : Lemma29Alt z k U := by
  obtain ⟨x, hxU, hx1⟩ : ∃ x ∈ U, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h4 := hU.2
    rw [this, Subgroup.card_bot] at h4
    omega
  have hxo : orderOf x = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact four_sq_eq_one hU hxU) hx1
  have hnc : IsNonCentralInvolution x := ⟨hxo, fun hc =>
    hz x hxU (P34.isConj_of_isCentralInvolution ctx hc)⟩
  exact lemma29Alt_of_noncentral hk hxU (hND G z k S ctx x hnc) (Or.inl hz)

end Class

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
