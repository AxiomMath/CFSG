module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Class

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section Embedding

theorem cyclic_or_dihedral_of_injective {P S : Type} [Group P] [Group S] (φ : P →* S)
    (hφ : Function.Injective φ) (hS : IsCyclic S ∨ IsDihedral S) : IsCyclic P ∨ IsDihedral P := by
  let e : P ≃* φ.range := MonoidHom.ofInjective hφ
  rcases hS with hc | hd
  · exact Or.inl (e.isCyclic.mpr (Subgroup.isCyclic φ.range))
  · rcases subgroup_of_dihedral hd φ.range with h | h
    · exact Or.inl (e.isCyclic.mpr h)
    · exact Or.inr (isDihedral_congr e h)

theorem cyclic_or_dihedral_of_pgroup_le {Q : Type} [Group Q] [Finite Q]
    (hQ : ∀ S : Sylow 2 Q, IsCyclic ↥S ∨ IsDihedral ↥S) (P : Subgroup Q) (hP : IsPGroup 2 ↥P) :
    IsCyclic ↥P ∨ IsDihedral ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact cyclic_or_dihedral_of_injective (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)
    (hQ S)

end Embedding

section Transport

theorem O2Of_le_self {G : Type} [Group G] (X : Subgroup G) : O2Of X ≤ X :=
  Subgroup.map_subtype_le _

theorem f_mem_O2Of {G H : Type} [Group G] [Group H] (X : Subgroup G) (E : Subgroup H)
    (f : ↥X →* H) (hrange : ∀ x, f x ∈ E) {x : ↥X} (hx : x ∈ oResidual 2 ↥X) : f x ∈ O2Of E := by
  unfold oResidual at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine mem_O2Of_of_coprime (hrange y) ?_
    have h1 : orderOf (f y) ∣ orderOf y := orderOf_map_dvd f y
    exact Nat.Coprime.coprime_dvd_left h1 hy
  | one => rw [map_one]; exact (O2Of E).one_mem
  | mul y₁ y₂ _ _ h₁ h₂ => rw [map_mul]; exact (O2Of E).mul_mem h₁ h₂
  | inv y _ h₁ => rw [map_inv]; exact (O2Of E).inv_mem h₁

theorem injective_on_pgroup {A B : Type} [Group A] [Group B] (g : A →* B)
    (hk : Odd (Nat.card g.ker)) (P : Subgroup A) (hP : IsPGroup 2 ↥P) :
    Function.Injective (g.comp P.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  have hag : (a : A) ∈ g.ker := by simpa using ha
  have h1 : orderOf (⟨(a : A), hag⟩ : ↥g.ker) ∣ Nat.card g.ker := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp hP a
  have hi' : orderOf (a : A) = 2 ^ i := by rw [Subgroup.orderOf_coe]; exact hi
  have hodd : Odd (orderOf (a : A)) := Odd.of_dvd_nat hk h1
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi'] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hi0, pow_zero] at hi'
  exact Subtype.ext (orderOf_eq_one_iff.mp hi')

theorem cyclic_or_dihedral_of_odd_ker {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (X : Subgroup G) (E : Subgroup H) (f : ↥X →* H) (hker : Odd (Nat.card f.ker))
    (hrange : ∀ x, f x ∈ E) (hE : ∀ S : Sylow 2 ↥(O2Of E), IsCyclic ↥S ∨ IsDihedral ↥S)
    (P : Sylow 2 ↥(O2Of X)) : IsCyclic ↥P ∨ IsDihedral ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥(O2Of X) →* ↥X := Subgroup.inclusion (O2Of_le_self X)
  have hπ : Function.Injective π := Subgroup.inclusion_injective _
  have hmem : ∀ x : ↥(O2Of X), f (π x) ∈ O2Of E := by
    intro x
    obtain ⟨y, hy, hyx⟩ := x.2
    have hπy : π x = y := by
      apply Subtype.ext
      exact hyx.symm
    rw [hπy]
    exact f_mem_O2Of X E f hrange hy
  let g : ↥(O2Of X) →* ↥(O2Of E) := (f.comp π).codRestrict (O2Of E) hmem
  have hgker : Odd (Nat.card g.ker) := by
    let ι : ↥g.ker →* ↥f.ker :=
      (π.comp g.ker.subtype).codRestrict f.ker fun x => by
        have h2 := congrArg Subtype.val x.2
        exact h2
    have hdvd : Nat.card g.ker ∣ Nat.card f.ker := by
      refine Subgroup.card_dvd_of_injective ι fun x y hxy => ?_
      apply Subtype.ext
      apply hπ
      exact congrArg Subtype.val hxy
    exact Odd.of_dvd_nat hker hdvd
  have hPinj := injective_on_pgroup g hgker (P : Subgroup ↥(O2Of X)) P.isPGroup'
  have hPbar : IsPGroup 2 ↥((g.comp (P : Subgroup ↥(O2Of X)).subtype).range) :=
    P.isPGroup'.of_surjective (g.comp (P : Subgroup ↥(O2Of X)).subtype).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hc := cyclic_or_dihedral_of_pgroup_le hE _ hPbar
  exact cyclic_or_dihedral_of_injective
    (g.comp (P : Subgroup ↥(O2Of X)).subtype).rangeRestrict (fun a b hab =>
      hPinj (Subtype.ext_iff.mp hab)) hc

end Transport

section Alt

variable {G : Type} [Group G] [Finite G]

theorem lemma29Alt_of_cyclic_or_dihedral {z : G} {k : Kind} (hk : IsClassicalKind k)
    {U : Subgroup G}
    (hdc : ∀ P : Sylow 2 ↥(O2Of (centralizer (U : Set G))), IsCyclic ↥P ∨ IsDihedral ↥P)
    (hz : (∀ u ∈ U, ¬ IsConj z u) ∨
      ∃ t g : G, SwapsComps z t ∧ conjugate (zpowers z ⊔ zpowers t) g = U) :
    Lemma29Alt z k U := by
  by_cases hcyc : ∃ P : Sylow 2 ↥(O2Of (centralizer (U : Set G))), IsCyclic ↥P
  · exact Or.inl (hasNormal2Compl_of_O2_cyclic _ hcyc)
  · exact Or.inr (Or.inl ⟨hk, fun P => (hdc P).resolve_left fun h => hcyc ⟨P, h⟩, hz⟩)

end Alt

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
