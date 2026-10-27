module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Pair
import CFSG.ClassicalInvolution.GenericLocal.SL2Automorphisms
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local
open scoped MatrixGroups

theorem l31c_not_index_two {Y : Type} [Group Y] [Group.IsPerfect Y] {H : Subgroup Y}
    (h : H.index = 2) : False := by
  have hn : H.Normal := Subgroup.normal_of_index_eq_two h
  have hcard : Nat.card (Y ⧸ H) = 2 := h
  have hfin : Finite (Y ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hp : IsPGroup 2 (Y ⧸ H) := IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have hnt : Nontrivial (Y ⧸ H) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  have := hp.isNilpotent
  exact Group.IsPerfect.not_isNilpotent (Y ⧸ H) this

theorem l31c_perfect_normalizes {X : Type} [Group X] {A B : Subgroup X} (hne : A ≠ B)
    (hA : IsComponent A) (hB : IsComponent B)
    (hAB : ∀ K : Subgroup X, IsComponent K → K = A ∨ K = B) {P : Subgroup X}
    (hP : Group.IsPerfect ↥P) :
    P ≤ normalizer (A : Set X) ∧ P ≤ normalizer (B : Set X) := by
  have hidx := L29Pair.index_dvd_two_of_components hne hA hB hAB P
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
  · have htop := Subgroup.index_eq_one.mp h
    have key : ∀ p : ↥P, (p : X) ∈ normalizer (A : Set X) ∧ (p : X) ∈ normalizer (B : Set X) := by
      intro p
      have : p ∈ (P ⊓ normalizer (A : Set X) ⊓ normalizer (B : Set X)).subgroupOf P := by
        rw [htop]
        exact Subgroup.mem_top _
      exact ⟨(Subgroup.mem_subgroupOf.mp this).1.2, (Subgroup.mem_subgroupOf.mp this).2⟩
    exact ⟨fun p hp => (key ⟨p, hp⟩).1, fun p hp => (key ⟨p, hp⟩).2⟩
  · exact (l31c_not_index_two (Y := ↥P) h).elim

theorem l31c_perfect_le_sup {X : Type} [Group X] {L₁ L₂ : Subgroup X}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hZ : ∀ c : X, (∀ a ∈ L₁, c * a = a * c) → (∀ b ∈ L₂, c * b = b * c) → c ∈ L₁ ⊓ L₂)
    {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    (h₁ : 4 ≤ Nat.card F₁) (h₂ : 4 ≤ Nat.card F₂)
    (e₁ : ↥L₁ ≃* SL(2, F₁)) (e₂ : ↥L₂ ≃* SL(2, F₂))
    {P : Subgroup X} (hP : Group.IsPerfect ↥P) (hP₁ : P ≤ normalizer (L₁ : Set X))
    (hP₂ : P ≤ normalizer (L₂ : Set X)) : P ≤ L₁ ⊔ L₂ := by
  intro p hp
  obtain ⟨⟨A₁, hA₁⟩, ha₁⟩ := CFSG.ClassicalInvolution.perfect_action_inner_of_equiv_sl2 h₁ e₁
    (Stage1.Main.actOnKHom L₁ P hP₁) ⟨p, hp⟩
  obtain ⟨⟨A₂, hA₂⟩, ha₂⟩ := CFSG.ClassicalInvolution.perfect_action_inner_of_equiv_sl2 h₂ e₂
    (Stage1.Main.actOnKHom L₂ P hP₂) ⟨p, hp⟩
  have hc₁ : ∀ x ∈ L₁, p * x * p⁻¹ = A₁ * x * A₁⁻¹ := by
    intro x hx
    have := congrArg (fun φ : MulAut ↥L₁ => ((φ ⟨x, hx⟩ : ↥L₁) : X)) ha₁
    simpa [Stage1.Main.actOnKHom_apply, MulAut.conj_apply] using this
  have hc₂ : ∀ y ∈ L₂, p * y * p⁻¹ = A₂ * y * A₂⁻¹ := by
    intro y hy
    have := congrArg (fun φ : MulAut ↥L₂ => ((φ ⟨y, hy⟩ : ↥L₂) : X)) ha₂
    simpa [Stage1.Main.actOnKHom_apply, MulAut.conj_apply] using this
  have hcL₁ : ∀ x ∈ L₁, (A₁ * A₂)⁻¹ * p * x = x * ((A₁ * A₂)⁻¹ * p) := by
    intro x hx
    have h2 := hcomm x hx A₂ hA₂
    have h3 : A₂ * x * A₂⁻¹ = x := by rw [← h2]; group
    have hgx : p * x * p⁻¹ = (A₁ * A₂) * x * (A₁ * A₂)⁻¹ := by
      calc p * x * p⁻¹ = A₁ * x * A₁⁻¹ := hc₁ x hx
        _ = A₁ * (A₂ * x * A₂⁻¹) * A₁⁻¹ := by rw [h3]
        _ = (A₁ * A₂) * x * (A₁ * A₂)⁻¹ := by group
    calc (A₁ * A₂)⁻¹ * p * x = (A₁ * A₂)⁻¹ * (p * x * p⁻¹) * p := by group
      _ = (A₁ * A₂)⁻¹ * ((A₁ * A₂) * x * (A₁ * A₂)⁻¹) * p := by rw [hgx]
      _ = x * ((A₁ * A₂)⁻¹ * p) := by group
  have hcL₂ : ∀ y ∈ L₂, (A₁ * A₂)⁻¹ * p * y = y * ((A₁ * A₂)⁻¹ * p) := by
    intro y hy
    have hw : A₂ * y * A₂⁻¹ ∈ L₂ := L₂.mul_mem (L₂.mul_mem hA₂ hy) (L₂.inv_mem hA₂)
    have h3 : A₁ * (A₂ * y * A₂⁻¹) * A₁⁻¹ = A₂ * y * A₂⁻¹ := by
      rw [hcomm A₁ hA₁ _ hw]; group
    have hgy : p * y * p⁻¹ = (A₁ * A₂) * y * (A₁ * A₂)⁻¹ := by
      calc p * y * p⁻¹ = A₂ * y * A₂⁻¹ := hc₂ y hy
        _ = A₁ * (A₂ * y * A₂⁻¹) * A₁⁻¹ := h3.symm
        _ = (A₁ * A₂) * y * (A₁ * A₂)⁻¹ := by group
    calc (A₁ * A₂)⁻¹ * p * y = (A₁ * A₂)⁻¹ * (p * y * p⁻¹) * p := by group
      _ = (A₁ * A₂)⁻¹ * ((A₁ * A₂) * y * (A₁ * A₂)⁻¹) * p := by rw [hgy]
      _ = y * ((A₁ * A₂)⁻¹ * p) := by group
  have hI := hZ _ hcL₁ hcL₂
  have hpe : p = A₁ * A₂ * ((A₁ * A₂)⁻¹ * p) := by group
  rw [hpe]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hA₁)
    (Subgroup.mem_sup_right hA₂)) (Subgroup.mem_sup_left hI.1)

theorem l31c_exists_perfect {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hJ : ¬ Group.IsSolvable ↥J) :
    ∃ P : Subgroup G, P ≤ J ∧ Group.IsPerfect ↥P ∧ ¬ Group.IsSolvable ↥P := by
  obtain ⟨-, -, hperf, -, -, hbot⟩ := perfect_residual_characterization (G := ↥J)
  have hne : perfectResidual ↥J ≠ ⊥ := fun h => hJ (hbot.mp h)
  refine ⟨(perfectResidual ↥J).map J.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have := hperf
    exact Group.IsPerfect.map J.subtype
  · have hP : (perfectResidual ↥J).map J.subtype ≠ ⊥ := fun h =>
      hne ((Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp h)
    have hnt : Nontrivial ↥((perfectResidual ↥J).map J.subtype) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hP
    have := hperf
    have : Group.IsPerfect ↥((perfectResidual ↥J).map J.subtype) := Group.IsPerfect.map J.subtype
    exact Group.IsPerfect.not_isSolvable _

theorem l31c_zpowers_two {G : Type} [Group G] {z : G} (hzz : z * z = 1) {w : G}
    (hw : w ∈ zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
  rw [zpow_eq_zpow_emod m hz2]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem l31c_isDihedral_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsDihedral B) : IsDihedral A := by
  obtain ⟨m, k, hm, hk, ⟨e'⟩⟩ := h
  exact ⟨m, k, hm, hk, ⟨e.trans e'⟩⟩

theorem l31c_mem_conjMap_iff {G : Type} [Group G] (c : G) (K : Subgroup G) (y : G) :
    y ∈ K.map (MulAut.conj c⁻¹).toMonoidHom ↔ ∃ x ∈ K, y = c⁻¹ * x * c := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
