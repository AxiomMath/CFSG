module

import CFSG.GH74.GLS.Stage2.Bender.Thm2.Naturality
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Assembly.ComponentTypeDefs
import CFSG.GH74.GLS.Stage2.Final.Thm4.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4a

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_Fm {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((Fm X : Subgroup G) : Set G) := by
  have h : X.map (MulAut.conj g).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hm := CFSG.GH74.GLS.Stage2.Bender.Thm2.inSubgroup_map (fun K _ => fittingSubgroup K)
    (fun _ _ _ _ _ _ e => CFSG.GH74.GLS.Stage2.Bender.Thm2.fitting_map_mulEquiv e)
    (MulAut.conj g) X
  rw [h] at hm
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hm.symm

theorem mem_normalizer_Em {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((Em X : Subgroup G) : Set G) := by
  have h : X.map (MulAut.conj g).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hm := CFSG.GH74.GLS.Stage2.Bender.Thm2.inSubgroup_map (fun K _ => layer K)
    (fun _ _ _ _ _ _ e => CFSG.GH74.GLS.Stage2.Bender.Thm2.layer_map_mulEquiv e)
    (MulAut.conj g) X
  rw [h] at hm
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hm.symm

theorem mem_normalizer_Fpi (σ : Set ℕ) {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer ((Fpi σ X : Subgroup G) : Set G) := by
  have hF : (Fm X).map (MulAut.conj g).toMonoidHom = Fm X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (mem_normalizer_Fm hg)
  have hOp : ∀ q, (Op q (Fm X)).map ((MulAut.conj g : G ≃* G) : G →* G) = Op q (Fm X) := fun q => by
    have := CFSG.GH74.GLS.Stage2.Bender.Thm2.Op_map q (MulAut.conj g) (Fm X)
    rw [hF] at this
    exact this.symm
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  unfold Fpi
  simp only [Subgroup.map_iSup, hOp]

end Normalizer

section Fitting

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_Fs_le (X : Subgroup G) :
    X ⊓ centralizer ((Fs X : Subgroup G) : Set G) ≤ Fs X := by
  rintro y ⟨hyX, hyc⟩
  have hcent : (⟨y, hyX⟩ : ↥X) ∈ centralizer (generalizedFitting ↥X : Set ↥X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : (w : G) ∈ Fs X := ⟨w, hw, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyc _ hw')
  exact ⟨_, centralizer_generalizedFitting_le ↥X hcent, rfl⟩

end Fitting

section Commutator

variable {G : Type} [Group G]

theorem zpow_involution_cases {z : G} (hz2 : z * z = 1) (n : ℤ) : z ^ n = 1 ∨ z ^ n = z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  induction n using Int.induction_on with
  | zero => exact Or.inl (zpow_zero z)
  | succ n ih =>
    rw [zpow_add_one]
    rcases ih with h | h
    · rw [h, one_mul]
      exact Or.inr rfl
    · rw [h, hz2]
      exact Or.inl rfl
  | pred n ih =>
    rw [zpow_sub_one, hzi]
    rcases ih with h | h
    · rw [h, one_mul]
      exact Or.inr rfl
    · rw [h, hz2]
      exact Or.inl rfl

theorem commutator_zpowers_le_of_forall {z : G} (hz2 : z * z = 1) {X T : Subgroup G}
    (h : ∀ x ∈ X, x * z * x⁻¹ * z⁻¹ ∈ T) : ⁅X, zpowers z⁆ ≤ T := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rcases zpow_involution_cases hz2 n with h1 | h1
  · rw [h1, commutatorElement_one_right]
    exact T.one_mem
  · rw [h1]
    exact h x hx

@[expose] def commPre (z : G) (X N : Subgroup G) (hN : X ≤ normalizer (N : Set G)) :
    Subgroup G where
  carrier := {x | x ∈ X ∧ x * z * x⁻¹ * z⁻¹ ∈ N}
  one_mem' := ⟨X.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haX, haN⟩ ⟨hbX, hbN⟩
    refine ⟨X.mul_mem haX hbX, ?_⟩
    have e : a * b * z * (a * b)⁻¹ * z⁻¹ =
        (a * (b * z * b⁻¹ * z⁻¹) * a⁻¹) * (a * z * a⁻¹ * z⁻¹) := by group
    rw [e]
    exact N.mul_mem ((mem_normalizer_iff.mp (hN haX) _).mp hbN) haN
  inv_mem' := by
    rintro a ⟨haX, haN⟩
    refine ⟨X.inv_mem haX, ?_⟩
    have e : a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ = a⁻¹ * (a * z * a⁻¹ * z⁻¹)⁻¹ * a := by group
    rw [e]
    have h1 : (a * z * a⁻¹ * z⁻¹)⁻¹ ∈ N := N.inv_mem haN
    have := (mem_normalizer_iff.mp (hN (X.inv_mem haX)) _).mp h1
    simpa [mul_assoc] using this

theorem Em_eq_bot_of_no_comp {X : Subgroup G} (h : ∀ J : Subgroup G, ¬ IsCompIn X J) :
    Em X = ⊥ := by
  rw [Em_eq, eq_bot_iff, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  have hsub : (K.map X.subtype).subgroupOf X = K :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective K
  exact absurd ⟨Subgroup.map_subtype_le K, by rw [hsub]; exact hK⟩ (h _)

end Commutator

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4a
