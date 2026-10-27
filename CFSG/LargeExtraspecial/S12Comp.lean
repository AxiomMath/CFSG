module

public import CFSG.LargeExtraspecial.OrthoF2Pairs
public import CFSG.LargeExtraspecial.S12Fuse

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

@[expose] def RootInvolutionComponentsInput.{u} : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V), q.polarBilin.Nondegenerate →
    ∀ H : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q), S12NoNormalTwo H →
    ∀ D : Set (TauCeti.QuadraticMap.orthogonalGroup q),
      D = {x | x ∈ H ∧ IsTypeA q (x : V ≃ₗ[ZMod 2] V) 2} →
      ∀ d ∈ D, ∀ e, Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) d e →
        ∃ x ∈ closure {f | Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) d f},
          e = x * d * x⁻¹

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def Dbar12 : Set S.O :=
  {x | x ∈ S.Mbar ∧ IsTypeA S.q (x : S.Qt ≃ₗ[ZMod 2] S.Qt) 2}

@[expose] def ncRel12 (x y : S.O) : Prop := x ∈ S.Dbar12 ∧ y ∈ S.Dbar12 ∧ x * y ≠ y * x

@[expose] def comp12 (τ : S.O) : Set S.O := {e | Relation.ReflTransGen S.ncRel12 τ e}

variable {S}

theorem Ebar12_subset_Dbar12 {g : G} : S.Ebar12 g ⊆ S.Dbar12 := fun _ h => ⟨h.1, h.2.1⟩

theorem ncRel12_symm {x y : S.O} (h : S.ncRel12 x y) : S.ncRel12 y x :=
  ⟨h.2.1, h.1, fun e => h.2.2 e.symm⟩

theorem mem_comp12_self (τ : S.O) : τ ∈ S.comp12 τ := Relation.ReflTransGen.refl

theorem comp12_symm {τ e : S.O} (h : e ∈ S.comp12 τ) : τ ∈ S.comp12 e := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hr ih => exact Relation.ReflTransGen.head (ncRel12_symm hr) ih

theorem comp12_trans {τ e f : S.O} (h₁ : e ∈ S.comp12 τ) (h₂ : f ∈ S.comp12 e) :
    f ∈ S.comp12 τ :=
  Relation.ReflTransGen.trans h₁ h₂

theorem mem_Dbar12_of_mem_comp12 {τ e : S.O} (hτ : τ ∈ S.Dbar12) (h : e ∈ S.comp12 τ) :
    e ∈ S.Dbar12 := by
  induction h with
  | refl => exact hτ
  | tail _ hr _ => exact hr.2.1

theorem commute_of_not_mem_comp12 {τ e f : S.O} (he : e ∈ S.comp12 τ) (hτ : τ ∈ S.Dbar12)
    (hf : f ∈ S.Dbar12) (hf' : f ∉ S.comp12 τ) : e * f = f * e := by
  by_contra hc
  exact hf' (Relation.ReflTransGen.tail he ⟨mem_Dbar12_of_mem_comp12 hτ he, hf, hc⟩)

theorem conj_mem_Dbar12 {m x : S.O} (hm : m ∈ S.Mbar) (hx : x ∈ S.Dbar12) :
    m * x * m⁻¹ ∈ S.Dbar12 := by
  refine ⟨S.Mbar.mul_mem (S.Mbar.mul_mem hm hx.1) (S.Mbar.inv_mem hm), ?_⟩
  rw [S.s12_coe_conj]
  exact s12_isTypeA_conj hx.2 m.2

theorem conj_mem_comp12 {m τ e : S.O} (hm : m ∈ S.Mbar) (h : e ∈ S.comp12 τ) :
    m * e * m⁻¹ ∈ S.comp12 (m * τ * m⁻¹) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hr ih =>
    refine Relation.ReflTransGen.tail ih ⟨conj_mem_Dbar12 hm hr.1, conj_mem_Dbar12 hm hr.2.1,
      fun e => hr.2.2 ?_⟩
    have := congrArg (fun y => m⁻¹ * y * m) e
    simpa [mul_assoc] using this

theorem orderOf_eq_two_of_isTypeA' {x : S.O} (hx : IsTypeA S.q (x : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    orderOf x = 2 := by
  refine orderOf_eq_prime ?_ fun e => hx.2.1 (by rw [e]; rfl)
  rw [pow_two]
  exact Subtype.ext hx.2.2.1

theorem Dbar12_rootInvolution :
    (∀ d ∈ S.Dbar12, ∀ e ∈ S.Dbar12, orderOf (d * e) ≤ 4) ∧
      (∀ d ∈ S.Dbar12, ∀ e ∈ S.Dbar12, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ S.Dbar12) := by
  constructor
  · intro d hd e he
    have h := (aschbacher_3_7 S.q_nondegenerate hd.2 he.2).1
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    omega
  · intro d hd e he h4
    have h := (aschbacher_3_7 S.q_nondegenerate hd.2 he.2).2
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
    refine ⟨S.Mbar.pow_mem (S.Mbar.mul_mem hd.1 he.1) 2, ?_⟩
    have := h h4
    simpa using this

theorem comp12_conj_of_mem (hRI : RootInvolutionComponentsInput.{u}) {g : G} {τ : S.O}
    (hτ : τ ∈ S.Ebar12 g) : ∃ X : Subgroup S.O, X = closure (S.comp12 τ) ∧
      ∀ e ∈ S.comp12 τ, ∃ x ∈ X, e = x * τ * x⁻¹ := by
  refine ⟨_, rfl, fun e he => ?_⟩
  exact hRI S.Qt S.q S.q_nondegenerate S.Mbar S.s12_noNormalTwo_Mbar S.Dbar12 rfl τ
    (Ebar12_subset_Dbar12 hτ) e he

theorem comp12_subset_Dbar12 {τ : S.O} (hτ : τ ∈ S.Dbar12) : S.comp12 τ ⊆ S.Dbar12 :=
  fun _ h => mem_Dbar12_of_mem_comp12 hτ h

theorem comp12_subset_Ebar12 (hRI : RootInvolutionComponentsInput.{u}) {g : G} {τ : S.O}
    (hτ : τ ∈ S.Ebar12 g) : S.comp12 τ ⊆ S.Ebar12 g := by
  intro e he
  obtain ⟨X, rfl, hX⟩ := comp12_conj_of_mem hRI hτ
  obtain ⟨x, hx, rfl⟩ := hX e he
  have hxM : x ∈ S.Mbar := by
    refine (closure_le _).mpr (fun y hy => ?_) hx
    exact (comp12_subset_Dbar12 (Ebar12_subset_Dbar12 hτ) hy).1
  exact conj_mem_Ebar12 hxM hτ

end Setting

end CFSG.LargeExtraspecial
