module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp31
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem memCenter_of_cover {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (π : A →* B) (hker : π.ker ≤ center A) {y : A} (hy : π y ∈ center B) : y ∈ center A := by
  have hc : ∀ g : A, y * g * y⁻¹ * g⁻¹ ∈ center A := fun g => hker (by
    rw [MonoidHom.mem_ker]
    have h1 := mem_center_iff.1 hy (π g)
    calc π (y * g * y⁻¹ * g⁻¹) = (π y * π g) * (π y)⁻¹ * (π g)⁻¹ := by simp only [map_mul, map_inv]
      _ = (π g * π y) * (π y)⁻¹ * (π g)⁻¹ := by rw [h1]
      _ = 1 := by group)
  let δ : A →* center A :=
    { toFun := fun g => ⟨y * g * y⁻¹ * g⁻¹, hc g⟩
      map_one' := by
        ext
        simp
      map_mul' := fun g h => by
        ext
        have h1 := mem_center_iff.1 (hc h) g
        calc y * (g * h) * y⁻¹ * (g * h)⁻¹
              = (y * g * y⁻¹ * g⁻¹) * (g * (y * h * y⁻¹ * h⁻¹) * g⁻¹) := by
              group
          _ = (y * g * y⁻¹ * g⁻¹) * (y * h * y⁻¹ * h⁻¹) := by rw [h1]; group }
  have hδ : ∀ x ∈ commutator A, δ x = 1 := by
    intro x hx
    rw [_root_.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, -, b, -, rfl⟩ := hx
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subtype.ext (mem_center_iff.1 (δ b).2 (δ a)))
    | one => exact map_one δ
    | mul a b _ _ ha hb => rw [map_mul, ha, hb, one_mul]
    | inv a _ ha => rw [map_inv, ha, inv_one]
  rw [mem_center_iff]
  intro g
  have h1 := congrArg Subtype.val (hδ g Group.IsPerfect.mem_commutator)
  have h2 : y * g * y⁻¹ * g⁻¹ = 1 := h1
  calc g * y = (y * g * y⁻¹ * g⁻¹)⁻¹ * (y * g) := by group
    _ = y * g := by rw [h2]; group

theorem cqEquiv_of_cover {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (π : A →* B) (hπ : Function.Surjective π) (hker : π.ker ≤ center A) :
    Nonempty ((A ⧸ center A) ≃* (B ⧸ center B)) := by
  have hcomp : Function.Surjective ((QuotientGroup.mk' (center B)).comp π) :=
    (QuotientGroup.mk'_surjective _).comp hπ
  have hkerc : ((QuotientGroup.mk' (center B)).comp π).ker = center A := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · exact memCenter_of_cover π hker
    · intro hx
      rw [mem_center_iff]
      intro k
      obtain ⟨y, rfl⟩ := hπ k
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hcomp)⟩

theorem isQuasisimple_of_cover {A B : Type*} [Group A] [Group B] (hA : CFSG.IsQuasisimple A)
    (π : A →* B) (hπ : Function.Surjective π) (hker : π.ker ≤ center A) :
    CFSG.IsQuasisimple B := by
  have : Group.IsPerfect A := hA.1
  obtain ⟨e⟩ := cqEquiv_of_cover π hπ hker
  refine ⟨Group.IsPerfect.ofSurjective (f := π) hπ, ?_, ?_⟩
  · have := hA.2.1
    exact MulEquiv.isSimpleGroup e.symm
  · obtain ⟨a, b, hab⟩ := hA.2.2
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa [map_mul] using h))⟩

variable {H : Type} [Group H] [Finite H]

theorem oddCore_le_center {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) : CFSG.oddCore X ≤ center X := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (inferInstance : (CFSG.oddCore X).Normal)
    with htop | hle
  · exfalso
    have hodd : Odd (Nat.card X) := by
      have h1 := odd_card_oddCore' X
      rw [htop, Subgroup.card_top] at h1
      exact h1
    have hsolv := CFSG.Milestones.odd_order_solvable hodd
    have : Group.IsPerfect X := hq.1
    have hsub : Subsingleton X := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable X hsolv
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [Subsingleton.elim a' b'])
  · exact hle

theorem klike_of_quot {IsK : GroupClass} {X : Subgroup H} (hq : CFSG.IsQuasisimple ↥X)
    (hX : IsK (↥X ⧸ CFSG.oddCore ↥X)) : KLike IsK X :=
  ⟨↥X ⧸ CFSG.oddCore ↥X, inferInstance, QuotientGroup.mk' (CFSG.oddCore ↥X),
    QuotientGroup.mk'_surjective _, by
      rw [QuotientGroup.ker_mk']
      exact oddCore_le_center hq, hX⟩

end CFSG.EvenSporadicStandard.Induction.Hyp
