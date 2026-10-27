module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp31
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Order
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

theorem mem_center_of_central_cover {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
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

theorem cqEquiv_of_central_cover {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (π : A →* B) (hπ : Function.Surjective π) (hker : π.ker ≤ center A) :
    Nonempty ((A ⧸ center A) ≃* (B ⧸ center B)) := by
  have hcomp : Function.Surjective ((QuotientGroup.mk' (center B)).comp π) :=
    (QuotientGroup.mk'_surjective _).comp hπ
  have hkerc : ((QuotientGroup.mk' (center B)).comp π).ker = center A := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · exact mem_center_of_central_cover π hker
    · intro hx
      rw [mem_center_iff]
      intro k
      obtain ⟨y, rfl⟩ := hπ k
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hcomp)⟩

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem cqOrd_eq_of_central_cover {M K₁ : Subgroup H} [Group.IsPerfect ↥M] (π : ↥M →* ↥K₁)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center ↥M) : cqOrd M = cqOrd K₁ := by
  obtain ⟨e⟩ := cqEquiv_of_central_cover π hπ hker
  exact Nat.card_congr e.toEquiv

theorem oddCore_le_center_of_isQuasisimple {X : Type} [Group X] [Finite X]
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

theorem klike_of_isK_quot {IsK : GroupClass} {X : Subgroup H} (hq : CFSG.IsQuasisimple ↥X)
    (hX : IsK (↥X ⧸ CFSG.oddCore ↥X)) : KLike IsK X :=
  ⟨↥X ⧸ CFSG.oddCore ↥X, inferInstance, QuotientGroup.mk' (CFSG.oddCore ↥X),
    QuotientGroup.mk'_surjective _, by
      rw [QuotientGroup.ker_mk']
      exact oddCore_le_center_of_isQuasisimple hq, hX⟩

theorem not_exc_of_central_cover {IsK IsL : GroupClass} (hrow : Hyp31Row IsK IsL)
    {K₁ M : Subgroup H} (hK₁q : CFSG.IsQuasisimple ↥K₁) (hMq : CFSG.IsQuasisimple ↥M)
    (hK₁ : IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) (π : ↥M →* ↥K₁) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center ↥M) :
    ¬ Nonempty ((↥M ⧸ center ↥M) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (↥M ⧸ center ↥M) .PSL 2 p f := by
  have : Group.IsPerfect ↥M := hMq.1
  have : Group.IsPerfect ↥K₁ := hK₁q.1
  obtain ⟨e₁⟩ := cqEquiv_of_central_cover π hπ hker
  obtain ⟨e₂⟩ := cqEquiv_of_central_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact oddCore_le_center_of_isQuasisimple hK₁q)
  have e := e₁.trans e₂
  obtain ⟨hA, hL⟩ := hrow.K_not_exc _ hK₁
  refine ⟨fun ⟨f⟩ => hA ⟨e.symm.trans f⟩, fun ⟨p, f, hp, hp2, hmodel⟩ => hL ⟨p, f, hp, hp2, ?_⟩⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel

end CFSG.EvenSporadicStandard.Induction
