module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsComp

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open
open scoped commutatorElement

section Comp

variable {G : Type*} [Group G]

theorem le_or_commutator_eq_bot_of_isSubnormal_of_normal {C E A N : Subgroup G}
    (hA : CFSG.Open.IsQuasisimple A) (hAE : A ≤ E) (hAn : ∀ e ∈ E, ∀ a ∈ A, e * a * e⁻¹ ∈ A)
    (hEC : E ≤ C) (hEn : ∀ c ∈ C, ∀ e ∈ E, c * e * c⁻¹ ∈ E) (hN : IsSubnormal N C) :
    A ≤ N ∨ ⁅A, N⁆ = ⊥ := by
  induction hN with
  | refl => exact Or.inl (hAE.trans hEC)
  | @step H M K' hHM hHn hM ih =>
    rcases ih hEC hEn with hAM | hAM
    · have hMn : M ≤ Subgroup.normalizer (H : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHn
      have hMC : M ≤ K' := CFSG.ClassicalInvolution.isSubnormal_le hM
      have hT : H ⊓ E ≤ Subgroup.normalizer (A : Set G) := fun x hx =>
        le_normalizer_of_forall_conj_mem hAn hx.2
      rcases le_or_commutator_eq_bot_of_normalizes hA hT inf_le_left (hAM.trans hMn) with
        hAH | hAT
      · exact Or.inl hAH
      · right
        have hAH : ⁅A, H⁆ ≤ H :=
          Subgroup.le_normalizer_iff_commutator_le_right.mp (hAM.trans hMn)
        have hAHE : ⁅A, H⁆ ≤ E := by
          rw [Subgroup.commutator_le]
          intro a ha h hh
          have : ⁅a, h⁆ = a * (h * a⁻¹ * h⁻¹) := by
            rw [commutatorElement_def]
            group
          rw [this]
          exact E.mul_mem (hAE ha) (hEn h (hMC (hHM hh)) a⁻¹ (E.inv_mem (hAE ha)))
        have hTC : H ⊓ E ≤ Subgroup.centralizer (A : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (by rw [Subgroup.commutator_comm]; exact hAT)
        have hDC : ⁅A, H⁆ ≤ Subgroup.centralizer (A : Set G) :=
          fun d hd => hTC ⟨hAH hd, hAHE hd⟩
        let : Group.IsPerfect A := ⟨hA.1⟩
        exact CFSG.ComponentClassification.Quasisimple.perfect_double_commutator A H
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDC)
    · exact Or.inr (eq_bot_iff.mpr (hAM ▸ Subgroup.commutator_mono le_rfl hHM))

theorem commute_of_isSubnormal_of_isSolvable_of_normal {C E A N : Subgroup G}
    (hA : CFSG.Open.IsQuasisimple A) (hAE : A ≤ E) (hAn : ∀ e ∈ E, ∀ a ∈ A, e * a * e⁻¹ ∈ A)
    (hEC : E ≤ C) (hEn : ∀ c ∈ C, ∀ e ∈ E, c * e * c⁻¹ ∈ E) (hN : IsSubnormal N C)
    (hs : Group.IsSolvable N) : ∀ n ∈ N, ∀ a ∈ A, n * a = a * n := by
  rcases le_or_commutator_eq_bot_of_isSubnormal_of_normal hA hAE hAn hEC hEn hN with h | h
  · exfalso
    have hAs : Group.IsSolvable ↥A :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h)
        (Subgroup.inclusion_injective h)
    exact false_of_isQuasisimple_of_isSolvable hA hAs
  · intro n hn a ha
    have hle : A ≤ Subgroup.centralizer (N : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact Subgroup.mem_centralizer_iff.mp (hle ha) n hn

end Comp

section OddGenerated

variable {G H : Type*} [Group G] [Group H]

theorem isOddGenerated_map {N : Subgroup G} (f : G →* H) (h : IsOddGenerated N) :
    IsOddGenerated (N.map f) := by
  refine (Subgroup.map_mono h).trans ?_
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxN, hxo⟩, rfl⟩
  exact ⟨Subgroup.mem_map_of_mem f hxN, hxo.of_dvd_nat (orderOf_map_dvd f x)⟩

theorem isOddGenerated_subgroupOf {N C : Subgroup G} (hNC : N ≤ C) (h : IsOddGenerated N) :
    IsOddGenerated (N.subgroupOf C) := by
  rw [IsOddGenerated, ← Subgroup.map_le_map_iff_of_injective C.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hNC, MonoidHom.map_closure]
  refine h.trans (Subgroup.closure_mono ?_)
  intro x ⟨hxN, hxo⟩
  refine ⟨⟨x, hNC hxN⟩, ⟨?_, ?_⟩, rfl⟩
  · exact Subgroup.mem_subgroupOf.mpr hxN
  · rwa [Subgroup.orderOf_mk]

end OddGenerated

end CFSG.ClassicalInvolution.Q3
