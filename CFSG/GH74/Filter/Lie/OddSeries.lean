module

public import CFSG.GH74.Filter.Lie.Q8Cube
public import CFSG.GH74.Filter.Statements
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.LocalAnalysis.SectionRank.Exceptional

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.SectionRank

@[expose] def stronglyOrthB (τ : Tag) (β γ : Fin τ.rank → ℤ) : Bool :=
  RootOps.isRootB τ β && RootOps.isRootB τ γ && decide (iform β γ = 0) &&
    !RootOps.isRootB τ (β + γ) && !RootOps.isRootB τ (β - γ)

theorem stronglyOrthB_spec
    {τ : Tag} {β γ : Fin τ.rank → ℤ} (h : stronglyOrthB τ β γ = true) :
    IsRoot τ β ∧ IsRoot τ γ ∧ iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ) := by
  simp only [stronglyOrthB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨RootOps.isRootB_iff.1 h1, RootOps.isRootB_iff.1 h2, h3, fun hr => ?_, fun hr => ?_⟩
  · rw [RootOps.isRootB_iff.2 hr] at h4
    exact Bool.noConfusion h4
  · rw [RootOps.isRootB_iff.2 hr] at h5
    exact Bool.noConfusion h5

@[expose] noncomputable def q8Root
    (τ : Tag) {K : Type} [Field K] {a b : K}
    (h : a ^ 2 + b ^ 2 = -1) (β : Fin τ.rank → ℤ) : QuaternionGroup 2 →* adjointGroup τ K :=
  ((rootSL2 τ K β).comp (quatHom h)).codRestrict (adjointGroup τ K) fun g => by
    obtain ⟨-, -, -, -, hρ, -⟩ := exceptional_Lang_root_rank_one_data τ K β
    exact hρ _

theorem q8Root_coe
    (τ : Tag) {K : Type} [Field K] {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (β : Fin τ.rank → ℤ) (g : QuaternionGroup 2) :
    ((q8Root τ h β g : adjointGroup τ K) : ModGL τ K) = rootSL2 τ K β (quatHom h g) := rfl

theorem q8Root_injective
    (τ : Tag) {K : Type} [Field K] {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (hK : ringChar K ≠ 2) (β : Fin τ.rank → ℤ) : Function.Injective (q8Root τ h β) := by
  obtain ⟨-, -, -, -, -, -, -, hinj, -⟩ := exceptional_Lang_root_rank_one_data τ K β
  intro x y hxy
  exact quatHom_injective hK h ((hinj hK).1 (congrArg Subtype.val hxy))

theorem q8Root_commute
    (τ : Tag) {K : Type} [Field K] {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    {β γ : Fin τ.rank → ℤ} (hs : stronglyOrthB τ β γ = true) (x y : QuaternionGroup 2) :
    Commute (q8Root τ h β x) (q8Root τ h γ y) := by
  obtain ⟨hβ, hγ, h0, hp, hm⟩ := stronglyOrthB_spec hs
  refine Subtype.ext ?_
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K hβ hγ h0 hp hm _
    ⟨quatHom h x, rfl⟩ _ ⟨quatHom h y, rfl⟩

theorem not_gen4_adjointQuotient_of_stronglyOrth
    (τ : Tag) (β : Fin 3 → Fin τ.rank → ℤ)
    (hs : ∀ i j, i ≠ j → stronglyOrthB τ (β i) (β j) = true) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) : ¬ Gen4 (AdjointQuotient τ K) := by
  obtain ⟨⟨a, b, hab⟩, -⟩ := odd_field_two_dimensional_quaternion_matrices (K := K) hK
  exact not_gen4_quotient_of_Q8_cube (Subgroup.center (adjointGroup τ K)) le_rfl
    (fun i => q8Root τ hab (β i)) (fun i => q8Root_injective τ hab hK (β i))
    (fun i j hij x y => q8Root_commute τ hab (hs i j hij) x y)

theorem not_gen4_of_untwistedModel_odd
    {G : Type} [Group G] [Finite G] {τ : Tag} {p f : ℕ}
    (hp2 : p ≠ 2) (β : Fin 3 → Fin τ.rank → ℤ)
    (hs : ∀ i j, i ≠ j → stronglyOrthB τ (β i) (β j) = true) (hp : p.Prime)
    (h : UntwistedChevalleyModel G τ (p ^ f)) : ¬ Gen4 G := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_natCard_eq_pow hK
  have hring : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  exact not_gen4_of_mulEquiv e.symm (not_gen4_adjointQuotient_of_stronglyOrth τ β hs hring)

@[expose] def stronglyOrthF4 : Fin 3 → Fin Tag.F4.rank → ℤ :=
  ![(![0, 1, 0, 0] : Fin 4 → ℤ), (![0, 1, 2, 0] : Fin 4 → ℤ), (![0, 1, 2, 2] : Fin 4 → ℤ)]

@[expose] def stronglyOrthE6 : Fin 3 → Fin Tag.E6.rank → ℤ :=
  ![(![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ),
    (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ)]

@[expose] def stronglyOrthE7 : Fin 3 → Fin Tag.E7.rank → ℤ :=
  ![(Pi.single (6 : Fin 7) 1 : Fin 7 → ℤ), (Pi.single (4 : Fin 7) 1 : Fin 7 → ℤ),
    (Pi.single (2 : Fin 7) 1 : Fin 7 → ℤ)]

@[expose] def stronglyOrthE8 : Fin 3 → Fin Tag.E8.rank → ℤ :=
  ![(Pi.single (7 : Fin 8) 1 : Fin 8 → ℤ), (Pi.single (5 : Fin 8) 1 : Fin 8 → ℤ),
    (Pi.single (3 : Fin 8) 1 : Fin 8 → ℤ)]

theorem stronglyOrthF4_check : ∀ i j, i ≠ j → stronglyOrthB .F4 (stronglyOrthF4 i)
    (stronglyOrthF4 j) = true := by decide +kernel

theorem stronglyOrthE6_check : ∀ i j, i ≠ j → stronglyOrthB .E6 (stronglyOrthE6 i)
    (stronglyOrthE6 j) = true := by decide +kernel

theorem stronglyOrthE7_check : ∀ i j, i ≠ j → stronglyOrthB .E7 (stronglyOrthE7 i)
    (stronglyOrthE7 j) = true := by decide +kernel

theorem stronglyOrthE8_check : ∀ i j, i ≠ j → stronglyOrthB .E8 (stronglyOrthE8 i)
    (stronglyOrthE8 j) = true := by decide +kernel

end CFSG.GH74.Filter.Lie

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.SectionRank

theorem t_F4_odd :
    S_F4_odd := fun _ _ _ _ _ hp2 h =>
  not_gen4_of_untwistedModel_odd hp2 stronglyOrthF4 stronglyOrthF4_check h.1.1 h.2

theorem t_E6_odd :
    S_E6_odd := fun _ _ _ _ _ hp2 h =>
  not_gen4_of_untwistedModel_odd hp2 stronglyOrthE6 stronglyOrthE6_check h.1.1 h.2

theorem t_E7_odd :
    S_E7_odd := fun _ _ _ _ _ hp2 h =>
  not_gen4_of_untwistedModel_odd hp2 stronglyOrthE7 stronglyOrthE7_check h.1.1 h.2

theorem t_E8_odd :
    S_E8_odd := fun _ _ _ _ _ hp2 h =>
  not_gen4_of_untwistedModel_odd hp2 stronglyOrthE8 stronglyOrthE8_check h.1.1 h.2

end CFSG.GH74.Filter
