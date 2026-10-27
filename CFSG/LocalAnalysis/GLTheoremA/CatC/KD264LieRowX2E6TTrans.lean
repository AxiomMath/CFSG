module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TPlan
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6Rank0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
open scoped Matrix

section Roots

theorem cartanE6_symm (i j : Fin 6) : cartanE6 i j = cartanE6 j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem rootRefl_apply_eq (i : E6Idx) (α : E6Idx → ℤ) (j : E6Idx) :
    rootRefl i α j = reflect Tag.E6 i α j := by
  have hc : ∀ k : E6Idx, Tag.E6.cartan i k = cartanE6 k i := fun k => cartan_eq_cartanE6 i k
  have hsum : ∑ l, Tag.E6.cartan i l * α l = ∑ k, α k * cartanE6 k i :=
    Finset.sum_congr rfl fun k _ => by rw [hc k, mul_comm]
  by_cases hji : j = i
  · subst hji
    have h1 : rootRefl j α j = α j - ∑ k, α k * cartanE6 k j := by
      exact if_pos rfl
    have h2 : reflect Tag.E6 j α j = α j - ∑ l, Tag.E6.cartan j l * α l := by
      unfold reflect
      rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    rw [h1, h2, hsum]
  · have h1 : rootRefl i α j = α j := by
      exact if_neg hji
    have h2 : reflect Tag.E6 i α j = α j := by
      unfold reflect
      rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hji, smul_zero, sub_zero]
    rw [h1, h2]

theorem rootRefl_eq_reflect (i : E6Idx) (α : E6Idx → ℤ) :
    rootRefl i α = reflect Tag.E6 i α :=
  funext fun j => rootRefl_apply_eq i α j

theorem isRoot_rootRefl {α : E6Idx → ℤ} (hα : IsRoot Tag.E6 α) (i : E6Idx) :
    IsRoot Tag.E6 (rootRefl i α : E6Idx → ℤ) := by
  have h := IsRoot.reflect (τ := Tag.E6) i hα
  have e : (reflect Tag.E6 i α : E6Idx → ℤ) = rootRefl i α := (rootRefl_eq_reflect i α).symm
  exact e ▸ h

theorem mem_rootsE6_iff {γ : E6Idx → ℤ} : γ ∈ rootsE6 ↔ IsRoot Tag.E6 γ := by
  constructor
  · intro h
    exact h {γ : Fin 6 → ℤ | IsRoot Tag.E6 γ} ⟨fun i => IsRoot.basis (τ := Tag.E6) i,
      fun α hα i => isRoot_rootRefl hα i⟩
  · intro h
    induction h with
    | basis j => exact rootsE6_simple j
    | @reflect i v _ ih =>
      have e : rootRefl i v = reflect Tag.E6 i v := rootRefl_eq_reflect i v
      exact e ▸ rootsE6_closed ih i


theorem iform_eq_cartanForm (α β : E6Idx → ℤ) :
    iform (τ := Tag.E6) α β = cartanForm α β := by
  unfold iform cartanForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : Tag.E6.symmetrizedCartan i j = cartanE6 i j := by
    have : Tag.E6.symmetrizedCartan i j = Tag.E6.cartan i j := by
      simp [Tag.symmetrizedCartan, Tag.symmetrizer]
    rw [this, cartan_eq_cartanE6 i j]
    exact cartanE6_symm j i
  rw [h1]
  ring

end Roots

section Character

variable
  {Ω : Type} [Field Ω]

@[expose] noncomputable def thetaTuple (ζ : Ωˣ) (u : Fin 6 → ZMod 3) : E6Idx → Ωˣ :=
  fun i => DiagTorus.theta ζ (u i)

theorem rootChar_theta_eq_one_iff {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (u : Fin 6 → ZMod 3) (γ : E6Idx → ℤ) :
    rootChar (thetaTuple ζ u) γ = 1 ↔ ∑ i, ((γ i : ℤ) : ZMod 3) * u i = 0 := by
  have h := DiagTorus.rootChar_theta hζ u γ
  rw [show rootChar (thetaTuple ζ u) γ = DiagTorus.theta ζ (DiagTorus.dotZ u γ) from h,
    ← DiagTorus.theta_zero ζ, (DiagTorus.theta_injective hζ').eq_iff]
  rfl

theorem mem_kernelRoots_iff_phiU {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (u : Fin 6 → ZMod 3) (γ : E6Idx → ℤ) :
    γ ∈ kernelRoots (rootCharHom (thetaTuple ζ u)) ↔ γ ∈ PhiU u := by
  rw [kernelRoots_rootCharHom]
  show (IsRoot Tag.E6 γ ∧ rootChar (thetaTuple ζ u) γ = 1) ↔
    (γ ∈ rootsE6 ∧ ∑ i, ((γ i : ℤ) : ZMod 3) * u i = 0)
  rw [mem_rootsE6_iff, rootChar_theta_eq_one_iff hζ hζ']

end Character

section Component

variable
  {τ : Tag} {M : Type*}
  [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)

theorem kernelComponent_eq_iff' (x y : kernelRoots χ) :
    (⟦x⟧ : KernelComponent χ) = ⟦y⟧ ↔ Relation.EqvGen
      (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y :=
  Quotient.eq (r := kernelRootSetoid χ)

@[expose] def KerAdj (α β : Fin τ.rank → ℤ) : Prop :=
  α ∈ kernelRoots χ ∧ β ∈ kernelRoots χ ∧ iform α β ≠ 0

instance kerAdj_symm : Std.Symm (KerAdj χ) :=
  ⟨fun _ _ ⟨ha, hb, h⟩ => ⟨hb, ha, by rwa [iform_comm]⟩⟩

theorem mem_componentRoots_iff (x : kernelRoots χ) (γ : Fin τ.rank → ℤ) :
    γ ∈ componentRoots χ (⟦x⟧ : KernelComponent χ) ↔
      γ ∈ kernelRoots χ ∧ Relation.ReflTransGen (KerAdj χ) (x : Fin τ.rank → ℤ) γ := by
  constructor
  · rintro ⟨hγ, hmk⟩
    refine ⟨hγ, ?_⟩
    have h := (kernelComponent_eq_iff' χ _ _).1 hmk
    have key : ∀ {a b : kernelRoots χ}, Relation.EqvGen
        (fun α β : kernelRoots χ =>
          (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) a b →
        Relation.ReflTransGen (KerAdj χ) (a : Fin τ.rank → ℤ) (b : Fin τ.rank → ℤ) := by
      intro a b hab
      induction hab with
      | rel x y hxy =>
        exact Relation.ReflTransGen.single ⟨x.2, y.2, by
          rwa [← dotProduct_mulVec_eq_iform]⟩
      | refl x => exact Relation.ReflTransGen.refl
      | symm x y _ ih => exact Std.Symm.symm _ _ ih
      | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    exact Std.Symm.symm _ _ (key h)
  · rintro ⟨hγ, hr⟩
    refine ⟨hγ, ?_⟩
    rw [kernelComponent_eq_iff' χ]
    have key : ∀ y, Relation.ReflTransGen (KerAdj χ) (x : Fin τ.rank → ℤ) y →
        ∃ hy : y ∈ kernelRoots χ, Relation.EqvGen
          (fun α β : kernelRoots χ =>
            (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
          x ⟨y, hy⟩ := by
      intro y hy
      induction hy with
      | refl => exact ⟨x.2, Relation.EqvGen.refl _⟩
      | @tail z w _ hstep ih =>
        obtain ⟨hz, hEq⟩ := ih
        obtain ⟨-, hw, hne⟩ := hstep
        exact ⟨hw, Relation.EqvGen.trans _ ⟨z, hz⟩ _ hEq
          (Relation.EqvGen.rel _ _ (by
            show (z : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (w : Fin τ.rank → ℤ)) ≠ 0
            rwa [dotProduct_mulVec_eq_iform]))⟩
    obtain ⟨hγ', hEq⟩ := key γ hr
    exact Relation.EqvGen.symm _ _ hEq

end Component

section PhiComponent

variable
  {M : Type*} [CommGroup M]

theorem isPhiComponent_componentRoots (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M)
    (u : Fin 6 → ZMod 3) (hker : ∀ γ, γ ∈ kernelRoots χ ↔ γ ∈ PhiU u) (i : KernelComponent χ) :
    IsPhiComponent u (componentRoots χ i) := by
  refine ⟨fun γ hγ => (hker γ).1 hγ.1, ?_, ?_⟩
  ·
    intro x hx y hy
    obtain ⟨hxk, hxi⟩ := hx
    have hy' : y ∈ componentRoots χ (⟦⟨x, hxk⟩⟧ : KernelComponent χ) := by rw [hxi]; exact hy
    obtain ⟨-, hr⟩ := (mem_componentRoots_iff χ ⟨x, hxk⟩ y).1 hy'
    have key : ∀ z, Relation.ReflTransGen (KerAdj χ) x z →
        z ∈ componentRoots χ i ∧ Relation.ReflTransGen
          (fun a b => a ∈ componentRoots χ i ∧ b ∈ componentRoots χ i ∧ cartanForm a b ≠ 0) x z := by
      intro z hz
      induction hz with
      | refl => exact ⟨⟨hxk, hxi⟩, Relation.ReflTransGen.refl⟩
      | tail hxz hstep ih =>
        rename_i z w
        obtain ⟨hzi, hzr⟩ := ih
        have hw : w ∈ componentRoots χ i := by
          rw [← hxi]
          exact (mem_componentRoots_iff χ ⟨x, hxk⟩ w).2 ⟨hstep.2.1, hxz.tail hstep⟩
        refine ⟨hw, hzr.tail ⟨hzi, hw, ?_⟩⟩
        exact fun h => hstep.2.2 ((iform_eq_cartanForm _ _).trans h)
    exact (key y hr).2
  ·
    intro D hDP hDc hΨD d hd
    obtain ⟨x₀, hx₀⟩ := Quotient.exists_rep i
    have hx₀Ψ : (x₀ : E6Idx → ℤ) ∈ componentRoots χ i := ⟨x₀.2, hx₀⟩
    have hx₀D : (x₀ : E6Idx → ℤ) ∈ D := hΨD hx₀Ψ
    have hr := hDc _ hx₀D d hd
    have key : ∀ z, Relation.ReflTransGen
        (fun a b => a ∈ D ∧ b ∈ D ∧ cartanForm a b ≠ 0) (x₀ : E6Idx → ℤ) z →
        Relation.ReflTransGen (KerAdj χ) (x₀ : E6Idx → ℤ) z := by
      intro z hz
      induction hz with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        refine ih.tail ⟨(hker _).2 (hDP hstep.1), (hker _).2 (hDP hstep.2.1), ?_⟩
        exact fun h => hstep.2.2 ((iform_eq_cartanForm _ _).symm.trans h)
    have hd' : d ∈ componentRoots χ (⟦x₀⟧ : KernelComponent χ) :=
      (mem_componentRoots_iff χ x₀ d).2 ⟨(hker _).2 (hDP hd), key d hr⟩
    rwa [hx₀] at hd'

end PhiComponent

section GroupTheory

theorem pow_three_eq_one (u : Multiplicative (Fin 6 → ZMod 3)) : u ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  ext i
  simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
  generalize Multiplicative.toAdd u i = x
  revert x
  decide

theorem exists_closure_pair {G : Subgroup (Multiplicative (Fin 6 → ZMod 3))}
    (hG : Nat.card G = 9) {u : Multiplicative (Fin 6 → ZMod 3)} (hu : u ∈ G) (hu1 : u ≠ 1) :
    ∃ v ∈ G, v ∉ Subgroup.zpowers u ∧ G = Subgroup.closure {u, v} := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have hord : orderOf u = 3 := orderOf_eq_prime (pow_three_eq_one u) hu1
  have hz : Nat.card (Subgroup.zpowers u) = 3 := by rw [Nat.card_zpowers, hord]
  have hzG : Subgroup.zpowers u ≤ G := (Subgroup.zpowers_le).2 hu
  obtain ⟨v, hvG, hvz⟩ : ∃ v ∈ G, v ∉ Subgroup.zpowers u := by
    by_contra hno
    push Not at hno
    have hle : G ≤ Subgroup.zpowers u := fun v hv => hno v hv
    have := Subgroup.card_le_of_le hle
    omega
  refine ⟨v, hvG, hvz, ?_⟩
  set H := Subgroup.closure ({u, v} : Set (Multiplicative (Fin 6 → ZMod 3))) with hH
  have hHG : H ≤ G := (Subgroup.closure_le _).2 (by
    intro x hx
    rcases hx with rfl | hx
    · exact hu
    · rw [Set.mem_singleton_iff.1 hx]; exact hvG)
  have hzH : Subgroup.zpowers u ≤ H := (Subgroup.zpowers_le).2
    (Subgroup.subset_closure (Set.mem_insert _ _))
  have hvH : v ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hd1 : Nat.card H ∣ 9 := by
    have := Subgroup.card_dvd_of_le hHG
    rwa [hG] at this
  have hd2 : 3 ∣ Nat.card H := by
    have := Subgroup.card_dvd_of_le hzH
    rwa [hz] at this
  have hne3 : Nat.card H ≠ 3 := by
    intro h3
    have := Subgroup.eq_of_le_of_card_ge hzH (le_of_eq (h3.trans hz.symm))
    exact hvz (this ▸ hvH)
  have h9 : Nat.card H = 9 := by
    have hle : Nat.card H ≤ 9 := Nat.le_of_dvd (by norm_num) hd1
    haveI : Finite H := Finite.of_injective (Subgroup.inclusion hHG)
      (Subgroup.inclusion_injective hHG)
    have hpos : 0 < Nat.card H := Nat.card_pos
    obtain ⟨k, hk⟩ := hd2
    have hk3 : k ≤ 3 := by omega
    interval_cases k <;> first | omega | (rw [hk] at hd1; norm_num at hd1)
  exact (Subgroup.eq_of_le_of_card_ge hHG (le_of_eq (hG.trans h9.symm))).symm

variable
  {Ω : Type} [Field Ω] {ζ : Ωˣ}

theorem centralizer_psi6_eq_inf (hζ : ζ ^ 3 = 1) {G : Subgroup (Multiplicative (Fin 6 → ZMod 3))}
    {u v : Multiplicative (Fin 6 → ZMod 3)} (hG : G = Subgroup.closure {u, v}) :
    Subgroup.centralizer ((Psi6 hζ : Multiplicative (Fin 6 → ZMod 3) →* ModGL Tag.E6 Ω) ''
        (G : Set (Multiplicative (Fin 6 → ZMod 3)))) =
      Subgroup.centralizer ({Psi6 hζ u} : Set (ModGL Tag.E6 Ω)) ⊓
        Subgroup.centralizer ({Psi6 hζ v} : Set (ModGL Tag.E6 Ω)) := by
  subst hG
  have h1 : ((Psi6 hζ : Multiplicative (Fin 6 → ZMod 3) →* ModGL Tag.E6 Ω) ''
      ((Subgroup.closure {u, v} : Subgroup _) : Set (Multiplicative (Fin 6 → ZMod 3)))) =
      ((Subgroup.closure ({Psi6 hζ u, Psi6 hζ v} : Set (ModGL Tag.E6 Ω)) : Subgroup _) :
        Set (ModGL Tag.E6 Ω)) := by
    rw [← Subgroup.coe_map, MonoidHom.map_closure, Set.image_pair]
  rw [h1, Subgroup.centralizer_closure]
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

end GroupTheory

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
