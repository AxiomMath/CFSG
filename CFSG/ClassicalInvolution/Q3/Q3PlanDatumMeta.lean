module

public import CFSG.ClassicalInvolution.Q3.Q3PlanDatumComm
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsComp
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Layer
public import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Component

variable {B : Type*} [Group B]

theorem isSubnormal_subgroupOf_unary {Y A : Subgroup B} (h : IsSubnormal A Y) :
    (A.subgroupOf Y).IsSubnormal := by
  have h1 := CFSG.ClassicalInvolution.isSubnormal_subgroupOf h Y
  rw [Subgroup.subgroupOf_self] at h1
  exact (CFSG.Adapters.isSubnormal_top_iff _).1 h1

theorem isQuasisimple_open_of_mulEquiv {A C : Type*} [Group A] [Group C] (e : A ≃* C)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple C :=
  CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native A).1 h))

theorem commute_of_isSubnormal_of_isQuasisimple {Y A N : Subgroup B} [Finite Y]
    (hA : CFSG.Open.IsQuasisimple A) (hAY : IsSubnormal A Y) (hNY : IsSubnormal N Y)
    (hsolv : Group.IsSolvable N) : ∀ n ∈ N, ∀ a ∈ A, n * a = a * n := by
  have hAle : A ≤ Y := CFSG.ClassicalInvolution.isSubnormal_le hAY
  have hNle : N ≤ Y := CFSG.ClassicalInvolution.isSubnormal_le hNY
  have hAq : CFSG.IsQuasisimple (A.subgroupOf Y) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAle).symm
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native A).1 hA)
  have hsolv' : Group.IsSolvable (N.subgroupOf Y) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNle).injective
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsolv'
    (isSubnormal_subgroupOf_unary hNY)).1 (A.subgroupOf Y)
    ⟨hAq, isSubnormal_subgroupOf_unary hAY⟩
  intro n hn a ha
  have hm := Subgroup.commutator_mem_commutator
    (Subgroup.mem_subgroupOf.2 ha : (⟨a, hAle ha⟩ : Y) ∈ A.subgroupOf Y)
    (Subgroup.mem_subgroupOf.2 hn : (⟨n, hNle hn⟩ : Y) ∈ N.subgroupOf Y)
  rw [hcomm, Subgroup.mem_bot] at hm
  exact (congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp hm)).symm

end Component

section Odd

variable {G : Type*} [Group G]

theorem le_of_isOddGenerated_of_sq_mem {N X : Subgroup G} (hodd : IsOddGenerated N)
    (h2 : ∀ y ∈ N, y ^ 2 ∈ X) : N ≤ X := by
  refine hodd.trans ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨hxN, k, hk⟩
  have h1 : x ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one x
  have h2' : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, h1, one_mul]
  rw [h2']
  exact pow_mem (h2 x hxN) _

end Odd

section Datum

open OrthogonalSemilinearFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem orbitGroup_isSubnormal (J' : Set.range D.classOrbit) :
    IsSubnormal (D.withOrbit J').orbitGroup
      (D.totalFixedGroup.map (adjointGroup τ k).subtype) := by
  have h1 := CFSG.ComponentClassification.Components.chain_map (adjointGroup τ k).subtype
    (CFSG.ClassicalInvolution.ModelFacts.isSubnormal_orbitGroupC_totalFixedGroup D J')
  rwa [OrthogonalSemilinearFixedRootDatum.orbitGroupC,
    Subgroup.map_subgroupOf_eq_of_le (D.withOrbit J').orbitGroup_le_adjointGroup] at h1

theorem orbitGroup_eq_bot_or_isQuasisimple (h3 : 3 < D.q) (J' : Set.range D.classOrbit) :
    (D.withOrbit J').orbitGroup = ⊥ ∨ CFSG.Open.IsQuasisimple ↥(D.withOrbit J').orbitGroup := by
  have hle := (D.withOrbit J').orbitGroup_le_adjointGroup
  rcases CFSG.ClassicalInvolution.ModelFacts.orbitGroupC_eq_bot_or_isQuasisimple
    (D.withOrbit J') h3 with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hle hx⟩ : adjointGroup τ k) ∈ (D.withOrbit J').orbitGroupC :=
      Subgroup.mem_subgroupOf.2 hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
  · right
    exact isQuasisimple_open_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) h

theorem derivedSeries_two_eq_bot_of_datum (h3 : 3 < D.q) {Xh X₀ : Subgroup (ModGL τ k)}
    (u : ModGL τ k) (hX : D.totalFixedGroup.map (adjointGroup τ k).subtype = Xh)
    (hconj : Xh.map (MulAut.conj u).toMonoidHom = X₀) {Y : Subgroup (ModGL τ k)} [Finite Y]
    (hCY : ∀ J' : Set.range D.classOrbit,
      ((D.withOrbit J').orbitGroup).map (MulAut.conj u).toMonoidHom ≤ Y)
    (hY2 : ∀ y ∈ Y, y ^ 2 ∈ X₀) (hYn : ∀ y ∈ Y, ∀ v ∈ X₀, y * v * y⁻¹ ∈ X₀)
    {N : Subgroup (ModGL τ k)} (hNs : IsSubnormal N Y) (hsolv : Group.IsSolvable N)
    (hodd : IsOddGenerated N) : derivedSeries ↥N 2 = ⊥ := by
  classical
  have hq4 : 4 ≤ D.q := h3
  have hNY : N ≤ Y := CFSG.ClassicalInvolution.isSubnormal_le hNs
  have hNX : N ≤ X₀ := le_of_isOddGenerated_of_sq_mem hodd fun y hy => hY2 y (hNY hy)
  have hZY : IsSubnormal (X₀ ⊓ Y) Y := by
    refine CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf inf_le_right
      ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hYn _ g.2 _ hn.1, Y.mul_mem (Y.mul_mem g.2 hn.2) (Y.inv_mem g.2)⟩
  have hcomm : ∀ J' : Set.range D.classOrbit, ∀ n ∈ N, ∀ a ∈ (D.withOrbit J').orbitGroup,
      n * (u * a * u⁻¹) = (u * a * u⁻¹) * n := by
    intro J' n hn a ha
    have hCsub : IsSubnormal (D.withOrbit J').orbitGroup Xh := by
      have h1 := orbitGroup_isSubnormal D J'
      rwa [hX] at h1
    have hC₀sub : IsSubnormal ((D.withOrbit J').orbitGroup.map (MulAut.conj u).toMonoidHom) X₀ := by
      have h1 := CFSG.ClassicalInvolution.isSubnormal_map_mulEquiv (MulAut.conj u) hCsub
      rwa [hconj] at h1
    have hC₀Z : IsSubnormal ((D.withOrbit J').orbitGroup.map (MulAut.conj u).toMonoidHom)
        (X₀ ⊓ Y) := by
      have h1 := CFSG.ClassicalInvolution.isSubnormal_inf hC₀sub Y
      rwa [inf_eq_left.mpr (hCY J')] at h1
    have hC₀Y : IsSubnormal ((D.withOrbit J').orbitGroup.map (MulAut.conj u).toMonoidHom) Y :=
      CFSG.ClassicalInvolution.isSubnormal_trans hC₀Z hZY
    rcases orbitGroup_eq_bot_or_isQuasisimple D h3 J' with hbot | hqs
    · rw [hbot, Subgroup.mem_bot] at ha
      subst ha
      simp
    · have hqs' := isQuasisimple_open_of_mulEquiv
        ((D.withOrbit J').orbitGroup.equivMapOfInjective (MulAut.conj u).toMonoidHom
          (MulAut.conj u).injective) hqs
      exact commute_of_isSubnormal_of_isQuasisimple hqs' hC₀Y hNs hsolv n hn _
        (Subgroup.mem_map_of_mem _ ha)
  have hS : ∀ n ∈ N, ∀ y ∈ D.kernelSpan, (u⁻¹ * n * u) * y = y * (u⁻¹ * n * u) := by
    intro n hn
    refine commute_kernelSpan_of_commute_orbitGroups D hq4 (g := u⁻¹ * n * u) fun J' x hx => ?_
    have h := hcomm J' n hn x hx
    calc (u⁻¹ * n * u) * x = u⁻¹ * (n * (u * x * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * x * u⁻¹) * n) * u := by rw [h]
      _ = x * (u⁻¹ * n * u) := by group
  set f := (MulAut.conj u⁻¹).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj u⁻¹).injective
  have hfapp : ∀ g, f g = u⁻¹ * g * u := fun g => by
    simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hN₁M : ∀ g ∈ N.map f, g ∈ D.torusKernelSpan := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨v, hv, hvn⟩ := Subgroup.mem_map.1
      (hconj ▸ hNX hn : n ∈ Xh.map (MulAut.conj u).toMonoidHom)
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1
      (hX ▸ hv : v ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype)
    have : f n = (x : ModGL τ k) := by
      rw [hfapp, ← hvn]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
      rfl
    rw [this]
    exact (D.mem_totalFixedGroup.1 hx).1
  refine derivedSeries_eq_bot_of_map f hfinj ?_
  refine derivedSeries_two_eq_bot_of_commutator_mem (B := N.map f ⊓ D.kernelSpan) ?_ ?_
  · rintro a ⟨⟨n, hn, rfl⟩, -⟩ b ⟨-, hb⟩
    rw [hfapp]
    exact hS n hn b hb
  · intro x hx y hy
    refine ⟨(N.map f).mul_mem ((N.map f).mul_mem ((N.map f).mul_mem hx hy)
      ((N.map f).inv_mem hx)) ((N.map f).inv_mem hy), ?_⟩
    exact commutatorElement_mem_of_le_normalizer (H := torusGroup τ k) (N := D.kernelSpan)
      (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
      (fun _ ha _ hb => mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha)
        (torusGroup_le_diagonalGroup hb)) (hN₁M x hx) (hN₁M y hy)

end Datum

end CFSG.ClassicalInvolution.Q3
