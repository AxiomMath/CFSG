module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigherRoots
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLift

public noncomputable section

namespace CFSG.LieType.Chevalley.SimplyLacedCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial
open Subgroup
open scoped commutatorElement

variable {τ : Tag}

theorem iform_neg_left
    (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left, neg_one_mul]

theorem iform_neg_right
    (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [iform_comm, iform_neg_left, iform_comm]

theorem iform_self_eq_two
    (hτ : ∀ i, τ.symmetrizer i i = 1) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  rw [hj, hτ j, mul_one]

theorem iform_mem
    (hτ : ∀ i, τ.symmetrizer i i = 1) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) :
    iform α β = -1 ∨ iform α β = 0 ∨ iform α β = 1 := by
  have h := iform_sq_lt hα hβ hne hne'
  rw [iform_self_eq_two hτ hα, iform_self_eq_two hτ hβ] at h
  have h1 : -1 ≤ iform α β := by nlinarith
  have h2 : iform α β ≤ 1 := by nlinarith
  omega

theorem ne_neg_of_iform
    (hτ : ∀ i, τ.symmetrizer i i = 1) {α β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h : iform α β ≠ -2) : α ≠ -β := by
  rintro rfl
  rw [iform_neg_left, iform_self_eq_two hτ hβ] at h
  exact h rfl

theorem isRoot_add
    (hτ : ∀ i, τ.symmetrizer i i = 1) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (h : iform α β = -1) : IsRoot τ (α + β) :=
  isRoot_add_of_iform_neg hα hβ (ne_neg_of_iform hτ hβ (by omega)) (by omega)

theorem not_isRoot_add
    (hτ : ∀ i, τ.symmetrizer i i = 1) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (h : 0 ≤ iform α β) : ¬ IsRoot τ (α + β) := by
  intro hr
  have h1 := iform_self_eq_two hτ hr
  rw [iform_add_left, iform_add_right, iform_add_right, iform_self_eq_two hτ hα,
    iform_self_eq_two hτ hβ, iform_comm β α] at h1
  omega

structure BinaryRoots (G : Type*) [Group G] (τ : Tag) where
  x : (Fin τ.rank → ℤ) → G
  mul_self : ∀ α, IsRoot τ α → x α * x α = 1
  comm : ∀ α β, IsRoot τ α → IsRoot τ β → α ≠ -β → 0 ≤ iform α β → x α * x β = x β * x α
  commutator : ∀ α β, IsRoot τ α → IsRoot τ β → iform α β = -1 → ⁅x α, x β⁆ = x (α + β)

variable (τ) in
@[expose] def DecompAt (α β : Fin τ.rank → ℤ) : Prop :=
  ∃ γ δ : Fin τ.rank → ℤ, IsRoot τ γ ∧ IsRoot τ δ ∧ γ + δ = α ∧ iform γ δ = -1 ∧ γ ≠ -β ∧
    0 ≤ iform γ β ∧ δ ≠ -β ∧ 0 ≤ iform δ β

variable (τ) in
@[expose] def HasDecomp : Prop :=
  ∀ α β : Fin τ.rank → ℤ, IsRoot τ α → IsRoot τ β → α ≠ -β → 0 ≤ iform α β → DecompAt τ α β

namespace BinaryRoots

variable {G E : Type*} [Group G] [Group E] (R : BinaryRoots G τ) (η : E →* G)
  (hker : ∀ z, η z = 1 → z ∈ center E) (hη : Function.Surjective η)
  (hτ : ∀ i, τ.symmetrizer i i = 1) (hD : HasDecomp τ)
include hker hη hD

theorem lift_mul_comm
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ -β) (h0 : 0 ≤ iform α β) {a c : E} (ha : η a = R.x α) (hc : η c = R.x β) :
    a * c = c * a := by
  obtain ⟨γ, δ, hγ, hδ, hsum, hγδ, hγβ, hγβ', hδβ, hδβ'⟩ := hD α β hα hβ hne h0
  obtain ⟨p, hp⟩ := hη (R.x γ)
  obtain ⟨q, hq⟩ := hη (R.x δ)
  have hne1 : β ≠ -γ := fun h => hγβ (by rw [h, neg_neg])
  have hne2 : β ≠ -δ := fun h => hδβ (by rw [h, neg_neg])
  have h1 : η (c * p * c⁻¹) = η p := by
    rw [map_mul, map_mul, map_inv, hc, hp, R.comm β γ hβ hγ hne1 (by rwa [iform_comm]),
      mul_inv_cancel_right]
  have h2 : η (c * q * c⁻¹) = η q := by
    rw [map_mul, map_mul, map_inv, hc, hq, R.comm β δ hβ hδ hne2 (by rwa [iform_comm]),
      mul_inv_cancel_right]
  have h3 : c * ⁅p, q⁆ = ⁅p, q⁆ * c := by
    have h := LinearCover.conj_commutatorElement_eq c p q
    rw [LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker h1 h2] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hz : ⁅p, q⁆⁻¹ * a ∈ center E := hker _ (by
    rw [map_mul, map_inv, map_commutatorElement, hp, hq, R.commutator γ δ hγ hδ hγδ, hsum, ha,
      inv_mul_cancel])
  calc a * c = ⁅p, q⁆ * (⁅p, q⁆⁻¹ * a) * c := by group
    _ = ⁅p, q⁆ * c * (⁅p, q⁆⁻¹ * a) := by
        rw [mul_assoc, ← mem_center_iff.mp hz c, ← mul_assoc]
    _ = c * a := by rw [← h3]; group

include hτ

theorem commutatorElement_lift_mul_self
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hγδ : iform γ δ = -1) {p q : E} (hp : η p = R.x γ) (hq : η q = R.x δ) :
    ⁅p, q⁆ * ⁅p, q⁆ = 1 := by
  have hp2 : p * p ∈ center E := hker _ (by rw [map_mul, hp, R.mul_self γ hγ])
  have hq2 : q * q ∈ center E := hker _ (by rw [map_mul, hq, R.mul_self δ hδ])
  have h := (LinearCover.commutatorElement_commutatorElement_eq_sq
    (mem_center_iff.mp hp2 q).symm (mem_center_iff.mp hq2 p).symm).1
  have hpq : η ⁅p, q⁆ = R.x (γ + δ) := by
    rw [map_commutatorElement, hp, hq, R.commutator γ δ hγ hδ hγδ]
  have hρ := isRoot_add hτ hγ hδ hγδ
  have hργ : iform (γ + δ) γ = 1 := by
    rw [iform_add_left, iform_self_eq_two hτ hγ, iform_comm, hγδ]
    norm_num
  have hc := R.lift_mul_comm η hker hη hD hρ hγ (ne_neg_of_iform hτ hγ (by omega)) (by omega)
    hpq hp
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc, eq_comm, sq] at h
  exact h

theorem commutatorElement_lift_eq_aux
    {u v u' v' : Fin τ.rank → ℤ} (hu : IsRoot τ u)
    (hv : IsRoot τ v) (hu' : IsRoot τ u') (hv' : IsRoot τ v') (huv : iform u v = -1)
    (hu'v' : iform u' v' = -1) (hsum : u + v = u' + v') (huu' : iform u u' = 1)
    {a b a' b' : E} (ha : η a = R.x u) (hb : η b = R.x v) (ha' : η a' = R.x u')
    (hb' : η b' = R.x v') : ⁅a, b⁆ = ⁅a', b'⁆ := by
  have hne : u ≠ u' := fun h => by
    rw [h, iform_self_eq_two hτ hu'] at huu'
    exact absurd huu' (by decide)
  have hq : IsRoot τ (u - u') := isRoot_sub_of_iform_pos hu hu' hne (by omega)
  have huu : iform u u = 2 := iform_self_eq_two hτ hu
  have hu'u' : iform u' u' = 2 := iform_self_eq_two hτ hu'
  have hvv' : v' = u - u' + v := by
    have := congrArg (fun x => x - u') hsum
    simp only [add_sub_cancel_left] at this
    rw [← this]
    abel
  have hu'v : iform u' v = 0 := by
    have e : v = u' + v' - u := by rw [← hsum]; abel
    rw [e, iform_sub_right, iform_add_right, hu'u', hu'v', iform_comm, huu']
    norm_num
  have hpq : iform u' (u - u') = -1 := by
    rw [iform_sub_right, hu'u', iform_comm, huu']
    norm_num
  have hqs : iform (u - u') v = -1 := by
    rw [iform_sub_left, huv, hu'v]
    norm_num
  have hρ : IsRoot τ (u + v) := isRoot_add hτ hu hv huv
  have huv'0 : iform u v' = 0 := by
    rw [hvv', iform_add_right, iform_sub_right, huu, huu', huv]
    norm_num
  have hρv' : iform (u + v) v' = 1 := by
    rw [hsum, iform_add_left, hu'v', iform_self_eq_two hτ hv']
    norm_num
  obtain ⟨b₀, hb₀⟩ := hη (R.x (u - u'))
  have hab₀ : η ⁅a', b₀⁆ = R.x u := by
    rw [map_commutatorElement, ha', hb₀, R.commutator u' (u - u') hu' hq hpq]
    congr 1
    abel
  have hb₀b : η ⁅b₀, b⁆ = R.x v' := by
    rw [map_commutatorElement, hb₀, hb, R.commutator (u - u') v hq hv hqs, hvv']
  have hX : η ⁅⁅a', b₀⁆, b⁆ = R.x (u + v) := by
    rw [map_commutatorElement, hab₀, hb, R.commutator u v hu hv huv]
  have hac : a' * b = b * a' :=
    R.lift_mul_comm η hker hη hD hu' hv (ne_neg_of_iform hτ hv (by omega)) (by omega) ha' hb
  have huv' : ⁅a', b₀⁆ * ⁅b₀, b⁆ = ⁅b₀, b⁆ * ⁅a', b₀⁆ :=
    R.lift_mul_comm η hker hη hD hu hv' (ne_neg_of_iform hτ hv' (by omega)) (by omega) hab₀ hb₀b
  have hXv : ⁅⁅a', b₀⁆, b⁆ * ⁅b₀, b⁆ = ⁅b₀, b⁆ * ⁅⁅a', b₀⁆, b⁆ :=
    R.lift_mul_comm η hker hη hD hρ hv' (ne_neg_of_iform hτ hv' (by omega)) (by omega) hX hb₀b
  have hY : ⁅a', ⁅b₀, b⁆⁆ = ⁅⁅a', b₀⁆, b⁆ := by
    rw [LinearCover.commutatorElement_commutatorElement_right_of_commute hac, huv',
      mul_inv_cancel_right, ← hXv, mul_inv_cancel_right]
  calc ⁅a, b⁆ = ⁅⁅a', b₀⁆, b⁆ :=
        LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker (by rw [ha, hab₀]) rfl
    _ = ⁅a', ⁅b₀, b⁆⁆ := hY.symm
    _ = ⁅a', b'⁆ :=
        LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker rfl (by rw [hb₀b, hb'])

theorem commutatorElement_lift_eq
    {u v u' v' : Fin τ.rank → ℤ} (hu : IsRoot τ u)
    (hv : IsRoot τ v) (hu' : IsRoot τ u') (hv' : IsRoot τ v') (huv : iform u v = -1)
    (hu'v' : iform u' v' = -1) (hsum : u + v = u' + v') {a b a' b' : E} (ha : η a = R.x u)
    (hb : η b = R.x v) (ha' : η a' = R.x u') (hb' : η b' = R.x v') : ⁅a, b⁆ = ⁅a', b'⁆ := by
  have huu : iform u u = 2 := iform_self_eq_two hτ hu
  have hvv : iform v v = 2 := iform_self_eq_two hτ hv
  have hrev : ∀ {a₁ b₁ : E}, η a₁ = R.x u' → η b₁ = R.x v' → ⁅b₁, a₁⁆ = ⁅a₁, b₁⁆ := by
    intro a₁ b₁ h₁ h₂
    have h := R.commutatorElement_lift_mul_self η hker hη hτ hD hu' hv' hu'v' h₁ h₂
    rw [← commutatorElement_inv, inv_eq_of_mul_eq_one_left h]
  by_cases h1 : u' = u
  · subst h1
    have hv'v : v' = v := add_left_cancel hsum.symm
    subst hv'v
    exact LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker
      (by rw [ha, ha']) (by rw [hb, hb'])
  by_cases h2 : u' = v
  · subst h2
    have hv'u : v' = u := by
      have := hsum
      rw [add_comm] at this
      exact (add_left_cancel this).symm
    subst hv'u
    rw [← hrev ha' hb']
    exact LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker
      (by rw [ha, hb']) (by rw [hb, ha'])
  have hsum' : iform u u' + iform u v' = 1 := by
    rw [← iform_add_right, ← hsum, iform_add_right, huu, huv]
    norm_num
  have hu'neg : u' ≠ -u := by
    intro h
    have hv'e : v' = u + u + v := by
      rw [h] at hsum
      have := congrArg (fun x => x + u) hsum
      simp only [neg_add_cancel_comm] at this
      rw [← this]
      abel
    have h' := iform_self_eq_two hτ hv'
    rw [hv'e] at h'
    simp only [iform_add_left, iform_add_right, huu, huv, hvv, iform_comm v u] at h'
    omega
  have hv'ne : v' ≠ u := fun h => h2 (by
    rw [h] at hsum
    have := hsum
    rw [add_comm u' u] at this
    exact (add_left_cancel this).symm)
  have hv'neg : v' ≠ -u := by
    intro h
    have hu'e : u' = u + u + v := by
      rw [h] at hsum
      have := congrArg (fun x => x + u) hsum
      simp only [neg_add_cancel_right] at this
      rw [← this]
      abel
    have h' := iform_self_eq_two hτ hu'
    rw [hu'e] at h'
    simp only [iform_add_left, iform_add_right, huu, huv, hvv, iform_comm v u] at h'
    omega
  have hm1 := iform_mem hτ hu hu' (Ne.symm h1) (fun h => hu'neg (by rw [h, neg_neg]))
  have hm2 := iform_mem hτ hu hv' (Ne.symm hv'ne) (fun h => hv'neg (by rw [h, neg_neg]))
  rcases hm1 with hm1 | hm1 | hm1
  · omega
  ·
    have hm2' : iform u v' = 1 := by omega
    rw [← hrev ha' hb']
    exact R.commutatorElement_lift_eq_aux η hker hη hτ hD hu hv hv' hu' huv
      (by rw [iform_comm]; exact hu'v') (by rw [hsum, add_comm]) hm2' ha hb hb' ha'
  · exact R.commutatorElement_lift_eq_aux η hker hη hτ hD hu hv hu' hv' huv hu'v' hsum hm1
      ha hb ha' hb'

end BinaryRoots

theorem card_closure_le_of_posRoots
    {E : Type*} [Group E] [Finite E]
    (hτ : ∀ i, τ.symmetrizer i i = 1) (y : (Fin τ.rank → ℤ) → E)
    (hy2 : ∀ α, IsRoot τ α → 0 < height α → y α * y α = 1)
    (hyc : ∀ α β, IsRoot τ α → 0 < height α → IsRoot τ β → 0 < height β → 0 ≤ iform α β →
      y α * y β = y β * y α)
    (hy3 : ∀ α β, IsRoot τ α → 0 < height α → IsRoot τ β → 0 < height β → iform α β = -1 →
      ⁅y α, y β⁆ = y (α + β)) :
    Nat.card (closure {g | ∃ α, IsRoot τ α ∧ 0 < height α ∧ y α = g}) ≤
      2 ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
  classical
  have key : ∀ T : Finset (Fin τ.rank → ℤ), (∀ α ∈ T, IsRoot τ α ∧ 0 < height α) →
      (∀ α ∈ T, ∀ β ∈ T, iform α β = -1 → α + β ∈ T) →
      Nat.card (closure (y '' (T : Set (Fin τ.rank → ℤ)))) ≤ 2 ^ T.card := by
    intro T
    induction T using Finset.induction_on_min_value height with
    | empty =>
      intro _ _
      simp
    | insert a s has hmin ih =>
      intro hpos hcl
      have ha := hpos a (Finset.mem_insert_self _ _)
      have hpos_s : ∀ α ∈ s, IsRoot τ α ∧ 0 < height α := fun α hα =>
        hpos α (Finset.mem_insert_of_mem hα)
      have hne_a : ∀ α ∈ s, ∀ β ∈ s, α + β ≠ a := by
        intro α hα β hβ h
        have h1 := hmin α hα
        have h2 := (hpos_s β hβ).2
        rw [← h, height_add] at h1
        omega
      have hcl_s : ∀ α ∈ s, ∀ β ∈ s, iform α β = -1 → α + β ∈ s := by
        intro α hα β hβ h
        rcases Finset.mem_insert.mp (hcl α (Finset.mem_insert_of_mem hα) β
          (Finset.mem_insert_of_mem hβ) h) with h' | h'
        · exact absurd h' (hne_a α hα β hβ)
        · exact h'
      have ih' := ih hpos_s hcl_s
      rw [Finset.coe_insert, Set.image_insert_eq, Finset.card_insert_of_notMem has, pow_succ']
      refine (LinearCover.card_closure_insert_le (hy2 a ha.1 ha.2) ?_).trans
        (Nat.mul_le_mul_left 2 ih')
      rintro _ ⟨β, hβ, rfl⟩
      have hβ' := hpos_s β hβ
      have hne : a ≠ β := fun h => has (h ▸ hβ)
      have hne' : a ≠ -β := fun h => by
        have h1 := congrArg height h
        have h2 : height (-β) = -height β := by simp [height]
        rw [h2] at h1
        omega
      rcases iform_mem hτ ha.1 hβ'.1 hne hne' with h | h | h
      · have hmem : a + β ∈ s := by
          rcases Finset.mem_insert.mp (hcl a (Finset.mem_insert_self _ _) β
            (Finset.mem_insert_of_mem hβ) h) with h' | h'
          · have h1 := congrArg height h'
            rw [height_add] at h1
            omega
          · exact h'
        rw [show y a * y β * (y a)⁻¹ = ⁅y a, y β⁆ * y β by
          simp only [commutatorElement_def]; group, hy3 a β ha.1 ha.2 hβ'.1 hβ'.2 h]
        exact mul_mem (subset_closure ⟨_, hmem, rfl⟩) (subset_closure ⟨_, hβ, rfl⟩)
      · rw [hyc a β ha.1 ha.2 hβ'.1 hβ'.2 (by omega), mul_inv_cancel_right]
        exact subset_closure ⟨_, hβ, rfl⟩
      · rw [hyc a β ha.1 ha.2 hβ'.1 hβ'.2 (by omega), mul_inv_cancel_right]
        exact subset_closure ⟨_, hβ, rfl⟩
  have hfin : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.Finite :=
    (finite_setOf_isRoot τ).subset fun _ h => h.1
  set T := hfin.toFinset with hTdef
  have hT := key T (fun α hα => (Set.Finite.mem_toFinset hfin).1 hα) (fun α hα β hβ h => by
    have hα' := (Set.Finite.mem_toFinset hfin).1 hα
    have hβ' := (Set.Finite.mem_toFinset hfin).1 hβ
    refine (Set.Finite.mem_toFinset hfin).2 ⟨isRoot_add hτ hα'.1 hβ'.1 h, ?_⟩
    rw [height_add]
    linarith [hα'.2, hβ'.2])
  have hset : y '' (T : Set (Fin τ.rank → ℤ)) = {g | ∃ α, IsRoot τ α ∧ 0 < height α ∧ y α = g} := by
    ext g
    simp only [hTdef, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq, and_assoc]
  rw [hset, ← Set.ncard_coe_finset, hTdef, Set.Finite.coe_toFinset] at hT
  exact hT

namespace BinaryRoots

variable {G : Type*} [Group G] (R : BinaryRoots G τ)

theorem ker_eq_bot
    (hτ : ∀ i, τ.symmetrizer i i = 1) (hD : HasDecomp τ) (S : Subgroup G)
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S)
    (hS : S ≤ closure {g | ∃ α, IsRoot τ α ∧ 0 < height α ∧ R.x α = g})
    (hcard : 2 ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard ≤ Nat.card S)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {η : E →* G}
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) :
    η.ker = ⊥ := by
  classical
  have hker : ∀ z, η z = 1 → z ∈ center E := fun z hz => hC hz
  choose e he using fun α => hη (R.x α)
  have hdec : ∀ ρ : Fin τ.rank → ℤ, ∃ γ δ : Fin τ.rank → ℤ, IsRoot τ ρ →
      IsRoot τ γ ∧ IsRoot τ δ ∧ γ + δ = ρ ∧ iform γ δ = -1 := by
    intro ρ
    by_cases hρ : IsRoot τ ρ
    · obtain ⟨γ, δ, hγ, hδ, hsum, hγδ, -⟩ := hD ρ ρ hρ hρ
        (ne_neg_of_iform hτ hρ (by rw [iform_self_eq_two hτ hρ]; decide))
        (by rw [iform_self_eq_two hτ hρ]; decide)
      exact ⟨γ, δ, fun _ => ⟨hγ, hδ, hsum, hγδ⟩⟩
    · exact ⟨0, 0, fun h => absurd h hρ⟩
  choose γ δ hγδ using hdec
  obtain ⟨y, hydef⟩ : ∃ y : (Fin τ.rank → ℤ) → E, ∀ ρ, y ρ = ⁅e (γ ρ), e (δ ρ)⁆ :=
    ⟨_, fun _ => rfl⟩
  have hy : ∀ ρ, IsRoot τ ρ → η (y ρ) = R.x ρ := fun ρ hρ => by
    obtain ⟨hγ, hδ, hsum, h⟩ := hγδ ρ hρ
    rw [hydef, map_commutatorElement, he, he, R.commutator _ _ hγ hδ h, hsum]
  have hy_eq : ∀ ρ, IsRoot τ ρ → ∀ u v, IsRoot τ u → IsRoot τ v → iform u v = -1 →
      u + v = ρ → ∀ a b, η a = R.x u → η b = R.x v → y ρ = ⁅a, b⁆ := by
    intro ρ hρ u v hu hv huv hsum a b ha hb
    obtain ⟨hγ, hδ, hsum', h⟩ := hγδ ρ hρ
    rw [hydef]
    exact R.commutatorElement_lift_eq η hker hη hτ hD hγ hδ hu hv h huv (hsum'.trans hsum.symm)
      (he _) (he _) ha hb
  have hy2 : ∀ ρ, IsRoot τ ρ → y ρ * y ρ = 1 := fun ρ hρ => by
    obtain ⟨hγ, hδ, -, h⟩ := hγδ ρ hρ
    rw [hydef]
    exact R.commutatorElement_lift_mul_self η hker hη hτ hD hγ hδ h (he _) (he _)
  have hcount := card_closure_le_of_posRoots hτ y (fun α hα _ => hy2 α hα)
    (fun α β hα hαp hβ hβp h0 => R.lift_mul_comm η hker hη hD hα hβ (fun h => by
      have h1 := congrArg height h
      have h2 : height (-β) = -height β := by simp [height]
      rw [h2] at h1
      omega) h0 (hy α hα) (hy β hβ))
    (fun α β hα _ hβ _ h => (hy_eq (α + β) (isRoot_add hτ hα hβ h) α β hα hβ h rfl _ _
      (hy α hα) (hy β hβ)).symm)
  set P₀ := closure {g | ∃ α, IsRoot τ α ∧ 0 < height α ∧ y α = g}
  have hmap : P₀.map η = closure {g | ∃ α, IsRoot τ α ∧ 0 < height α ∧ R.x α = g} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨α, hα, hαp, rfl⟩, rfl⟩
      exact ⟨α, hα, hαp, (hy α hα).symm⟩
    · rintro ⟨α, hα, hαp, rfl⟩
      exact ⟨y α, ⟨α, hα, hαp, rfl⟩, hy α hα⟩
  have hSP : S ≤ P₀.map η := hmap ▸ hS
  have : Finite (P₀.map η) := Finite.of_surjective _ (η.subgroupMap_surjective P₀)
  have hbij : Function.Bijective (η.subgroupMap P₀) := by
    refine (η.subgroupMap_surjective P₀).bijective_of_nat_card_le ?_
    calc Nat.card P₀ ≤ 2 ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := hcount
      _ ≤ Nat.card S := hcard
      _ ≤ Nat.card (P₀.map η) := Subgroup.card_le_of_le hSP
  have hinj : ∀ z ∈ P₀, η z = 1 → z = 1 := by
    intro z hz hz1
    have h : η.subgroupMap P₀ ⟨z, hz⟩ = η.subgroupMap P₀ 1 :=
      Subtype.ext (by rw [map_one]; exact hz1)
    exact congrArg Subtype.val (hbij.1 h)
  obtain ⟨SG, hSG⟩ := hSyl
  have hle := OrthogonalSplit.ker_le_of_sylow_le_map η hη hC h2 SG P₀ (by rw [hSG]; exact hSP)
  rw [eq_bot_iff]
  intro z hz
  exact mem_bot.mpr (hinj z (hle hz) hz)

end BinaryRoots

end CFSG.LieType.Chevalley.SimplyLacedCover
