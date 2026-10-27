module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

theorem altHeart_eq_top_of_moved {k : ℕ} (hk : 4 ≤ k) (Y : AddSubgroup (altHeart k))
    (hY : ∀ σ ∈ alternatingGroup (Fin k), ∀ z ∈ Y, altAct σ z ∈ Y)
    (hne : ∃ z ∈ Y, z ≠ 0) : Y = ⊤ := by
  rcases altHeart_irreducible hk Y (fun σ hσ x hx => by rw [← altAct_mk]; exact hY σ hσ _ hx)
    with h | h
  · obtain ⟨z, hz, hz0⟩ := hne
    rw [h] at hz
    exact absurd ((AddSubgroup.mem_bot).1 hz) hz0
  · exact h

theorem exists_altAct_ne {k : ℕ} (hk : 4 ≤ k) :
    ∃ σ ∈ alternatingGroup (Fin k), ∃ z : altHeart k, altAct σ z ≠ z := by
  by_contra h
  push Not at h
  have := altHeart_nontrivial (n := k) (by omega)
  obtain ⟨z, hz⟩ := exists_ne (0 : altHeart k)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  exact hz (altHeart_fixed_eq_zero hk x fun σ hσ => by rw [← altAct_mk]; exact h σ hσ _)

theorem altHeart_eq_zero_of_fixed {k : ℕ} (hk : 4 ≤ k) (z : altHeart k)
    (hz : ∀ σ ∈ alternatingGroup (Fin k), altAct σ z = z) : z = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  exact altHeart_fixed_eq_zero hk x fun σ hσ => by rw [← altAct_mk]; exact hz σ hσ

section Mul

variable {V : Type*} [CommGroup V] {G : Type*} [Group G] {k : ℕ}

@[expose] def NatShape (ρ : G →* MulAut V) (α : G →* Perm (Fin k)) : Prop :=
  ∃ M₀ M₁ : Subgroup V, M₀ ≤ M₁ ∧ (∀ g, ∀ v ∈ M₀, ρ g v = v) ∧ (∀ g v, ρ g v * v⁻¹ ∈ M₁) ∧
    ∃ π : ↥M₁ →* Multiplicative (altHeart k), Function.Surjective π ∧
      π.ker = M₀.subgroupOf M₁ ∧
      ∀ g (u v : ↥M₁), (v : V) = ρ g u →
        Multiplicative.toAdd (π v) = altAct (α g) (Multiplicative.toAdd (π u))

theorem NatShape.comp {G' : Type*} [Group G'] (f : G →* G') {ρ : G' →* MulAut V}
    {α : G' →* Perm (Fin k)} (h : NatShape ρ α) : NatShape (ρ.comp f) (α.comp f) := by
  obtain ⟨M₀, M₁, hM, h₀, h₁, π, hπ, hker, heq⟩ := h
  exact ⟨M₀, M₁, hM, fun g => h₀ (f g), fun g => h₁ (f g), π, hπ, hker, fun g => heq (f g)⟩

theorem isAltNaturalSection_of_natShape {V : Type} [CommGroup V] (hk : 4 ≤ k)
    (L : Subgroup (MulAut V)) (α : ↥L →* alternatingGroup (Fin k)) (hα : Function.Surjective α)
    (h : NatShape L.subtype ((alternatingGroup (Fin k)).subtype.comp α)) :
    IsAltNaturalSection L (commV L) k := by
  obtain ⟨M₀, M₁, hM, h₀, h₁, π, hπ, hker, heq⟩ := h
  have hle : commV L ≤ M₁ := by
    rw [commV, Subgroup.closure_le]
    rintro w ⟨x, hx, v, rfl⟩
    exact h₁ ⟨x, hx⟩ v
  have hinv : ∀ (l : ↥L) (u : V), u ∈ commV L → (l : MulAut V) u ∈ commV L := fun l u hu => by
    have h1 : (l : MulAut V) u * u⁻¹ ∈ commV L := Subgroup.subset_closure ⟨l, l.2, u, rfl⟩
    have h2 := (commV L).mul_mem h1 hu
    rwa [inv_mul_cancel_right] at h2
  let π' : ↥(commV L) →* Multiplicative (altHeart k) := π.comp (Subgroup.inclusion hle)
  have heq' : ∀ (l : ↥L) (u v : ↥(commV L)), (v : V) = (l : MulAut V) (u : V) →
      Multiplicative.toAdd (π' v) =
        altAct ((α l : alternatingGroup (Fin k)) : Perm (Fin k)) (Multiplicative.toAdd (π' u)) :=
    fun l u v huv => heq l (Subgroup.inclusion hle u) (Subgroup.inclusion hle v) huv
  refine ⟨α, hα, π', ?_, ?_, ?_⟩
  ·
    let Y : AddSubgroup (altHeart k) :=
      { carrier := {z | ∃ u : ↥(commV L), Multiplicative.toAdd (π' u) = z}
        add_mem' := by
          rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
          exact ⟨u * v, by rw [map_mul]; rfl⟩
        zero_mem' := ⟨1, by rw [map_one]; rfl⟩
        neg_mem' := by
          rintro _ ⟨u, rfl⟩
          exact ⟨u⁻¹, by rw [map_inv]; rfl⟩ }
    have hY : ∀ σ ∈ alternatingGroup (Fin k), ∀ z ∈ Y, altAct σ z ∈ Y := by
      rintro σ hσ _ ⟨u, rfl⟩
      obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
      refine ⟨⟨(l : MulAut V) u, hinv l u u.2⟩, ?_⟩
      rw [heq' l u _ rfl, hl]
    have hne : ∃ z ∈ Y, z ≠ 0 := by
      obtain ⟨σ, hσ, z, hz⟩ := exists_altAct_ne hk
      obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd z)
      obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
      have hlu : (l : MulAut V) (u : V) ∈ M₁ := by
        have := M₁.mul_mem (h₁ l u) u.2
        rwa [inv_mul_cancel_right] at this
      have hmem : (l : MulAut V) (u : V) * (u : V)⁻¹ ∈ commV L :=
        Subgroup.subset_closure ⟨l, l.2, u, rfl⟩
      have hval : Subgroup.inclusion hle ⟨_, hmem⟩ = ⟨(l : MulAut V) u, hlu⟩ * u⁻¹ :=
        Subtype.ext rfl
      refine ⟨_, ⟨⟨_, hmem⟩, rfl⟩, ?_⟩
      change Multiplicative.toAdd (π (Subgroup.inclusion hle ⟨_, hmem⟩)) ≠ 0
      rw [hval, map_mul, map_inv, toAdd_mul, toAdd_inv, heq l u ⟨_, hlu⟩ rfl, hu, toAdd_ofAdd]
      intro h
      apply hz
      have h2 := congrArg (· + z) h
      simp only [neg_add_cancel_right, zero_add] at h2
      have hσ' : (((alternatingGroup (Fin k)).subtype.comp α) l) = σ := by
        rw [MonoidHom.comp_apply, hl]; rfl
      rwa [hσ'] at h2
    have htop := altHeart_eq_top_of_moved hk Y hY hne
    intro w
    obtain ⟨u, hu⟩ := (show Multiplicative.toAdd w ∈ Y from htop ▸ AddSubgroup.mem_top _)
    exact ⟨u, Multiplicative.toAdd.injective hu⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hu
      refine ⟨u.2, fun x hx => ?_⟩
      have hu' : Subgroup.inclusion hle u ∈ M₀.subgroupOf M₁ := by
        rw [← hker, MonoidHom.mem_ker]; exact hu
      exact h₀ ⟨x, hx⟩ u hu'
    · rintro ⟨-, hfix⟩
      have hz : Multiplicative.toAdd (π' u) = 0 := by
        refine altHeart_eq_zero_of_fixed hk _ fun σ hσ => ?_
        obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
        have := heq' l u u (hfix l l.2).symm
        rw [hl] at this
        exact this.symm
      exact hz
  · intro l u v huv x hx
    rw [heq' l u v huv, hx, altAct_mk]

end Mul

section Add

variable {W : Type*} [AddCommGroup W] {G : Type*} [Group G] {k : ℕ}

@[expose] def fixA (r : G →* AddMonoid.End W) : AddSubgroup W where
  carrier := {w | ∀ g, r g w = w}
  add_mem' := fun ha hb g => by rw [map_add, ha g, hb g]
  zero_mem' := fun g => map_zero (r g)
  neg_mem' := fun ha g => by rw [map_neg, ha g]

@[expose] def commA (r : G →* AddMonoid.End W) : AddSubgroup W :=
  AddSubgroup.closure {w | ∃ g v, r g v - v = w}

theorem sub_mem_commA (r : G →* AddMonoid.End W) (g : G) (v : W) : r g v - v ∈ commA r :=
  AddSubgroup.subset_closure ⟨g, v, rfl⟩

theorem commA_le {r : G →* AddMonoid.End W} {Y : AddSubgroup W} (h : ∀ g v, r g v - v ∈ Y) :
    commA r ≤ Y := by
  rw [commA, AddSubgroup.closure_le]
  rintro w ⟨g, v, rfl⟩
  exact h g v

theorem apply_mem_of_sub_mem {r : G →* AddMonoid.End W} {Y : AddSubgroup W}
    (h : ∀ g v, r g v - v ∈ Y) (g : G) {w : W} (hw : w ∈ Y) : r g w ∈ Y := by
  have := Y.add_mem (h g w) hw
  rwa [sub_add_cancel] at this

theorem apply_mem_commA (r : G →* AddMonoid.End W) (g : G) {w : W} (hw : w ∈ commA r) :
    r g w ∈ commA r :=
  apply_mem_of_sub_mem (sub_mem_commA r) g hw

@[expose] def NatShapeA (r : G →* AddMonoid.End W) (α : G →* Perm (Fin k)) : Prop :=
  ∃ M₀ M₁ : AddSubgroup W, M₀ ≤ M₁ ∧ (∀ g, ∀ w ∈ M₀, r g w = w) ∧ (∀ g w, r g w - w ∈ M₁) ∧
    ∃ π : ↥M₁ →+ altHeart k, Function.Surjective π ∧ π.ker = M₀.addSubgroupOf M₁ ∧
      ∀ g (u v : ↥M₁), (v : W) = r g u → π v = altAct (α g) (π u)

theorem NatShapeA.canonical (hk : 4 ≤ k) {r : G →* AddMonoid.End W} {α : G →* Perm (Fin k)}
    (hα : ∀ σ ∈ alternatingGroup (Fin k), ∃ g, α g = σ) (h : NatShapeA r α) :
    ∃ π : ↥(commA r) →+ altHeart k, Function.Surjective π ∧
      (∀ u : ↥(commA r), π u = 0 ↔ (u : W) ∈ fixA r) ∧
      ∀ g (u v : ↥(commA r)), (v : W) = r g u → π v = altAct (α g) (π u) := by
  obtain ⟨M₀, M₁, hM, h₀, h₁, π, hπ, hker, heq⟩ := h
  have hle : commA r ≤ M₁ := commA_le h₁
  let π' : ↥(commA r) →+ altHeart k := π.comp (AddSubgroup.inclusion hle)
  have heq' : ∀ g (u v : ↥(commA r)), (v : W) = r g u → π' v = altAct (α g) (π' u) :=
    fun g u v huv => heq g (AddSubgroup.inclusion hle u) (AddSubgroup.inclusion hle v) huv
  refine ⟨π', ?_, fun u => ?_, heq'⟩
  · have hY : ∀ σ ∈ alternatingGroup (Fin k), ∀ z ∈ π'.range, altAct σ z ∈ π'.range := by
      rintro σ hσ _ ⟨u, rfl⟩
      obtain ⟨g, rfl⟩ := hα σ hσ
      exact ⟨⟨r g u, apply_mem_commA r g u.2⟩, heq' g u _ rfl⟩
    have hne : ∃ z ∈ π'.range, z ≠ 0 := by
      obtain ⟨σ, hσ, z, hz⟩ := exists_altAct_ne hk
      obtain ⟨u, rfl⟩ := hπ z
      obtain ⟨g, rfl⟩ := hα σ hσ
      have hgu : r g u ∈ M₁ := apply_mem_of_sub_mem h₁ g u.2
      refine ⟨_, ⟨⟨r g u - u, sub_mem_commA r g u⟩, rfl⟩, ?_⟩
      have hval : AddSubgroup.inclusion hle ⟨r g u - u, sub_mem_commA r g u⟩ =
          ⟨r g u, hgu⟩ - u := Subtype.ext rfl
      change π (AddSubgroup.inclusion hle _) ≠ 0
      rw [hval, map_sub, heq g u ⟨_, hgu⟩ rfl, sub_ne_zero]
      exact hz
    have htop := altHeart_eq_top_of_moved hk π'.range hY hne
    intro z
    exact (show z ∈ π'.range from htop ▸ AddSubgroup.mem_top z)
  · constructor
    · intro hu g
      have hu' : AddSubgroup.inclusion hle u ∈ M₀.addSubgroupOf M₁ := by
        rw [← hker, AddMonoidHom.mem_ker]; exact hu
      exact h₀ g u hu'
    · intro hfix
      refine altHeart_eq_zero_of_fixed hk _ fun σ hσ => ?_
      obtain ⟨g, rfl⟩ := hα σ hσ
      exact (heq' g u u (hfix g).symm).symm

variable {V : Type*} [CommGroup V]

@[expose] def autToEnd : MulAut V →* AddMonoid.End (Additive V) where
  toFun φ := (MulEquiv.toAdditive φ).toAddMonoidHom
  map_one' := rfl
  map_mul' _ _ := rfl

theorem natShape_iff_natShapeA (ρ : G →* MulAut V) (α : G →* Perm (Fin k)) :
    NatShape ρ α ↔ NatShapeA (autToEnd.comp ρ) α := by
  constructor
  · rintro ⟨M₀, M₁, hM, h₀, h₁, π, hπ, hker, heq⟩
    let π' : ↥(Subgroup.toAddSubgroup M₁) →+ altHeart k :=
      { toFun := fun u => Multiplicative.toAdd (π ⟨Additive.toMul (u : Additive V), u.2⟩)
        map_zero' := by
          change Multiplicative.toAdd (π 1) = 0
          rw [map_one]; rfl
        map_add' := fun u v => by
          change Multiplicative.toAdd (π (⟨_, u.2⟩ * ⟨_, v.2⟩)) = _
          rw [map_mul]; rfl }
    refine ⟨Subgroup.toAddSubgroup M₀, Subgroup.toAddSubgroup M₁, fun x hx => hM hx,
      fun g w hw => congrArg Additive.ofMul (h₀ g _ hw), fun g w => by
        change ρ g (Additive.toMul w) / Additive.toMul w ∈ M₁
        rw [div_eq_mul_inv]
        exact h₁ g (Additive.toMul w),
      π', fun z => ?_, ?_, fun g u v huv => heq g ⟨_, u.2⟩ ⟨_, v.2⟩ (congrArg Additive.toMul huv)⟩
    · obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd z)
      exact ⟨⟨Additive.ofMul (u : V), u.2⟩, by
        change Multiplicative.toAdd (π ⟨(u : V), u.2⟩) = z
        rw [hu]; rfl⟩
    · ext u
      rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
      have := congrArg (fun H : Subgroup ↥M₁ => (⟨Additive.toMul (u : Additive V), u.2⟩ : ↥M₁) ∈ H)
        hker
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, eq_iff_iff] at this
      exact this
  · rintro ⟨M₀, M₁, hM, h₀, h₁, π, hπ, hker, heq⟩
    let π' : ↥(AddSubgroup.toSubgroup' M₁) →* Multiplicative (altHeart k) :=
      { toFun := fun u => Multiplicative.ofAdd (π ⟨Additive.ofMul (u : V), u.2⟩)
        map_one' := by
          change Multiplicative.ofAdd (π 0) = 1
          rw [map_zero]; rfl
        map_mul' := fun u v => by
          change Multiplicative.ofAdd (π (⟨_, u.2⟩ + ⟨_, v.2⟩)) = _
          rw [map_add]; rfl }
    refine ⟨AddSubgroup.toSubgroup' M₀, AddSubgroup.toSubgroup' M₁, fun x hx => hM hx,
      fun g v hv => congrArg Additive.toMul (h₀ g _ hv), fun g v => by
        have := h₁ g (Additive.ofMul v)
        change Additive.ofMul (ρ g v / v) ∈ M₁ at this
        rwa [div_eq_mul_inv] at this,
      π', fun z => ?_, ?_, fun g u v huv => heq g ⟨_, u.2⟩ ⟨_, v.2⟩ (congrArg Additive.ofMul huv)⟩
    · obtain ⟨u, hu⟩ := hπ (Multiplicative.toAdd z)
      exact ⟨⟨Additive.toMul (u : Additive V), u.2⟩, by
        change Multiplicative.ofAdd (π ⟨(u : Additive V), u.2⟩) = z
        rw [hu]; rfl⟩
    · ext u
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have := congrArg (fun H : AddSubgroup ↥M₁ =>
        (⟨Additive.ofMul (u : V), u.2⟩ : ↥M₁) ∈ H) hker
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, eq_iff_iff] at this
      exact this

end Add

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
