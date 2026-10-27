module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Shape
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Lift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {W : Type*} [AddCommGroup W] {G : Type*} [Group G]

theorem endo_mul_apply (r : G →* AddMonoid.End W) (a b : G) (w : W) :
    r (a * b) w = r a (r b w) := by
  rw [map_mul]; rfl

theorem endo_apply_inv_apply (r : G →* AddMonoid.End W) (a : G) (w : W) :
    r a (r a⁻¹ w) = w := by
  rw [← endo_mul_apply, mul_inv_cancel, map_one]; rfl

theorem endo_inv_apply_apply (r : G →* AddMonoid.End W) (a : G) (w : W) :
    r a⁻¹ (r a w) = w := by
  rw [← endo_mul_apply, inv_mul_cancel, map_one]; rfl

theorem sub_mem_of_perfect (hG : commutator G = ⊤) (r : G →* AddMonoid.End W) (S T : Set W)
    (Z : AddSubgroup W) (hST : ∀ g, ∀ w ∈ S, r g w - w ∈ T)
    (hTZ : ∀ g, ∀ t ∈ T, r g t - t ∈ Z) : ∀ g, ∀ w ∈ S, r g w - w ∈ Z := by
  let δ : G →* Multiplicative (S → W ⧸ Z) :=
    { toFun := fun g => Multiplicative.ofAdd fun w => ((r g w - w : W) : W ⧸ Z)
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext w
        simp
      map_mul' := fun g h => by
        apply Multiplicative.toAdd.injective
        funext w
        simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply, endo_mul_apply]
        rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq]
        have h1 := hTZ g _ (hST h w w.2)
        have h2 : -(r g (r h w) - w) + (r g w - w + (r h w - w)) =
            -(r g (r h w - w) - (r h w - w)) := by
          rw [map_sub]; abel
        rw [h2]
        exact Z.neg_mem h1 }
  intro g w hw
  have hg : g ∈ δ.ker := Abelianization.commutator_subset_ker δ (hG ▸ Subgroup.mem_top g)
  have := congrFun (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 hg)) ⟨w, hw⟩
  exact (QuotientAddGroup.eq_zero_iff _).1 this

theorem apply_eq_of_perfect (hG : commutator G = ⊤) (r : G →* AddMonoid.End W) (S : Set W)
    (hS : ∀ g, ∀ w ∈ S, ∀ g', r g' (r g w - w) = r g w - w) : ∀ g, ∀ w ∈ S, r g w = w := by
  intro g w hw
  have := sub_mem_of_perfect hG r S {t | ∀ g', r g' t = t} ⊥ (fun g w hw g' => hS g w hw g')
    (fun g t ht => by rw [ht g, sub_self]; exact AddSubgroup.zero_mem _) g w hw
  rwa [AddSubgroup.mem_bot, sub_eq_zero] at this

@[expose] def restrictEnd (r : G →* AddMonoid.End W) (Y : AddSubgroup W)
    (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) : G →* AddMonoid.End ↥Y where
  toFun g :=
    { toFun := fun y => ⟨r g (y : W), hY g y y.2⟩
      map_zero' := Subtype.ext (map_zero (r g))
      map_add' := fun y z => Subtype.ext (map_add (r g) (y : W) (z : W)) }
  map_one' := by
    ext y
    change r 1 (y : W) = y
    rw [map_one]; rfl
  map_mul' g h := by
    ext y
    change r (g * h) (y : W) = r g (r h (y : W))
    exact endo_mul_apply r g h y

@[expose] def quotEnd (r : G →* AddMonoid.End W) (Y : AddSubgroup W)
    (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) : G →* AddMonoid.End (W ⧸ Y) where
  toFun g := QuotientAddGroup.map Y Y (r g) fun y hy => hY g y hy
  map_one' := by
    refine AddMonoidHom.ext fun w => ?_
    induction w using QuotientAddGroup.induction_on with
    | H w =>
      change ((r 1 w : W) : W ⧸ Y) = (w : W ⧸ Y)
      rw [map_one]; rfl
  map_mul' g h := by
    refine AddMonoidHom.ext fun w => ?_
    induction w using QuotientAddGroup.induction_on with
    | H w =>
      change ((r (g * h) w : W) : W ⧸ Y) = ((r g (r h w) : W) : W ⧸ Y)
      rw [endo_mul_apply]

theorem quotEnd_mk (r : G →* AddMonoid.End W) (Y : AddSubgroup W)
    (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) (g : G) (w : W) :
    quotEnd r Y hY g (w : W ⧸ Y) = ((r g w : W) : W ⧸ Y) :=
  rfl

theorem isThreeCycle_altLift {m n : ℕ} (ι : Fin m ↪ Fin n) {σ : alternatingGroup (Fin m)}
    (hσ : (σ : Perm (Fin m)).IsThreeCycle) : (altLift ι σ : Perm (Fin n)).IsThreeCycle := by
  classical
  unfold IsThreeCycle at hσ ⊢
  rw [coe_altLift, viaEmbedding]
  convert hσ using 1
  convert cycleType_extendDomain (Equiv.ofInjective ι.1 ι.2) (g := (σ : Perm (Fin m)))

theorem exists_isThreeCycle {m : ℕ} (hm : 3 ≤ m) :
    ∃ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)).IsThreeCycle := by
  set a : Fin m := ⟨0, by omega⟩
  set b : Fin m := ⟨1, by omega⟩
  set c : Fin m := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have h3 := isThreeCycle_swap_mul_swap_same hab hac hbc
  exact ⟨⟨_, h3.mem_alternatingGroup⟩, h3⟩

section Dichotomy

variable {m n : ℕ}

theorem shape_dichotomy (hm : 5 ≤ m) {r : alternatingGroup (Fin m) →* AddMonoid.End W}
    (h : NatShapeA r (alternatingGroup (Fin m)).subtype) (Y : AddSubgroup W)
    (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) :
    (∀ g, ∀ y ∈ Y, r g y = y) ∨ (∀ g w, r g w - w ∈ Y) := by
  have hperf : commutator (alternatingGroup (Fin m)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm)
  obtain ⟨π, hπ, hker, heq⟩ := h.canonical (by omega) fun σ hσ => ⟨⟨σ, hσ⟩, rfl⟩
  let Q : AddSubgroup (altHeart m) := (Y.addSubgroupOf (commA r)).map π
  have hQ : ∀ σ ∈ alternatingGroup (Fin m), ∀ z ∈ Q, altAct σ z ∈ Q := by
    rintro σ hσ _ ⟨u, hu, rfl⟩
    refine ⟨⟨r ⟨σ, hσ⟩ u, apply_mem_commA r _ u.2⟩, hY _ _ hu, ?_⟩
    exact heq ⟨σ, hσ⟩ u _ rfl
  rcases altHeart_irreducible (by omega) Q (fun σ hσ x hx => by
    rw [← altAct_mk]; exact hQ σ hσ _ hx) with hQ0 | hQ1
  ·
    left
    refine apply_eq_of_perfect hperf r Y fun g y hy g' => ?_
    have hmem : r g y - y ∈ commA r := sub_mem_commA r g y
    have hπ0 : π ⟨_, hmem⟩ = 0 := by
      have : π ⟨_, hmem⟩ ∈ Q := ⟨⟨_, hmem⟩, Y.sub_mem (hY g y hy) hy, rfl⟩
      rw [hQ0] at this
      exact (AddSubgroup.mem_bot).1 this
    exact (hker ⟨_, hmem⟩).1 hπ0 g'
  ·
    right
    refine fun g w => sub_mem_of_perfect hperf r Set.univ (commA r) Y
      (fun g w _ => sub_mem_commA r g w) (fun g t ht => ?_) g w (Set.mem_univ w)
    obtain ⟨u, hu, hπu⟩ := (show π ⟨t, ht⟩ ∈ Q from hQ1 ▸ AddSubgroup.mem_top _)
    have hfix : (t - u : W) ∈ fixA r := by
      have := (hker (⟨t, ht⟩ - u)).1 (by rw [map_sub, hπu, sub_self])
      exact this
    have : r g t - t = (r g u - u) + (r g (t - u) - (t - u)) := by
      rw [map_sub]; abel
    rw [this, hfix g, sub_self, add_zero]
    exact Y.sub_mem (hY g u hu) hu

@[expose] def fixSub (r : G →* AddMonoid.End W) (Y : AddSubgroup W)
    (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) : Subgroup G where
  carrier := {g | ∀ y ∈ Y, r g y = y}
  one_mem' := fun y _ => by rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb y hy => by rw [endo_mul_apply, hb y hy, ha y hy]
  inv_mem' := fun {a} ha y hy => by
    have h1 := ha (r a⁻¹ y) (hY _ y hy)
    rw [endo_apply_inv_apply] at h1
    exact h1.symm

theorem conj_mem_fixSub (r : G →* AddMonoid.End W) (Y : AddSubgroup W)
    (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) (g s : G) (hs : s ∈ fixSub r Y hY) :
    g * s * g⁻¹ ∈ fixSub r Y hY := fun y hy => by
  rw [endo_mul_apply, endo_mul_apply, hs _ (hY _ y hy), endo_apply_inv_apply]

@[expose] def cofixSub (r : G →* AddMonoid.End W) (Y : AddSubgroup W) : Subgroup G where
  carrier := {g | ∀ w, r g w - w ∈ Y}
  one_mem' := fun w => by rw [map_one]; exact (sub_self w) ▸ Y.zero_mem
  mul_mem' := fun {a b} ha hb w => by
    have : r (a * b) w - w = (r a (r b w) - r b w) + (r b w - w) := by
      rw [endo_mul_apply]; abel
    rw [this]
    exact Y.add_mem (ha _) (hb w)
  inv_mem' := fun {a} ha w => by
    have h1 := ha (r a⁻¹ w)
    rw [endo_apply_inv_apply] at h1
    have : r a⁻¹ w - w = -(w - r a⁻¹ w) := by abel
    rw [this]
    exact Y.neg_mem h1

theorem conj_mem_cofixSub (r : G →* AddMonoid.End W) (Y : AddSubgroup W)
    (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) (g s : G) (hs : s ∈ cofixSub r Y) :
    g * s * g⁻¹ ∈ cofixSub r Y := fun w => by
  have : r (g * s * g⁻¹) w - w = r g (r s (r g⁻¹ w) - r g⁻¹ w) := by
    rw [endo_mul_apply, endo_mul_apply, map_sub, endo_apply_inv_apply]
  rw [this]
  exact hY g _ (hs _)

theorem alt_dichotomy (hn : 6 ≤ n) (ι : Fin m ↪ Fin n) (hmn : m + 1 = n)
    {r : alternatingGroup (Fin n) →* AddMonoid.End W}
    (h : NatShapeA (r.comp (altLift ι)) (alternatingGroup (Fin m)).subtype) (Y : AddSubgroup W)
    (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) :
    (∀ g, ∀ y ∈ Y, r g y = y) ∨ (∀ g w, r g w - w ∈ Y) := by
  obtain ⟨t, ht⟩ := exists_isThreeCycle (m := m) (by omega)
  have ht' := isThreeCycle_altLift ι ht
  rcases shape_dichotomy (by omega) h Y (fun g y hy => hY _ y hy) with hK | hK
  · left
    have hS := eq_top_of_isThreeCycle_mem (by omega) (fixSub r Y hY)
      (conj_mem_fixSub r Y hY) ht' (hK t)
    intro g y hy
    exact (show g ∈ fixSub r Y hY from hS ▸ Subgroup.mem_top g) y hy
  · right
    have hS := eq_top_of_isThreeCycle_mem (by omega) (cofixSub r Y)
      (conj_mem_cofixSub r Y hY) ht' (hK t)
    intro g w
    exact (show g ∈ cofixSub r Y from hS ▸ Subgroup.mem_top g) w

end Dichotomy

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
