module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.Semidihedral

universe u

variable {G : Type u} [Group G]

theorem centralHall_commute {A : Subgroup G} (hA : A ≤ Subgroup.center G)
    {a g : G} (ha : a ∈ A) : Commute a g := by
  change a * g = g * a
  exact (Subgroup.mem_center_iff.mp (hA ha) g).symm

@[expose] noncomputable def centralHallComplement (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) : Subgroup G :=
  letI : A.Normal := Subgroup.normal_of_le_center hA
  Classical.choose (Subgroup.exists_right_complement'_of_coprime hcop)

theorem centralHallComplement_isComplement (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) :
    A.IsComplement' (centralHallComplement A hA hcop) := by
  let : A.Normal := Subgroup.normal_of_le_center hA
  exact Classical.choose_spec (Subgroup.exists_right_complement'_of_coprime hcop)

theorem centralHallComplement_card (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) :
    Nat.card (centralHallComplement A hA hcop) = A.index :=
  (centralHallComplement_isComplement A hA hcop).symm.index_eq_card.symm

theorem centralHallComplement_mem_iff (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) (g : G) :
    g ∈ centralHallComplement A hA hcop ↔ g ^ A.index = 1 := by
  let K := centralHallComplement A hA hcop
  have hcard : Nat.card K = A.index := centralHallComplement_card A hA hcop
  have hpow (k : K) : (k : G) ^ A.index = 1 := by
    have hk := congrArg (fun x : K => (x : G)) (pow_card_eq_one' (x := k))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hcard] using hk
  change g ∈ K ↔ g ^ A.index = 1
  constructor
  · intro hg
    exact hpow ⟨g, hg⟩
  · intro hg
    obtain ⟨⟨a, k⟩, rfl⟩ := (centralHallComplement_isComplement A hA hcop).2 g
    rw [(centralHall_commute hA a.property).mul_pow, hpow k, mul_one] at hg
    have ha : a ^ A.index = 1 := Subtype.ext hg
    have ha1 : a = 1 :=
      (pow_eq_one_iff_of_coprime hcop).mp ⟨pow_card_eq_one', ha⟩
    simp [ha1]

instance centralHallComplement_characteristic (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) :
    (centralHallComplement A hA hcop).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro e g hg
  change e g ∈ centralHallComplement A hA hcop
  apply (centralHallComplement_mem_iff A hA hcop (e g)).mpr
  simpa only [map_pow, map_one] using
    congrArg e ((centralHallComplement_mem_iff A hA hcop g).mp hg)

instance centralHallComplement_normal (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) :
    (centralHallComplement A hA hcop).Normal := inferInstance

theorem centralHallComplement_unique [Finite G] (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index)
    (L : Subgroup G) (hL : Nat.card L = A.index) :
    L = centralHallComplement A hA hcop := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro g hg
    apply (centralHallComplement_mem_iff A hA hcop g).mpr
    have hpow := congrArg (fun x : L => (x : G))
      (pow_card_eq_one' (x := (⟨g, hg⟩ : L)))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hL] using hpow
  · exact Nat.le_of_eq ((centralHallComplement_card A hA hcop).trans hL.symm)

theorem centralHallComplement_sup (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) :
    A ⊔ centralHallComplement A hA hcop = ⊤ :=
  (centralHallComplement_isComplement A hA hcop).sup_eq_top

theorem centralHallComplement_inf (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) :
    A ⊓ centralHallComplement A hA hcop = ⊥ :=
  (centralHallComplement_isComplement A hA hcop).isCompl.inf_eq_bot

theorem centralHallComplement_commutator (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) :
    ⁅A, centralHallComplement A hA hcop⁆ = ⊥ :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hA.trans (Subgroup.center_le_centralizer _))

@[expose] noncomputable def centralHallComplementMulEquiv (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) :
    A × centralHallComplement A hA hcop ≃* G :=
  MulEquiv.ofBijective
    (A.subtype.noncommCoprod (centralHallComplement A hA hcop).subtype
      (fun a _ => centralHall_commute hA a.property))
    (centralHallComplement_isComplement A hA hcop)

theorem centralHallComplementMulEquiv_apply (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index)
    (a : A) (k : centralHallComplement A hA hcop) :
    centralHallComplementMulEquiv A hA hcop (a, k) = (a : G) * (k : G) := rfl

theorem centralHallComplement_bot :
    centralHallComplement (⊥ : Subgroup G) bot_le (by simp) = ⊤ :=
  Subgroup.isComplement'_bot_left.mp (centralHallComplement_isComplement _ _ _)

theorem centralHallComplement_top (hG : (⊤ : Subgroup G) ≤ Subgroup.center G) :
    centralHallComplement (⊤ : Subgroup G) hG (by simp) = ⊥ :=
  Subgroup.isComplement'_top_left.mp (centralHallComplement_isComplement _ _ _)

theorem central_hall_subgroup_direct_complement [Finite G] (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hcop : (Nat.card A).Coprime A.index) :
    ∃ K : Subgroup G,
      K.Characteristic ∧ Nat.card K = A.index ∧
      A.IsComplement' K ∧ A ⊔ K = ⊤ ∧ A ⊓ K = ⊥ ∧
      (∀ a ∈ A, ∀ k ∈ K, Commute a k) ∧ ⁅A, K⁆ = ⊥ ∧
      (∀ L : Subgroup G, Nat.card L = A.index → L = K) ∧
      (∀ g : G, g ∈ K ↔ g ^ A.index = 1) ∧
      ∃ e : A × K ≃* G, ∀ (a : A) (k : K), e (a, k) = (a : G) * (k : G) := by
  refine ⟨centralHallComplement A hA hcop, inferInstance,
    centralHallComplement_card A hA hcop,
    centralHallComplement_isComplement A hA hcop,
    centralHallComplement_sup A hA hcop,
    centralHallComplement_inf A hA hcop, ?_,
    centralHallComplement_commutator A hA hcop,
    centralHallComplement_unique A hA hcop,
    centralHallComplement_mem_iff A hA hcop,
    centralHallComplementMulEquiv A hA hcop,
    centralHallComplementMulEquiv_apply A hA hcop⟩
  exact fun _ ha _ _ => centralHall_commute hA ha

end CFSG.Semidihedral
