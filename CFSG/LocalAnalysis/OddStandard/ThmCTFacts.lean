module

public import CFSG.LocalAnalysis.OddStandard.ThmCDefs
public import CFSG.LocalAnalysis.OddStandard.ThmCTGen

public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

theorem orderOf_eq_two_iff_sq {G : Type*} [Group G] {x : G} :
    orderOf x = 2 ↔ x * x = 1 ∧ x ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff, pow_two]

section Equiv

variable {P Q : Type*} [Group P] [Group Q]

theorem mem_center_equiv_iff (e : P ≃* Q) (x : P) :
    x ∈ Subgroup.center P ↔ e x ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h q
    obtain ⟨p, rfl⟩ := e.surjective q
    rw [← map_mul, ← map_mul, h p]
  · intro h p
    apply e.injective
    rw [map_mul, map_mul, h (e p)]

theorem card_comap_equiv (e : P ≃* Q) (H : Subgroup Q) :
    Nat.card (H.comap e.toMonoidHom) = Nat.card H :=
  Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun _ => Iff.rfl)

end Equiv

structure IsTwoE16 (P : Type*) [Group P] (A B : Subgroup P) : Prop where
  normal_left : A.Normal
  normal_right : B.Normal
  inf_eq : A ⊓ B = Subgroup.center P
  sup_eq : A ⊔ B = ⊤
  ne : A ≠ B
  card_center : Nat.card (Subgroup.center P) = 4
  card_left : Nat.card A = 16
  card_right : Nat.card B = 16
  sq_left : ∀ x ∈ A, x * x = 1
  sq_right : ∀ x ∈ B, x * x = 1
  comm_left : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  comm_right : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x
  sq_iff : ∀ x : P, x * x = 1 ↔ x ∈ A ∨ x ∈ B
  le_or : ∀ E : Subgroup P, (∀ x ∈ E, x * x = 1) → E ≤ A ∨ E ≤ B
  card_le : ∀ E : Subgroup P, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 16
  eq_or : ∀ E : Subgroup P, (∀ x ∈ E, x * x = 1) → Nat.card E = 16 → E = A ∨ E = B
  centralizer_left : ∀ x ∈ A, x ∉ Subgroup.center P → Subgroup.centralizer ({x} : Set P) = A
  centralizer_right : ∀ x ∈ B, x ∉ Subgroup.center P → Subgroup.centralizer ({x} : Set P) = B
  swap : ∃ φ : P ≃* P, A.comap φ.toMonoidHom = B

section Transport

variable {P : Type*} [Group P] (e : P ≃* Tc)

include e

theorem finite_of_equiv : Finite P := Finite.of_equiv Tc e.symm.toEquiv

theorem card_eq_of_equiv : Nat.card P = 64 := by
  rw [Nat.card_congr e.toEquiv]; exact card_Tc

theorem mem_center_of_equiv (x : P) :
    x ∈ Subgroup.center P ↔ (e x).a = 0 ∧ (e x).b = 0 :=
  (mem_center_equiv_iff e x).trans (mem_center_iff _)

theorem card_center_of_equiv : Nat.card (Subgroup.center P) = 4 :=
  (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (mem_center_equiv_iff e))).trans card_center

theorem sq_mem_center_of_equiv (x : P) : x * x ∈ Subgroup.center P := by
  rw [mem_center_equiv_iff e, map_mul]
  exact sq_mem_center _

theorem commutator_mem_center_of_equiv (x y : P) : ⁅x, y⁆ ∈ Subgroup.center P := by
  rw [mem_center_equiv_iff e, map_commutatorElement]
  exact commutator_mem_center _ _

theorem sq_eq_one_of_mem_center_of_equiv {z : P} (hz : z ∈ Subgroup.center P) : z * z = 1 := by
  apply e.injective
  rw [map_mul, map_one]
  exact sq_eq_one_of_mem_center ((mem_center_equiv_iff e z).1 hz)

theorem card_involutions_of_equiv : Nat.card {x : P // x * x = 1 ∧ x ≠ 1} = 27 := by
  rw [← card_involutions]
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
  show x * x = 1 ∧ x ≠ 1 ↔ e x * e x = 1 ∧ e x ≠ 1
  rw [← map_mul, MulEquiv.map_eq_one_iff, Ne, Ne, MulEquiv.map_eq_one_iff]

theorem isTwoE16_of_equiv : IsTwoE16 P (A.comap e.toMonoidHom) (B.comap e.toMonoidHom) where
  normal_left := A_normal.comap _
  normal_right := B_normal.comap _
  inf_eq := by
    ext x
    rw [Subgroup.mem_inf, mem_center_of_equiv e x]
    exact and_comm
  sup_eq := by
    have h : (MulEquiv.comapSubgroup e) (A ⊔ B) =
        (MulEquiv.comapSubgroup e) A ⊔ (MulEquiv.comapSubgroup e) B :=
      (MulEquiv.comapSubgroup e).map_sup A B
    rw [A_sup_B, (MulEquiv.comapSubgroup e).map_top] at h
    exact h.symm
  ne := fun h => A_ne_B ((MulEquiv.comapSubgroup e).injective h)
  card_center := card_center_of_equiv e
  card_left := (card_comap_equiv e A).trans card_A
  card_right := (card_comap_equiv e B).trans card_B
  sq_left := fun x hx => e.injective (by
    rw [map_mul, map_one]
    exact sq_eq_one_of_mem_A hx)
  sq_right := fun x hx => e.injective (by
    rw [map_mul, map_one]
    exact sq_eq_one_of_mem_B hx)
  comm_left := fun x hx y hy => by
    have hx' : (e x).b = 0 := hx
    have hy' : (e y).b = 0 := hy
    apply e.injective
    rw [map_mul, map_mul, commute_iff, hx', hy']
    simp
  comm_right := fun x hx y hy => by
    have hx' : (e x).a = 0 := hx
    have hy' : (e y).a = 0 := hy
    apply e.injective
    rw [map_mul, map_mul, commute_iff, hx', hy']
    simp
  sq_iff := fun x => by
    have h := sq_eq_one_iff_mem (e x)
    rw [← map_mul, ← map_one e, e.injective.eq_iff] at h
    exact h
  le_or := fun E hE => by
    have h : ∀ y ∈ E.map e.toMonoidHom, y * y = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hE x hx, map_one]
    rcases elemAbelian_le_or h with h1 | h1
    · exact Or.inl (Subgroup.map_le_iff_le_comap.1 h1)
    · exact Or.inr (Subgroup.map_le_iff_le_comap.1 h1)
  card_le := fun E hE => by
    have h : ∀ y ∈ E.map e.toMonoidHom, y * y = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hE x hx, map_one]
    have := card_le_sixteen h
    rwa [Subgroup.card_map_of_injective e.injective] at this
  eq_or := fun E hE hc => by
    have h : ∀ y ∈ E.map e.toMonoidHom, y * y = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hE x hx, map_one]
    have hc' : Nat.card (E.map e.toMonoidHom) = 16 := by
      rw [Subgroup.card_map_of_injective e.injective, hc]
    have hE' : E = (E.map e.toMonoidHom).comap e.toMonoidHom :=
      (Subgroup.comap_map_eq_self_of_injective e.injective E).symm
    rcases eq_A_or_B h hc' with h1 | h1
    · exact Or.inl (by rw [hE', h1])
    · exact Or.inr (by rw [hE', h1])
  centralizer_left := fun x hx hxZ => by
    have hxA : e x ∈ A := hx
    have h := centralizer_of_mem_A hxA ((mem_center_equiv_iff e x).not.1 hxZ)
    ext y
    have h1 : e y ∈ Subgroup.centralizer ({e x} : Set Tc) ↔ e y ∈ A := by rw [h]
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    rw [← e.injective.eq_iff, map_mul, map_mul]
    exact h1
  centralizer_right := fun x hx hxZ => by
    have hxB : e x ∈ B := hx
    have h := centralizer_of_mem_B hxB ((mem_center_equiv_iff e x).not.1 hxZ)
    ext y
    have h1 : e y ∈ Subgroup.centralizer ({e x} : Set Tc) ↔ e y ∈ B := by rw [h]
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    rw [← e.injective.eq_iff, map_mul, map_mul]
    exact h1
  swap := ⟨(e.trans swap).trans e.symm, by
    ext x
    show (e ((e.trans swap).trans e.symm x)).b = 0 ↔ (e x).a = 0
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact swap_mem_A_iff⟩

theorem normal_dichotomy_of_equiv {N : Subgroup P} (hN : N.Normal) :
    N ≤ Subgroup.center P ∨ Subgroup.center P ≤ N := by
  have hN' : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
  rcases normal_dichotomy hN' with h | h
  · left
    intro x hx
    exact (mem_center_equiv_iff e x).2 (h (Subgroup.mem_map_of_mem e.toMonoidHom hx))
  · right
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 (h ((mem_center_equiv_iff e z).1 hz))
    have : y = z := e.injective hyz
    rwa [← this]

theorem gen4_of_equiv (Q : Subgroup P) :
    ∃ s : Finset P, s.card ≤ 4 ∧ Subgroup.closure (s : Set P) = Q := by
  classical
  obtain ⟨s, hs, hsQ⟩ := gen4 (Q.map e.toMonoidHom)
  refine ⟨s.image e.symm, Finset.card_image_le.trans hs, ?_⟩
  have h1 : (Subgroup.closure (s : Set Tc)).map e.symm.toMonoidHom =
      Subgroup.closure (e.symm '' (s : Set Tc)) := MonoidHom.map_closure _ _
  rw [Finset.coe_image, ← h1, hsQ, Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id P := by ext x; simp
  rw [this, Subgroup.map_id]

end Transport

abbrev IsT (P : Type*) [Group P] : Prop := Nonempty (P ≃* SylSL3_4)

theorem IsT.nonempty_equiv {P : Type*} [Group P] (hT : IsT P) : Nonempty (P ≃* Tc) :=
  hT.map fun e => e.trans sylLCongr

section Syl

variable {P : Type*} [Group P] (hT : IsT P)

include hT

theorem IsT.finite : Finite P := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact finite_of_equiv e

theorem IsT.card_eq : Nat.card P = 64 := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact card_eq_of_equiv e

theorem IsT.card_center : Nat.card (Subgroup.center P) = 4 := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact card_center_of_equiv e

theorem IsT.sq_mem_center (x : P) : x * x ∈ Subgroup.center P := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact sq_mem_center_of_equiv e x

theorem IsT.commutator_mem_center (x y : P) : ⁅x, y⁆ ∈ Subgroup.center P := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact commutator_mem_center_of_equiv e x y

theorem IsT.sq_eq_one_of_mem_center {z : P} (hz : z ∈ Subgroup.center P) : z * z = 1 := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact sq_eq_one_of_mem_center_of_equiv e hz

theorem IsT.card_involutions : Nat.card {x : P // x * x = 1 ∧ x ≠ 1} = 27 := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact card_involutions_of_equiv e

theorem IsT.exists_twoE16 : ∃ A B : Subgroup P, IsTwoE16 P A B := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact ⟨_, _, isTwoE16_of_equiv e⟩

theorem IsT.normal_dichotomy {N : Subgroup P} (hN : N.Normal) :
    N ≤ Subgroup.center P ∨ Subgroup.center P ≤ N := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact normal_dichotomy_of_equiv e hN

theorem IsT.gen4 (Q : Subgroup P) :
    ∃ s : Finset P, s.card ≤ 4 ∧ Subgroup.closure (s : Set P) = Q := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  exact gen4_of_equiv e Q

theorem IsT.exists_involution_not_mem {E : Subgroup P} (hE : ∀ x ∈ E, x * x = 1) :
    ∃ x : P, x * x = 1 ∧ x ≠ 1 ∧ x ∉ E := by
  by_contra hcon
  push Not at hcon
  have := hT.finite
  obtain ⟨A, B, hAB⟩ := hT.exists_twoE16
  have h16 := hAB.card_le E hE
  have hle : Nat.card {x : P // x * x = 1 ∧ x ≠ 1} ≤ Nat.card E :=
    Nat.card_le_card_of_injective (fun x => ⟨x.1, hcon x.1 x.2.1 x.2.2⟩)
      (fun a b hab => Subtype.ext (congrArg (fun y : E => (y : P)) hab))
  rw [hT.card_involutions] at hle
  omega

theorem IsT.exists_central_involution :
    ∃ z : P, z ∈ Subgroup.center P ∧ z * z = 1 ∧ z ≠ 1 := by
  have hne : Subgroup.center P ≠ ⊥ := by
    intro h
    have := hT.card_center
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  exact ⟨z, z.2, hT.sq_eq_one_of_mem_center z.2, fun h => hz (Subtype.ext h)⟩

end Syl

theorem tFacts : TFacts where
  elem16 := by
    obtain ⟨A', B', hAB⟩ : ∃ A B : Subgroup SylSL3_4, IsTwoE16 SylSL3_4 A B :=
      IsT.exists_twoE16 ⟨MulEquiv.refl _⟩
    refine ⟨A', ⟨⟨⟨fun x y => Subtype.ext (hAB.comm_left x x.2 y y.2)⟩⟩, fun x hx => ?_⟩,
      hAB.card_left⟩
    rw [pow_two]
    exact hAB.sq_left x hx
  gen4 := IsT.gen4 ⟨MulEquiv.refl _⟩

end CFSG.OddStandard.ThmC.T
