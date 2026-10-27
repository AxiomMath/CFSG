module

public import CFSG.CGT.PushingUpLit.CGT6.RouteCDefs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Quasithin.Background.Module

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.SectionRank.Ccomm
open scoped Matrix

section Coord

variable {V : Type} [CommGroup V]

theorem exists_coord [Finite V] (hV : ∀ v : V, v ^ 2 = 1) :
    ∃ n : ℕ, Nonempty (V ≃* Multiplicative (Fin n → ZMod 2)) := by
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by simp [hV v]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV2
  exact ⟨n, nonempty_mulEquiv_of_elementary (p := 2) mul_comm (fun a => by simpa using hV a) hn⟩

end Coord

section Comm

variable {V : Type} [CommGroup V]

@[expose] def commHom (a : MulAut V) : V →* V where
  toFun v := a v * v⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem commHom_apply (a : MulAut V) (v : V) : commHom a v = a v * v⁻¹ := rfl

theorem commV_zpowers_eq_range (a : MulAut V) :
    commV (Subgroup.zpowers a) = (commHom a).range := by
  apply le_antisymm
  · set R := (commHom a).range with hR
    let H : Subgroup (MulAut V) :=
      { carrier := {b | ∀ v, b v * v⁻¹ ∈ R}
        one_mem' := fun v => by simp
        mul_mem' := fun {b c} hb hc v => by
          have e : (b * c) v * v⁻¹ = (b (c v) * (c v)⁻¹) * (c v * v⁻¹) := by
            simp only [MulAut.mul_apply]
            group
          rw [e]
          exact R.mul_mem (hb _) (hc v)
        inv_mem' := fun {b} hb v => by
          have h1 := hb (b⁻¹ v)
          have e : b⁻¹ v * v⁻¹ = (b (b⁻¹ v) * (b⁻¹ v)⁻¹)⁻¹ := by
            rw [MulAut.apply_inv_self]
            group
          rw [e]
          exact R.inv_mem h1 }
    have hzH : Subgroup.zpowers a ≤ H :=
      (Subgroup.zpowers_le (g := a) (H := H)).mpr fun v => ⟨v, rfl⟩
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    exact hzH hx v
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, v, rfl⟩

variable {n : ℕ} (e : V ≃* Multiplicative (Fin n → ZMod 2))

abbrev coord (v : V) : Fin n → ZMod 2 := Multiplicative.toAdd (e v)

theorem coord_injective : Function.Injective (coord e) := fun _ _ h =>
  e.injective (Multiplicative.toAdd.injective h)

theorem coord_mul (x y : V) : coord e (x * y) = coord e x + coord e y := by
  simp [coord]

theorem coord_inv (x : V) : coord e x⁻¹ = -coord e x := by
  rw [coord, coord, map_inv, toAdd_inv]

theorem exists_coord_eq (u : Fin n → ZMod 2) : ∃ x : V, coord e x = u :=
  ⟨e.symm (Multiplicative.ofAdd u), by simp [coord]⟩

theorem mulVec_coord (a : MulAut V) (v : V) :
    (elemAutEquivGL e a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ coord e v = coord e (a v) :=
  elemAutEquivGL_mulVec e a v

theorem coord_commHom (a : MulAut V) (v : V) :
    coord e (commHom a v) =
      ((elemAutEquivGL e a : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ coord e v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, mulVec_coord, commHom_apply, coord_mul, coord_inv]
  abel

theorem mem_commV_zpowers_iff (a : MulAut V) (x : V) :
    x ∈ commV (Subgroup.zpowers a) ↔ coord e x ∈ imSubOne (elemAutEquivGL e a) := by
  rw [commV_zpowers_eq_range, imSubOne, LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨coord e v, by rw [Matrix.mulVecLin_apply, ← coord_commHom]⟩
  · rintro ⟨c, hc⟩
    obtain ⟨v, rfl⟩ := exists_coord_eq e c
    refine ⟨v, coord_injective e ?_⟩
    rw [coord_commHom, ← hc, Matrix.mulVecLin_apply]

theorem card_commV_zpowers (a : MulAut V) :
    Nat.card ↥(commV (Subgroup.zpowers a)) =
      2 ^ Module.finrank (ZMod 2) ↥(imSubOne (elemAutEquivGL e a)) := by
  have h1 : Nat.card ↥(commV (Subgroup.zpowers a)) =
      Nat.card ↥(imSubOne (elemAutEquivGL e a)) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x => ⟨coord e x, (mem_commV_zpowers_iff e a x).mp x.2⟩) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext (coord_injective e (congrArg Subtype.val hxy))
    · rintro ⟨u, hu⟩
      obtain ⟨x, rfl⟩ := exists_coord_eq e u
      exact ⟨⟨x, (mem_commV_zpowers_iff e a x).mpr hu⟩, rfl⟩
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := ↥(imSubOne (elemAutEquivGL e a))), Nat.card_zmod]

theorem finrank_imSubOne_of_card_commV (a : MulAut V)
    (h : Nat.card ↥(commV (Subgroup.zpowers a)) = 4) :
    Module.finrank (ZMod 2) ↥(imSubOne (elemAutEquivGL e a)) = 2 := by
  rw [card_commV_zpowers e] at h
  exact Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num : 4 = 2 ^ 2))

theorem imSubOne_sup_eq_top (y d t : MulAut V)
    (h : commV (Subgroup.zpowers y) ⊔ commV (Subgroup.zpowers d) ⊔
      commV (Subgroup.zpowers t) = ⊤) :
    imSubOne (elemAutEquivGL e y) ⊔ imSubOne (elemAutEquivGL e d) ⊔
      imSubOne (elemAutEquivGL e t) = ⊤ := by
  set S := imSubOne (elemAutEquivGL e y) ⊔ imSubOne (elemAutEquivGL e d) ⊔
    imSubOne (elemAutEquivGL e t) with hS
  let K : Subgroup V :=
    { carrier := {x | coord e x ∈ S}
      one_mem' := by simp [coord, S.zero_mem]
      mul_mem' := fun {a b} ha hb => by
        show coord e (a * b) ∈ S
        rw [coord_mul]
        exact S.add_mem ha hb
      inv_mem' := fun {a} ha => by
        show coord e a⁻¹ ∈ S
        rw [coord_inv]
        exact S.neg_mem ha }
  have hle : commV (Subgroup.zpowers y) ⊔ commV (Subgroup.zpowers d) ⊔
      commV (Subgroup.zpowers t) ≤ K := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      exact Submodule.mem_sup_left (Submodule.mem_sup_left
        ((mem_commV_zpowers_iff e y x).mp hx))
    · intro x hx
      exact Submodule.mem_sup_left (Submodule.mem_sup_right
        ((mem_commV_zpowers_iff e d x).mp hx))
    · intro x hx
      exact Submodule.mem_sup_right ((mem_commV_zpowers_iff e t x).mp hx)
  rw [h] at hle
  rw [eq_top_iff]
  intro u _
  obtain ⟨x, rfl⟩ := exists_coord_eq e u
  exact hle (Subgroup.mem_top x)

end Comm

end CFSG.CGT.PushingUpLit.CGT6
