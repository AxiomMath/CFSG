module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.GH74.GLS.Stage1.Thm6

open Subgroup

abbrev C4 : Type := Multiplicative (ZMod 4)
abbrev C2 : Type := Multiplicative (ZMod 2)
abbrev N4 : Type := C4 × C4
abbrev G2 : Type := C2 × C2

theorem mem_zpowers_c4 (x : C4) : x ∈ zpowers (Multiplicative.ofAdd (1 : ZMod 4)) := by
  refine ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
  simp [← ofAdd_zsmul]

theorem mem_zpowers_c2 (x : C2) : x ∈ zpowers (Multiplicative.ofAdd (1 : ZMod 2)) := by
  refine ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
  simp [← ofAdd_zsmul]

theorem orderOf_c4 : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem orderOf_c2 : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

noncomputable def hom4 {S : Type*} [Group S] (s : S) (hs : s ^ 4 = 1) : C4 →* S :=
  monoidHomOfForallMemZpowers (g := Multiplicative.ofAdd (1 : ZMod 4)) mem_zpowers_c4
    (g' := s) (by rw [orderOf_c4]; exact orderOf_dvd_of_pow_eq_one hs)

noncomputable def hom2 {S : Type*} [Group S] (s : S) (hs : s ^ 2 = 1) : C2 →* S :=
  monoidHomOfForallMemZpowers (g := Multiplicative.ofAdd (1 : ZMod 2)) mem_zpowers_c2
    (g' := s) (by rw [orderOf_c2]; exact orderOf_dvd_of_pow_eq_one hs)

theorem hom4_gen {S : Type*} [Group S] (s : S) (hs : s ^ 4 = 1) :
    hom4 s hs (Multiplicative.ofAdd 1) = s := monoidHomOfForallMemZpowers_apply_gen _ _

theorem hom2_gen {S : Type*} [Group S] (s : S) (hs : s ^ 2 = 1) :
    hom2 s hs (Multiplicative.ofAdd 1) = s := monoidHomOfForallMemZpowers_apply_gen _ _

def swapAut : MulAut N4 := MulEquiv.prodComm
def invAut : MulAut N4 := MulEquiv.inv N4

theorem swapAut_sq : swapAut ^ 2 = 1 := by
  ext n <;> simp [swapAut, pow_two]
theorem invAut_sq : invAut ^ 2 = 1 := by
  ext n <;> simp [invAut, pow_two]
theorem swap_inv_comm : Commute swapAut invAut := by
  ext n <;> simp [swapAut, invAut]

@[expose] def prodHom {A B S : Type*} [Group A] [Group B] [Group S] (f : A →* S) (g : B →* S)
    (h : ∀ a b, Commute (f a) (g b)) : A × B →* S :=
  MonoidHom.mk' (fun p => f p.1 * g p.2) (by
    intro p q
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    calc f p.1 * f q.1 * (g p.2 * g q.2) = f p.1 * (f q.1 * g p.2) * g q.2 := by group
      _ = f p.1 * (g p.2 * f q.1) * g q.2 := by rw [(h q.1 p.2).eq]
      _ = f p.1 * g p.2 * (f q.1 * g q.2) := by group)

theorem prodHom_apply {A B S : Type*} [Group A] [Group B] [Group S] (f : A →* S) (g : B →* S)
    (h : ∀ a b, Commute (f a) (g b)) (p : A × B) : prodHom f g h p = f p.1 * g p.2 := rfl

theorem commute_hom2_hom2 {S : Type*} [Group S] (s t : S) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hst : Commute s t) (a b : C2) : Commute (hom2 s hs a) (hom2 t ht b) := by
  obtain ⟨i, rfl⟩ := mem_zpowers_c2 a
  obtain ⟨j, rfl⟩ := mem_zpowers_c2 b
  rw [map_zpow, map_zpow, hom2_gen, hom2_gen]
  exact hst.zpow_zpow i j

noncomputable def phi : G2 →* MulAut N4 :=
  prodHom (hom2 swapAut swapAut_sq) (hom2 invAut invAut_sq)
    (commute_hom2_hom2 _ _ _ _ swap_inv_comm)

theorem card_model : Nat.card (N4 ⋊[phi] G2) = 64 := by
  rw [Nat.card_congr SemidirectProduct.equivProd]
  simp

structure M12Struct {S : Type*} [Group S] (a b y x : S) : Prop where
  ha : a ^ 4 = 1
  hb : b ^ 4 = 1
  hab : Commute a b
  hy : y ^ 2 = 1
  hx : x ^ 2 = 1
  hyx : Commute y x
  hya : y * a * y⁻¹ = b
  hyb : y * b * y⁻¹ = a
  hxa : x * a * x⁻¹ = a⁻¹
  hxb : x * b * x⁻¹ = b⁻¹
  gen : Subgroup.closure ({a, b, y, x} : Set S) = ⊤

theorem commute_hom4_hom4 {S : Type*} [Group S] (s t : S) (hs : s ^ 4 = 1) (ht : t ^ 4 = 1)
    (hst : Commute s t) (a b : C4) : Commute (hom4 s hs a) (hom4 t ht b) := by
  obtain ⟨i, rfl⟩ := mem_zpowers_c4 a
  obtain ⟨j, rfl⟩ := mem_zpowers_c4 b
  rw [map_zpow, map_zpow, hom4_gen, hom4_gen]
  exact hst.zpow_zpow i j

theorem hom_ext_prod {A B S : Type*} [Group A] [Group B] [Group S] {f g : A × B →* S}
    (h1 : ∀ a, f (a, 1) = g (a, 1)) (h2 : ∀ b, f (1, b) = g (1, b)) : f = g := by
  refine MonoidHom.ext fun p => ?_
  have : p = (p.1, 1) * (1, p.2) := by simp
  rw [this, map_mul, map_mul, h1, h2]

section Lift

variable {S : Type*} [Group S] {a b y x : S}

@[expose] noncomputable def liftN (h : M12Struct a b y x) : N4 →* S :=
  prodHom (hom4 a h.ha) (hom4 b h.hb) (commute_hom4_hom4 _ _ _ _ h.hab)

@[expose] noncomputable def liftG (h : M12Struct a b y x) : G2 →* S :=
  prodHom (hom2 y h.hy) (hom2 x h.hx) (commute_hom2_hom2 _ _ _ _ h.hyx)

theorem liftN_apply (h : M12Struct a b y x) (n : N4) :
    liftN h n = hom4 a h.ha n.1 * hom4 b h.hb n.2 := rfl

theorem liftG_apply (h : M12Struct a b y x) (g : G2) :
    liftG h g = hom2 y h.hy g.1 * hom2 x h.hx g.2 := rfl

theorem ext_N4 {f g : N4 →* S}
    (h1 : f (Multiplicative.ofAdd 1, 1) = g (Multiplicative.ofAdd 1, 1))
    (h2 : f (1, Multiplicative.ofAdd 1) = g (1, Multiplicative.ofAdd 1)) : f = g := by
  refine hom_ext_prod (fun c => ?_) (fun c => ?_)
  · obtain ⟨k, rfl⟩ := mem_zpowers_c4 c
    have : ((Multiplicative.ofAdd (1 : ZMod 4)) ^ k, (1 : C4)) =
        ((Multiplicative.ofAdd (1 : ZMod 4)), (1 : C4)) ^ k := by simp
    rw [this, map_zpow, map_zpow, h1]
  · obtain ⟨k, rfl⟩ := mem_zpowers_c4 c
    have : ((1 : C4), (Multiplicative.ofAdd (1 : ZMod 4)) ^ k) =
        ((1 : C4), (Multiplicative.ofAdd (1 : ZMod 4))) ^ k := by simp
    rw [this, map_zpow, map_zpow, h2]

theorem liftN_e1 (h : M12Struct a b y x) : liftN h (Multiplicative.ofAdd 1, 1) = a := by
  simp [liftN_apply, hom4_gen]

theorem liftN_1e (h : M12Struct a b y x) : liftN h (1, Multiplicative.ofAdd 1) = b := by
  simp [liftN_apply, hom4_gen]

theorem liftG_e1 (h : M12Struct a b y x) : liftG h (Multiplicative.ofAdd 1, 1) = y := by
  simp [liftG_apply, hom2_gen]

theorem liftG_1e (h : M12Struct a b y x) : liftG h (1, Multiplicative.ofAdd 1) = x := by
  simp [liftG_apply, hom2_gen]

theorem compat (h : M12Struct a b y x) (g : G2) :
    (liftN h).comp (phi g).toMonoidHom = (MulAut.conj (liftG h g)).toMonoidHom.comp (liftN h) := by
  have h2 : ∀ k : C2, k = 1 ∨ k = Multiplicative.ofAdd 1 := by decide
  obtain ⟨g1, g2⟩ := g
  rcases h2 g1 with rfl | rfl <;> rcases h2 g2 with rfl | rfl
  · rw [Prod.mk_one_one, map_one, map_one]
    ext n
    simp
  · apply ext_N4
    · simp [phi, prodHom_apply, hom2_gen, invAut, liftG_apply, liftN_apply, hom4_gen, h.hxa]
    · simp [phi, prodHom_apply, hom2_gen, invAut, liftG_apply, liftN_apply, hom4_gen, h.hxb]
  · apply ext_N4
    · simp [phi, prodHom_apply, hom2_gen, swapAut, liftG_apply, liftN_apply, hom4_gen, h.hya]
    · simp [phi, prodHom_apply, hom2_gen, swapAut, liftG_apply, liftN_apply, hom4_gen, h.hyb]
  · apply ext_N4
    · simp [phi, prodHom_apply, hom2_gen, swapAut, invAut, liftG_apply, liftN_apply, hom4_gen]
      rw [h.hxa, ← h.hya]
      group
    · simp [phi, prodHom_apply, hom2_gen, swapAut, invAut, liftG_apply, liftN_apply, hom4_gen]
      rw [h.hxb, ← h.hyb]
      group

@[expose] noncomputable def toGroup (h : M12Struct a b y x) : (N4 ⋊[phi] G2) →* S :=
  SemidirectProduct.lift (liftN h) (liftG h) (compat h)

theorem toGroup_surjective (h : M12Struct a b y x) : Function.Surjective (toGroup h) := by
  have hr : (toGroup h).range = ⊤ := by
    rw [eq_top_iff, ← h.gen, Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd 1, 1), by
        simp [toGroup, liftN_e1]⟩
    · exact ⟨SemidirectProduct.inl (1, Multiplicative.ofAdd 1), by
        simp [toGroup, liftN_1e]⟩
    · exact ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1, 1), by
        simp [toGroup, liftG_e1]⟩
    · exact ⟨SemidirectProduct.inr (1, Multiplicative.ofAdd 1), by
        simp [toGroup, liftG_1e]⟩
  exact MonoidHom.range_eq_top.mp hr

instance : Finite (N4 ⋊[phi] G2) :=
  Finite.of_equiv (N4 × G2) SemidirectProduct.equivProd.symm

theorem toGroup_bijective [Finite S] (hcard : Nat.card S = 64) (h : M12Struct a b y x) :
    Function.Bijective (toGroup h) :=
  (toGroup_surjective h).bijective_of_nat_card_le (by rw [card_model, hcard])

end Lift

end CFSG.GH74.GLS.Stage1.Thm6
