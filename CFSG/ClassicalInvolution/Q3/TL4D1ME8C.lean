module

public import CFSG.ClassicalInvolution.Q3.TL4D1ME8B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open Matrix CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {X E : Subgroup G} {e : Fin 3 → G}

theorem matrix_ext_mulVec {M N : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : ∀ v, M *ᵥ v = N *ᵥ v) :
    M = N := by
  ext i k
  have := congrFun (h (Pi.single k 1)) i
  simpa [mulVec, dotProduct, Pi.single_apply] using this

theorem conjMat_mul (he : E8Basis E e) {x y : G} (hx : ∀ z ∈ E, x * z * x⁻¹ ∈ E)
    (hy : ∀ z ∈ E, y * z * y⁻¹ ∈ E) : conjMat he (x * y) = conjMat he x * conjMat he y := by
  have hxy : ∀ z ∈ E, x * y * z * (x * y)⁻¹ ∈ E := fun z hz => by
    have := hx _ (hy z hz)
    rwa [show x * (y * z * y⁻¹) * x⁻¹ = x * y * z * (x * y)⁻¹ by group] at this
  refine matrix_ext_mulVec fun v => e8Coord_injective he ?_
  rw [← mulVec_mulVec, ← conj_e8Coord he hxy, ← conj_e8Coord he hx, ← conj_e8Coord he hy]
  group

theorem conjMat_one (he : E8Basis E e) : conjMat he 1 = 1 := by
  refine matrix_ext_mulVec fun v => e8Coord_injective he ?_
  rw [one_mulVec, ← conj_e8Coord he (fun z hz => by simpa using hz)]
  group

theorem det_conjMat (he : E8Basis E e) {x : G} (hx : ∀ z ∈ E, x * z * x⁻¹ ∈ E)
    (hx' : ∀ z ∈ E, x⁻¹ * z * x⁻¹⁻¹ ∈ E) : (conjMat he x).det = 1 := by
  have h : conjMat he x * conjMat he x⁻¹ = 1 := by
    rw [← conjMat_mul he hx hx', mul_inv_cancel, conjMat_one he]
  have h' := congrArg Matrix.det h
  rw [det_mul, det_one] at h'
  have h0 : (conjMat he x).det ≠ 0 := left_ne_zero_of_mul_eq_one h'
  generalize (conjMat he x).det = d at h0 ⊢
  revert d
  decide

@[expose] noncomputable def e8Hom (hE : E8Struct X E) (he : E8Basis E e) :
    ↥X →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun x := ⟨conjMat he x, det_conjMat he (hE.normal x x.2) (hE.normal _ (X.inv_mem x.2))⟩
  map_one' := Subtype.ext (conjMat_one he)
  map_mul' x y := Subtype.ext (conjMat_mul he (hE.normal x x.2) (hE.normal y y.2))

theorem e8Hom_val (hE : E8Struct X E) (he : E8Basis E e) (x : ↥X) :
    (e8Hom hE he x).1 = conjMat he x := rfl

theorem conj_e8Coord_e8Hom (hE : E8Struct X E) (he : E8Basis E e) (x : ↥X)
    (v : Fin 3 → ZMod 2) :
    (x : G) * e8Coord e v * (x : G)⁻¹ = e8Coord e ((e8Hom hE he x).1 *ᵥ v) := by
  rw [e8Hom_val]
  exact conj_e8Coord he (hE.normal x x.2) v

theorem e8Hom_eq_one_iff (hE : E8Struct X E) (he : E8Basis E e) (x : ↥X) :
    e8Hom hE he x = 1 ↔ (x : G) ∈ E := by
  constructor
  · intro h
    refine hE.cent x x.2 fun z hz => ?_
    obtain ⟨v, rfl⟩ := exists_e8Coord_eq he hz
    have h1 := conj_e8Coord_e8Hom hE he x v
    rw [h, show (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)).1 = 1 from rfl,
      one_mulVec] at h1
    calc (x : G) * e8Coord e v = (x : G) * e8Coord e v * (x : G)⁻¹ * x := by group
      _ = e8Coord e v * x := by rw [h1]
  · intro hx
    refine Subtype.ext (matrix_ext_mulVec fun v => e8Coord_injective he ?_)
    rw [← conj_e8Coord_e8Hom, show (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)).1 = 1 from rfl,
      one_mulVec, comm_of_sq hE.sq hx (e8Coord_mem he v)]
    group

theorem ker_e8Hom (hE : E8Struct X E) (he : E8Basis E e) :
    (e8Hom hE he).ker = E.subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact e8Hom_eq_one_iff hE he x

theorem card_sl3Two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field, ZMod.card]
  decide

theorem e8Hom_surjective (hE : E8Struct X E) (he : E8Basis E e) :
    Function.Surjective (e8Hom hE he) := by
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker, ker_e8Hom, card_sl3Two]
  exact hE.index

end CFSG.ClassicalInvolution.Q3.TL4
