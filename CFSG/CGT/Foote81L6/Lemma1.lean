module

public import CFSG.CGT.Foote81L6.Part1
public import CFSG.CGT.Foote81L6.Part2
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.CGT.Foote81L6

open DihedralGroup

abbrev X (r e f : ℕ) :=
  DihedralGroup (2 ^ (r - 1)) × DihedralGroup (2 ^ (e - 1)) × DihedralGroup (2 ^ (f - 1))

abbrev expo (r e f : ℕ) : Fin 3 → ℕ := ![r - 1, e - 1, f - 1]

@[expose] def eX (r e f : ℕ) : X r e f ≃* PX (expo r e f) where
  toFun x := fun i => match i with
    | 0 => x.1
    | 1 => x.2.1
    | 2 => x.2.2
  invFun p := (p 0, p 1, p 2)
  left_inv x := rfl
  right_inv p := by
    funext i; fin_cases i <;> rfl
  map_mul' x y := by
    funext i; fin_cases i <;> rfl

theorem commAut_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) (y : MulAut G) :
    commAut (MulAut.congr e y) = (commAut y).map e.toMonoidHom := by
  unfold commAut
  rw [MonoidHom.map_closure]
  congr 1
  ext h
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(e.symm p)⁻¹ * y (e.symm p), ⟨e.symm p, rfl⟩, by simp [MulAut.congr_apply]⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, by simp [MulAut.congr_apply]⟩

@[expose] def eY (r e f : ℕ) :
    DihedralGroup (2 ^ (e - 1)) × DihedralGroup (2 ^ (f - 1)) ≃* PY (expo r e f) where
  toFun x := fun i => match i with
    | 0 => x.1
    | 1 => x.2
  invFun p := (p 0, p 1)
  left_inv x := rfl
  right_inv p := by
    funext i; fin_cases i <;> rfl
  map_mul' x y := by
    funext i; fin_cases i <;> rfl

theorem eX_symm_ιY (r e f : ℕ) (g : PY (expo r e f)) :
    (eX r e f).symm (ιY (expo r e f) g) = (1, g 0, g 1) := by
  refine Prod.ext (ιY_zero g) (Prod.ext (ιY_succ g 0) (ιY_succ g 1))

section Transport

variable {r e f : ℕ} (y : MulAut (X r e f))

theorem congr_ne_one (hy : y ≠ 1) : MulAut.congr (eX r e f) y ≠ 1 := fun h =>
  hy ((MulAut.congr (eX r e f)).injective (h.trans (map_one _).symm))

theorem congr_orderOf : orderOf (MulAut.congr (eX r e f) y) = orderOf y :=
  MulEquiv.orderOf_eq (MulAut.congr (eX r e f)) y

theorem congr_pow_orderOf : MulAut.congr (eX r e f) y ^ orderOf y = 1 := by
  have := pow_orderOf_eq_one (MulAut.congr (eX r e f) y)
  rwa [congr_orderOf] at this

end Transport

@[expose] noncomputable def commEquiv {r e f : ℕ} (y : MulAut (X r e f)) :
    ↥(commAut y) ≃* ↥(commAut (MulAut.congr (eX r e f) y)) :=
  (Subgroup.equivMapOfInjective _ (eX r e f).toMonoidHom (eX r e f).injective).trans
    (MulEquiv.subgroupCongr (commAut_congr _ y).symm)

theorem commEquiv_coe {r e f : ℕ} (y : MulAut (X r e f)) (x : ↥(commAut y)) :
    ((commEquiv y x : ↥(commAut (MulAut.congr (eX r e f) y))) : PX (expo r e f)) =
      eX r e f x := rfl

theorem lemma1_one {r e f : ℕ} (hr : 2 ≤ r) (hre : r < e) (hef : e ≤ f) (y : MulAut (X r e f))
    (hy : y ≠ 1) (hodd : Odd (orderOf y)) :
    r = 2 ∧ orderOf y = 3 ∧ Nat.card (commAut y) = 4 ∧ (∀ x ∈ commAut y, x * x = 1) ∧
      ∃ φ : ↥(commAut y) × DihedralGroup (2 ^ (e - 1)) × DihedralGroup (2 ^ (f - 1)) ≃* X r e f,
        ∀ x a b, φ (x, a, b) = (x : X r e f) * (1, a, 1) * (1, 1, b) := by
  have hr2 : r = 2 := by
    by_contra hne
    have ha : ∀ i, 2 ≤ expo r e f i := by
      intro i; fin_cases i <;> simp [expo] <;> omega
    obtain ⟨hae, -⟩ :=
      part2 (expo r e f) ha (MulAut.congr (eX r e f) y) (congr_ne_one y hy) hodd
        (congr_pow_orderOf y)
    have h01 : r - 1 = e - 1 := hae 0 1
    omega
  subst hr2
  have h0 : expo 2 e f 0 = 1 := rfl
  have h1 : 2 ≤ expo 2 e f 1 := by show 2 ≤ e - 1; omega
  have h2 : 2 ≤ expo 2 e f 2 := by show 2 ≤ f - 1; omega
  obtain ⟨hord, hcard, hsq, φ, hφ⟩ := part1 (a := expo 2 e f) h0 h1 h2
    (MulAut.congr (eX 2 e f) y) (congr_ne_one y hy) hodd (congr_pow_orderOf y)
  refine ⟨rfl, by rwa [congr_orderOf] at hord, ?_, ?_, ?_⟩
  · rw [← hcard]; exact (Nat.card_congr (commEquiv y).toEquiv)
  · intro x hx
    have := hsq _ ((commEquiv y ⟨x, hx⟩).2)
    apply (eX 2 e f).injective
    rw [map_mul, map_one]
    exact this
  · refine ⟨((commEquiv y).prodCongr (eY 2 e f)).trans (φ.trans (eX 2 e f).symm), ?_⟩
    intro x a b
    show (eX 2 e f).symm (φ (commEquiv y x, eY 2 e f (a, b))) = _
    rw [hφ, map_mul]
    have h1 : (eX 2 e f).symm ((commEquiv y x : ↥(commAut (MulAut.congr (eX 2 e f) y))) :
        PX (expo 2 e f)) = (x : X 2 e f) := by
      rw [commEquiv_coe]; simp
    rw [h1, eX_symm_ιY, mul_assoc]
    congr 1
    show ((1 : DihedralGroup (2 ^ (2 - 1))), a, b) = _
    simp [Prod.ext_iff]

end CFSG.CGT.Foote81L6
