module

public import CFSG.LieType.Chevalley.G2FieldFourCoverRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourLift

public noncomputable section

namespace CFSG.LieType.Chevalley.G2FieldFour

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ExceptionalCover
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {K : Type} [Field K] {E : Type*} [Group E]

structure RootLifts (η : E →* adjointGroup Tag.G2 K) where
  A : (Fin Tag.G2.rank → ℤ) → K → E
  map_A : ∀ d ∈ posRoots, ∀ c, η (A d c) = rootX d c
  A_add : ∀ d ∈ posRoots, ∀ c c', A d (c + c') = A d c * A d c'
  A_conj : ∀ d ∈ posRoots, ∀ (t : Fin Tag.G2.rank → Kˣ) (g : E), η g = torusX t →
    ∀ c, g * A d c * g⁻¹ = A d ((rootChar K d t : K) * c)

variable (η : E →* adjointGroup Tag.G2 K)

theorem exists_rootLifts
    {ω : Kˣ} (hω : orderOf ω = 3) (hη : Function.Surjective η)
    (hker : ∀ z, η z = 1 → z ∈ Subgroup.center E)
    (hab : ∀ d ∈ posRoots, ∀ (e e' : E) (c c' : K), η e = rootX d c → η e' = rootX d c' →
      e * e' = e' * e) :
    Nonempty (RootLifts η) := by
  have key : ∀ d ∈ posRoots, ∃ A : K → E, (∀ c, η (A c) = rootX d c) ∧
      (∀ c c', A (c + c') = A c * A c') ∧ ∀ (t : Fin Tag.G2.rank → Kˣ) (g : E),
        η g = torusX t → ∀ c, g * A c * g⁻¹ = A ((rootChar K d t : K) * c) := by
    intro d hd
    obtain ⟨t₀, ht₀⟩ := exists_rootChar_ne_one hω hd
    obtain ⟨xl, h1, h2, h3⟩ := LinearCover.exists_torus_lift η hker hη (x := rootX d)
      (rootX_add d) (fun e e' a b he he' => hab d hd e e' a b he he') ht₀
      (fun a => torusX_conj_rootX (mem_posRoots.1 hd).1 t₀ a)
    exact ⟨xl, h1, h2, fun t g hg c => h3 g _ (by rw [hg]; exact torusX_mul_comm t t₀)
      (fun a => by rw [hg]; exact torusX_conj_rootX (mem_posRoots.1 hd).1 t a) c⟩
  choose! A hA using key
  exact ⟨⟨A, fun d hd => (hA d hd).1, fun d hd => (hA d hd).2.1, fun d hd => (hA d hd).2.2⟩⟩

theorem lift_comm
    (hη : Function.Surjective η) (hker : ∀ z, η z = 1 → z ∈ Subgroup.center E)
    {d d' : Fin Tag.G2.rank → ℤ} (hd : IsRoot .G2 d) (hd' : IsRoot .G2 d')
    (hcomm : ∀ x y : K, Commute (rootX d x) (rootX d' y)) (t : Fin Tag.G2.rank → Kˣ)
    (ht : (rootChar K d t : K) ≠ 1) (ht' : rootChar K d' t = 1) {e e' : E} {x y : K}
    (he : η e = rootX d x) (he' : η e' = rootX d' y) : Commute e e' :=
  LinearCover.lift_mul_comm_of_torus η hker hη (x := rootX d) (y := rootX d') (rootX_add d)
    (fun a b => hcomm a b) ht (fun a => torusX_conj_rootX hd t a)
    (fun b => by rw [torusX_conj_rootX hd' t b, ht', Units.val_one, one_mul]) he he'

theorem commute_commutatorElement {G : Type*} [Group G] {g h k : G} (hh : Commute g h)
    (hk : Commute g k) : Commute g ⁅h, k⁆ := by
  rw [commutatorElement_def]
  exact ((hh.mul_right hk).mul_right hh.inv_right).mul_right hk.inv_right

theorem commutatorElement_mul_of_commute {G : Type*} [Group G] {a a' b : G}
    (h : Commute a' b) : ⁅a * a', b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
    show a * a' * b = a * b * a' by rw [mul_assoc, h.eq, ← mul_assoc]]
  group

theorem conj_eq_of_commute {G : Type*} [Group G] {g k : G} (h : Commute g k) :
    g * k * g⁻¹ = k := by
  rw [h.eq, mul_inv_cancel_right]

theorem commutatorElement_mul_left' {G : Type*} [Group G] (a a' b : G) :
    ⁅a * a', b⁆ = a * ⁅a', b⁆ * a⁻¹ * ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_commutatorElement_mul' {G : Type*} [Group G] (g h : G) :
    g * h * g⁻¹ = ⁅g, h⁆ * h := by
  simp only [commutatorElement_def]
  group

theorem add_sq_of_charTwo {R : Type*} [CommRing R] [CharP R 2] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  linear_combination (a * b) * CharTwo.two_eq_zero (R := R)

section Center

variable
    {η} (hker : ∀ z, η z = 1 → z ∈ Subgroup.center E) (L : RootLifts η)
include hker

theorem eq_A_mul_center
    {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) {e : E} {c : K}
    (he : η e = rootX d c) : e = L.A d c * ((L.A d c)⁻¹ * e) ∧
      (L.A d c)⁻¹ * e ∈ Subgroup.center E :=
  ⟨(mul_inv_cancel_left _ _).symm, hker _ (by rw [map_mul, map_inv, L.map_A d hd, he,
    inv_mul_cancel])⟩

theorem comm_of_comm_A
    {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) {f e : E} {c : K}
    (he : η e = rootX d c) (hf : Commute f (L.A d c)) : Commute f e := by
  obtain ⟨h1, h2⟩ := eq_A_mul_center hker L hd he
  have hz : Commute f ((L.A d c)⁻¹ * e) := Subgroup.mem_center_iff.1 h2 f
  rw [h1]
  exact hf.mul_right hz

end Center

section Relations

variable {η} [CharP K 2] {ω : Kˣ} (hω : orderOf ω = 3) (hη : Function.Surjective η)
  (hker : ∀ z, η z = 1 → z ∈ Subgroup.center E)
include hω hη hker

theorem comm_au
    {e e' : E} {x y : K} (he : η e = rootX rootA x) (he' : η e' = rootX rootU y) :
    Commute e e' :=
  lift_comm η hη hker (mem_posRoots.1 rootA_mem).1 (mem_posRoots.1 rootU_mem).1
    (fun x y => commute_rootX_au x y) (torusPow ω ![1, 1])
    (rootChar_torusPow_ne_one hω (by decide +kernel))
    (rootChar_torusPow_eq_one hω (by decide +kernel)) he he'

theorem comm_av
    {e e' : E} {x y : K} (he : η e = rootX rootA x) (he' : η e' = rootX rootV y) :
    Commute e e' :=
  lift_comm η hη hker (mem_posRoots.1 rootA_mem).1 (mem_posRoots.1 rootV_mem).1
    (fun x y => commute_rootX_av x y) (torusPow ω ![1, 0])
    (rootChar_torusPow_ne_one hω (by decide +kernel))
    (rootChar_torusPow_eq_one hω (by decide +kernel)) he he'

theorem comm_rb
    {e e' : E} {x y : K} (he : η e = rootX rootR x) (he' : η e' = rootX rootB y) :
    Commute e e' :=
  lift_comm η hη hker (mem_posRoots.1 rootR_mem).1 (mem_posRoots.1 rootB_mem).1
    (fun x y => commute_rootX_rb x y) (torusPow ω ![0, 1])
    (rootChar_torusPow_ne_one hω (by decide +kernel))
    (rootChar_torusPow_eq_one hω (by decide +kernel)) he he'

theorem comm_rc
    {e e' : E} {x y : K} (he : η e = rootX rootR x) (he' : η e' = rootX rootC y) :
    Commute e e' :=
  lift_comm η hη hker (mem_posRoots.1 rootR_mem).1 (mem_posRoots.1 rootC_mem).1
    (fun x y => commute_rootX_rc x y) (torusPow ω ![0, 1])
    (rootChar_torusPow_ne_one hω (by decide +kernel))
    (rootChar_torusPow_eq_one hω (by decide +kernel)) he he'

theorem comm_ub
    {e e' : E} {x y : K} (he : η e = rootX rootU x) (he' : η e' = rootX rootB y) :
    Commute e e' :=
  lift_comm η hη hker (mem_posRoots.1 rootU_mem).1 (mem_posRoots.1 rootB_mem).1
    (fun x y => commute_rootX_ub x y) (torusPow ω ![0, 1])
    (rootChar_torusPow_ne_one hω (by decide +kernel))
    (rootChar_torusPow_eq_one hω (by decide +kernel)) he he'

theorem comm_uc
    {e e' : E} {x y : K} (he : η e = rootX rootU x) (he' : η e' = rootX rootC y) :
    Commute e e' :=
  lift_comm η hη hker (mem_posRoots.1 rootU_mem).1 (mem_posRoots.1 rootC_mem).1
    (fun x y => commute_rootX_uc x y) (torusPow ω ![0, 1])
    (rootChar_torusPow_ne_one hω (by decide +kernel))
    (rootChar_torusPow_eq_one hω (by decide +kernel)) he he'

theorem comm_vb
    {e e' : E} {x y : K} (he : η e = rootX rootV x) (he' : η e' = rootX rootB y) :
    Commute e e' :=
  lift_comm η hη hker (mem_posRoots.1 rootV_mem).1 (mem_posRoots.1 rootB_mem).1
    (fun x y => commute_rootX_vb x y) (torusPow ω ![0, 1])
    (rootChar_torusPow_ne_one hω (by decide +kernel))
    (rootChar_torusPow_eq_one hω (by decide +kernel)) he he'

theorem comm_vc
    {e e' : E} {x y : K} (he : η e = rootX rootV x) (he' : η e' = rootX rootC y) :
    Commute e e' :=
  lift_comm η hη hker (mem_posRoots.1 rootV_mem).1 (mem_posRoots.1 rootC_mem).1
    (fun x y => commute_rootX_vc x y) (torusPow ω ![0, 1])
    (rootChar_torusPow_ne_one hω (by decide +kernel))
    (rootChar_torusPow_eq_one hω (by decide +kernel)) he he'

variable
    (hab : ∀ d ∈ posRoots, ∀ (e e' : E) (c c' : K), η e = rootX d c → η e' = rootX d c' →
  e * e' = e' * e) (L : RootLifts η)
include hab

theorem commutator_A_rv
    (s t : K) : ⁅L.A rootR s, L.A rootV t⁆ = L.A rootB (s * t) := by
  obtain ⟨g, hg⟩ := hη (torusX (torusPow ω ![1, 0]))
  have hr : (rootChar K rootR (torusPow ω ![1, 0]) : K) ≠ 1 :=
    rootChar_torusPow_ne_one hω (by decide +kernel)
  have hv : rootChar K rootV (torusPow ω ![1, 0]) = 1 :=
    rootChar_torusPow_eq_one hω (by decide +kernel)
  have hb : rootChar K rootB (torusPow ω ![1, 0]) = rootChar K rootR (torusPow ω ![1, 0]) :=
    rootChar_torusPow_eq hω (by decide +kernel)
  refine LinearCover.commutatorElement_lift_eq_of_torus η hker (x := rootX rootR)
    (y := rootX rootV) (z := rootX rootB) (L.map_A _ rootR_mem) (L.map_A _ rootV_mem)
    (L.map_A _ rootB_mem) (L.A_add _ rootR_mem) (L.A_add _ rootB_mem)
    (fun a b => commutator_rootX_rv a b)
    (fun a e c he => comm_rb hω hη hker (L.map_A _ rootR_mem a) he)
    (fun e e' c c' he he' => hab _ rootB_mem e e' c c' he he') hr
    (fun a => L.A_conj _ rootR_mem _ g hg a) (fun b => ?_) (fun c => ?_) s t
  · rw [L.A_conj _ rootV_mem _ g hg, hv, Units.val_one, one_mul]
  · rw [L.A_conj _ rootB_mem _ g hg, hb]

theorem commutator_A_uv
    (s t : K) : ⁅L.A rootU s, L.A rootV t⁆ = L.A rootC (s * t) := by
  obtain ⟨g, hg⟩ := hη (torusX (torusPow ω ![1, 0]))
  have hu : (rootChar K rootU (torusPow ω ![1, 0]) : K) ≠ 1 :=
    rootChar_torusPow_ne_one hω (by decide +kernel)
  have hv : rootChar K rootV (torusPow ω ![1, 0]) = 1 :=
    rootChar_torusPow_eq_one hω (by decide +kernel)
  have hc : rootChar K rootC (torusPow ω ![1, 0]) = rootChar K rootU (torusPow ω ![1, 0]) :=
    rootChar_torusPow_eq hω (by decide +kernel)
  refine LinearCover.commutatorElement_lift_eq_of_torus η hker (x := rootX rootU)
    (y := rootX rootV) (z := rootX rootC) (L.map_A _ rootU_mem) (L.map_A _ rootV_mem)
    (L.map_A _ rootC_mem) (L.A_add _ rootU_mem) (L.A_add _ rootC_mem)
    (fun a b => commutator_rootX_uv a b)
    (fun a e c he => comm_uc hω hη hker (L.map_A _ rootU_mem a) he)
    (fun e e' c c' he he' => hab _ rootC_mem e e' c c' he he') hu
    (fun a => L.A_conj _ rootU_mem _ g hg a) (fun b => ?_) (fun c => ?_) s t
  · rw [L.A_conj _ rootV_mem _ g hg, hv, Units.val_one, one_mul]
  · rw [L.A_conj _ rootC_mem _ g hg, hc]

theorem comm_ac
    {e e' : E} {x y : K} (he : η e = rootX rootA x) (he' : η e' = rootX rootC y) :
    Commute e e' := by
  obtain ⟨L⟩ := exists_rootLifts η hω hη hker hab
  refine comm_of_comm_A hker L rootC_mem he' ?_
  have h := commutator_A_uv hω hη hker hab L 1 y
  rw [one_mul] at h
  rw [← h]
  exact commute_commutatorElement (comm_au hω hη hker he (L.map_A _ rootU_mem 1))
    (comm_av hω hη hker he (L.map_A _ rootV_mem y))

theorem comm_bc
    {e e' : E} {x y : K} (he : η e = rootX rootB x) (he' : η e' = rootX rootC y) :
    Commute e e' := by
  obtain ⟨L⟩ := exists_rootLifts η hω hη hker hab
  refine comm_of_comm_A hker L rootC_mem he' ?_
  have h := commutator_A_uv hω hη hker hab L 1 y
  rw [one_mul] at h
  rw [← h]
  exact commute_commutatorElement
    (comm_ub hω hη hker (L.map_A _ rootU_mem 1) he).symm
    (comm_vb hω hη hker (L.map_A _ rootV_mem y) he).symm

theorem commutator_A_ab
    (x y : K) : ⁅L.A rootA x, L.A rootB y⁆ = L.A rootC (x * y) := by
  have hbk : L.A rootB y = ⁅L.A rootR 1, L.A rootV y⁆ := by
    rw [commutator_A_rv hω hη hker hab L, one_mul]
  have hgk : Commute (L.A rootA x) (L.A rootV y) :=
    comm_av hω hη hker (L.map_A _ rootA_mem x) (L.map_A _ rootV_mem y)
  set W := L.A rootU x * (L.A rootV x * L.A rootB x * L.A rootC (x ^ 2)) with hW
  have hz : W⁻¹ * ⁅L.A rootA x, L.A rootR 1⁆ ∈ Subgroup.center E := hker _ (by
    rw [map_mul, map_inv, map_commutatorElement, L.map_A _ rootA_mem, L.map_A _ rootR_mem,
      commutator_rootX_ar, hW, map_mul, map_mul, map_mul, L.map_A _ rootU_mem,
      L.map_A _ rootV_mem, L.map_A _ rootB_mem, L.map_A _ rootC_mem]
    simp only [mul_one, one_pow]
    group)
  set z := W⁻¹ * ⁅L.A rootA x, L.A rootR 1⁆ with hzdef
  have hm : ⁅L.A rootA x, L.A rootR 1⁆ = W * z := by rw [hzdef, mul_inv_cancel_left]
  have hbW : Commute (L.A rootB y) W := by
    refine (comm_ub hω hη hker (L.map_A _ rootU_mem x)
      (L.map_A _ rootB_mem y)).symm.mul_right (((comm_vb hω hη hker (L.map_A _ rootV_mem x)
        (L.map_A _ rootB_mem y)).symm.mul_right ?_).mul_right ?_)
    · exact (hab _ rootB_mem _ _ _ _ (L.map_A _ rootB_mem y) (L.map_A _ rootB_mem x) :)
    · exact comm_bc hω hη hker hab (L.map_A _ rootB_mem y) (L.map_A _ rootC_mem _)
  have hbm : Commute (L.A rootB y) ⁅L.A rootA x, L.A rootR 1⁆ := by
    rw [hm]
    exact hbW.mul_right (Subgroup.mem_center_iff.1 hz _)
  have hmk : ⁅⁅L.A rootA x, L.A rootR 1⁆, L.A rootV y⁆ = L.A rootC (x * y) := by
    have hR : Commute ((L.A rootV x * L.A rootB x * L.A rootC (x ^ 2)) * z) (L.A rootV y) := by
      have hvv : Commute (L.A rootV x) (L.A rootV y) :=
        hab _ rootV_mem _ _ _ _ (L.map_A _ rootV_mem x) (L.map_A _ rootV_mem y)
      refine ((hvv.mul_left ?_).mul_left ?_).mul_left ?_
      · exact (comm_vb hω hη hker (L.map_A _ rootV_mem y) (L.map_A _ rootB_mem x)).symm
      · exact (comm_vc hω hη hker (L.map_A _ rootV_mem y) (L.map_A _ rootC_mem _)).symm
      · exact (Subgroup.mem_center_iff.1 hz _).symm
    rw [hm, hW, mul_assoc, commutatorElement_mul_of_commute hR,
      commutator_A_uv hω hη hker hab L]
  have hcb : Commute (L.A rootC (x * y)) (L.A rootB y) :=
    (comm_bc hω hη hker hab (L.map_A _ rootB_mem y) (L.map_A _ rootC_mem _)).symm
  rw [hbk, LinearCover.commutatorElement_commutatorElement_right_of_commute hgk.eq, ← hbk,
    conj_eq_of_commute hbm.symm, hmk, hcb.symm.eq, mul_inv_cancel_right]

theorem commutator_A_ru
    (s t : K) :
    ⁅L.A rootR s, L.A rootU t⁆ = L.A rootC (s * t ^ 2) * L.A rootB (s ^ 2 * t) := by
  obtain ⟨g, hg⟩ := hη (torusX (torusPow ω ![1, 1]))
  have hr : (rootChar K rootR (torusPow ω ![1, 1]) : K) ≠ 1 :=
    rootChar_torusPow_ne_one hω (by decide +kernel)
  have hu : rootChar K rootU (torusPow ω ![1, 1]) = 1 :=
    rootChar_torusPow_eq_one hω (by decide +kernel)
  have hc : rootChar K rootC (torusPow ω ![1, 1]) = rootChar K rootR (torusPow ω ![1, 1]) :=
    rootChar_torusPow_eq hω (by decide +kernel)
  have hb : (rootChar K rootB (torusPow ω ![1, 1]) : K) =
      (rootChar K rootR (torusPow ω ![1, 1]) : K) ^ 2 :=
    rootChar_torusPow_eq_sq hω (by decide +kernel)
  have hcen : ∀ a : K, (L.A rootC (a * t ^ 2) * L.A rootB (a ^ 2 * t))⁻¹ *
      ⁅L.A rootR a, L.A rootU t⁆ ∈ Subgroup.center E := fun a => hker _ (by
    rw [map_mul, map_inv, map_commutatorElement, map_mul, L.map_A _ rootR_mem,
      L.map_A _ rootU_mem, L.map_A _ rootC_mem, L.map_A _ rootB_mem, commutator_rootX_ru,
      inv_mul_cancel])
  have hpr : ∀ a b : K, Commute (L.A rootR a) ⁅L.A rootR b, L.A rootU t⁆ := fun a b => by
    rw [← mul_inv_cancel_left (L.A rootC (b * t ^ 2) * L.A rootB (b ^ 2 * t))
      ⁅L.A rootR b, L.A rootU t⁆]
    refine ((comm_rc hω hη hker (L.map_A _ rootR_mem a) (L.map_A _ rootC_mem _)).mul_right
      (comm_rb hω hη hker (L.map_A _ rootR_mem a) (L.map_A _ rootB_mem _))).mul_right ?_
    exact Subgroup.mem_center_iff.1 (hcen b) _
  have hp1 : ∀ a b : K, ⁅L.A rootR (a + b), L.A rootU t⁆ =
      ⁅L.A rootR b, L.A rootU t⁆ * ⁅L.A rootR a, L.A rootU t⁆ := fun a b => by
    rw [L.A_add _ rootR_mem, commutatorElement_mul_left', conj_eq_of_commute (hpr a b)]
  refine LinearCover.eq_of_conj_eq_smul η hker (p := fun s => ⁅L.A rootR s, L.A rootU t⁆)
    (q := fun s => L.A rootC (s * t ^ 2) * L.A rootB (s ^ 2 * t)) (g := g) (fun a b => ?_)
    (fun a b => ?_) (fun a => ?_) hr (fun a => ?_) (fun a => ?_) s
  · rw [add_comm, hp1]
  · have hcb : Commute (L.A rootB (a ^ 2 * t)) (L.A rootC (b * t ^ 2)) :=
      comm_bc hω hη hker hab (L.map_A _ rootB_mem _) (L.map_A _ rootC_mem _)
    rw [add_sq_of_charTwo, add_mul, add_mul, L.A_add _ rootC_mem, L.A_add _ rootB_mem,
      mul_assoc, ← mul_assoc (L.A rootC (b * t ^ 2)), ← hcb.eq]
    group
  · change η ⁅L.A rootR a, L.A rootU t⁆ = η (L.A rootC (a * t ^ 2) * L.A rootB (a ^ 2 * t))
    rw [map_commutatorElement, map_mul, L.map_A _ rootR_mem, L.map_A _ rootU_mem,
      L.map_A _ rootC_mem, L.map_A _ rootB_mem, commutator_rootX_ru]
  · rw [LinearCover.conj_commutatorElement_eq, L.A_conj _ rootR_mem _ g hg,
      L.A_conj _ rootU_mem _ g hg, hu, Units.val_one, one_mul]
  · rw [show g * (L.A rootC (a * t ^ 2) * L.A rootB (a ^ 2 * t)) * g⁻¹ =
        g * L.A rootC (a * t ^ 2) * g⁻¹ * (g * L.A rootB (a ^ 2 * t) * g⁻¹) by group,
      L.A_conj _ rootC_mem _ g hg, L.A_conj _ rootB_mem _ g hg, hc, hb]
    congr 2 <;> ring

end Relations

end CFSG.LieType.Chevalley.G2FieldFour
