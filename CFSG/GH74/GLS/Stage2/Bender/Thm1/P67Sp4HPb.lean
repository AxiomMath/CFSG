module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4Act

public section

open CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

namespace HPSL2

variable {K : Type} [Field K]

@[expose] def pairIncl (e f : Fin 2 ⊕ Fin 2 → K) : (Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) where
  toFun x := x 0 • e + x 1 • f
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply]

@[expose] noncomputable def pairCoord (e f : Fin 2 ⊕ Fin 2 → K) :
    (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun v := ![spForm 2 K v f, -spForm 2 K v e]
  map_add' v w := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

theorem pairIncl_apply (e f : Fin 2 ⊕ Fin 2 → K) (x : Fin 2 → K) :
    pairIncl e f x = x 0 • e + x 1 • f := rfl

theorem pairCoord_zero (e f v : Fin 2 ⊕ Fin 2 → K) : pairCoord e f v 0 = spForm 2 K v f := rfl

theorem pairCoord_one (e f v : Fin 2 ⊕ Fin 2 → K) : pairCoord e f v 1 = -spForm 2 K v e := rfl

theorem spForm_pairIncl_right (e f v : Fin 2 ⊕ Fin 2 → K) (y : Fin 2 → K) :
    spForm 2 K v (pairIncl e f y) = pairCoord e f v 0 * y 1 - pairCoord e f v 1 * y 0 := by
  rw [pairIncl_apply, map_add, map_smul, map_smul, pairCoord_zero, pairCoord_one, smul_eq_mul,
    smul_eq_mul]
  ring

theorem spForm_pairIncl_left (e f : Fin 2 ⊕ Fin 2 → K) (x : Fin 2 → K) (w : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K (pairIncl e f x) w = x 0 * pairCoord e f w 1 - x 1 * pairCoord e f w 0 := by
  rw [pairIncl_apply, map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
    LinearMap.smul_apply, pairCoord_zero, pairCoord_one, smul_eq_mul, smul_eq_mul,
    spForm_neg_left w e, spForm_neg_left w f]
  ring

variable {e f : Fin 2 ⊕ Fin 2 → K}

theorem pairCoord_pairIncl (hef : spForm 2 K e f = 1) (x : Fin 2 → K) :
    pairCoord e f (pairIncl e f x) = x := by
  have hfe : spForm 2 K f e = -1 := by rw [spForm_neg_left e f, hef]
  ext i
  fin_cases i
  · simp [pairCoord_zero, pairIncl_apply, hef, spForm_self]
  · simp [pairCoord_one, pairIncl_apply, hfe, spForm_self]

theorem spForm_pairIncl_pairIncl (hef : spForm 2 K e f = 1) (x y : Fin 2 → K) :
    spForm 2 K (pairIncl e f x) (pairIncl e f y) = x 0 * y 1 - x 1 * y 0 := by
  rw [spForm_pairIncl_left, pairCoord_pairIncl hef]

structure IsHypFrame (P : Submodule K (Fin 2 ⊕ Fin 2 → K)) (e f : Fin 2 ⊕ Fin 2 → K) : Prop where
  mem_e : e ∈ P
  mem_f : f ∈ P
  spForm_e_f : spForm 2 K e f = 1
  incl_coord : ∀ w ∈ P, pairIncl e f (pairCoord e f w) = w

theorem pairIncl_mem {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (he : e ∈ P) (hf : f ∈ P)
    (x : Fin 2 → K) : pairIncl e f x ∈ P :=
  P.add_mem (P.smul_mem _ he) (P.smul_mem _ hf)

theorem exists_hyperbolic_pair {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hP : Module.finrank K P = 2)
    (hPo : P ⊓ orth P = ⊥) : ∃ e ∈ P, ∃ f ∈ P, spForm 2 K e f = 1 := by
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hP
    exact absurd hP (by norm_num)
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hne : e ∉ orth P := fun h => he0 (by
    have : e ∈ P ⊓ orth P := ⟨he, h⟩
    rw [hPo] at this
    exact this)
  rw [mem_orth] at hne
  push Not at hne
  obtain ⟨u, hu, hue⟩ := hne
  refine ⟨e, he, (-spForm 2 K u e)⁻¹ • u, P.smul_mem _ hu, ?_⟩
  rw [map_smul, smul_eq_mul, spForm_neg_left u e]
  exact inv_mul_cancel₀ (neg_ne_zero.mpr hue)

theorem exists_isHypFrame {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hP : Module.finrank K P = 2)
    (hPo : P ⊓ orth P = ⊥) : ∃ e f, IsHypFrame P e f := by
  obtain ⟨e, he, f, hf, hef⟩ := exists_hyperbolic_pair hP hPo
  refine ⟨e, f, he, hf, hef, fun w hw => ?_⟩
  let r : P →ₗ[K] (Fin 2 → K) := (pairCoord e f).domRestrict P
  have hsurj : Function.Surjective r := fun x =>
    ⟨⟨pairIncl e f x, pairIncl_mem he hf x⟩, pairCoord_pairIncl hef x⟩
  have hinj : Function.Injective r :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hP, Module.finrank_fin_fun])).mpr hsurj
  have := @hinj ⟨pairIncl e f (pairCoord e f w), pairIncl_mem he hf _⟩ ⟨w, hw⟩
    (by simp [r, pairCoord_pairIncl hef])
  exact congrArg Subtype.val this

namespace IsHypFrame

variable {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (H : IsHypFrame P e f)
include H

theorem incl_mem (x : Fin 2 → K) : pairIncl e f x ∈ P := pairIncl_mem H.mem_e H.mem_f x

theorem coord_eq_zero {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ orth P) : pairCoord e f v = 0 := by
  ext i
  fin_cases i
  · exact spForm_isRefl _ _ ((mem_orth.mp hv) f H.mem_f)
  · simp only [Fin.mk_one, pairCoord_one, Pi.zero_apply, neg_eq_zero]
    exact spForm_isRefl _ _ ((mem_orth.mp hv) e H.mem_e)

theorem sub_incl_coord_mem_orth (v : Fin 2 ⊕ Fin 2 → K) :
    v - pairIncl e f (pairCoord e f v) ∈ orth P := by
  rw [mem_orth]
  intro u hu
  have hu' := H.incl_coord u hu
  have h1 : spForm 2 K u v = spForm 2 K (pairIncl e f (pairCoord e f u)) v := by rw [hu']
  have h2 : spForm 2 K u (pairIncl e f (pairCoord e f v)) =
      spForm 2 K (pairIncl e f (pairCoord e f u)) (pairIncl e f (pairCoord e f v)) := by
    rw [hu']
  rw [map_sub, h1, h2, spForm_pairIncl_left, spForm_pairIncl_pairIncl H.spForm_e_f, sub_self]

end IsHypFrame

theorem act_mem_HP {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} {h : StatedSp 2 K} (hh : h ∈ HP P)
    {w : Fin 2 ⊕ Fin 2 → K} (hw : w ∈ P) : act h w ∈ P := by
  rw [← orth_orth P, mem_orth]
  intro z hz
  have h1 : spForm 2 K (act h w) z = 0 := by
    have := spForm_act h w z
    rw [hh z hz] at this
    rw [this]
    exact (mem_orth.mp hz) w hw
  exact spForm_isRefl _ _ h1

end HPSL2

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4
