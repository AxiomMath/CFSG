module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44LinConj
public import CFSG.GH74.GLS.IVK.Proofs2.Std44LinGen

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.LinGenAux
  CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

namespace L3InvLin

section Layer

variable {F : Type} [Field F]

theorem comm_mem_range_β₃ {g h : SpecialLinearGroup (Fin 3) F}
    (g02 : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0) (g12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (g20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (g21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h02 : (h : Matrix (Fin 3) (Fin 3) F) 0 2 = 0) (h12 : (h : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h20 : (h : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (h : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    ⁅g, h⁆ ∈ (β₃ F).range := by
  have hdg : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
  have hdh : (h : Matrix (Fin 3) (Fin 3) F).det = 1 := h.2
  rw [Matrix.det_fin_three, g02, g12, g20, g21] at hdg
  rw [Matrix.det_fin_three, h02, h12, h20, h21] at hdh
  rw [commutatorElement_def]
  refine mem_range_β₃_of ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_three, Matrix.mul_apply, Fin.sum_univ_three, g02, g12, g20, g21, h02,
      h12, h20, h21]
  linear_combination
    ((h : Matrix (Fin 3) (Fin 3) F) 2 2 * ((h : Matrix (Fin 3) (Fin 3) F) 0 0 *
      (h : Matrix (Fin 3) (Fin 3) F) 1 1 - (h : Matrix (Fin 3) (Fin 3) F) 0 1 *
      (h : Matrix (Fin 3) (Fin 3) F) 1 0)) * hdg + hdh

theorem comm_mem_range₃ (h2 : (2 : F) ≠ 0) {x y : StatedProj (StatedSL 3 F)}
    (hx : x ∈ Subgroup.centralizer ({linU₀ F} : Set (StatedProj (StatedSL 3 F))))
    (hy : y ∈ Subgroup.centralizer ({linU₀ F} : Set (StatedProj (StatedSL 3 F)))) :
    ⁅x, y⁆ ∈ ((projSL F).comp (β₃ F)).range := by
  obtain ⟨gx, rfl⟩ := projSL_surjective F x
  obtain ⟨gy, rfl⟩ := projSL_surjective F y
  have hx' : gx * t₃ F = t₃ F * gx := by
    refine commute_of_projSL_commute (trace_t₃_ne_zero F) ?_
    rw [projSL_t₃]
    exact Subgroup.mem_centralizer_singleton_iff.1 hx
  have hy' : gy * t₃ F = t₃ F * gy := by
    refine commute_of_projSL_commute (trace_t₃_ne_zero F) ?_
    rw [projSL_t₃]
    exact Subgroup.mem_centralizer_singleton_iff.1 hy
  obtain ⟨gx02, gx12, gx20, gx21⟩ := block₃_of_commute h2 hx'
  obtain ⟨gy02, gy12, gy20, gy21⟩ := block₃_of_commute h2 hy'
  obtain ⟨A, hA⟩ := comm_mem_range_β₃ gx02 gx12 gx20 gx21 gy02 gy12 gy20 gy21
  exact ⟨A, by rw [MonoidHom.comp_apply, hA, map_commutatorElement]⟩

theorem Ez_linU₀_le_range (h2 : (2 : F) ≠ 0) :
    Ez (linU₀ F) ≤ ((projSL F).comp (β₃ F)).range := by
  set C : Subgroup (StatedProj (StatedSL 3 F)) :=
    Subgroup.centralizer ({linU₀ F} : Set (StatedProj (StatedSL 3 F))) with hC
  set R : Subgroup (StatedProj (StatedSL 3 F)) := ((projSL F).comp (β₃ F)).range with hR
  have h1 : CFSG.layer C ≤ R.subgroupOf C := by
    calc CFSG.layer C = ⁅CFSG.layer C, CFSG.layer C⁆ := (CFSG.LocalCores.layer_perfect).symm
      _ ≤ ⁅(⊤ : Subgroup C), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ ≤ R.subgroupOf C := Subgroup.commutator_le.2 fun x _ y _ => comm_mem_range₃ h2 x.2 y.2
  calc Ez (linU₀ F) = (CFSG.layer C).map C.subtype := rfl
    _ ≤ (R.subgroupOf C).map C.subtype := Subgroup.map_mono h1
    _ = R ⊓ C := Subgroup.subgroupOf_map_subtype R C
    _ ≤ R := inf_le_left

theorem Ez_linU₀_eq [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    Ez (linU₀ F) = ((projSL F).comp (β₃ F)).range :=
  le_antisymm (Ez_linU₀_le_range h2) (range₃_le_Ez h2 h4)

end Layer

section Torus

variable {F : Type} [Field F]

@[expose] def torusEmb (a : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨Matrix.diagonal ![(a : F), ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_diagonal, Fin.prod_univ_two]⟩

theorem coe_torusEmb (a : Fˣ) :
    (torusEmb a : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(a : F), ((a⁻¹ : Fˣ) : F)] :=
  rfl

variable (F) in
@[expose] def torusHom : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun := torusEmb
  map_one' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_torusEmb]
  map_mul' a b := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_torusEmb, mul_comm]

theorem torusHom_injective : Function.Injective (torusHom F) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have := congrFun (congrFun (congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F)) ha) 0) 0
  simpa [torusHom, coe_torusEmb] using this

variable (F) in
@[expose] def torusSub : Subgroup (SpecialLinearGroup (Fin 2) F) :=
  (Subgroup.centralizer ({t₂ F} : Set (SpecialLinearGroup (Fin 3) F))).comap (β₃ F)

theorem mem_torusSub (A : SpecialLinearGroup (Fin 2) F) :
    A ∈ torusSub F ↔ β₃ F A * t₂ F = t₂ F * β₃ F A := by
  rw [torusSub, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]

theorem mem_torusSub_iff (h2 : (2 : F) ≠ 0) (A : SpecialLinearGroup (Fin 2) F) :
    A ∈ torusSub F ↔
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [mem_torusSub]
  have key : β₃ F A * t₂ F = t₂ F * β₃ F A ↔
      blk₃ (A : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal ![-1, 1, -1] =
        Matrix.diagonal ![-1, 1, -1] * blk₃ (A : Matrix (Fin 2) (Fin 2) F) := by
    constructor
    · intro h
      have := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
      simpa [Matrix.SpecialLinearGroup.coe_mul, coe_β₃, coe_t₂] using this
    · intro h
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      have := congrFun (congrFun h i) j
      simpa [Matrix.SpecialLinearGroup.coe_mul, coe_β₃, coe_t₂] using this
  rw [key]
  constructor
  · intro h
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    simp [blk₃, Matrix.mul_diagonal, Matrix.diagonal_mul] at e01 e10
    refine ⟨?_, ?_⟩
    · have : (2 : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -e10
      exact (mul_eq_zero.mp this).resolve_left h2
  · rintro ⟨h01, h10⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk₃, Matrix.mul_apply, Matrix.diagonal_apply, h01, h10]

theorem torusSub_eq_range (h2 : (2 : F) ≠ 0) : torusSub F = (torusHom F).range := by
  ext A
  rw [mem_torusSub_iff h2, MonoidHom.mem_range]
  constructor
  · rintro ⟨h01, h10⟩
    have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have := A.2
      rw [Matrix.det_fin_two, h01, h10] at this
      simpa using this
    refine ⟨Units.mkOfMulEqOne _ _ hdet, ?_⟩
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [torusHom, coe_torusEmb, h01, h10]
    exact inv_eq_of_mul_eq_one_right hdet
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_⟩ <;> simp [torusHom, coe_torusEmb]

theorem card_torusSub (h2 : (2 : F) ≠ 0) [Finite F] : Nat.card (torusSub F) = Nat.card F - 1 := by
  have : Nat.card ↥(torusHom F).range = Nat.card Fˣ :=
    (Nat.card_congr (MonoidHom.ofInjective torusHom_injective).toEquiv).symm
  rw [torusSub_eq_range h2, this, Nat.card_units]

theorem centralizer_inf_range₃ :
    Subgroup.centralizer ({linU₀' F} : Set (StatedProj (StatedSL 3 F))) ⊓
        ((projSL F).comp (β₃ F)).range =
      (torusSub F).map ((projSL F).comp (β₃ F)) := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hx, A, rfl⟩
    refine ⟨A, ?_, rfl⟩
    rw [mem_torusSub]
    refine commute_of_projSL_commute (trace_t₂_ne_zero F) ?_
    rw [projSL_t₂]
    exact Subgroup.mem_centralizer_singleton_iff.1 hx
  · rintro ⟨A, hA, rfl⟩
    refine ⟨?_, A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← projSL_t₂, MonoidHom.comp_apply, ← map_mul,
      ← map_mul, (mem_torusSub A).1 hA]

theorem card_centralizer_inf_Ez (h2 : (2 : F) ≠ 0) [Finite F] (h4 : 4 ≤ Nat.card F) :
    Nat.card ↥(Subgroup.centralizer ({linU₀' F} : Set (StatedProj (StatedSL 3 F))) ⊓
      Ez (linU₀ F)) = Nat.card F - 1 := by
  rw [Ez_linU₀_eq h2 h4, centralizer_inf_range₃,
    Subgroup.card_map_of_injective (projSL_comp_β₃_injective F), card_torusSub h2]

end Torus

section Transport

variable {J X : Type} [Group J] [Group X]

theorem card_centralizer_inf_Ez_of_iso (φ : J ≃* X) (a b : J) :
    Nat.card ↥(centralizer ({b} : Set J) ⊓ Ez a) =
      Nat.card ↥(centralizer ({φ b} : Set X) ⊓ Ez (φ a)) := by
  have hmap : (centralizer ({b} : Set J) ⊓ Ez a).map φ.toMonoidHom =
      centralizer ({φ b} : Set X) ⊓ Ez (φ a) := by
    rw [← Ez_map φ a]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_left fun _ => ?_
    constructor
    · intro h
      have := congrArg φ h
      simpa using this
    · intro h
      apply φ.injective
      simpa using h
  rw [← hmap, Subgroup.card_map_of_injective φ.injective]

end Transport

end L3InvLin

theorem l3InvTorus_lin (J : Type) [Group J] [Finite J] (q : ℕ) (hq : Odd q) (hq5 : 5 ≤ q)
    (hJ : IsLnEps 3 J 1 q) (a b : J) (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b)
    (hcomm : a * b = b * a) :
    (Nat.card ↥(Subgroup.centralizer ({b} : Set J) ⊓ Ez a) : ℤ) = (q : ℤ) - 1 := by
  rcases hJ with ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨h, -⟩
  · have hodd : Odd (Nat.card F) := hF ▸ hq
    have h4 : 4 ≤ Nat.card F := by rw [hF]; omega
    have h2 : (2 : F) ≠ 0 := CFSG.GorensteinWalter.two_ne_zero_of_odd_card F hodd
    have h1a : orderOf (e a) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha
    have h1b : orderOf (e b) = 2 := by rw [MulEquiv.orderOf_eq]; exact hb
    have hne : e a ≠ e b := fun h => hab (e.injective h)
    have hc : e a * e b = e b * e a := by rw [← map_mul, ← map_mul, hcomm]
    obtain ⟨g, hg1, hg2⟩ := linConj F hodd (e a) (e b) h1a h1b hne hc
    have hφa : (e.trans (MulAut.conj g)) a = linU₀ F := by simpa [MulAut.conj_apply] using hg1
    have hφb : (e.trans (MulAut.conj g)) b = linU₀' F := by simpa [MulAut.conj_apply] using hg2
    have hcard := L3InvLin.card_centralizer_inf_Ez_of_iso (e.trans (MulAut.conj g)) a b
    rw [hφa, hφb, L3InvLin.card_centralizer_inf_Ez h2 h4] at hcard
    have hq1 : 1 ≤ q := by omega
    rw [hcard, hF]
    push_cast [Nat.cast_sub hq1]
    ring
  · exact absurd h (by norm_num)

end CFSG.GH74.GLS.LU.Local
