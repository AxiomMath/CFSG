module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3ClassicalSp

public section

namespace CFSG.EvenSmallLie.Child3.SelK3Classical

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

@[ext] structure GF25 where
  re : ZMod 5
  im : ZMod 5
deriving DecidableEq

namespace GF25

@[expose] def equivProd : GF25 ≃ ZMod 5 × ZMod 5 where
  toFun x := (x.re, x.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype GF25 := Fintype.ofEquiv _ equivProd.symm
instance : Zero GF25 := ⟨⟨0, 0⟩⟩
instance : One GF25 := ⟨⟨1, 0⟩⟩
instance : Add GF25 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg GF25 := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Mul GF25 :=
  ⟨fun x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re - x.im * y.im⟩⟩

@[expose] def norm (x : GF25) : ZMod 5 := x.re * x.re - x.re * x.im + x.im * x.im

instance : Inv GF25 := ⟨fun x => ⟨(norm x)⁻¹ * (x.re - x.im), -((norm x)⁻¹ * x.im)⟩⟩

@[simp] theorem zero_re : (0 : GF25).re = 0 := rfl
@[simp] theorem zero_im : (0 : GF25).im = 0 := rfl
@[simp] theorem one_re : (1 : GF25).re = 1 := rfl
@[simp] theorem one_im : (1 : GF25).im = 0 := rfl
@[simp] theorem add_re (x y : GF25) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : GF25) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : GF25) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : GF25) : (-x).im = -x.im := rfl
@[simp] theorem mul_re (x y : GF25) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : GF25) :
    (x * y).im = x.re * y.im + x.im * y.re - x.im * y.im := rfl
@[simp] theorem inv_re (x : GF25) : x⁻¹.re = (norm x)⁻¹ * (x.re - x.im) := rfl
@[simp] theorem inv_im (x : GF25) : x⁻¹.im = -((norm x)⁻¹ * x.im) := rfl

theorem norm_ne_zero : ∀ x : GF25, x ≠ 0 → norm x ≠ 0 := by decide

instance : Field GF25 :=
  Field.ofMinimalAxioms GF25
    (fun a b c => by ext <;> simp <;> ring)
    (fun a => by ext <;> simp)
    (fun a => by ext <;> exact neg_add_cancel _)
    (fun a b c => by ext <;> simp <;> ring)
    (fun a b => by ext <;> simp <;> ring)
    (fun a => by ext <;> simp)
    (fun a ha => by
      have h := norm_ne_zero a ha
      ext
      · simp only [mul_re, inv_re, inv_im, one_re]
        rw [show a.re * (a.norm⁻¹ * (a.re - a.im)) - a.im * -(a.norm⁻¹ * a.im) =
          a.norm⁻¹ * (a.re * a.re - a.re * a.im + a.im * a.im) by ring]
        exact inv_mul_cancel₀ h
      · simp only [mul_im, inv_re, inv_im, one_im]
        ring)
    (by decide)
    (fun a b c => by ext <;> simp <;> ring)
    ⟨0, 1, by decide⟩

theorem card : Nat.card GF25 = 25 := by
  rw [Nat.card_eq_fintype_card]
  rfl

end GF25

section Scalars

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem eq_diagonal_of_mem_statedScalars {M : GL ι K} (hM : M ∈ StatedScalars ι K) (i : ι) :
    (M : Matrix ι ι K) = Matrix.diagonal fun _ => (M : Matrix ι ι K) i i := by
  obtain ⟨c, rfl⟩ := hM
  ext j k
  simp [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem not_mem_statedScalars_of_ne_diagonal {M : GL ι K} (i : ι)
    (h : (M : Matrix ι ι K) ≠ Matrix.diagonal fun _ => (M : Matrix ι ι K) i i) :
    M ∉ StatedScalars ι K :=
  fun hM => h (eq_diagonal_of_mem_statedScalars hM i)

end Scalars

section Concrete

abbrev M25 : Type := Matrix (Fin 3) (Fin 3) GF25

@[expose] def conjT (A : M25) : M25 := (A.map (· ^ 5))ᵀ

@[expose] def su5 (A : M25) (h1 : A * conjT A = 1) (h2 : conjT A * A = 1) (hdet : A.det = 1) :
    StatedSU 3 5 GF25 :=
  ⟨⟨A, conjT A, h1, h2⟩, Subgroup.subset_closure ⟨hdet, h2⟩⟩

@[expose] def gw : GF25 := ⟨0, 1⟩
@[expose] def gw2 : GF25 := ⟨4, 4⟩

@[expose] def mT : M25 := !![1, 0, 0; 0, gw, 0; 0, 0, gw2]
@[expose] def mC : M25 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
@[expose] def mW : M25 := !![gw, 0, 0; 0, gw, 0; 0, 0, gw]
@[expose] def mTU : M25 := !![1, 0, 0; 0, -1, 0; 0, 0, -1]
@[expose] def mTV : M25 := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
@[expose] def mCU : M25 :=
  !![⟨3, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩; ⟨4, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩; ⟨4, 0⟩, ⟨4, 0⟩, ⟨3, 0⟩]
@[expose] def mCV : M25 :=
  !![⟨3, 0⟩, ⟨0, 4⟩, ⟨1, 1⟩; ⟨1, 1⟩, ⟨3, 0⟩, ⟨0, 4⟩; ⟨0, 4⟩, ⟨1, 1⟩, ⟨3, 0⟩]
@[expose] def mTCU : M25 :=
  !![⟨3, 0⟩, ⟨1, 1⟩, ⟨4, 0⟩; ⟨0, 4⟩, ⟨3, 0⟩, ⟨0, 4⟩; ⟨4, 0⟩, ⟨1, 1⟩, ⟨3, 0⟩]
@[expose] def mTCV : M25 :=
  !![⟨3, 0⟩, ⟨4, 0⟩, ⟨1, 1⟩; ⟨4, 0⟩, ⟨3, 0⟩, ⟨1, 1⟩; ⟨0, 4⟩, ⟨0, 4⟩, ⟨3, 0⟩]
@[expose] def mT2CU : M25 :=
  !![⟨3, 0⟩, ⟨0, 4⟩, ⟨4, 0⟩; ⟨1, 1⟩, ⟨3, 0⟩, ⟨1, 1⟩; ⟨4, 0⟩, ⟨0, 4⟩, ⟨3, 0⟩]
@[expose] def mT2CV : M25 :=
  !![⟨3, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩; ⟨0, 4⟩, ⟨3, 0⟩, ⟨4, 0⟩; ⟨0, 4⟩, ⟨4, 0⟩, ⟨3, 0⟩]

@[expose] def suT : StatedSU 3 5 GF25 :=
  su5 mT (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suC : StatedSU 3 5 GF25 :=
  su5 mC (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suW : StatedSU 3 5 GF25 :=
  su5 mW (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suTU : StatedSU 3 5 GF25 :=
  su5 mTU (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suTV : StatedSU 3 5 GF25 :=
  su5 mTV (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suCU : StatedSU 3 5 GF25 :=
  su5 mCU (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suCV : StatedSU 3 5 GF25 :=
  su5 mCV (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suTCU : StatedSU 3 5 GF25 :=
  su5 mTCU (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suTCV : StatedSU 3 5 GF25 :=
  su5 mTCV (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suT2CU : StatedSU 3 5 GF25 :=
  su5 mT2CU (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)
@[expose] def suT2CV : StatedSU 3 5 GF25 :=
  su5 mT2CV (by decide) (by decide) (by rw [Matrix.det_fin_three]; decide)

abbrev PSU35 : Type := StatedProj (StatedSU 3 5 GF25)

theorem suW_mem_scalars : (suW : GL (Fin 3) GF25) ∈ StatedScalars (Fin 3) GF25 :=
  ⟨⟨gw, gw2, by decide, by decide⟩, Units.ext (by decide)⟩

theorem su5_not_mem_scalars {x : StatedSU 3 5 GF25}
    (h : ((x : GL (Fin 3) GF25) : M25) ≠
      Matrix.diagonal fun _ => ((x : GL (Fin 3) GF25) : M25) 0 0) :
    (x : GL (Fin 3) GF25) ∉ StatedScalars (Fin 3) GF25 :=
  not_mem_statedScalars_of_ne_diagonal 0 h

theorem su5_mul_comm {x y : StatedSU 3 5 GF25} (h : x * y = y * x) :
    (x : PSU35) * y = y * x := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem card_PSU35 : Nat.card PSU35 = 126000 := by
  have hT : StatedClassicalModel PSU35 .PSU 3 5 1 :=
    ⟨⟨by norm_num, le_rfl, le_rfl, by decide⟩, GF25, inferInstance, inferInstance,
      by rw [GF25.card]; norm_num, ⟨MulEquiv.refl _⟩⟩
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hT]
  decide

theorem orderOf_suT : orderOf (suT : PSU35) = 3 :=
  orderOf_statedProj_mk (by rw [(by decide : suT ^ 3 = 1)]; exact one_mem _)
    (su5_not_mem_scalars (by decide))

theorem orderOf_suC : orderOf (suC : PSU35) = 3 :=
  orderOf_statedProj_mk (by rw [(by decide : suC ^ 3 = 1)]; exact one_mem _)
    (su5_not_mem_scalars (by decide))

theorem commute_suT_suC : Commute (suT : PSU35) (suC : PSU35) := by
  change (suT : PSU35) * suC = suC * suT
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact statedProj_mk_eq_of_eq_mul (s := suW) (by decide) suW_mem_scalars

theorem suC_not_mem_zpowers : (suC : PSU35) ∉ zpowers (suT : PSU35) := by
  rw [mem_zpowers_of_orderOf_eq_three orderOf_suT]
  rintro (h | h | h)
  · exact su5_not_mem_scalars (by decide) ((statedProj_mk_eq_one_iff _).mp h)
  · exact su5_not_mem_scalars (x := suC⁻¹ * suT) (by decide)
      ((statedProj_mk_eq_mk_iff _ _).mp h)
  · rw [← QuotientGroup.mk_pow] at h
    exact su5_not_mem_scalars (x := suC⁻¹ * suT ^ 2) (by decide)
      ((statedProj_mk_eq_mk_iff _ _).mp h)

theorem four_dvd_card_centralizer_su5 {g u v : StatedSU 3 5 GF25} (hug : u * g = g * u)
    (hvg : v * g = g * v) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (huv : u * v = v * u)
    (hu : ((u : GL (Fin 3) GF25) : M25) ≠
      Matrix.diagonal fun _ => ((u : GL (Fin 3) GF25) : M25) 0 0)
    (hv : ((v : GL (Fin 3) GF25) : M25) ≠
      Matrix.diagonal fun _ => ((v : GL (Fin 3) GF25) : M25) 0 0)
    (huv' : (((u⁻¹ * v : StatedSU 3 5 GF25) : GL (Fin 3) GF25) : M25) ≠
      Matrix.diagonal fun _ => (((u⁻¹ * v : StatedSU 3 5 GF25) : GL (Fin 3) GF25) : M25) 0 0) :
    4 ∣ Nat.card (centralizer ({(g : PSU35)} : Set PSU35)) := by
  refine four_dvd_card_centralizer_of_klein (u := (u : PSU35)) (v := (v : PSU35))
    (orderOf_statedProj_mk (by rw [hu2]; exact one_mem _) (su5_not_mem_scalars hu))
    (orderOf_statedProj_mk (by rw [hv2]; exact one_mem _) (su5_not_mem_scalars hv)) ?_
    (su5_mul_comm huv) (su5_mul_comm hug) (su5_mul_comm hvg)
  intro h
  exact su5_not_mem_scalars huv' ((statedProj_mk_eq_mk_iff _ _).mp h)

theorem four_dvd_card_centralizer_suT :
    4 ∣ Nat.card (centralizer ({(suT : PSU35)} : Set PSU35)) :=
  four_dvd_card_centralizer_su5 (u := suTU) (v := suTV) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem four_dvd_card_centralizer_suC :
    4 ∣ Nat.card (centralizer ({(suC : PSU35)} : Set PSU35)) :=
  four_dvd_card_centralizer_su5 (u := suCU) (v := suCV) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem four_dvd_card_centralizer_suT_mul_suC :
    4 ∣ Nat.card (centralizer {(suT : PSU35) * suC}) := by
  rw [← QuotientGroup.mk_mul]
  exact four_dvd_card_centralizer_su5 (u := suTCU) (v := suTCV) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem four_dvd_card_centralizer_suT_sq_mul_suC :
    4 ∣ Nat.card (centralizer {(suT : PSU35) ^ 2 * suC}) := by
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
  exact four_dvd_card_centralizer_su5 (u := suT2CU) (v := suT2CV) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem four_dvd_card_centralizer_PSU35 (x : PSU35) (hx : orderOf x = 3) :
    4 ∣ Nat.card (centralizer {x}) :=
  four_dvd_card_centralizer_of_sylow (by rw [card_PSU35]; norm_num)
    (by rw [card_PSU35]; norm_num) orderOf_suT orderOf_suC commute_suT_suC
    suC_not_mem_zpowers four_dvd_card_centralizer_suT four_dvd_card_centralizer_suC
    four_dvd_card_centralizer_suT_mul_suC four_dvd_card_centralizer_suT_sq_mul_suC x hx

@[expose] def statedProjEquivOfEq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H H' : Subgroup (GL ι K)} (h : H = H') : StatedProj H ≃* StatedProj H' := by
  subst h
  exact MulEquiv.refl _

theorem four_dvd_card_centralizer_of_PSU_three_five {T : Type} [Group T]
    (hT : StatedClassicalModel T .PSU 3 5 1) (x : T) (hx : orderOf x = 3) :
    4 ∣ Nat.card (centralizer {x}) := by
  obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hT
  rw [pow_one] at hK
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card GF25 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GF25.card]
    norm_num
  set φ := FiniteField.ringEquivOfCardEq hcard
  set e : T ≃* PSU35 := (eT.trans (statedProjEquivOfEq (by rw [pow_one]))).trans
    (statedProjCongr (glCongr φ) (glCongr_statedSU φ 3 5) (glCongr_statedScalars φ))
  rw [← card_centralizer_mulEquiv e x]
  exact four_dvd_card_centralizer_PSU35 (e x) (by rw [MulEquiv.orderOf_eq]; exact hx)

end Concrete

end CFSG.EvenSmallLie.Child3.SelK3Classical
