module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Basic
public import CFSG.Open.StatedAPI

public section

namespace CFSG.ComponentClassification.CatFC.DS81.ClSp

open Matrix Subgroup CFSG.Open CFSG.ComponentClassification.CatFC.DS81.ClLift

variable {n : ℕ} {K : Type} [Field K]

abbrev J (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 0 1 (-1) 0

theorem J_mul_J : J n K * J n K = -1 := by
  simp only [J, fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem isUnit_det_J : IsUnit (J n K).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := -J n K)
  rw [Matrix.mul_neg, J_mul_J, neg_neg]

theorem J_transpose [CharP K 2] : ((J n K).map (RingHom.id K))ᵀ = J n K := by
  rw [show (J n K).map (RingHom.id K) = J n K from Matrix.map_id' _]
  simp only [J, fromBlocks_transpose, transpose_zero, transpose_one, transpose_neg]
  have h : (-1 : Matrix (Fin n) (Fin n) K) = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, CharTwo.neg_eq]
  rw [h]

theorem eightynine_dvd_card_centralizer [Finite K] [CharP K 2]
    (τ : StatedProj (StatedSp n K)) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSp n K))))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSp n K)))) := by
  classical
  obtain ⟨th, rfl⟩ := QuotientGroup.mk_surjective τ
  have hτ2 : (QuotientGroup.mk th : StatedProj (StatedSp n K)) ^ 2 = 1 := by
    rw [← hτ]; exact pow_orderOf_eq_one _
  obtain ⟨yh, b, hyb, hy1, hc⟩ := exists_commuting_pow_lift th hτ2 h23
  set g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (((yh : StatedSp n K) : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    with hg
  have hgform : (g.map (RingHom.id K))ᵀ * J n K * g = J n K := by
    rw [show g.map (RingHom.id K) = g from Matrix.map_id' g]
    exact StatedAPI.mem_statedSp_iff.mp yh.2
  have hgb : g ^ (23 ^ b) = 1 := (pow_eq_one_iff_matrix yh _).mp hyb
  have hg1 : g ≠ 1 := by
    intro h
    apply hy1
    rw [(matrix_eq_one_iff yh).mp h, QuotientGroup.mk_one]
  obtain ⟨zM, hzR, hzform, hz89, hz1⟩ := ClCore.exists_form_order_eightynine (RingHom.id K)
    (fun _ => rfl) (J n K) isUnit_det_J J_transpose g hgform hgb hg1
  let zU : GL (Fin n ⊕ Fin n) K := glOfPow89 zM hz89
  have hzU : (zU : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = zM := rfl
  have hzform' : (zU : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J n K *
      (zU : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J n K := by
    rw [hzU]
    rwa [show zM.map (RingHom.id K) = zM from Matrix.map_id' zM] at hzform
  let zh : StatedSp n K := ⟨zU, StatedAPI.mem_statedSp_iff.mpr hzform'⟩
  have hzh : (((zh : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = zM := rfl
  have hcm : Commute ((((th : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) g := (commute_iff_matrix th yh).mp hc
  have hcz : Commute zM ((((th : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hzR hcm).symm
  have hzth : Commute th zh := by
    rw [commute_iff_matrix, hzh]
    exact hcz.symm
  have hzh89 : zh ^ 89 = 1 := (pow_eq_one_iff_matrix zh 89).mpr (by rw [hzh]; exact hz89)
  have hzne : (QuotientGroup.mk zh : StatedProj (StatedSp n K)) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot,
      Subgroup.mem_bot] at h
    apply hz1
    rw [← hzh, (matrix_eq_one_iff zh).mpr h]
  exact eightynine_dvd_of_commute th zh hzth hzh89 hzne

theorem lie23To89_psp {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hm : StatedClassicalModel X .PSp n 2 f) (τ : X) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set X))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set X)) := by
  obtain ⟨-, K, _, _, hcard, ⟨φ⟩⟩ := hm
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  rw [card_centralizer_eq φ τ] at h23 ⊢
  exact eightynine_dvd_card_centralizer (φ τ) (by rw [MulEquiv.orderOf_eq]; exact hτ) h23

end CFSG.ComponentClassification.CatFC.DS81.ClSp
