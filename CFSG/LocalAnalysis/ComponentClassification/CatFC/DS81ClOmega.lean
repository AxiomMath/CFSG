module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClCore
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Basic

public section

namespace CFSG.ComponentClassification.CatFC.DS81.ClOmega

open Matrix Subgroup CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatFC.DS81.ClLift

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem gram_facts (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    IsUnit (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)).det ∧
      (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q))ᵀ =
        LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) ∧
      ∀ u v : ι → K, Q (u + v) = Q u + Q v +
        u ⬝ᵥ (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) *ᵥ v) := by
  set M := LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) with hM
  have hB : Matrix.toBilin' M = QuadraticMap.polarBilin Q := by
    rw [hM, Matrix.toBilin'_toMatrix']
  refine ⟨?_, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, ← LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero, hB]
    exact hQ
  · ext i j
    rw [Matrix.transpose_apply, hM, LinearMap.BilinForm.toMatrix'_apply,
      LinearMap.BilinForm.toMatrix'_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  · intro u v
    have h1 : u ⬝ᵥ (M *ᵥ v) = QuadraticMap.polar Q u v := by
      rw [← Matrix.toBilin'_apply', hB, QuadraticMap.polarBilin_apply_apply]
    rw [h1, QuadraticMap.polar]
    ring

theorem quad_mulVec_of_mem_closure {Q₀ : (ι → K) → K} {A : GL ι K}
    (hA : A ∈ Subgroup.closure {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v})
    (v : ι → K) : Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v := by
  induction hA using Subgroup.closure_induction generalizing v with
  | mem A hA => exact hA v
  | one => simp
  | mul A B _ _ hA hB => rw [Units.val_mul, ← mulVec_mulVec, hA, hB]
  | inv A _ hA =>
    have h1 := hA (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h1
    exact h1.symm

theorem quad_mulVec_of_mem_statedOmega {Q₀ : (ι → K) → K} {A : GL ι K}
    (hA : A ∈ StatedOmega Q₀) (v : ι → K) : Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v := by
  have hle : StatedOmega Q₀ ≤
      Subgroup.closure {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v} := by
    refine Subgroup.commutator_le.2 ?_
    intro a ha b hb
    rw [commutatorElement_def]
    exact (Subgroup.closure _).mul_mem ((Subgroup.closure _).mul_mem
      ((Subgroup.closure _).mul_mem ha hb) ((Subgroup.closure _).inv_mem ha))
      ((Subgroup.closure _).inv_mem hb)
  exact quad_mulVec_of_mem_closure (hle hA) v

theorem mem_statedOmega_of_odd_order [Finite K] {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {y : GL ι K} (hy : ∀ v, Q₀ ((y : Matrix ι ι K) *ᵥ v) = Q₀ v) {m : ℕ} (hm : Odd m)
    (hym : y ^ m = 1) : y ∈ StatedOmega Q₀ := by
  have hodd := (CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts
    hnd hT).2.2.2.2.2.2.1
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ, Subgroup.mem_comap]
  have hg : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K y ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hQ]
      exact hy v
  have hord : Odd (orderOf (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K y)) := by
    rw [MulEquiv.orderOf_eq]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym)
  exact hodd _ hg hord

theorem eightynine_dvd_card_centralizer [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (τ : StatedProj (StatedOmega Q₀)) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedOmega Q₀))))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedOmega Q₀)))) := by
  classical
  obtain ⟨hMu, hMT, hpolar⟩ := gram_facts Q hnd
  set M := LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) with hMdef
  have hpolar0 : ∀ u v, Q₀ (u + v) = Q₀ u + Q₀ v + u ⬝ᵥ (M *ᵥ v) := by
    intro u v; rw [← hQ]; exact hpolar u v
  obtain ⟨th, rfl⟩ := QuotientGroup.mk_surjective τ
  have hτ2 : (QuotientGroup.mk th : StatedProj (StatedOmega Q₀)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk th : StatedProj (StatedOmega Q₀))
    rwa [hτ] at this
  obtain ⟨yh, b, hyb, hy1, hc⟩ := exists_commuting_pow_lift th hτ2 h23
  set g : Matrix ι ι K := (((yh : StatedOmega Q₀) : GL ι K) : Matrix ι ι K) with hg
  have hgQ : ∀ v, Q₀ (g *ᵥ v) = Q₀ v := quad_mulVec_of_mem_statedOmega yh.2
  have hgb : g ^ (23 ^ b) = 1 := (pow_eq_one_iff_matrix yh _).mp hyb
  have hg1 : g ≠ 1 := by
    intro h
    apply hy1
    rw [(matrix_eq_one_iff yh).mp h, QuotientGroup.mk_one]
  haveI : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hg1 (Subsingleton.elim _ _)
  obtain ⟨zM, hzR, hzQ, hz89, hz1⟩ := ClCore.exists_quadForm_order_eightynine Q₀ M hMu hMT
    hpolar0 g hgQ hgb hg1
  let zU : GL ι K := glOfPow89 zM hz89
  have hzU : (zU : Matrix ι ι K) = zM := rfl
  have hzU89 : zU ^ 89 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hzU, hz89, Units.val_one])
  have hzmem : zU ∈ StatedOmega Q₀ :=
    mem_statedOmega_of_odd_order hQ hnd hT (by rw [hzU]; exact hzQ) (by decide : Odd 89) hzU89
  let zh : StatedOmega Q₀ := ⟨zU, hzmem⟩
  have hzh : (((zh : StatedOmega Q₀) : GL ι K) : Matrix ι ι K) = zM := rfl
  have hcm : Commute ((((th : StatedOmega Q₀) : GL ι K) : Matrix ι ι K)) g :=
    (commute_iff_matrix th yh).mp hc
  have hcz : Commute zM ((((th : StatedOmega Q₀) : GL ι K) : Matrix ι ι K)) :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hzR hcm).symm
  have hzth : Commute th zh := by
    rw [commute_iff_matrix, hzh]
    exact hcz.symm
  have hzh89 : zh ^ 89 = 1 := (pow_eq_one_iff_matrix zh 89).mpr (by rw [hzh]; exact hz89)
  have hzM : (zM.map (RingHom.id K))ᵀ * M * zM = M := by
    rw [show zM.map (RingHom.id K) = zM from Matrix.map_id' zM]
    apply ClCore.eq_of_dotProduct_mulVec
    intro x y
    rw [← ClCore.dotProduct_mulVec_conj]
    have h1 := hpolar0 (zM *ᵥ x) (zM *ᵥ y)
    have h2 := hpolar0 x y
    rw [← Matrix.mulVec_add, hzQ, hzQ, hzQ] at h1
    exact add_left_cancel (h1.symm.trans h2)
  have hzne : (QuotientGroup.mk zh : StatedProj (StatedOmega Q₀)) ≠ 1 := by
    apply mk_ne_one_of_not_scalar
    intro c hcM
    rw [hzh] at hcM
    have hc89 : c ^ 89 = 1 := by
      have h1 : Matrix.scalar ι (c ^ 89) = Matrix.scalar ι 1 := by
        rw [map_pow, ← hcM, hz89, map_one]
      exact (Matrix.scalar_inj).mp h1
    have hcc : c * c = 1 := form_scalar (RingHom.id K) M hMu c (by rw [← hcM]; exact hzM)
    have hc2 : c ^ 2 = 1 := by rw [sq]; exact hcc
    have hc1 : c = 1 := eq_one_of_pow_eq_one_of_coprime (by norm_num : Nat.Coprime 2 89) hc2 hc89
    apply hz1
    rw [hcM, hc1, map_one]
  exact eightynine_dvd_of_commute th zh hzth hzh89 hzne

theorem lie23To89_pomegaPlus {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hm : StatedClassicalModel X .POmegaPlus n 2 f) (τ : X) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set X))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set X)) := by
  obtain ⟨hadm, K, _, _, hcard, ⟨φ⟩⟩ := hm
  have hn : 4 ≤ n := hadm.2.2
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n)
    (by omega)
  rw [card_centralizer_eq φ τ] at h23 ⊢
  exact eightynine_dvd_card_centralizer (CFSG.LieType.Universal.Spin.coe_quadPlus n K) hnd hT
    (φ τ) (by rw [MulEquiv.orderOf_eq]; exact hτ) h23

theorem lie23To89_pomegaMinus {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hm : StatedClassicalModel X .POmegaMinus n 2 f) (τ : X) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set X))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set X)) := by
  obtain ⟨hadm, K, _, _, hcard, b, c, hirr, ⟨φ⟩⟩ := hm
  have hn : 4 ≤ n := hadm.2.2
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) hn hirr
  rw [card_centralizer_eq φ τ] at h23 ⊢
  exact eightynine_dvd_card_centralizer (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c) hnd hT
    (φ τ) (by rw [MulEquiv.orderOf_eq]; exact hτ) h23

end CFSG.ComponentClassification.CatFC.DS81.ClOmega
