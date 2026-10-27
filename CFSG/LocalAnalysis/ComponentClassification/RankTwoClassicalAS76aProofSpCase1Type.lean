module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep74All
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSplitBC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSplitA

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Main

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]
  {A : Subgroup G}

theorem jGroup_ne_alphaGroup_sp {e : rankTwoQuot A ≃* StatedProj (StatedSp n K)}
    (hZ : Odd (Nat.card (center ↥A))) {p : G} {M : GL (Fin n ⊕ Fin n) K}
    (hpM : Represents e p M) (hM2 : orderOf M = 2) (hr : commRank M ≠ 1)
    (hc : ∃ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) ≠ 0) :
    jGroup A p ≠ alphaGroup e p := by
  intro hJ
  classical
  obtain ⟨B, hBdef⟩ : ∃ B, B = (quadPlus n K).polarBilin := ⟨_, rfl⟩
  have hB : B.Nondegenerate := by
    rw [hBdef]
    exact nondegenerate_polarBilin_quadPlus n K
  have hBs : ∀ x y, B x y = B y x := by
    rw [hBdef]
    exact polarBilin_comm (quadPlus n K)
  have hsymp : ∀ v w, B v w = sympForm n K v w := by
    rw [hBdef]
    exact polarBilin_quadPlus
  have hBX : ∀ {X : GL (Fin n ⊕ Fin n) K}, X ∈ StatedSp n K → ∀ u v,
      B ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u)
        ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = B u v := by
    intro X hX u v
    rw [hBdef]
    exact polarBilin_mulVec_of_mem_statedSp hX u v
  have hMsp : M ∈ StatedSp n K := hpM.2.1
  have hadj := polarBilin_sub_one_adj (hBX hMsp) hM2
  have hN := sub_one_mul_self_eq_zero hM2
  obtain ⟨z, hz⟩ := exists_sqrt_vector_of_adj hB hBs hadj
  have hz0 : z ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hc
    apply hv
    rw [← sympForm_sub_one_mulVec, ← hsymp, ← hz v, map_zero, zero_pow two_ne_zero]
  set E := polMat (quadPlus n K) z z with hE
  have hEv : ∀ v, E *ᵥ v = B v z • z := fun v => by
    rw [hE, polMat_mulVec, hBdef]
  have hEE : E * E = 0 := by
    rw [hE, polMat_mul, TypeCData.pol_self, zero_smul]
  have hEadj : ∀ u v, B (E *ᵥ u) v = B u (E *ᵥ v) := fun u v => by
    rw [hEv, hEv, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, hBs z v,
      mul_comm]
  obtain ⟨x₀, hx₀⟩ : ∃ x, B x z ≠ 0 := by
    by_contra! h
    exact hz0 (hB.2 z h)
  have hE0 : E ≠ 0 := fun h => by
    have h1 := hEv x₀
    rw [h, zero_mulVec] at h1
    exact hx₀ ((smul_eq_zero.mp h1.symm).resolve_right hz0)
  have hrE : E.rank = 1 := rank_eq_one_of hz0 (fun v => ⟨_, hEv v⟩)
    ⟨(B x₀ z)⁻¹ • x₀, by
      rw [hEv, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx₀, one_smul]⟩
  have hTH : unipGL E hEE 1 ∈ StatedSp n K := unipGL_mem_statedSp_of_adj hBdef hEE hEadj 1
  have hcommT : ∀ X : GL (Fin n ⊕ Fin n) K, X ∈ StatedSp n K →
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * M =
        (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * X →
      X * unipGL E hEE 1 = unipGL E hEE 1 * X := by
    intro X hX hXM
    have hXN : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) =
        ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) * X := by
      rw [mul_sub, sub_mul, hXM, mul_one, one_mul]
    have hXz := mulVec_sqrt_vector_of_commute_adj hB hz (hBX hX) hXN
    have hXE : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * E = E * X :=
      Matrix.ext_iff_mulVec.mpr fun v => by
        rw [← mulVec_mulVec, ← mulVec_mulVec, hEv, hEv, mulVec_smul, hXz]
        congr 1
        conv_rhs => rw [← hXz]
        exact (hBX hX v z).symm
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_unipGL, one_smul, mul_add, add_mul, mul_one, one_mul,
      hXE]
  obtain ⟨t, ht2, ht⟩ := exists_represents_sq_eq_one (e := e) hZ hTH (unipGL_sq hEE 1)
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hcent : ∀ x ∈ A ⊓ centralizer ({p} : Set G), x * t = t * x := by
    intro x hx
    obtain ⟨X, hX⟩ := exists_represents e hx.1
    have hxp : x * p = p * x := mem_centralizer_singleton_iff.mp hx.2
    exact commute_of_represents hZ hX ht ht2 (hcommT X hX.2.1 (hX.mul_comm_of_commute hpM hM2' hxp))
  have hpC : p ∈ A ⊓ centralizer ({p} : Set G) :=
    ⟨hpM.1, mem_centralizer_singleton_iff.mpr rfl⟩
  have htC : t ∈ A ⊓ centralizer ({p} : Set G) :=
    ⟨ht.1, mem_centralizer_singleton_iff.mpr (hcent p hpC).symm⟩
  have htJ : t ∈ jGroup A p := by
    refine ⟨?_, ?_⟩
    · refine le_pCoreIn_of_central (S := zpowers t) (zpowers_le.mpr htC) ?_ ?_ (mem_zpowers t)
      · intro s hs h hh
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
        exact (Commute.zpow_left (show Commute t h from (hcent h hh).symm) k).eq
      · intro s hs
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ht2,
          _root_.one_zpow]
    · show t ∈ centralizer (conjCommuting A p)
      rw [mem_centralizer_iff]
      rintro w ⟨b, hb, rfl, hcomm⟩
      exact hcent _ (Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem hb hpM.1) (A.inv_mem hb),
        mem_centralizer_singleton_iff.mpr hcomm.eq⟩)
  have hT1 : unipGL E hEE 1 ≠ 1 := unipGL_ne_one hEE one_ne_zero hE0
  have ht1 : t ≠ 1 := by
    rintro rfl
    obtain ⟨c, hc'⟩ := represents_one.exists_scalar ht
    have hc'' : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) + (1 : K) • E = (c : K) • 1 := by
      have h := congrArg (fun N : GL (Fin n ⊕ Fin n) K =>
        (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hc'
      simp only [coe_unipGL, one_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
      rw [h, Matrix.smul_one_eq_diagonal]
      rfl
    exact one_ne_zero (eq_zero_of_unip_eq_scalar hEE hE0 hc'')
  have hM1 : M ≠ 1 := fun h => by
    rw [h, orderOf_one] at hM2
    omega
  have hH : ∀ a : K, unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hN a ∈
      StatedSp n K := fun a => unipGL_mem_statedSp hMsp hM2' hN a
  obtain ⟨a, ha, -, hta⟩ := exists_of_mem_alphaGroup hZ hpM hM2 hN hH (hJ ▸ htJ) ht1
  have heq := ht.eq_of_orderOf_eq_two hta (orderOf_unipGL hEE one_ne_zero hE0)
    (orderOf_unipGL hN ha (sub_one_ne_zero hM1))
  have h1 := commRank_unipGL hEE (one_ne_zero (α := K))
  rw [heq, commRank_unipGL hN ha, hrE] at h1
  exact hr h1

end Main

theorem symplecticCase1Type : SymplecticCase1Type := by
  intro G _ _ A D hD _ hZ _ p ℓ hp hcase
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨hJ, -, -⟩ := hcase
    rcases hp with ⟨hℓ, -, M, hpM, hM2, hr, hodd⟩ | ⟨-, M, hpM, hM2, hr, hev, hc⟩
    · refine jGroup_ne_alphaGroup_sp hZ hpM hM2 (by omega) ?_ hJ
      by_contra! h
      have hev := even_commRank_of_sympForm_eq_zero hpM.2.1 hM2 h
      rw [hr] at hev
      exact Nat.not_even_iff_odd.mpr hodd hev
    · refine jGroup_ne_alphaGroup_sp hZ hpM hM2 ?_ hc hJ
      rw [hr]
      rintro rfl
      exact Nat.not_even_one hev
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
