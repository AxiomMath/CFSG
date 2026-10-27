module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUModGens
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUModFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Recognition.HSMultiplier
  Matrix

@[expose] def mzNegData : List ℕ := [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3]

theorem matOfList_mzNegData : matOfList mzNegData = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem mzRData_lt : ∀ x ∈ mzRData, x < 4 := by decide

theorem mzRData_c2 : colOf mzRData 2 = [0, 0, 1, 0] := by decide

theorem mzRData_ev : ∀ j ∈ [0, 1, 3], (colOf mzRData j).getD 2 0 % 2 = 0 := by decide

theorem mzNegData_lt : ∀ x ∈ mzNegData, x < 4 := by decide

theorem mzNegData_c2 : colOf mzNegData 2 = [0, 0, 3, 0] := by decide

theorem mzNegData_ev : ∀ j ∈ [0, 1, 3], (colOf mzNegData j).getD 2 0 % 2 = 0 := by decide

theorem mzEps_lt : ∀ i, mzEps.getD i 0 < 4 := by
  intro i
  by_cases hi : i < 4
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [mzEps]; omega)]
    decide

theorem mzEps_ev : mzEps.getD 2 0 % 2 = 0 := by decide

theorem vecOfList_mzEps_add : vecOfList mzEps + vecOfList mzEps = 0 := by
  funext i
  fin_cases i <;> decide

theorem ECoord.inv_conj_of_mat_eq_neg_one {G : Type} [Group G] {C : ECoord G} {x : G}
    (hx : x ∈ normalizer (C.E : Set G)) (hxm : C.mat x = -1) {e : G} (he : e ∈ C.E) :
    x * e * x⁻¹ = e⁻¹ := by
  have := C.conj_elt hx (C.vec e)
  rw [C.elt_vec he, hxm, neg_mulVec, one_mulVec, C.elt_neg, C.elt_vec he] at this
  exact this

section Model

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f y : G}

theorem bL_comm_f2 (hF : FourHyp G L f) (ι : L ≃* HSCover) (l : HSCover) :
    bL ι l * f ^ 2 = f ^ 2 * bL ι l :=
  ((show Commute (bL ι l) f from bL_comm_f hF ι l).pow_right 2).eq

theorem ModelData.y₁_comm_f2 (hF : FourHyp G L f) (M : ModelData G L y)
    (hy₁f : M.y₁ * f * M.y₁⁻¹ = f⁻¹) : M.y₁ * f ^ 2 = f ^ 2 * M.y₁ := by
  have hsq : M.y₁ * f ^ 2 * M.y₁⁻¹ = f ^ 2 := by
    have e : M.y₁ * f ^ 2 * M.y₁⁻¹ = (M.y₁ * f * M.y₁⁻¹) ^ 2 := conj_pow.symm
    rw [e, hy₁f]
    have h2 : f ^ 2 * f ^ 2 = 1 := by rw [← pow_add]; exact hF.pow_four
    calc f⁻¹ ^ 2 = (f ^ 2)⁻¹ := by group
      _ = f ^ 2 := inv_eq_of_mul_eq_one_right h2
  calc M.y₁ * f ^ 2 = (M.y₁ * f ^ 2 * M.y₁⁻¹) * M.y₁ := by group
    _ = f ^ 2 * M.y₁ := by rw [hsq]

theorem ModelData.y₁_mul_bL (M : ModelData G L y) (l : HSCover) :
    M.y₁ * bL M.ι l = bL M.ι (M.hΛ.sigma l) * M.y₁ := by
  calc M.y₁ * bL M.ι l = (M.y₁ * bL M.ι l * M.y₁⁻¹) * M.y₁ := by group
    _ = bL M.ι (M.hΛ.sigma l) * M.y₁ := by rw [M.conj_bL]

theorem ModelData.y₁_mul_bL_inv (M : ModelData G L y) (l : HSCover) :
    M.y₁ * (bL M.ι l)⁻¹ = (bL M.ι (M.hΛ.sigma l))⁻¹ * M.y₁ := by
  have := M.y₁_mul_bL l⁻¹
  rwa [bL_inv, map_inv, bL_inv] at this

theorem ModelData.conj_L_aY (M : ModelData G L y) (l a : HSCover) :
    bL M.ι l * (bL M.ι a * M.y₁) * (bL M.ι l)⁻¹ =
      bL M.ι (l * a * (M.hΛ.sigma l)⁻¹) * M.y₁ := by
  calc bL M.ι l * (bL M.ι a * M.y₁) * (bL M.ι l)⁻¹
      = bL M.ι l * bL M.ι a * (M.y₁ * (bL M.ι l)⁻¹) := by group
    _ = bL M.ι l * bL M.ι a * ((bL M.ι (M.hΛ.sigma l))⁻¹ * M.y₁) := by rw [M.y₁_mul_bL_inv]
    _ = bL M.ι (l * a * (M.hΛ.sigma l)⁻¹) * M.y₁ := by
      rw [bL_mul, bL_mul, bL_inv]
      group

theorem ModelData.conj_LY_aY (M : ModelData G L y) (l a : HSCover) :
    (bL M.ι l * M.y₁) * (bL M.ι a * M.y₁) * (bL M.ι l * M.y₁)⁻¹ =
      bL M.ι (l * M.hΛ.sigma a * (M.hΛ.sigma l)⁻¹) * M.y₁ := by
  have hinv : M.y₁⁻¹ = M.y₁ := inv_eq_of_mul_eq_one_right M.sq
  rw [_root_.mul_inv_rev, hinv]
  calc bL M.ι l * M.y₁ * (bL M.ι a * M.y₁) * (M.y₁ * (bL M.ι l)⁻¹)
      = bL M.ι l * (M.y₁ * bL M.ι a) * (M.y₁ * M.y₁) * (bL M.ι l)⁻¹ := by group
    _ = bL M.ι l * (bL M.ι (M.hΛ.sigma a) * M.y₁) * 1 * (bL M.ι l)⁻¹ := by
      rw [M.y₁_mul_bL a, M.sq]
    _ = bL M.ι l * bL M.ι (M.hΛ.sigma a) * (M.y₁ * (bL M.ι l)⁻¹) := by group
    _ = bL M.ι l * bL M.ι (M.hΛ.sigma a) * ((bL M.ι (M.hΛ.sigma l))⁻¹ * M.y₁) := by
      rw [M.y₁_mul_bL_inv]
    _ = bL M.ι (l * M.hΛ.sigma a * (M.hΛ.sigma l)⁻¹) * M.y₁ := by
      rw [bL_mul, bL_mul, bL_inv]
      group

theorem zdata_model (hF : FourHyp G L f) (hyy : y * y = 1)
    (hyf : y * f * y⁻¹ = f⁻¹)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) (M : ModelData G L y) :
    ZData (basisCoord M.hΛ hF M.ι) L f y (bL M.ι mzR) (bL M.ι mzA * M.y₁) (bL M.ι mzP) := by
  obtain ⟨hR3, hR1, hRrel, hAA, hArel, hRA, hP3, hP1, hPR, hPR2, hPRc, hPA, hg1, hg2⟩ :=
    M.hΛ.mz_facts
  set C := basisCoord M.hΛ hF M.ι with hC
  have hy₁f : M.y₁ * f * M.y₁⁻¹ = f⁻¹ := H1_conj_f_of_not_mem hF hyy hyf hN M.mem M.not_mem
  have hy₁c : M.y₁ * f ^ 2 = f ^ 2 * M.y₁ := M.y₁_comm_f2 hF hy₁f
  have hbc := bL_comm_f2 hF M.ι
  have hrel : ∀ j < 3, mzR * bet j * mzR⁻¹ = kapL (colOf mzRData ([0, 1, 3].getD j 0)) := by
    intro j hj
    rw [hRrel j hj]
    group
  have hrn : bL M.ι mzR ∈ normalizer (C.E : Set G) :=
    realL_normalizer hF M mzRData_lt mzRData_c2 mzRData_ev hrel
  have hrM : bL M.ι mzR ∈ SAU.M0 C f := SAU.mem_M0.2 ⟨hbc mzR, hrn⟩
  have hrelA : ∀ j < 3, mzA * M.hΛ.sigma (bet j) * mzA⁻¹ =
      kapL (colOf mzNegData ([0, 1, 3].getD j 0)) := by
    intro j hj
    rw [hArel j hj]
    have : bet j ^ 3 * mzA * mzA⁻¹ = bet j ^ 3 := by group
    rw [this]
    interval_cases j <;> simp [kapL, colOf, mzNegData]
  have hwn : bL M.ι mzA * M.y₁ ∈ normalizer (C.E : Set G) :=
    realLy_normalizer hF M hy₁f mzNegData_lt mzNegData_c2 mzNegData_ev hrelA
  have hwm : C.mat (bL M.ι mzA * M.y₁) = -1 := by
    rw [realLy_mat hF M hy₁f mzNegData_lt mzNegData_c2 mzNegData_ev hrelA]
    exact matOfList_mzNegData
  have hwinv : ∀ e ∈ C.E, (bL M.ι mzA * M.y₁) * e * (bL M.ι mzA * M.y₁)⁻¹ = e⁻¹ :=
    fun e he => ECoord.inv_conj_of_mat_eq_neg_one hwn hwm he
  have hwt : bL M.ι mzA * M.y₁ * f ^ 2 = f ^ 2 * (bL M.ι mzA * M.y₁) := by
    calc bL M.ι mzA * M.y₁ * f ^ 2 = bL M.ι mzA * (M.y₁ * f ^ 2) := by rw [mul_assoc]
      _ = bL M.ι mzA * (f ^ 2 * M.y₁) := by rw [hy₁c]
      _ = (bL M.ι mzA * f ^ 2) * M.y₁ := by rw [mul_assoc]
      _ = f ^ 2 * (bL M.ι mzA * M.y₁) := by rw [hbc mzA, mul_assoc]
  have hwM : bL M.ι mzA * M.y₁ ∈ SAU.M0 C f := SAU.mem_M0.2 ⟨hwt, hwn⟩
  have hwH : bL M.ι mzA * M.y₁ ∈ L ⊔ zpowers y :=
    (L ⊔ zpowers y).mul_mem (Subgroup.mem_sup_left (bL_mem M.ι mzA)) M.mem
  have hww : bL M.ι mzA * M.y₁ * (bL M.ι mzA * M.y₁) = 1 := by
    calc bL M.ι mzA * M.y₁ * (bL M.ι mzA * M.y₁)
        = bL M.ι mzA * (M.y₁ * bL M.ι mzA) * M.y₁ := by group
      _ = bL M.ι mzA * (bL M.ι (M.hΛ.sigma mzA) * M.y₁) * M.y₁ := by rw [M.y₁_mul_bL]
      _ = bL M.ι (mzA * M.hΛ.sigma mzA) * (M.y₁ * M.y₁) := by rw [bL_mul]; group
      _ = 1 := by rw [hAA, M.sq, bL_one, one_mul]
  have hLF : ListFacts := Certificates.certificate26753
  obtain ⟨hact, hcent⟩ := ModelData.count_core hF hyy hyf hN M
  have hx₁n : bL M.ι gamma1L ∈ normalizer (C.E : Set G) :=
    ModelData.normalizer_of_basis hF M fun j => by
      rw [ModelData.hx1 hF M j]
      exact C.elt_mem _
  have hx₁m : C.mat (bL M.ι gamma1L) = gamma1Mat :=
    mat_eq_of_conj_basis fun j => by
      rw [ModelData.elt_single hF M j]
      exact ModelData.hx1 hF M j
  have hx₂n : bL M.ι gamma2L * M.y₁ ∈ normalizer (C.E : Set G) :=
    ModelData.normalizer_of_basis hF M fun j => by
      rw [ModelData.hx2 hF hyy hyf hN M j]
      exact C.elt_mem _
  have hx₂m : C.mat (bL M.ι gamma2L * M.y₁) = gamma2Mat :=
    mat_eq_of_conj_basis fun j => by
      rw [ModelData.elt_single hF M j]
      exact ModelData.hx2 hF hyy hyf hN M j
  have hx₂t : bL M.ι gamma2L * M.y₁ * f ^ 2 = f ^ 2 * (bL M.ι gamma2L * M.y₁) := by
    calc bL M.ι gamma2L * M.y₁ * f ^ 2 = bL M.ι gamma2L * (M.y₁ * f ^ 2) := by rw [mul_assoc]
      _ = bL M.ι gamma2L * (f ^ 2 * M.y₁) := by rw [hy₁c]
      _ = (bL M.ι gamma2L * f ^ 2) * M.y₁ := by rw [mul_assoc]
      _ = f ^ 2 * (bL M.ι gamma2L * M.y₁) := by rw [hbc gamma2L, mul_assoc]
  have hκ : bL M.ι (kapL mzEps) = C.elt (vecOfList mzEps) :=
    bL_kapL M.hΛ hF M.ι mzEps_lt mzEps_ev
  have hκE : bL M.ι (kapL mzEps) ∈ C.E := by rw [hκ]; exact C.elt_mem _
  have hκκ : bL M.ι (kapL mzEps) * bL M.ι (kapL mzEps) = 1 := by
    rw [hκ, ← C.elt_add, vecOfList_mzEps_add, C.elt_zero]
  have hκw : bL M.ι (kapL mzEps) * (bL M.ι mzA * M.y₁) =
      (bL M.ι mzA * M.y₁) * bL M.ι (kapL mzEps) := by
    have h1 := hwinv _ hκE
    have h2 : (bL M.ι (kapL mzEps))⁻¹ = bL M.ι (kapL mzEps) := inv_eq_of_mul_eq_one_right hκκ
    rw [h2] at h1
    calc bL M.ι (kapL mzEps) * (bL M.ι mzA * M.y₁)
        = ((bL M.ι mzA * M.y₁) * bL M.ι (kapL mzEps) * (bL M.ι mzA * M.y₁)⁻¹) *
          (bL M.ι mzA * M.y₁) := by rw [h1]
      _ = (bL M.ι mzA * M.y₁) * bL M.ι (kapL mzEps) := by group
  have hcl : Cl16 C f (bL M.ι mzA * M.y₁) := by
    refine cl16_of_gens hLF hact hcent hwinv hwn (hbc gamma1L) hx₁n hx₁m hx₂t hx₂n hx₂m ?_ ?_
    · refine ⟨bL M.ι (kapL mzEps), hκE, hκκ, ?_⟩
      have e1 : gamma1L * mzA * (M.hΛ.sigma gamma1L)⁻¹ = kapL mzEps * mzA := by
        rw [hg1]
        group
      calc bL M.ι gamma1L * (bL M.ι mzA * M.y₁) * (bL M.ι gamma1L)⁻¹
          = bL M.ι (gamma1L * mzA * (M.hΛ.sigma gamma1L)⁻¹) * M.y₁ := M.conj_L_aY _ _
        _ = bL M.ι (kapL mzEps) * (bL M.ι mzA * M.y₁) := by rw [e1, bL_mul, mul_assoc]
        _ = (bL M.ι mzA * M.y₁) * bL M.ι (kapL mzEps) := hκw
    · refine ⟨bL M.ι (kapL mzEps), hκE, hκκ, ?_⟩
      have e2 : gamma2L * M.hΛ.sigma mzA * (M.hΛ.sigma gamma2L)⁻¹ = kapL mzEps * mzA := by
        rw [hg2]
        group
      calc (bL M.ι gamma2L * M.y₁) * (bL M.ι mzA * M.y₁) * (bL M.ι gamma2L * M.y₁)⁻¹
          = bL M.ι (gamma2L * M.hΛ.sigma mzA * (M.hΛ.sigma gamma2L)⁻¹) * M.y₁ :=
            M.conj_LY_aY _ _
        _ = bL M.ι (kapL mzEps) * (bL M.ι mzA * M.y₁) := by rw [e2, bL_mul, mul_assoc]
        _ = (bL M.ι mzA * M.y₁) * bL M.ι (kapL mzEps) := hκw
  have hr3 : bL M.ι mzR ^ 3 = 1 := by rw [← bL_pow, hR3, bL_one]
  have hr1 : bL M.ι mzR ≠ 1 := fun h => hR1 (bL_injective M.ι (h.trans (bL_one M.ι).symm))
  refine ⟨hrM, hr3, hr1, ⟨hwM, hwinv, hwH⟩, hww, hcl, ?_, by rw [← bL_pow, hP3, bL_one],
    hbc mzP, ?_, ?_, ?_⟩
  · calc bL M.ι mzR * (bL M.ι mzA * M.y₁) = bL M.ι (mzR * mzA) * M.y₁ := by
          rw [bL_mul, mul_assoc]
      _ = bL M.ι (mzA * M.hΛ.sigma mzR) * M.y₁ := by rw [hRA]
      _ = bL M.ι mzA * (bL M.ι (M.hΛ.sigma mzR) * M.y₁) := by rw [bL_mul, mul_assoc]
      _ = bL M.ι mzA * (M.y₁ * bL M.ι mzR) := by rw [M.y₁_mul_bL]
      _ = (bL M.ι mzA * M.y₁) * bL M.ι mzR := by rw [mul_assoc]
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    have hrord : orderOf (bL M.ι mzR) = 3 := orderOf_eq_prime hr3 hr1
    have hmod : (bL M.ι mzR) ^ (k % 3) = bL M.ι mzP := by
      rw [← hk]
      have := zpow_mod_orderOf (bL M.ι mzR) k
      rw [hrord] at this
      exact_mod_cast this
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · rw [h0, zpow_zero] at hmod
      exact hP1 (bL_injective M.ι (hmod.symm.trans (bL_one M.ι).symm))
    · rw [h1, zpow_one] at hmod
      exact hPR (bL_injective M.ι hmod.symm)
    · rw [h2] at hmod
      have : bL M.ι (mzR * mzR) = bL M.ι mzP := by
        rw [bL_mul, ← hmod, zpow_two]
      exact hPR2 (bL_injective M.ι this).symm
  · calc bL M.ι mzP * bL M.ι mzR = bL M.ι (mzP * mzR) := (bL_mul _ _ _).symm
      _ = bL M.ι (mzR * mzP) := by rw [hPRc]
      _ = bL M.ι mzR * bL M.ι mzP := bL_mul _ _ _
  · calc bL M.ι mzP * (bL M.ι mzA * M.y₁) = bL M.ι (mzP * mzA) * M.y₁ := by
          rw [bL_mul, mul_assoc]
      _ = bL M.ι (mzA * M.hΛ.sigma mzP) * M.y₁ := by rw [hPA]
      _ = bL M.ι mzA * (bL M.ι (M.hΛ.sigma mzP) * M.y₁) := by rw [bL_mul, mul_assoc]
      _ = bL M.ι mzA * (M.y₁ * bL M.ι mzP) := by rw [M.y₁_mul_bL]
      _ = (bL M.ι mzA * M.y₁) * bL M.ι mzP := by rw [mul_assoc]

end Model

end CFSG.EvenSporadicStandard.TwoHS
