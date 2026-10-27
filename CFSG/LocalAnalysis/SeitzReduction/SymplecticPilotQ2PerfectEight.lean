module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotPositionB
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Perfect
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.ComponentClassification.PresentationLocal (sympFour isPerfect_commutator_sympFour
  isSimpleGroup_commutator_sympFour)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

section Helpers

variable {G : Type*} [Group G]

theorem commElt_mul_right_of_commute_spQ2 {a b c : G} (h : a * c = c * a) :
    ⁅a, b * c⁆ = ⁅a, b⁆ := by
  have h' : c * a⁻¹ * c⁻¹ = a⁻¹ := by
    have hc : Commute a c := h
    rw [← (Commute.inv_left hc).eq, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹ = a * b * (c * a⁻¹ * c⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h']

theorem commElt_mul_right_eq_spQ2 (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
  group

theorem commutator_sup_le_sup_commutator_of_le_normalizer {Q M : Subgroup G}
    (hMN : M ≤ normalizer (Q : Set G)) : ⁅Q ⊔ M, Q ⊔ M⁆ ≤ Q ⊔ ⁅M, M⁆ := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₁' : g₁ ∈ ((Q ⊔ M : Subgroup G) : Set G) := hg₁
  have hg₂' : g₂ ∈ ((Q ⊔ M : Subgroup G) : Set G) := hg₂
  rw [coe_mul_of_right_le_normalizer_left Q M hMN] at hg₁' hg₂'
  obtain ⟨q₁, hq₁, m₁, hm₁, rfl⟩ := hg₁'
  obtain ⟨q₂, hq₂, m₂, hm₂, rfl⟩ := hg₂'
  have hc : ∀ {m q : G}, m ∈ M → q ∈ Q → m * q * m⁻¹ ∈ Q := fun hm hq =>
    (mem_normalizer_iff.1 (hMN hm) _).1 hq
  have e : ⁅q₁ * m₁, q₂ * m₂⁆ = q₁ * (m₁ * q₂ * m₁⁻¹) * ⁅m₁, m₂⁆ * (m₂ * q₁⁻¹ * m₂⁻¹) * q₂⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [e]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mem_sup_left hq₁) (mem_sup_left (hc hm₁ hq₂)))
    (mem_sup_right (commutator_mem_commutator hm₁ hm₂)))
    (mem_sup_left (hc hm₂ (inv_mem hq₁)))) (mem_sup_left (inv_mem hq₂))

end Helpers

section Braid

variable [CharP K 2] {m : ℕ}

theorem transvectionUnit_one_mul_self {j k : Fin m} (hjk : j ≠ k) :
    TauCeti.transvectionUnit hjk (1 : K) * TauCeti.transvectionUnit hjk 1 = 1 := by
  rw [← TauCeti.transvectionUnit_add, CharTwo.add_self_eq_zero, TauCeti.transvectionUnit_zero]

theorem pow_three_transvectionUnit_mul {j k : Fin m} (hjk : j ≠ k) :
    (TauCeti.transvectionUnit hjk (1 : K) * TauCeti.transvectionUnit hjk.symm 1) ^ 3 = 1 := by
  set a := TauCeti.transvectionUnit hjk (1 : K) with ha
  set b := TauCeti.transvectionUnit hjk.symm (1 : K) with hb
  have haa : a * a = 1 := transvectionUnit_one_mul_self hjk
  have hbb : b * b = 1 := transvectionUnit_one_mul_self hjk.symm
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  have hw : TauCeti.transvectionWeylElement (A := K) hjk = a * b * a := by
    rw [TauCeti.transvectionWeylElement_def, hneg]
  have hw' : TauCeti.transvectionWeylElement (A := K) hjk.symm = b * a * b := by
    rw [TauCeti.transvectionWeylElement_def, hneg]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hbraid : a * b * a = b * a * b := by
    have h := TauCeti.transvectionWeylElement_inv (A := K) hjk
    rw [hw, hw', _root_.mul_inv_rev, _root_.mul_inv_rev, hai, hbi] at h
    rw [← h]
    group
  calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by rw [pow_three]; group
    _ = (a * b * a) * (a * b * a) := by rw [hbraid]
    _ = a * b * (a * a) * b * a := by group
    _ = 1 := by rw [haa, mul_one, mul_assoc a b b, hbb, mul_one, haa]

theorem leviTv_mul_leviTv_eq_commutatorElement {j k : Fin m} (hjk : j ≠ k) :
    leviTv K hjk.symm 1 * leviTv K hjk 1 = ⁅leviTv K hjk 1, leviTv K hjk.symm 1⁆ := by
  set a := TauCeti.transvectionUnit hjk (1 : K) with ha
  set b := TauCeti.transvectionUnit hjk.symm (1 : K) with hb
  have haa : a * a = 1 := transvectionUnit_one_mul_self hjk
  have hbb : b * b = 1 := transvectionUnit_one_mul_self hjk.symm
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have h3 := pow_three_transvectionUnit_mul (K := K) hjk
  rw [← ha, ← hb] at h3
  have key : b * a = ⁅a, b⁆ := by
    rw [commutatorElement_def, hai, hbi]
    calc b * a = b * a * ((a * b) ^ 3) := by rw [h3, mul_one]
      _ = b * a * (a * b) * (a * b * a * b) := by rw [pow_three]; group
      _ = a * b * a * b := by
          rw [show b * a * (a * b) = 1 by
            rw [mul_assoc b a, ← mul_assoc a a b, haa, one_mul, hbb], one_mul]
  simp only [leviTv]
  rw [← ha, ← hb, ← map_mul, key, map_commutatorElement]

end Braid

section Prime

variable [Finite K] (hK : Nat.card K = 2)
include hK

noncomputable def sympFourEquivSpCompl12One : sympFour ≃* spCompl12 K 1 :=
  (F4Pilot.sp4EquivSympFour hK).symm.trans (spCompl12Equiv K 1)

noncomputable def sympFourToSp8 : sympFour →* StatedSp (1 + 3) K :=
  (spCompl12 K 1).subtype.comp (sympFourEquivSpCompl12One hK).toMonoidHom

theorem sympFourToSp8_injective : Function.Injective (sympFourToSp8 hK) :=
  (spCompl12 K 1).subtype_injective.comp (sympFourEquivSpCompl12One hK).injective

theorem spCompl12_one_eq_map_top :
    spCompl12 K 1 = (⊤ : Subgroup sympFour).map (sympFourToSp8 hK) := by
  rw [← MonoidHom.range_eq_map]
  ext x
  constructor
  · intro hx
    exact ⟨(sympFourEquivSpCompl12One hK).symm ⟨x, hx⟩, by simp [sympFourToSp8]⟩
  · rintro ⟨y, rfl⟩
    exact ((sympFourEquivSpCompl12One hK) y).2

theorem commutator_spCompl12_one_eq_map :
    ⁅spCompl12 K 1, spCompl12 K 1⁆ = (commutator sympFour).map (sympFourToSp8 hK) := by
  rw [_root_.commutator_def, Subgroup.map_commutator, ← spCompl12_one_eq_map_top hK]

theorem commutator_commutator_spCompl12_one :
    ⁅⁅spCompl12 K 1, spCompl12 K 1⁆, ⁅spCompl12 K 1, spCompl12 K 1⁆⁆ =
      ⁅spCompl12 K 1, spCompl12 K 1⁆ := by
  set H : Subgroup sympFour := commutator sympFour with hHdef
  have hHperf : ⁅H, H⁆ = H := by
    have h := congrArg (Subgroup.map H.subtype)
      (Group.isPerfect_def.1 isPerfect_commutator_sympFour)
    clear_value H
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  rw [commutator_spCompl12_one_eq_map hK, ← hHdef, ← Subgroup.map_commutator, hHperf]

noncomputable def commutatorSpCompl12OneEquiv :
    (⁅spCompl12 K 1, spCompl12 K 1⁆ : Subgroup (StatedSp (1 + 3) K)) ≃* commutator sympFour :=
  (MulEquiv.subgroupCongr (commutator_spCompl12_one_eq_map hK)).trans
    ((commutator sympFour).equivMapOfInjective _ (sympFourToSp8_injective hK)).symm

theorem isSimpleGroup_commutator_spCompl12_one :
    IsSimpleGroup (⁅spCompl12 K 1, spCompl12 K 1⁆ : Subgroup (StatedSp (1 + 3) K)) :=
  have : IsSimpleGroup (commutator sympFour) := isSimpleGroup_commutator_sympFour
  (commutatorSpCompl12OneEquiv hK).isSimpleGroup_congr.2 this

end Prime

section XZero

variable [CharP K 2]

@[expose] def sl2UpperOne : SL(2, K) := mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])

@[expose] def sl2LowerOne : SL(2, K) := mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])

theorem sl2UpperOne_mul_self : (sl2UpperOne : SL(2, K)) * sl2UpperOne = 1 := by
  refine Subtype.ext ?_
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2UpperOne, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem sl2LowerOne_mul_self : (sl2LowerOne : SL(2, K)) * sl2LowerOne = 1 := by
  refine Subtype.ext ?_
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2LowerOne, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem sl2UpperOne_mul_sl2LowerOne : (sl2UpperOne : SL(2, K)) * sl2LowerOne = zThreeSL := by
  refine Subtype.ext ?_
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2UpperOne, sl2LowerOne, zThreeSL, zThreeMat, Matrix.mul_apply, Fin.sum_univ_two, h2,
      hneg]

theorem zThreeSL_eq_commutatorElement_sq :
    (zThreeSL : SL(2, K)) = ⁅(sl2UpperOne : SL(2, K)), sl2LowerOne⁆ ^ 2 := by
  have hu : (sl2UpperOne : SL(2, K))⁻¹ = sl2UpperOne :=
    inv_eq_of_mul_eq_one_right sl2UpperOne_mul_self
  have hl : (sl2LowerOne : SL(2, K))⁻¹ = sl2LowerOne :=
    inv_eq_of_mul_eq_one_right sl2LowerOne_mul_self
  have hc : ⁅(sl2UpperOne : SL(2, K)), sl2LowerOne⁆ = (zThreeSL : SL(2, K)) ^ 2 := by
    rw [commutatorElement_def, hu, hl, ← sl2UpperOne_mul_sl2LowerOne, pow_two]
    group
  rw [hc, ← pow_mul]
  calc (zThreeSL : SL(2, K)) = zThreeSL ^ 3 * zThreeSL := by rw [zThreeSL_pow_three, one_mul]
    _ = zThreeSL ^ (2 * 2) := by rw [← pow_succ]

theorem nsElt_mem_commutator_longRootSp2 {m : ℕ} (k : Fin m) :
    nsElt (K := K) k ∈ ⁅longRootSp2 K m k, longRootSp2 K m k⁆ := by
  rw [nsElt, zThreeSL_eq_commutatorElement_sq, map_pow, map_commutatorElement]
  exact pow_mem (commutator_mem_commutator
    (⟨sl2UpperOne, rfl⟩ : longBlock K m k sl2UpperOne ∈ longRootSp2 K m k)
    (⟨sl2LowerOne, rfl⟩ : longBlock K m k sl2LowerOne ∈ longRootSp2 K m k)) 2

theorem nsTorusSp_le_commutator_spCompl12 {n : ℕ} :
    nsTorusSp K (0 : Fin (n + 3)) ≤ ⁅spCompl12 K n, spCompl12 K n⁆ := by
  rw [nsTorusSp, zpowers_le]
  exact commutator_mono (longRootSp2_le_spCompl12 n) (longRootSp2_le_spCompl12 n)
    (nsElt_mem_commutator_longRootSp2 0)

end XZero

section PerfectW

variable [CharP K 2] {n : ℕ}

theorem commutator_wRadical_sup_commutator_spCompl12_of_perfect (hn : 1 ≤ n)
    (hS : ⁅⁅spCompl12 K n, spCompl12 K n⁆, ⁅spCompl12 K n, spCompl12 K n⁆⁆ =
      ⁅spCompl12 K n, spCompl12 K n⁆) :
    ⁅wRadical K (1 : Fin (n + 3)) 2 ⊔ ⁅spCompl12 K n, spCompl12 K n⁆,
      wRadical K (1 : Fin (n + 3)) 2 ⊔ ⁅spCompl12 K n, spCompl12 K n⁆⁆ =
      wRadical K (1 : Fin (n + 3)) 2 ⊔ ⁅spCompl12 K n, spCompl12 K n⁆ := by
  set S := spCompl12 K n with hSdef
  set P := wRadical K (1 : Fin (n + 3)) 2 ⊔ ⁅S, S⁆ with hP
  have h12 : (1 : Fin (n + 3)) ≠ 2 := one_ne_two_fin
  have hQP : wRadical K (1 : Fin (n + 3)) 2 ≤ P := le_sup_left
  have hMP : ⁅S, S⁆ ≤ P := le_sup_right
  have hM : ⁅S, S⁆ ≤ ⁅P, P⁆ := by
    rw [← hS]
    exact commutator_mono hMP hMP
  have hik : ∀ {i k : Fin (n + 3)}, (i = 1 ∨ i = 2) → k ≠ 1 → k ≠ 2 → i ≠ k := by
    rintro i k (rfl | rfl) hk1 hk2 <;> [exact Ne.symm hk1; exact Ne.symm hk2]
  have hE : ∀ {j k : Fin (n + 3)} (hjk : j ≠ k), j ≠ 1 → j ≠ 2 → k ≠ 1 → k ≠ 2 → ∀ c : K,
      siegPair K j k c * siegDiag K j c ∈ ⁅S, S⁆ := by
    intro j k hjk hj1 hj2 hk1 hk2 c
    have e := commutatorElement_leviTv_siegDiag hjk (1 : K) c
    rw [one_mul, one_mul, one_mul] at e
    rw [← e]
    exact commutator_mem_commutator (leviTv_mem_spCompl12 hjk hj1 hj2 hk1 hk2 1)
      (longRootSp2_le_spCompl12_of_ne hk1 hk2 (siegDiag_mem_longRootSp2 k c))
  have hF : ∀ {j k : Fin (n + 3)} (hjk : j ≠ k), j ≠ 1 → j ≠ 2 → k ≠ 1 → k ≠ 2 →
      leviTv K hjk.symm 1 * leviTv K hjk 1 ∈ ⁅S, S⁆ := by
    intro j k hjk hj1 hj2 hk1 hk2
    rw [leviTv_mul_leviTv_eq_commutatorElement]
    exact commutator_mem_commutator (leviTv_mem_spCompl12 hjk hj1 hj2 hk1 hk2 1)
      (leviTv_mem_spCompl12 hjk.symm hk1 hk2 hj1 hj2 1)
  have hcommD : ∀ {i j k : Fin (n + 3)} (hik' : i ≠ k), j ≠ k → ∀ c d : K,
      leviTv K hik' d * siegDiag K j c = siegDiag K j c * leviTv K hik' d := by
    intro i j k hik' hjk c d
    refine leviTv_commute_upperUnipotentSp hik' d _ (fun y => ?_) (fun x => ?_)
    · simp [hjk]
    · simp [hjk]
  have hSm : ∀ (i j : Fin (n + 3)), (i = 1 ∨ i = 2) → j ≠ 1 → j ≠ 2 → ∀ c : K,
      siegPair K i j c ∈ ⁅P, P⁆ := by
    intro i j hi hj1 hj2 c
    obtain ⟨k, hk1, hk2, hkj⟩ := exists_fin_ne_one_two hn j
    have hi_k := hik hi hk1 hk2
    have e1 := commElt_mul_right_of_commute_spQ2 (b := siegPair K j k c)
      (hcommD hi_k (Ne.symm hkj) c 1)
    have e2 := commutatorElement_leviTv_siegPair hi_k (Ne.symm hkj) (1 : K) c
    rw [one_mul, siegPair_comm k j] at e2
    rw [e2] at e1
    rw [← e1]
    exact commutator_mem_commutator (hQP (leviTv_mem_wRadical h12 hi_k hi hk1 hk2 1))
      (hMP (hE (Ne.symm hkj) hj1 hj2 hk1 hk2 c))
  have hL : ∀ (i j : Fin (n + 3)) (hij : i ≠ j), (i = 1 ∨ i = 2) → j ≠ 1 → j ≠ 2 → ∀ c : K,
      leviTv K hij c ∈ ⁅P, P⁆ := by
    intro i j hij hi hj1 hj2 c
    obtain ⟨k, hk1, hk2, hkj⟩ := exists_fin_ne_one_two hn j
    have hi_k := hik hi hk1 hk2
    have hcomm : leviTv K hi_k c * leviTv K (Ne.symm hkj) 1 =
        leviTv K (Ne.symm hkj) 1 * leviTv K hi_k c := by
      have h := TauCeti.commute_transvectionUnit (A := K) hi_k (Ne.symm hkj) hkj
        (Ne.symm hi_k) c 1
      simp only [leviTv]
      rw [← map_mul, ← map_mul, h.eq]
    have e1 := commElt_mul_right_of_commute_spQ2 (b := leviTv K hkj 1) hcomm
    have e2 := commutatorElement_leviTv_leviTv hi_k hkj hij c (1 : K)
    rw [mul_one] at e2
    rw [e2] at e1
    rw [← e1]
    exact commutator_mem_commutator (hQP (leviTv_mem_wRadical h12 hi_k hi hk1 hk2 c))
      (hMP (hF (Ne.symm hkj) hj1 hj2 hk1 hk2))
  have h0 : (0 : Fin (n + 3)) ≠ 1 := by simp
  have h0' : (0 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_two] at h'
    omega
  have hD : ∀ (i : Fin (n + 3)), (i = 1 ∨ i = 2) → ∀ c : K, siegDiag K i c ∈ ⁅P, P⁆ := by
    intro i hi c
    obtain ⟨j, hj1, hj2, hj0⟩ := exists_fin_ne_one_two hn 0
    have hi0 : i ≠ 0 := hik hi h0 h0'
    have e := commElt_mul_right_eq_spQ2 (leviTv K hi0 1) (siegPair K 0 j c) (siegDiag K 0 c)
    have e2 := commutatorElement_leviTv_siegPair hi0 (hik hi hj1 hj2 |> fun h => by
      intro hj; exact hj0 hj) (1 : K) c
    rw [one_mul] at e2
    have e3 := commutatorElement_leviTv_siegDiag hi0 (1 : K) c
    rw [one_mul, one_mul, one_mul] at e3
    rw [e2, e3] at e
    have hc1 : Commute (siegPair K 0 j c) (siegPair K i 0 c) := upperUnipotentSp_commute _ _
    have hc2 : Commute (siegPair K 0 j c) (siegDiag K i c) := upperUnipotentSp_commute _ _
    have hcomm : siegPair K 0 j c * (siegPair K i 0 c * siegDiag K i c) *
        (siegPair K 0 j c)⁻¹ = siegPair K i 0 c * siegDiag K i c := by
      rw [(hc1.mul_right hc2).eq, mul_inv_cancel_right]
    rw [hcomm] at e
    have h1 : ⁅leviTv K hi0 1, siegPair K 0 j c * siegDiag K 0 c⁆ ∈ ⁅P, P⁆ :=
      commutator_mem_commutator (hQP (leviTv_mem_wRadical h12 hi0 hi h0 h0' 1))
        (hMP (hE (Ne.symm hj0) h0 h0' hj1 hj2 c))
    rw [e] at h1
    have h2 := mul_mem (inv_mem (mul_mem (hSm i j hi hj1 hj2 c) (hSm i 0 hi h0 h0' c))) h1
    rwa [← mul_assoc (siegPair K i j c), inv_mul_cancel_left] at h2
  have hP12 : ∀ c : K, siegPair K (1 : Fin (n + 3)) 2 c ∈ ⁅P, P⁆ := by
    intro c
    have h10 : (1 : Fin (n + 3)) ≠ 0 := Ne.symm h0
    have e := commutatorElement_leviTv_siegPair h10 (Ne.symm h0') 1 c
    rw [one_mul] at e
    rw [← e]
    refine commutator_mem_commutator (hQP (leviTv_mem_wRadical h12 h10 (Or.inl rfl) h0 h0' 1))
      (hQP ?_)
    rw [siegPair_comm]
    exact siegPair_mem_wRadical (Or.inr rfl) _
  have hQ : wRadical K (1 : Fin (n + 3)) 2 ≤ ⁅P, P⁆ :=
    wRadical_le_of_forall_mem h12 (hD 1 (Or.inl rfl)) (hD 2 (Or.inr rfl)) hP12
      (fun i j hij hi hj1 hj2 c => hL i j hij hi hj1 hj2 c)
      (fun i j hi hj1 hj2 c => hSm i j hi hj1 hj2 c)
  exact le_antisymm (Subgroup.commutator_le_self _) (sup_le hQ hM)

end PerfectW

section CoresEight

variable [Finite K] [CharP K 2]

theorem perfectCore_centralizer_twoCentralElt_one_two (hK : Nat.card K = 2) {a : K}
    (ha : a = 0 ∨ a = 1) :
    perfectCore (centralizer ({twoCentralElt (1 + 3) 1 2 a 1} : Set (StatedSp (1 + 3) K))) =
      wRadical K (1 : Fin (1 + 3)) 2 ⊔ ⁅spCompl12 K 1, spCompl12 K 1⁆ := by
  have : Finite (StatedSp (1 + 3) K) := by
    have : Finite (GL (Fin (1 + 3) ⊕ Fin (1 + 3)) K) := inferInstance
    exact Subtype.finite
  have hP := commutator_wRadical_sup_commutator_spCompl12_of_perfect (K := K) (n := 1) le_rfl
    (commutator_commutator_spCompl12_one hK)
  refine le_antisymm ?_ (le_perfectCore_of_perfect
    (sup_le (wRadical_le_centralizer_twoCentralElt a 1)
      ((Subgroup.commutator_le_self _).trans (spCompl12_le_centralizer_twoCentralElt 1 a 1))) hP)
  set Λ := perfectCore (centralizer ({twoCentralElt (1 + 3) 1 2 a 1} :
    Set (StatedSp (1 + 3) K))) with hΛdef
  have hΛ : Λ ≤ wRadical K (1 : Fin (1 + 3)) 2 ⊔ spCompl12 K 1 := by
    rcases ha with rfl | rfl
    · exact perfectCore_centralizer_a2_le_two hK
    · exact perfectCore_centralizer_c2_le
  have hSN : spCompl12 K 1 ≤ normalizer (wRadical K (1 : Fin (1 + 3)) 2 :
      Set (StatedSp (1 + 3) K)) :=
    (spCompl12_le_range_leviHom_c2 (K := K) (n := 1)).trans
      (range_leviHom_le_normalizer_wRadical one_ne_two_fin one_ne_zero)
  calc Λ = ⁅Λ, Λ⁆ := (perfectCore_perfect _).symm
    _ ≤ ⁅wRadical K (1 : Fin (1 + 3)) 2 ⊔ spCompl12 K 1,
        wRadical K (1 : Fin (1 + 3)) 2 ⊔ spCompl12 K 1⁆ := commutator_mono hΛ hΛ
    _ ≤ wRadical K (1 : Fin (1 + 3)) 2 ⊔ ⁅spCompl12 K 1, spCompl12 K 1⁆ :=
        commutator_sup_le_sup_commutator_of_le_normalizer hSN

end CoresEight

end CFSG.SeitzReduction.SymplecticPilot
