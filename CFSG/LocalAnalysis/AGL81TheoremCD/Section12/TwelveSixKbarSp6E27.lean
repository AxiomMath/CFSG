module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarE27Kit
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofSp62
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLSp6Facts
public import CFSG.RankThree.PartTwo.Sec8.Hering611RSp62Inner

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarE27

open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open scoped Matrix
open CFSG.RankThree.PartTwo.Sec4.Res417Four (sm6 mk6 z6 t6' wreathFacts_sp6 card_W6 fixCard
  fixCard_conj fix_cases6 six6)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

local instance decEqH6' : DecidableEq H6 := inferInstance

@[expose] def c0M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 1]

@[expose] def c1M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1]

@[expose] def c2M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0; 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem c0_check : sm6 c0M * sm6 c0M = 1 ∧ sm6 c0M * sm6 c0M = 1 ∧
    (sm6 c0M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 c0M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem c1_check : sm6 c1M * sm6 c1M = 1 ∧ sm6 c1M * sm6 c1M = 1 ∧
    (sm6 c1M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 c1M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem c2_check : sm6 c2M * sm6 c2M = 1 ∧ sm6 c2M * sm6 c2M = 1 ∧
    (sm6 c2M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 c2M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

@[expose] def c6 : Fin 3 → H6 :=
  ![mk6 c0M c0M c0_check, mk6 c1M c1M c1_check, mk6 c2M c2M c2_check]

theorem c6_spec :
    (c6 0 ^ 2 = 1 ∧ c6 0 * z6 0 = z6 0 * c6 0 ∧ (z6 1 * (c6 0 * z6 2 * (c6 0)⁻¹)) ^ 5 = 1 ∧
      z6 1 * (c6 0 * z6 2 * (c6 0)⁻¹) ≠ 1) ∧
    (c6 1 ^ 2 = 1 ∧ c6 1 * z6 1 = z6 1 * c6 1 ∧ (z6 0 * (c6 1 * z6 2 * (c6 1)⁻¹)) ^ 5 = 1 ∧
      z6 0 * (c6 1 * z6 2 * (c6 1)⁻¹) ≠ 1) ∧
    (c6 2 ^ 2 = 1 ∧ c6 2 * z6 2 = z6 2 * c6 2 ∧ (z6 0 * (c6 2 * z6 1 * (c6 2)⁻¹)) ^ 5 = 1 ∧
      z6 0 * (c6 2 * z6 1 * (c6 2)⁻¹) ≠ 1) := by
  decide +kernel

theorem six6_cases : ∀ i : Fin 6, ∃ k : Fin 3, six6 i = z6 k ∨ six6 i = (z6 k)⁻¹ := by
  decide +kernel

theorem z6_spec : (∀ k : Fin 3, fixCard (z6 k) = 16) ∧
    ∀ k m : Fin 3, (z6 k = z6 m ∨ z6 k = (z6 m)⁻¹) → k = m := by
  decide +kernel

theorem sp6Kit : E27Kit (⊤ : Subgroup H6) z6 (fun A => fixCard A = 16) where
  conj V hV hV27 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hVp : IsPGroup 3 V := IsPGroup.of_card (n := 3) (by rw [hV27]; norm_num)
    obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := Item434Kit.wreathW z6 t6')
      (by rw [card_W6, Item434SmallTwoIII.factorization_card_H6]; norm_num) hVp
    have hle := Item434AltPerm.map_conj_inv_le hg
    have heq := Item434Kit.eq_baseA_of_le_wreathW wreathFacts_sp6 card_W6 hle (hV.map _)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hV27])
    refine ⟨g, ?_⟩
    rw [← Item434AltPerm.map_conj_map_conj_inv V g, heq]
    rfl
  P_conj σ x hx := by
    show fixCard (σ * x * σ⁻¹) = 16
    rw [fixCard_conj]
    exact hx
  P_base x hx hPx := by
    obtain ⟨v, rfl⟩ := (Item434Kit.mem_baseA_iff wreathFacts_sp6).1 hx
    obtain ⟨i, hi⟩ := fix_cases6.1 v hPx
    obtain ⟨k, hk⟩ := six6_cases i
    exact ⟨k, by rw [hi]; exact hk⟩
  P_z := z6_spec.1
  distinct := z6_spec.2
  cube := wreathFacts_sp6.pow_z
  ne_one := Item434Kit.z_ne_one wreathFacts_sp6
  normal := inferInstance
  five k := by
    fin_cases k
    · exact ⟨1, 2, c6 0, mem_top _, c6_spec.1⟩
    · exact ⟨0, 2, c6 1, mem_top _, c6_spec.2.1⟩
    · exact ⟨0, 1, c6 2, mem_top _, c6_spec.2.2⟩

theorem five_dvd_card_sp6 {Y : Type} [Group Y] (hY : StatedClassicalModel Y .PSp 3 2 1)
    {V W₁ W₂ W₃ J : Subgroup (MulAut Y)} {t₁ t₂ t₃ : MulAut Y}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) (hVJ : V ≤ J)
    (hN₁ : ∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W₁, w y = y) →
      MulAut.conj y ∈ normalizer (J : Set (MulAut Y)))
    (hN₂ : ∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W₂, w y = y) →
      MulAut.conj y ∈ normalizer (J : Set (MulAut Y)))
    (hN₃ : ∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W₃, w y = y) →
      MulAut.conj y ∈ normalizer (J : Set (MulAut Y))) :
    5 ∣ Nat.card J := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec21.nonempty_mulEquiv_H6_of_stated hY
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    Item434Kit.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartTwo.Sec8.Hering611.center_eq_bot_of_sp62 hY)
  have hsurj : Function.Surjective (MulAut.conj : Y →* MulAut Y) := fun α => by
    obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.Sec21.exists_eq_conj_of_sp6Model hY α
    exact ⟨y, hy.symm⟩
  set C : Y ≃* MulAut Y := MulEquiv.ofBijective MulAut.conj ⟨hinj, hsurj⟩ with hC
  set Θ : MulAut Y ≃* H6 := C.symm.trans e with hΘ
  have hΘconj : ∀ y : Y, Θ (MulAut.conj y) = e y := by
    intro y
    have : C.symm (MulAut.conj y) = y := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hΘ, MulEquiv.trans_apply, this]
  exact five_dvd_card_of_kit_aut Θ sp6Kit
    (fun c _ => ⟨e.symm c, by rw [hΘconj, MulEquiv.apply_symm_apply]⟩) hinj hc hVJ hN₁ hN₂ hN₃

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarE27
