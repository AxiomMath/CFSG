module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmMinusBlocks
public import CFSG.LargeExtraspecial.O62Basic
public import CFSG.LargeExtraspecial.S4Restrict

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine
  CFSG.LieType.SeitzGeneration.HyperBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem mem_blockSet {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A] {D : Hyperplane A 3} :
    D ∈ blockSet A ↔ blockSpace A D.1 ≠ ⊥ :=
  mem_nonBotBlocks A 3

theorem blockSpace_eq_bot_of_not_mem_blockSet {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    {D : Hyperplane A 3} (hD : D ∉ blockSet A) : blockSpace A D.1 = ⊥ := by
  by_contra hne
  exact hD ((mem_blockSet).2 hne)

theorem finrank_eq_fixedSpaceOf_add_sum_blockSet {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    (hA : IsElemAbelian 3 A) :
    finrank (ZMod 2) V = finrank (ZMod 2) (fixedSpaceOf A) +
      ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpF : (3 : ZMod 2) ≠ 0 := by decide
  rw [finrank_eq_finrank_fixedSpaceOf_add_sum_blockSpace A hp hpF hA]
  congr 1
  exact (Finset.sum_subset (Finset.subset_univ _) fun D _ hD => by
    simp [blockSpace_eq_bot_of_not_mem_blockSet hD]).symm

theorem sum_projBlock_eq_self_of_fixedSpace_bot {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    (hp : Nat.Prime 3) (hpF : (3 : ZMod 2) ≠ 0) (hA : IsElemAbelian 3 A)
    (hC : fixedSpaceOf A = ⊥) (v : V) :
    ∑ D ∈ blockSet A, projBlock A hp hpF hA D v = v := by
  classical
  set L : Module.End (ZMod 2) V :=
    1 - ∑ D ∈ blockSet A, projBlock A hp hpF hA D with hL
  have hLker : L = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff]
    intro v _
    have hsup : fixedSpaceOf A ⊔ (⨆ D : Hyperplane A 3, blockSpace A D.1) = ⊤ :=
      sup_fixedSpaceOf_iSup_blockSpace A hp hpF hA
    have hv : v ∈ fixedSpaceOf A ⊔ (⨆ D : Hyperplane A 3, blockSpace A D.1) := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    have hc0 : c = 0 := by
      rw [hC] at hc
      simpa using hc
    subst hc0
    rw [zero_add, LinearMap.mem_ker]
    have hLw : ∀ x ∈ (⨆ D : Hyperplane A 3, blockSpace A D.1), L x = 0 := by
      intro x hx
      refine Submodule.iSup_induction (fun D : Hyperplane A 3 => blockSpace A D.1)
        (motive := fun x => L x = 0) hx ?_ ?_ ?_
      · intro D x hx
        have hsum : ∑ E ∈ blockSet A, projBlock A hp hpF hA E x =
            projBlock A hp hpF hA D x := by
          refine Finset.sum_eq_single D ?_ ?_
          · intro E _ hED
            exact projBlock_apply_of_mem_block A hp hpF hA (D := E) (E := D)
              (fun h => hED h.symm) hx
          · intro hD
            have hbot : blockSpace A D.1 = ⊥ := blockSpace_eq_bot_of_not_mem_blockSet hD
            have hmem := projBlock_apply_mem A hp hpF hA D x
            rwa [hbot, Submodule.mem_bot] at hmem
        rw [hL, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply, hsum]
        by_cases hD : D ∈ blockSet A
        · rw [projBlock_apply_of_mem A hp hpF hA D hx, sub_self]
        · have hbot : blockSpace A D.1 = ⊥ := blockSpace_eq_bot_of_not_mem_blockSet hD
          rw [hbot, Submodule.mem_bot] at hx
          rw [hx, map_zero, sub_self]
      · simp [hL]
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    exact hLw w hw
  have h := congrArg (fun f : Module.End (ZMod 2) V => f v) hLker
  simp only [hL, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply,
    LinearMap.sum_apply] at h
  exact (sub_eq_zero.mp h).symm

theorem exists_projBlock_ne_zero_of_fixedSpace_bot {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    (hp : Nat.Prime 3) (hpF : (3 : ZMod 2) ≠ 0) (hA : IsElemAbelian 3 A)
    (hC : fixedSpaceOf A = ⊥) {v : V} (hv : v ≠ 0) :
    ∃ D ∈ blockSet A, projBlock A hp hpF hA D v ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  rw [← sum_projBlock_eq_self_of_fixedSpace_bot hp hpF hA hC v]
  exact Finset.sum_eq_zero fun D hD => h D hD

theorem projBlock_apply_mem_of_invariant {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    (hp : Nat.Prime 3) (hpF : (3 : ZMod 2) ≠ 0) (hA : IsElemAbelian 3 A)
    {R : Submodule (ZMod 2) V} (hR : ∀ a : ↥A, ∀ v ∈ R, (a : V ≃ₗ[ZMod 2] V) v ∈ R)
    {D : Hyperplane A 3} {v : V} (hv : v ∈ R) :
    projBlock A hp hpF hA D v ∈ R := by
  rw [projBlock_apply_eq]
  refine Submodule.sub_mem _ ?_ ?_
  · refine Submodule.smul_mem _ _ ?_
    rw [sumOp, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun a _ => hR a v hv
  · refine Submodule.smul_mem _ _ ?_
    rw [sumOp, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun a _ => hR a v hv

theorem iInf_blockSet_eq_bot {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    (hp : Nat.Prime 3) (hpF : (3 : ZMod 2) ≠ 0) (hA : IsElemAbelian 3 A)
    (hfaith : ∀ a : ↥A, (∀ v : V, (a : V ≃ₗ[ZMod 2] V) v = v) → a = 1) :
    (⨅ D ∈ blockSet A, D.1) = ⊥ := by
  classical
  refine le_antisymm (fun a ha => ?_) bot_le
  have haD : ∀ D ∈ blockSet A, (a : ↥A) ∈ D.1 := fun D hD => Subgroup.mem_iInf.mp
    (Subgroup.mem_iInf.mp ha D) hD
  have hfix : ∀ v : V, (a : V ≃ₗ[ZMod 2] V) v = v := by
    intro v
    have hsup : fixedSpaceOf A ⊔ (⨆ D : Hyperplane A 3, blockSpace A D.1) = ⊤ :=
      sup_fixedSpaceOf_iSup_blockSpace A hp hpF hA
    have hv : v ∈ fixedSpaceOf A ⊔ (⨆ D : Hyperplane A 3, blockSpace A D.1) := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    have hc' : (a : V ≃ₗ[ZMod 2] V) c = c := (mem_fixedSpaceOf A).1 hc a
    have hw' : (a : V ≃ₗ[ZMod 2] V) w = w := by
      refine Submodule.iSup_induction (fun D : Hyperplane A 3 => blockSpace A D.1)
        (motive := fun x => (a : V ≃ₗ[ZMod 2] V) x = x) hw ?_ ?_ ?_
      · intro D x hx
        by_cases hD : D ∈ blockSet A
        · exact (mem_blockSpace A).1 hx |>.1 a (haD D hD)
        · have hbot : blockSpace A D.1 = ⊥ := blockSpace_eq_bot_of_not_mem_blockSet hD
          rw [hbot, Submodule.mem_bot] at hx
          rw [hx, map_zero]
      · exact map_zero _
      · intro x y hx hy
        rw [map_add, hx, hy]
    rw [map_add, hc', hw']
  exact Subgroup.mem_bot.2 (hfaith a hfix)


theorem index_iInf_erase_le {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    [DecidableEq (Hyperplane A 3)] {D0 : Hyperplane A 3} (hD0 : D0 ∈ blockSet A)
    (h4 : (blockSet A).card = 4) :
    (⨅ D : {D // D ∈ (blockSet A).erase D0}, D.1.1).index ≤ 3 ^ 3 := by
  classical
  refine (Subgroup.index_iInf_le (fun D : {D // D ∈ (blockSet A).erase D0} => D.1.1)).trans ?_
  have hprod : (∏ D : {D // D ∈ (blockSet A).erase D0}, (D.1.1).index) = 3 ^ 3 := by
    calc (∏ D : {D // D ∈ (blockSet A).erase D0}, (D.1.1).index)
        = ∏ _D : {D // D ∈ (blockSet A).erase D0}, 3 :=
          Finset.prod_congr rfl fun D _ => D.1.2
      _ = 3 ^ Fintype.card {D // D ∈ (blockSet A).erase D0} := by
          rw [Finset.prod_const, Finset.card_univ]
      _ = 3 ^ 3 := by
          have hc : Fintype.card {D // D ∈ (blockSet A).erase D0} = 3 := by
            rw [Fintype.card_coe, Finset.card_erase_of_mem hD0, h4]
          rw [hc]
  rw [hprod]

theorem exists_mem_iInf_erase_not_mem {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    [DecidableEq (Hyperplane A 3)] {D0 : Hyperplane A 3} (hcardA : Nat.card ↥A = 3 ^ 4)
    (h4 : (blockSet A).card = 4) (hD0 : D0 ∈ blockSet A)
    (hall : (⨅ D ∈ blockSet A, D.1) = ⊥) :
    ∃ y : ↥A, (∀ D : Hyperplane A 3, D ∈ (blockSet A).erase D0 → y ∈ D.1) ∧ y ∉ D0.1 := by
  classical
  let S : Subgroup ↥A := ⨅ D : {D // D ∈ (blockSet A).erase D0}, D.1.1
  have hidx : S.index ≤ 3 ^ 3 := index_iInf_erase_le hD0 h4
  have hcardS : Nat.card ↥S * S.index = 3 ^ 4 := by
    rw [Subgroup.card_mul_index, hcardA]
  have hS3 : 3 ≤ Nat.card ↥S := by
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card ↥S ≤ 2 := by omega
    have : Nat.card ↥S * S.index ≤ 2 * 3 ^ 3 := Nat.mul_le_mul h2 hidx
    omega
  have hSne : S ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hS3
    omega
  have hSle : ¬ S ≤ D0.1 := by
    intro hle
    apply hSne
    refine le_antisymm (fun y hy => ?_) bot_le
    have hyall : ∀ D : Hyperplane A 3, D ∈ blockSet A → y ∈ D.1 := by
      intro D hD
      by_cases hDD0 : D = D0
      · subst hDD0
        exact hle hy
      · exact Subgroup.mem_iInf.mp hy ⟨D, Finset.mem_erase.2 ⟨hDD0, hD⟩⟩
    exact Subgroup.mem_bot.2 (by
      have hmem : y ∈ ⨅ D ∈ blockSet A, D.1 := by
        rw [Subgroup.mem_iInf]
        intro D
        rw [Subgroup.mem_iInf]
        exact hyall D
      rw [hall] at hmem
      simpa using hmem)
  obtain ⟨y, hyS, hyD0⟩ := Set.not_subset.mp hSle
  exact ⟨y, fun D hD => Subgroup.mem_iInf.mp hyS ⟨D, hD⟩, hyD0⟩

theorem iInf_erase_eq_zpowers {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    [DecidableEq (Hyperplane A 3)] (hA : IsElemAbelian 3 A) {D0 : Hyperplane A 3}
    (hcardA : Nat.card ↥A = 3 ^ 4) (h4 : (blockSet A).card = 4) (hD0 : D0 ∈ blockSet A)
    (hall : (⨅ D ∈ blockSet A, D.1) = ⊥)
    {y : ↥A} (hyS : ∀ D : Hyperplane A 3, D ∈ (blockSet A).erase D0 → y ∈ D.1)
    (hy1 : y ≠ 1) :
    (⨅ D : {D // D ∈ (blockSet A).erase D0}, D.1.1) = Subgroup.zpowers y := by
  classical
  haveI : IsMulCommutative ↥A := hA.1
  letI : CommGroup ↥A := IsMulCommutative.instCommGroup
  haveI : D0.1.Normal := Subgroup.normal_of_comm D0.1
  let S : Subgroup ↥A := ⨅ D : {D // D ∈ (blockSet A).erase D0}, D.1.1
  have hidx : S.index ≤ 3 ^ 3 := index_iInf_erase_le hD0 h4
  have hS3 : 3 ≤ Nat.card ↥S := by
    by_contra hlt
    push Not at hlt
    have hcardS : Nat.card ↥S * S.index = 3 ^ 4 := by
      rw [Subgroup.card_mul_index, hcardA]
    have h2 : Nat.card ↥S ≤ 2 := by omega
    have : Nat.card ↥S * S.index ≤ 2 * 3 ^ 3 := Nat.mul_le_mul h2 hidx
    omega
  have hSinf : S ⊓ D0.1 = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hxS : x ∈ S := hx.1
    have hxD0 : x ∈ D0.1 := hx.2
    have hxall : ∀ D : Hyperplane A 3, D ∈ blockSet A → x ∈ D.1 := by
      intro D hD
      by_cases hDD0 : D = D0
      · subst hDD0; exact hxD0
      · exact Subgroup.mem_iInf.mp hxS ⟨D, Finset.mem_erase.2 ⟨hDD0, hD⟩⟩
    exact Subgroup.mem_bot.2 (by
      have hmem : x ∈ ⨅ D ∈ blockSet A, D.1 := by
        rw [Subgroup.mem_iInf]
        intro D
        rw [Subgroup.mem_iInf]
        exact hxall D
      rw [hall] at hmem
      simpa using hmem)
  have hinj : Function.Injective (fun s : ↥S => QuotientGroup.mk' D0.1 (s : ↥A)) := by
    intro s t hst
    change QuotientGroup.mk' D0.1 (s : ↥A) = QuotientGroup.mk' D0.1 (t : ↥A) at hst
    obtain ⟨z, hzD, hzs⟩ := (QuotientGroup.mk'_eq_mk' D0.1).1 hst
    have hmem : (s : ↥A)⁻¹ * t ∈ D0.1 := by
      have hz : (s : ↥A)⁻¹ * t = z := by
        rw [← hzs]
        group
      rwa [hz]
    have hmemS : (s : ↥A)⁻¹ * t ∈ S := S.mul_mem (S.inv_mem s.2) t.2
    have hbot : (s : ↥A)⁻¹ * t ∈ S ⊓ D0.1 := ⟨hmemS, hmem⟩
    rw [hSinf, Subgroup.mem_bot] at hbot
    exact Subtype.ext (inv_mul_eq_one.mp hbot)
  have hle3 : Nat.card ↥S ≤ 3 := by
    have h := Nat.card_le_card_of_injective _ hinj
    have hq : Nat.card (↥A ⧸ D0.1) = 3 := by
      rw [← Subgroup.index_eq_card]
      exact D0.2
    rwa [hq] at h
  have hS3eq : Nat.card ↥S = 3 := le_antisymm hle3 hS3
  have hy3 : orderOf y = 3 := by
    rw [orderOf_eq_prime (Subtype.ext (by simpa using hA.2 y y.2)) hy1]
  have hle : Subgroup.zpowers y ≤ S := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_iInf.mpr fun D => hyS D.1 D.2
  have hcardz : Nat.card ↥(Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, hy3]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hS3eq, hcardz])).symm


theorem five_blocks_data {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (hA : IsElemAbelian 3 A) (hdim : finrank (ZMod 2) V = 2 * 5)
    (hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[ZMod 2] V) u) ((a : V ≃ₗ[ZMod 2] V) v) = polarBilin Q u v)
    (h5 : (blockSet A).card = 5) :
    fixedSpaceOf A = ⊥ ∧ ∀ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) = 2 := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpF : (3 : ZMod 2) ≠ 0 := by decide
  have h2 : (2 : ZMod 2) = 0 := by decide
  have htwo : ∀ D ∈ blockSet A, 2 ≤ finrank (ZMod 2) (blockSpace A D.1) := fun D hD =>
    two_le_finrank_blockSpace A h2 hQ hp hpF hA hB D ((mem_blockSet).1 hD)
  have hsumle : ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) ≤ 10 := by
    calc ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1)
        ≤ ∑ D : Hyperplane A 3, finrank (ZMod 2) (blockSpace A D.1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)
      _ ≤ finrank (ZMod 2) V := sum_finrank_blockSpace_le_finrank A hp hpF hA
      _ = 10 := by rw [hdim]
  have hge : 10 ≤ ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) := by
    calc 10 = 5 * 2 := by norm_num
      _ = ∑ _D ∈ blockSet A, (2 : ℕ) := by
          rw [Finset.sum_const, h5, smul_eq_mul]
      _ ≤ ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) := Finset.sum_le_sum htwo
  have hsum : ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) = 10 :=
    le_antisymm hsumle hge
  have hdimsum := finrank_eq_fixedSpaceOf_add_sum_blockSet (A := A) hA
  rw [hsum, hdim] at hdimsum
  have hC : fixedSpaceOf A = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    omega
  refine ⟨hC, fun D hD => ?_⟩
  have h1 : finrank (ZMod 2) (blockSpace A D.1) +
      ∑ E ∈ (blockSet A).erase D, finrank (ZMod 2) (blockSpace A E.1) = 10 := by
    rw [Finset.add_sum_erase (blockSet A) (fun E => finrank (ZMod 2) (blockSpace A E.1)) hD, hsum]
  have h2' : 4 * 2 ≤ ∑ E ∈ (blockSet A).erase D, finrank (ZMod 2) (blockSpace A E.1) := by
    calc 4 * 2 = ∑ _E ∈ (blockSet A).erase D, (2 : ℕ) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem hD, h5, smul_eq_mul]
      _ ≤ ∑ E ∈ (blockSet A).erase D, finrank (ZMod 2) (blockSpace A E.1) :=
          Finset.sum_le_sum fun E hE => htwo E (Finset.mem_of_mem_erase hE)
  have hgeD : 2 ≤ finrank (ZMod 2) (blockSpace A D.1) := htwo D hD
  omega

theorem exists_plane_block_of_card_four {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (hA : IsElemAbelian 3 A) (hdim : finrank (ZMod 2) V = 2 * 5)
    (hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[ZMod 2] V) u) ((a : V ≃ₗ[ZMod 2] V) v) = polarBilin Q u v)
    (h4 : (blockSet A).card = 4) :
    ∃ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) = 2 := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpF : (3 : ZMod 2) ≠ 0 := by decide
  have h2 : (2 : ZMod 2) = 0 := by decide
  have htwo : ∀ D ∈ blockSet A, 2 ≤ finrank (ZMod 2) (blockSpace A D.1) := fun D hD =>
    two_le_finrank_blockSpace A h2 hQ hp hpF hA hB D ((mem_blockSet).1 hD)
  by_contra hcon
  push Not at hcon
  have hfour : ∀ D ∈ blockSet A, 4 ≤ finrank (ZMod 2) (blockSpace A D.1) := by
    intro D hD
    obtain ⟨k, hk⟩ := even_finrank_blockSpace A h2 hQ hp hpF hA hB D
    have h2D := htwo D hD
    have hne := hcon D hD
    omega
  have hsumle : ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) ≤ 10 := by
    calc ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1)
        ≤ ∑ D : Hyperplane A 3, finrank (ZMod 2) (blockSpace A D.1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)
      _ ≤ finrank (ZMod 2) V := sum_finrank_blockSpace_le_finrank A hp hpF hA
      _ = 10 := by rw [hdim]
  have hge : 4 * 4 ≤ ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) := by
    calc 4 * 4 = ∑ _D ∈ blockSet A, (4 : ℕ) := by
          rw [Finset.sum_const, h4, smul_eq_mul]
      _ ≤ ∑ D ∈ blockSet A, finrank (ZMod 2) (blockSpace A D.1) := Finset.sum_le_sum hfour
  omega

theorem mem_of_forall_mem_blockSpace {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    (hp : Nat.Prime 3) (hpF : (3 : ZMod 2) ≠ 0) (hA : IsElemAbelian 3 A)
    {D : Hyperplane A 3} (hD : D ∈ blockSet A) {a : ↥A}
    (ha : ∀ v ∈ blockSpace A D.1, (a : V ≃ₗ[ZMod 2] V) v = v) : a ∈ D.1 := by
  classical
  let U : Submodule (ZMod 2) V := blockSpace A D.1
  have hU : ∀ b : ↥A, ∀ u ∈ U, (b : V ≃ₗ[ZMod 2] V) u ∈ U := fun b u hu =>
    blockSpace_invariant A hp hpF hA hu
  let φ : ↥A →* (U ≃ₗ[ZMod 2] U) :=
    { toFun := fun b => CFSG.LargeExtraspecial.S4.restrictEquiv (b : V ≃ₗ[ZMod 2] V) U
        (hU b) (fun u hu => by simpa using hU b⁻¹ u hu)
      map_one' := LinearEquiv.ext fun u => Subtype.ext (by simp)
      map_mul' := fun b c => LinearEquiv.ext fun u => Subtype.ext (by simp [map_mul]) }
  have hDle : D.1 ≤ φ.ker := by
    intro d hd
    rw [MonoidHom.mem_ker]
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    exact (mem_blockSpace A).1 u.2 |>.1 d hd
  have hker_ne : φ.ker ≠ ⊤ := by
    intro htop
    have hUfix : U ≤ fixedSpaceOf A := by
      intro v hv
      rw [mem_fixedSpaceOf]
      intro b
      have hb : b ∈ φ.ker := by rw [htop]; exact Subgroup.mem_top b
      have h1 : φ b ⟨v, hv⟩ = ⟨v, hv⟩ := by
        rw [MonoidHom.mem_ker.1 hb]
        rfl
      have h2 : ((φ b) ⟨v, hv⟩ : V) = v := by
        have h3 := congrArg (fun u : U => (u : V)) h1
        simpa [φ] using h3
      simpa [φ] using h2
    have hUbot : U = ⊥ := by
      refine le_antisymm (fun v hv => ?_) bot_le
      have hc : v ∈ fixedSpaceOf A := hUfix hv
      have hcomm : v ∈ commutatorSpaceOf A := blockSpace_le_commutatorSpaceOf A D.1 hv
      have hinf : v ∈ fixedSpaceOf A ⊓ commutatorSpaceOf A := ⟨hc, hcomm⟩
      rw [fixedSpaceOf_inf_commutatorSpaceOf A hp hpF hA] at hinf
      exact hinf
    exact (mem_blockSet.1 hD) hUbot
  have hDmax : IsCoatom D.1 := Subgroup.isCoatom_of_index_prime (by rw [D.2]; norm_num)
  have hker : φ.ker = D.1 := by
    by_contra hne
    have hlt : D.1 < φ.ker := lt_of_le_of_ne hDle (Ne.symm hne)
    exact hker_ne (hDmax.lt_iff.mp hlt)
  rw [← hker]
  rw [MonoidHom.mem_ker]
  apply LinearEquiv.ext
  intro u
  apply Subtype.ext
  exact ha u.1 u.2

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
