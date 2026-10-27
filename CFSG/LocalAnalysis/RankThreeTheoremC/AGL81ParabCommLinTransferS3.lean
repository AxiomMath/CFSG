module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransfer

import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open CFSG.Open CFSG.AGLEmbedding

theorem natCard_ne_three_of_charTwo (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card K ≠ 3 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hcard]
  intro h
  have h3 : 2 ^ (f : ℕ) % 2 = 1 := by rw [h]
  rw [Nat.pow_mod, Nat.mod_self, zero_pow f.ne_zero] at h3
  exact absurd h3 (by norm_num)

theorem center_specialLinear_two_eq_bot (K : Type) [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h : (r - 1) ^ 2 = 0 := by
    linear_combination hr + (1 - r) * (CharP.cast_eq_zero K 2)
  have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  refine Subtype.ext ?_
  rw [← hrA, hr1, map_one]
  rfl

theorem nonempty_mulEquiv_perm_three_of_card_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨f⟩ := CFSG.BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two hK
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (center_specialLinear_two_eq_bot K)).trans
    QuotientGroup.quotientBot).symm.trans f⟩

theorem isQuasisimple_or_perm_three {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {S : Type} [Group S] (e : Matrix.SpecialLinearGroup (Fin m) K ≃* S) :
    CFSG.Open.IsQuasisimple S ∨ Nonempty (S ≃* Equiv.Perm (Fin 3)) := by
  classical
  by_cases hq : 3 ≤ m ∨ ∃ s : Finset K, s.card = 4
  · exact Or.inl (CFSG.Open.IsQuasisimple.of_mulEquiv e.symm
      ⟨(CFSG.LinearGroups.special_linear_isPerfect hm hq).commutator_eq_top,
        (CFSG.LinearGroups.linear_projective_simple hm hq).2.1⟩)
  · refine Or.inr ?_
    push Not at hq
    obtain rfl : m = 2 := by omega
    have := Fintype.ofFinite K
    have hlt : Nat.card K < 4 := by
      by_contra hge
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
      exact hq.2 s hs
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    have h3 := natCard_ne_three_of_charTwo K
    obtain ⟨f⟩ := nonempty_mulEquiv_perm_three_of_card_two (K := K) (by omega)
    exact ⟨e.symm.trans f⟩

theorem isQuasisimple_of_surjective_of_ker_le_center {P Q : Type*} [Group P] [Group Q]
    (hP : CFSG.Open.IsQuasisimple P) (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center P) : CFSG.Open.IsQuasisimple Q := by
  have hperf : Group.IsPerfect P := ⟨hP.1⟩
  have hc : Subgroup.center P = ((QuotientGroup.mk' (Subgroup.center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hperf f hf hker]
  let e : P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))
  have := hP.2
  exact ⟨(Group.IsPerfect.ofSurjective (f := f) hf).commutator_eq_top, e.symm.isSimpleGroup⟩

theorem isSubnormal_top_of_normal {G : Type*} [Group G] {E : Subgroup G} (hE : E.Normal) :
    CFSG.Open.IsSubnormal E ⊤ :=
  CFSG.Open.IsSubnormal.step le_top (hE.subgroupOf ⊤) (CFSG.Open.IsSubnormal.refl ⊤)

theorem le_wSup_of_normal {G : Type} [Group G] {E : Subgroup G} (hE : E.Normal)
    (h : E = ⊥ ∨ IsComponentOf E ⊤ ∨ IsSymThreeOrSUThreeTwo ↥E) : E ≤ wSup G := by
  rcases h with rfl | h
  · exact bot_le
  · exact le_iSup₂_of_le E ⟨isSubnormal_top_of_normal hE, h⟩ le_rfl

theorem range_le_wSup_of_isQuasisimple {G : Type} [Group G] {S : Type} [Group S] (ψ : S →* G)
    (hnormal : ψ.range.Normal) (hS : CFSG.Open.IsQuasisimple S) : ψ.range ≤ wSup G := by
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab.normal_eq_top_or_le_center
    hS ψ.normal_ker with h | h
  · refine le_wSup_of_normal hnormal (Or.inl ?_)
    refine (Subgroup.eq_bot_iff_forall _).2 ?_
    rintro _ ⟨s, rfl⟩
    exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top s)
  · refine le_wSup_of_normal hnormal
      (Or.inr (Or.inl ⟨le_top, isSubnormal_top_of_normal hnormal, ?_⟩))
    exact isQuasisimple_of_surjective_of_ker_le_center hS ψ.rangeRestrict
      ψ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])

private theorem perm_three_sq_cases (g : Equiv.Perm (Fin 3)) :
    g ^ 2 = 1 ∨ g ^ 2 = finRotate 3 ∨ g ^ 2 = (finRotate 3)⁻¹ := by
  revert g
  decide

private theorem perm_three_cycle_mem (x : Equiv.Perm (Fin 3)) (hx : x ≠ 1) :
    finRotate 3 = x ∨ finRotate 3 = x⁻¹ ∨ finRotate 3 = x * (finRotate 3 * x * (finRotate 3)⁻¹) ∨
      finRotate 3 = (x * (finRotate 3 * x * (finRotate 3)⁻¹))⁻¹ := by
  revert x
  decide

theorem sq_eq_one_of_not_injective {G : Type*} [Group G] (f : Equiv.Perm (Fin 3) →* G)
    (hf : ¬ Function.Injective f) (g : Equiv.Perm (Fin 3)) : f g ^ 2 = 1 := by
  rw [injective_iff_map_eq_one] at hf
  push Not at hf
  obtain ⟨x, hx, hx1⟩ := hf
  have hc : f (finRotate 3) = 1 := by
    rcases perm_three_cycle_mem x hx1 with h | h | h | h
    · rw [h, hx]
    · rw [h, map_inv, hx, inv_one]
    · rw [h]
      simp [hx]
    · rw [h]
      simp [hx]
  rcases perm_three_sq_cases g with h | h | h
  · rw [← map_pow, h, map_one]
  · rw [← map_pow, h, hc]
  · rw [← map_pow, h, map_inv, hc, inv_one]

theorem range_le_wSup_of_perm_three {G : Type} [Group G] (hG : CFSG.pCore 2 G = ⊥)
    (f : Equiv.Perm (Fin 3) →* G) (hnormal : f.range.Normal) : f.range ≤ wSup G := by
  by_cases hinj : Function.Injective f
  · exact le_wSup_of_normal hnormal
      (Or.inr (Or.inr (Or.inl ⟨(MonoidHom.ofInjective hinj).symm⟩)))
  · have hP : IsPGroup 2 f.range := by
      rintro ⟨_, g, rfl⟩
      exact ⟨1, Subtype.ext (by simpa using sq_eq_one_of_not_injective f hinj g)⟩
    have hle : f.range ≤ CFSG.pCore 2 G := le_sSup ⟨hnormal, hP⟩
    rw [hG] at hle
    exact hle.trans bot_le

theorem range_le_wSup {G : Type} [Group G] [Finite G] (hG : CFSG.pCore 2 G = ⊥) {D S : Type}
    [Group D] [Group S] (ℓ : D →* S) (hℓ : Function.Surjective ℓ) (φ : D →* G)
    (hker : ℓ.ker ≤ φ.ker) (hnormal : φ.range.Normal)
    (hS : CFSG.Open.IsQuasisimple S ∨ Nonempty (S ≃* Equiv.Perm (Fin 3))) :
    φ.range ≤ CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.wSup G := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : S →* G, ψ.comp ℓ = φ :=
    ⟨ℓ.liftOfSurjective hℓ ⟨φ, hker⟩, MonoidHom.liftOfRightInverse_comp _ _ _ _⟩
  have hrange : φ.range = ψ.range := by
    rw [← hψ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hℓ, Subgroup.map_top]
  rw [hrange] at hnormal ⊢
  rcases hS with hq | he
  · exact range_le_wSup_of_isQuasisimple ψ hnormal hq
  · obtain ⟨e⟩ := he
    have hr : (ψ.comp e.symm.toMonoidHom).range = ψ.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, Subgroup.map_top]
    rw [← hr] at hnormal ⊢
    exact range_le_wSup_of_perm_three hG _ hnormal

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
