module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ABlk
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine CFSG.LocalAnalysis.GLTheoremA.S265A

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem exists_finrank_fixedByEnd_eq_eight (hF : Nat.card F = 2) (hV : Module.finrank F V = 10)
    {f : LinearMap.BilinForm F V} (halt : f.IsAlt) (hnd : f.Nondegenerate)
    {A : Subgroup (V ≃ₗ[F] V)} (hA : IsElemAbelian 3 A) (h81 : 81 ≤ Nat.card A)
    (hAf : ∀ a ∈ A, ∀ u v : V, f (a u) (a v) = f u v) {d : V ≃ₗ[F] V} (hdA : d ∈ A)
    (hd : fixedByEnd d = ⊥) {T : Subgroup (V ≃ₗ[F] V)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTf : ∀ t ∈ T, ∀ u v : V, f (t u) (t v) = f u v)
    (hAT : A ≤ Subgroup.normalizer (T : Set (V ≃ₗ[F] V))) :
    ∃ e ∈ A, Module.finrank F ↥(fixedByEnd e) = 8 := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e e' h => LinearEquiv.ext (congrFun h)
  letI : Fintype A := Fintype.ofFinite A
  have hAf' : InvariantBilin A f := fun a => hAf a a.2
  have hpF := cast_three_ne_zero_of_card_two (F := F) hF
  have h3 := Nat.prime_three
  have hC : fixedSpaceOf A = ⊥ := by
    refine eq_bot_iff.2 fun v hv => ?_
    have hv' : v ∈ fixedByEnd d := mem_fixedByEnd.2 ((mem_fixedSpaceOf A).1 hv ⟨d, hdA⟩)
    rw [hd] at hv'
    exact hv'
  have heven : ∀ D : Hyperplane A 3, Even (Module.finrank F ↥(blockSpace A D.1)) := fun D => by
    have halt' : (LinearMap.BilinForm.restrict f (blockSpace A D.1)).IsAlt := fun u => by
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
      exact halt _
    exact halt'.even_finrank (blockSpace_nondegenerate A h3 hpF hA halt hAf' hnd D)
  have hsum : ∑ D : Hyperplane A 3, Module.finrank F ↥(blockSpace A D.1) = 10 := by
    have h := finrank_eq_finrank_fixedSpaceOf_add_sum_blockSpace A h3 hpF hA
    rw [hC, finrank_bot, hV] at h
    omega
  set S := nonBotBlocks A 3
  have hSmem : ∀ D, D ∈ S ↔ blockSpace A D.1 ≠ ⊥ := fun D => mem_nonBotBlocks A 3
  have hge2 : ∀ D ∈ S, 2 ≤ Module.finrank F ↥(blockSpace A D.1) := fun D hD => by
    have hpos : 0 < Module.finrank F ↥(blockSpace A D.1) :=
      Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 ((hSmem D).1 hD))
    obtain ⟨k, hk⟩ := heven D
    omega
  have hbotS : ∀ D, D ∉ S → blockSpace A D.1 = ⊥ := fun D hD =>
    by_contra fun h => hD ((hSmem D).2 h)
  have hzero : ∀ D ∉ S, Module.finrank F ↥(blockSpace A D.1) = 0 := fun D hD => by
    rw [hbotS D hD, finrank_bot]
  have hsumS : ∑ D ∈ S, Module.finrank F ↥(blockSpace A D.1) = 10 := by
    rw [← hsum]
    exact Finset.sum_subset (Finset.subset_univ S) fun D _ hD => hzero D hD
  have hfaith : ∀ a : ↥A, (∀ D ∈ S, a ∈ D.1) → a = 1 := by
    intro a ha
    have hle : fixedSpaceOf A ⊔ (⨆ D : Hyperplane A 3, blockSpace A D.1) ≤
        fixedByEnd (a : V ≃ₗ[F] V) := by
      refine sup_le (fun v hv => mem_fixedByEnd.2 ((mem_fixedSpaceOf A).1 hv a))
        (iSup_le fun D v hv => ?_)
      by_cases hD : D ∈ S
      · exact mem_fixedByEnd.2 (((mem_blockSpace A).1 hv).1 a (ha D hD))
      · rw [hbotS D hD] at hv
        rw [(Submodule.mem_bot F).1 hv]
        exact Submodule.zero_mem _
    rw [sup_fixedSpaceOf_iSup_blockSpace A h3 hpF hA] at hle
    exact Subtype.ext (LinearEquiv.ext fun v => mem_fixedByEnd.1 (hle Submodule.mem_top))
  have hbot : (⨅ D : S, (D : Hyperplane A 3).1) = ⊥ := by
    refine eq_bot_iff.2 fun a ha => ?_
    rw [Subgroup.mem_iInf] at ha
    exact (Subgroup.mem_bot).2 (hfaith a fun D hD => ha ⟨D, hD⟩)
  have hcard : Nat.card A ≤ 3 ^ S.card := by
    have h := Subgroup.index_iInf_le (fun D : S => (D : Hyperplane A 3).1)
    rw [hbot, Subgroup.index_bot] at h
    refine h.trans (le_of_eq ?_)
    calc _ = ∏ _D : S, 3 := Finset.prod_congr rfl fun D _ => D.1.2
      _ = 3 ^ S.card := by simp
  have hS4 : 4 ≤ S.card := by
    by_contra hlt
    have := (Nat.pow_le_pow_right (by norm_num) (by omega : S.card ≤ 3)).trans
      (by norm_num : 3 ^ 3 ≤ 27)
    omega
  have hS5 : S.card ≤ 5 := by
    have := Finset.card_nsmul_le_sum S (fun D => Module.finrank F ↥(blockSpace A D.1)) 2 hge2
    rw [hsumS, smul_eq_mul] at this
    omega
  rcases (by omega : S.card = 4 ∨ S.card = 5) with hn | hn
  · obtain ⟨D₀, hD₀S, hmin⟩ := Finset.exists_min_image S
      (fun D => Module.finrank F ↥(blockSpace A D.1)) (Finset.card_pos.1 (by omega))
    have h2 : Module.finrank F ↥(blockSpace A D₀.1) = 2 := by
      have h := Finset.card_nsmul_le_sum S (fun D => Module.finrank F ↥(blockSpace A D.1))
        (Module.finrank F ↥(blockSpace A D₀.1)) hmin
      rw [hsumS, hn, smul_eq_mul] at h
      have := hge2 D₀ hD₀S
      omega
    set G : Subgroup ↥A := ⨅ D : (S.erase D₀), (D : Hyperplane A 3).1
    have hGidx : G.index ≤ 27 := by
      have h := Subgroup.index_iInf_le (fun D : (S.erase D₀) => (D : Hyperplane A 3).1)
      refine h.trans (le_of_eq ?_)
      calc _ = ∏ _D : (S.erase D₀), 3 := Finset.prod_congr rfl fun D _ => D.1.2
        _ = 27 := by simp [Finset.card_erase_of_mem hD₀S, hn]
    have hGcard : 3 ≤ Nat.card G := by
      by_contra hlt
      have h := Subgroup.card_mul_index G
      have : Nat.card G * G.index ≤ 2 * 27 := Nat.mul_le_mul (by omega) hGidx
      omega
    obtain ⟨e, heG, he1⟩ : ∃ e ∈ G, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hGbot : G = ⊥ := eq_bot_iff.2 fun x hx => (Subgroup.mem_bot).2 (hcon x hx)
      rw [hGbot, Subgroup.card_bot] at hGcard
      omega
    have heG' : ∀ D ∈ S, D ≠ D₀ → e ∈ D.1 := fun D hD hDD =>
      (Subgroup.mem_iInf.1 heG) ⟨D, Finset.mem_erase.2 ⟨hDD, hD⟩⟩
    have heD₀ : e ∉ D₀.1 := fun h =>
      he1 (hfaith e fun D hD => by
        by_cases hDD : D = D₀
        · rw [hDD]; exact h
        · exact heG' D hD hDD)
    have hbr := finrank_eq_fixedByEnd_add_nOut A h3 hpF hA e
    have hn2 : nOut (fun D : Hyperplane A 3 => D.1)
        (fun D => Module.finrank F ↥(blockSpace A D.1)) e = 2 := by
      unfold nOut
      rw [Finset.sum_eq_single D₀]
      · show (if e ∈ D₀.1 then 0 else Module.finrank F ↥(blockSpace A D₀.1)) = 2
        rw [if_neg heD₀, h2]
      · intro D _ hDD
        by_cases hD : D ∈ S
        · rw [if_pos (heG' D hD hDD)]
        · show (if e ∈ D.1 then 0 else Module.finrank F ↥(blockSpace A D.1)) = 0
          rw [hzero D hD]
          simp
      · intro h
        exact absurd (Finset.mem_univ D₀) h
    exact ⟨(e : V ≃ₗ[F] V), e.2, by omega⟩
  · exfalso
    have hblk : ∀ D : Hyperplane A 3, Module.finrank F ↥(blockSpace A D.1) ≤ 2 := by
      intro D
      by_cases hD : D ∈ S
      · by_contra hlt
        have h1 := Finset.add_sum_erase S (fun D => Module.finrank F ↥(blockSpace A D.1)) hD
        have h2 := Finset.card_nsmul_le_sum (S.erase D)
          (fun D => Module.finrank F ↥(blockSpace A D.1)) 2
          fun E hE => hge2 E (Finset.mem_of_mem_erase hE)
        rw [Finset.card_erase_of_mem hD, hn, smul_eq_mul] at h2
        rw [hsumS] at h1
        omega
      · rw [hzero D hD]
        omega
    exact hT1 (two_group_eq_bot_of_small_blocks hF halt hnd hA hAf' hC hblk hT hTf hAT)

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
