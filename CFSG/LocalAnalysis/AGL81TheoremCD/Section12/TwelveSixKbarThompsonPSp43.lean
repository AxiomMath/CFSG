module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarThompsonCount
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalModel
import CFSG.LieType.PSp43Local.Transport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Small

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarThompson

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs (xS siegelRadicalData_psp4 normalizer_xS)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag projUnipotent)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (projStabilizer isotropic_subspace_index
  finrank_flag unitriangular_invariant_isotropic_subspaces)

private theorem card_normalizer_siegel [Fact (Nat.Prime 3)] :
    Nat.card (normalizer ((xS 3).U : Set (CFSG.AGLEmbedding.KlingenSpFour.PSp4 3))) = 648 := by
  rw [normalizer_xS (p := 3) (by norm_num)]
  have hW := (((unitriangular_invariant_isotropic_subspaces (r := 2) (K := ZMod 3)).2.1
    (flag 2 (ZMod 3) 2)).2 ⟨2, le_rfl, rfl⟩).1
  have hWk : Module.finrank (ZMod 3) (flag 2 (ZMod 3) 2) = 2 := finrank_flag (by norm_num)
  obtain ⟨-, hidx, -, hprod⟩ :=
    isotropic_subspace_index (r := 2) (K := ZMod 3) (Nat.card_zmod 3) (k := 2) le_rfl
  have h40 : ((projStabilizer 2 (ZMod 3) (flag 2 (ZMod 3) 2)).index : ℚ) = 40 := by
    rw [hidx _ hW hWk, hprod]
    norm_num [Finset.prod_range_succ]
  have h40' : (projStabilizer 2 (ZMod 3) (flag 2 (ZMod 3) 2)).index = 40 := by
    exact_mod_cast h40
  have h := card_mul_index (projStabilizer 2 (ZMod 3) (flag 2 (ZMod 3) 2))
  rw [h40', CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.card_PSp43] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 40) (h.trans (by norm_num))

theorem psp43_facts {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Blueprint.LieModel Y .PSp 2 3 1)
    (P : Sylow 3 Y) :
    Nonempty (↥(P : Subgroup Y) ≃* W3) ∧
      Nat.card (normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y)) ∣ 648 ∧
      ∀ B : Subgroup Y, normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y) ≤ B →
        B = normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y) ∨ B = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eW⟩ := CFSG.LieType.PSp43Local.nonempty_mulEquiv_W3_of_lieModel hY P
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.psp43_equiv_of_lieModel hY
  have hD := siegelRadicalData_psp4 3 (by norm_num)
  have hfac : (Nat.card (⊤ : Subgroup CFSG.GH74.Exceptional.PSp43)).factorization 3 = 4 := by
    rw [card_top, CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.card_PSp43]
    decide +kernel
  have hT₀ : CFSG.ABGLocalTools.IsSylowOf 3 (projUnipotent 2 (ZMod 3)) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by rw [hD.card_T, hfac])
  have hP₁ : CFSG.ABGLocalTools.IsSylowOf 3 ((P : Subgroup Y).map e.toMonoidHom) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by
      rw [card_map_of_injective e.injective, card_of_equiv eW, hfac]
      norm_num)
  obtain ⟨k, -, hk⟩ := hT₀.exists_mem_conj hP₁
  set φ : Y ≃* CFSG.GH74.Exceptional.PSp43 := e.trans (MulAut.conj k⁻¹) with hφ
  have hφapp : ∀ y, φ y = k⁻¹ * e y * k := fun y => by
    rw [hφ, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hφP : (P : Subgroup Y).map φ.toMonoidHom = projUnipotent 2 (ZMod 3) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hφapp]
      exact (hk (e y)).1 ⟨y, hy, rfl⟩
    · intro hx
      have hx' : k * x * k⁻¹ ∈ (P : Subgroup Y).map e.toMonoidHom :=
        (hk (k * x * k⁻¹)).2 (by simpa [mul_assoc] using hx)
      obtain ⟨y, hy, hyx⟩ := hx'
      refine ⟨y, hy, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, hφapp]
      rw [MulEquiv.coe_toMonoidHom] at hyx
      rw [hyx]
      group
  let e₀ : ↥(projUnipotent 2 (ZMod 3)) ≃* W3 :=
    (MulEquiv.subgroupCongr hφP).symm.trans ((φ.subgroupMap (P : Subgroup Y)).symm.trans eW)
  have hJ₀ : CFSG.Open.thompsonSubgroup (projUnipotent 2 (ZMod 3)) = (xS 3).U := by
    rw [thompsonSubgroup_eq_baseIn e₀]
    refine (eq_baseIn_of_comm e₀ hD.U_le ?_ ?_).symm
    · intro a ha b hb
      exact congrArg Subtype.val (hD.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · simp [hD.card_U]
  have hJ : (CFSG.Open.thompsonSubgroup (P : Subgroup Y)).map φ.toMonoidHom = (xS 3).U := by
    rw [CFSG.map_ambientMaxCardThompson_of_injective φ.toMonoidHom _
      (φ.injective.comp (P : Subgroup Y).subtype_injective), hφP]
    exact hJ₀
  have hrange : φ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 φ.surjective
  obtain ⟨hc, hm⟩ := normalizer_facts_of_embedding φ.toMonoidHom φ.injective hJ
    (by rw [hrange, inf_top_eq, card_normalizer_siegel]) (by rw [hrange]; exact hD.coatom)
  exact ⟨⟨eW⟩, hc, hm⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarThompson
