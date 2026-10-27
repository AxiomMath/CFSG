module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClSpQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClBlk
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClEl
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial (sesqUnitaryGroup mem_sesqUnitaryGroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks (fixedByEnd mem_fixedByEnd)

private abbrev V5 : Type := Fin 5 ⊕ Fin 5 → ZMod 2

private noncomputable def rep : StatedSp 5 (ZMod 2) →* (V5 ≃ₗ[ZMod 2] V5) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V5).toMonoidHom.comp
    (spLin 5 (ZMod 2))

private theorem rep_injective : Function.Injective rep :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V5).injective.comp spLin_injective

private theorem rep_form (g : StatedSp 5 (ZMod 2)) (u v : V5) :
    spForm 5 (ZMod 2) (rep g u) (rep g v) = spForm 5 (ZMod 2) u v :=
  mem_sesqUnitaryGroup.1 (spLin_mem g) u v

private theorem exists_rep_eq {h : V5 ≃ₗ[ZMod 2] V5}
    (hh : ∀ u v, spForm 5 (ZMod 2) (h u) (h v) = spForm 5 (ZMod 2) u v) : ∃ g, rep g = h := by
  have hmem : (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V5).symm h ∈
      sesqUnitaryGroup (spForm 5 (ZMod 2)) := mem_sesqUnitaryGroup.2 hh
  rw [← range_spLin] at hmem
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, by
    rw [rep, MonoidHom.comp_apply]
    simp only [MulEquiv.coe_toMonoidHom, hg, MulEquiv.apply_symm_apply]⟩

private theorem fixedByEnd_rep (g : StatedSp 5 (ZMod 2)) :
    fixedByEnd (rep g) = LinearMap.ker (spEnd g - 1) := by
  ext v
  rw [mem_fixedByEnd, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  exact Iff.rfl

private theorem finrank_V5 : Module.finrank (ZMod 2) V5 = 10 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem ker_spEnd_sub_one_eq_bot_of_commute_eleven {d y : StatedSp 5 (ZMod 2)} (hd : d ≠ 1)
    (hy : y ^ 11 = 1) (hy1 : y ≠ 1) (hdy : d * y = y * d) :
    LinearMap.ker (spEnd d - 1) = ⊥ := by
  rw [← fixedByEnd_rep]
  exact fixedByEnd_eq_bot_of_commute_eleven (Nat.card_zmod 2) finrank_V5
    (fun h => hd (rep_injective (h.trans (map_one rep).symm)))
    (by rw [← map_pow, hy, map_one])
    (fun h => hy1 (rep_injective (h.trans (map_one rep).symm)))
    (by rw [← map_mul, ← map_mul, hdy])

theorem finrank_ker_spEnd_sub_one_ne_eight {d y : StatedSp 5 (ZMod 2)} (hy : y ^ 11 = 1)
    (hy1 : y ≠ 1) (hdy : d * y = y * d) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (spEnd d - 1)) ≠ 8 := by
  by_cases hd : d = 1
  · have h0 : spEnd d - 1 = 0 := by
      rw [hd]
      simp [spEnd]
    rw [h0, LinearMap.ker_zero, finrank_top, finrank_V5]
    norm_num
  · rw [ker_spEnd_sub_one_eq_bot_of_commute_eleven hd hy hy1 hdy, finrank_bot]
    norm_num

private theorem finite_linearEquiv_V5 : Finite (V5 ≃ₗ[ZMod 2] V5) :=
  Finite.of_injective (fun g : V5 ≃ₗ[ZMod 2] V5 => (g : V5 → V5)) fun _ _ h =>
    LinearEquiv.ext (congrFun h)

theorem exists_layer_pair_statedSp_five {A T : Subgroup (StatedSp 5 (ZMod 2))}
    (hA : IsElemAbelian 3 A) (h81 : 81 ≤ Nat.card A) {d : StatedSp 5 (ZMod 2)} (hdA : d ∈ A)
    (hd : LinearMap.ker (spEnd d - 1) = ⊥) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hAT : A ≤ Subgroup.normalizer (T : Set (StatedSp 5 (ZMod 2)))) :
    ∃ e ∈ A, Module.finrank (ZMod 2) ↥(LinearMap.ker (spEnd e - 1)) = 8 ∧
      GLAPLayer 3 (Subgroup.centralizer ({d} : Set (StatedSp 5 (ZMod 2))) ⊓
        Subgroup.centralizer ({e} : Set (StatedSp 5 (ZMod 2)))) ≠ ⊥ := by
  haveI := finite_linearEquiv_V5
  have hAf : ∀ a ∈ A.map rep, ∀ u v : V5,
      spForm 5 (ZMod 2) (a u) (a v) = spForm 5 (ZMod 2) u v := by
    rintro _ ⟨g, -, rfl⟩ u v
    exact rep_form g u v
  have hTf : ∀ t ∈ T.map rep, ∀ u v : V5,
      spForm 5 (ZMod 2) (t u) (t v) = spForm 5 (ZMod 2) u v := by
    rintro _ ⟨g, -, rfl⟩ u v
    exact rep_form g u v
  have hAT' : A.map rep ≤ Subgroup.normalizer ((T.map rep : Subgroup _) : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    simp only [SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨a * t * a⁻¹, (Subgroup.mem_normalizer_iff.1 (hAT ha) t).1 ht, by simp⟩
    · rintro ⟨t, ht, hte⟩
      refine ⟨a⁻¹ * t * a, ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.1 (hAT (A.inv_mem ha)) t).1 ht
      · rw [map_mul, map_mul, map_inv, hte]
        group
  obtain ⟨e', he'A, he8⟩ := exists_finrank_fixedByEnd_eq_eight (Nat.card_zmod 2) finrank_V5
    spForm_isAlt spForm_nondegenerate (hA.map rep)
    (by rw [Subgroup.card_map_of_injective rep_injective]; exact h81) hAf
    (Subgroup.mem_map_of_mem rep hdA) (by rw [fixedByEnd_rep]; exact hd) (hT.map rep)
    (fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ rep_injective).1 h)) hTf hAT'
  obtain ⟨e, heA, rfl⟩ := Subgroup.mem_map.1 he'A
  refine ⟨e, heA, by rw [← fixedByEnd_rep]; exact he8, fun hbot => ?_⟩
  have hde : d * e = e * d := hA.comm hdA heA
  have hmap : (Subgroup.centralizer ({d} : Set (StatedSp 5 (ZMod 2))) ⊓
      Subgroup.centralizer ({e} : Set (StatedSp 5 (ZMod 2)))).map rep =
      rep.range ⊓ Subgroup.centralizer ({rep d} : Set (V5 ≃ₗ[ZMod 2] V5)) ⊓
        Subgroup.centralizer ({rep e} : Set (V5 ≃ₗ[ZMod 2] V5)) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MonoidHom.mem_range]
    constructor
    · rintro ⟨g, ⟨hgd, hge⟩, rfl⟩
      exact ⟨⟨⟨g, rfl⟩, by rw [← map_mul, ← map_mul, hgd]⟩, by rw [← map_mul, ← map_mul, hge]⟩
    · rintro ⟨⟨⟨g, rfl⟩, hgd⟩, hge⟩
      exact ⟨g, ⟨rep_injective (by rw [map_mul, map_mul, hgd]),
        rep_injective (by rw [map_mul, map_mul, hge])⟩, rfl⟩
  have hL := CFSG.glaPLayer_map_eq_of_injective Nat.prime_three rep rep_injective
    (Subgroup.centralizer ({d} : Set (StatedSp 5 (ZMod 2))) ⊓
      Subgroup.centralizer ({e} : Set (StatedSp 5 (ZMod 2))))
  rw [hbot, Subgroup.map_bot, hmap] at hL
  exact glaPLayer_inf_ne_bot_of_symplectic (Nat.card_zmod 2) finrank_V5 spForm_isAlt
    spForm_nondegenerate (d := rep d) (e := rep e) (by rw [← map_pow, hA.2 d hdA, map_one])
    (by rw [← map_pow, hA.2 e heA, map_one]) (by rw [← map_mul, ← map_mul, hde])
    (rep_form d) (rep_form e) (by rw [fixedByEnd_rep]; exact hd) he8 (X := rep.range)
    (fun g hg => exists_rep_eq hg) (fun g ⟨x, hx⟩ u v => hx ▸ rep_form x u v) hL.symm

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
