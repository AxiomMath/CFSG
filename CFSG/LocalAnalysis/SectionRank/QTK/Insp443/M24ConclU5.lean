module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.KGFactC31M24Q
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFn
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat
public import CFSG.Quasithin.Vol2.Ch4Sec4L446Nat

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24
open scoped IsMulCommutative Matrix

namespace M24

theorem ker_e3Hom_u5 :
    (E8.e3Hom basis_u5 Lq_le).ker = (eSub basis_et).subgroupOf Lq := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E8.e3Hom_eq_one_iff]
  constructor
  · intro h
    have h2 : (x : G₀) ∈ Lq ⊓ Subgroup.centralizer (eSub basis_u5 : Set G₀) := ⟨x.2, h⟩
    rwa [Lq_inf_cent] at h2
  · intro hx
    exact et_le_cent hx

theorem surjective_e3Hom_u5 :
    Function.Surjective (E8.e3Hom basis_u5 Lq_le) := by
  have h1 := card_range_eq et_le_Lq (E8.e3Hom basis_u5 Lq_le) ker_e3Hom_u5
  rw [card_eSub, card_Lq] at h1
  have h2 : Nat.card (E8.e3Hom basis_u5 Lq_le).range = Nat.card ↥(StatedSL 3 (ZMod 2)) := by
    rw [E8.card_statedSL3]; omega
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ h2

theorem pCoreOf_Lq : pCoreOf 2 Lq = eSub basis_et := by
  haveI : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
  exact pCoreOf_eq_of_surj et_le_Lq (IsPGroup.of_card (n := 6) (card_eSub basis_et)) _
    surjective_e3Hom_u5 ker_e3Hom_u5 (noNormalTwo_of_simple not_isPGroup_sl3)

theorem isPSL_Lq : IsPSL 3 2 1 (↥Lq ⧸ CFSG.pCore 2 ↥Lq) := by
  have hpk : CFSG.pCore 2 ↥Lq = (E8.e3Hom basis_u5 Lq_le).ker := by
    rw [← Hex.pCoreOf_subgroupOf', pCoreOf_Lq, ker_e3Hom_u5]
  exact E8.isPSL_of_equiv3 ((QuotientGroup.quotientMulEquivOfEq hpk).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ surjective_e3Hom_u5))

theorem binaryNaturalSL_u5 [IsMulCommutative ↥(eSub basis_u5)] :
    BinaryNaturalSL (V := ↥(eSub basis_u5)) (autOn Lq (eSub basis_u5)) ⊤ ⊥ 3 1 := by
  let α := E8.e3Hom basis_u5 Lq_le
  let β : ↥(eSub basis_u5) →* Multiplicative (Fin 3 → ZMod 2) := (ecoords basis_u5).toMonoidHom
  refine ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
  exact T4213N.realizes_of_equiv Lq_le (FFModel.nat (StatedSL 3 (ZMod 2)))
    (fun _ => trivial) (fun x => Subgroup.mem_bot) (fun _ => rfl)
    α surjective_e3Hom_u5
    (fun a ha => by
      have hmem : (a : G₀) ∈ eSub basis_et := by
        have h2 : a ∈ α.ker := ha
        rwa [ker_e3Hom_u5, Subgroup.mem_subgroupOf] at h2
      exact et_le_cent hmem)
    (MulEquiv.ofBijective β ⟨(ecoords basis_u5).injective, (ecoords basis_u5).surjective⟩)
    (fun a w w' hw => by
      show β w' = (FFModel.nat (StatedSL 3 (ZMod 2))).act (α a) (β w)
      apply Multiplicative.toAdd.injective
      show Multiplicative.toAdd (β w') = (((α a : ↥(StatedSL 3 (ZMod 2))) :
        Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (β w)
      rw [E8.e3Hom_coe]
      exact ecoords_conj basis_u5 ⟨a, Lq_le a.2⟩ w w' hw)

end M24

open M24 in
theorem conclK_m24_u5 (MK : Subgroup G₀) :
    ConclK G₀ Lq (eSub basis_u5) MK := by
  unfold ConclK
  let α := E8.e3Hom basis_u5 Lq_le
  have hpsl : IsPSL 3 2 1 (↥Lq ⧸ CFSG.pCore 2 ↥Lq) := isPSL_Lq
  have hcardX : Nat.card (↥Lq ⧸ CFSG.pCore 2 ↥Lq) = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hpsl
  have hq : CFSG.IsQuasisimple (↥Lq ⧸ CFSG.pCore 2 ↥Lq) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥Lq ⧸ CFSG.pCore 2 ↥Lq) .PSL 3 2 1 := Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥Lq ⧸ CFSG.pCore 2 ↥Lq) := Or.inr (Or.inl hLM)
  let β : ↥(eSub basis_u5) →* Multiplicative (Fin 3 → ZMod 2) :=
    (ecoords basis_u5).toMonoidHom
  have hβinj : Function.Injective β := (ecoords basis_u5).injective
  have hβsurj : Function.Surjective β := (ecoords basis_u5).surjective
  have hsec : IsNaturalSection Lq (eSub basis_u5) ⊥ ((eSub basis_et).subgroupOf Lq)
      (StatedSL 3 (ZMod 2)) := by
    refine ⟨Lq_le, α, surjective_e3Hom_u5, ker_e3Hom_u5, β, hβsurj, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr hβinj
    · intro a u w hw
      exact ecoords_conj basis_u5 ⟨a, Lq_le a.2⟩ u w hw
  have hsum : IsSumOfNaturalModules Lq (eSub basis_u5) ⊥ ((eSub basis_et).subgroupOf Lq)
      (StatedSL 3 (ZMod 2)) false 1 :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  have hcommV : IsMulCommutative ↥(eSub basis_u5) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_u5 x y hx hy
  letI : IsMulCommutative ↥(eSub basis_u5) := hcommV
  have hFFL : IsFFModule (autOn Lq (eSub basis_u5)) :=
    FFn.isFFModule_autOn_of_sum (n := 2) (k := 1) (by decide) le_rfl (by norm_num) hsum
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub basis_u5 : Set G₀))
      (eSub basis_u5)) :=
    isFFModule_of_le (autOn_mono' Lq_le) hFFL
  have hnat : IsNaturalSumUnder 3 Lq (eSub basis_u5) := by
    refine ⟨1, fun _ => eSub basis_u5, by norm_num, ?_, ?_, iSupIndep_subsingleton _, ?_⟩
    · intro i
      exact ⟨le_rfl, Lq_le, ⟨hcommV, binaryNaturalSL_u5⟩⟩
    · intro i j
      exact isXSectionIso₂_of_isLEquiv (φ := MulEquiv.refl _) (fun l hl a a' ha' => ha')
    · rw [iSup_const]
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro _
    exact hnat
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, hc, -⟩
    rw [F420.center_eq_bot_of_statedPSL hpsl] at hc
    rw [Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro _ h64
    rw [card_eSub] at h64
    norm_num at h64

end CFSG.SectionRank.QTK.Insp443

end
