module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.KGFactC31M24Oct
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFn
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
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

theorem conclK_m24_octad
    (MK : Subgroup G₀) : ConclK G₀ Mo (eSub basis_o) MK := by
  unfold ConclK
  let α := E16.eNHom basis_o Mo_le
  have hker_le : α.ker ≤ (eSub basis_o).subgroupOf Mo := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    have h := (E16.eNHom_eq_one_iff basis_o Mo_le x).mp hx
    rwa [cent_o] at h
  have hker_card_le : Nat.card α.ker ≤ 16 := by
    have hinj : Function.Injective fun x : ↥α.ker =>
        (⟨((x : ↥Mo) : G₀),
          Subgroup.mem_subgroupOf.mp (hker_le x.2)⟩ : ↥(eSub basis_o)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(eSub basis_o) => (z : G₀)) hxy))
    have h := Nat.card_le_card_of_injective _ hinj
    rw [card_eSub] at h
    norm_num at h
    exact h
  have hrange_card_le : Nat.card α.range ≤ 20160 := by
    have h := Nat.card_le_card_of_injective
      (fun x : ↥α.range => ((x : α.range) : ↥(StatedSL 4 (ZMod 2))))
      Subtype.val_injective
    rw [E16.card_statedSL4] at h
    exact h
  have hcard : Nat.card α.range * Nat.card α.ker = Nat.card ↥Mo := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv] at h
    exact h.symm
  have hprod : Nat.card α.range * Nat.card α.ker = 20160 * 16 := by
    rw [hcard, card_Mo]
  have hsurj_card : Nat.card α.range = 20160 := by
    have h1 : 20160 * 16 ≤ Nat.card α.range * 16 := by
      rw [← hprod]
      exact Nat.mul_le_mul_left _ hker_card_le
    exact le_antisymm hrange_card_le (Nat.le_of_mul_le_mul_right h1 (by norm_num))
  have hker_card : Nat.card α.ker = 16 := by
    rw [hsurj_card] at hprod
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hprod
  have hinf_card_ge : 16 ≤ Nat.card ↥(eSub basis_o ⊓ Mo) := by
    have hinj : Function.Injective fun x : ↥α.ker =>
        (⟨((x : ↥Mo) : G₀),
          ⟨Subgroup.mem_subgroupOf.mp (hker_le x.2), (x : ↥Mo).2⟩⟩ :
          ↥(eSub basis_o ⊓ Mo)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(eSub basis_o ⊓ Mo) => (z : G₀)) hxy))
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [hker_card] at h
  have hinf_card_le : Nat.card ↥(eSub basis_o ⊓ Mo) ≤ 16 := by
    have h := Nat.card_le_card_of_injective
      (fun x : ↥(eSub basis_o ⊓ Mo) => (⟨(x : G₀), x.2.1⟩ : ↥(eSub basis_o)))
      (fun x y hxy => Subtype.ext
        (congrArg (fun z : ↥(eSub basis_o) => (z : G₀)) hxy))
    rw [card_eSub] at h
    norm_num at h
    exact h
  have hRM : eSub basis_o ≤ Mo := by
    have hcard_eSub_le : Nat.card ↥(eSub basis_o) ≤ Nat.card ↥(eSub basis_o ⊓ Mo) := by
      rw [card_eSub]
      norm_num
      exact hinf_card_ge
    exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left hcard_eSub_le)
  have hE2 : IsPGroup 2 ↥(eSub basis_o) := IsPGroup.of_card (n := 4) (card_eSub basis_o)
  haveI : IsSimpleGroup ↥(StatedSL 4 (ZMod 2)) := E16.isSimpleGroup_statedSL4
  have hNo : NoNormalTwo ↥(StatedSL 4 (ZMod 2)) :=
    noNormalTwo_of_simple not_isPGroup_sl4
  have hsurj : Function.Surjective α := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _
      (by rw [E16.card_statedSL4]; exact hsurj_card)
  have hC : Mo ⊓ Subgroup.centralizer (eSub basis_o : Set G₀) = eSub basis_o := by
    rw [cent_o, inf_eq_right.mpr hRM]
  have hker₀ : α.ker = (eSub basis_o).subgroupOf Mo := ker_eNHom basis_o Mo_le hC
  have hO : pCoreOf 2 Mo = eSub basis_o :=
    pCoreOf_eq_of_surj hRM hE2 α hsurj hker₀ hNo
  have hpk : CFSG.pCore 2 ↥Mo = α.ker := by
    rw [← Hex.pCoreOf_subgroupOf' Mo, hO, hker₀]
  let eQ : ↥Mo ⧸ CFSG.pCore 2 ↥Mo ≃* ↥(StatedSL 4 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj)
  have hpsl : IsPSL 4 2 1 (↥Mo ⧸ CFSG.pCore 2 ↥Mo) := E16.isPSL_of_equiv4 eQ
  have hcardX : Nat.card (↥Mo ⧸ CFSG.pCore 2 ↥Mo) = 20160 := by
    rw [Nat.card_congr eQ.toEquiv, E16.card_statedSL4]
  have hq : CFSG.IsQuasisimple (↥Mo ⧸ CFSG.pCore 2 ↥Mo) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥Mo ⧸ CFSG.pCore 2 ↥Mo) .PSL 4 2 1 := Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥Mo ⧸ CFSG.pCore 2 ↥Mo) := Or.inr (Or.inr (Or.inl hLM))
  let β : ↥(eSub basis_o) →* Multiplicative (Fin 4 → ZMod 2) := (ecoords basis_o).toMonoidHom
  have hβinj : Function.Injective β := (ecoords basis_o).injective
  have hβsurj : Function.Surjective β := (ecoords basis_o).surjective
  have hsec : IsNaturalSection Mo (eSub basis_o) ⊥ ((eSub basis_o).subgroupOf Mo)
      (StatedSL 4 (ZMod 2)) := by
    refine ⟨Mo_le, α, hsurj, hker₀, β, hβsurj, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr hβinj
    · intro a u w hw
      rw [E16.eNHom_coe]
      exact ecoords_conj basis_o ⟨a, Mo_le a.2⟩ u w hw
  have hsum : IsSumOfNaturalModules Mo (eSub basis_o) ⊥ ((eSub basis_o).subgroupOf Mo)
      (StatedSL 4 (ZMod 2)) false 1 :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  have hcommV : IsMulCommutative ↥(eSub basis_o) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_o x y hx hy
  letI : IsMulCommutative ↥(eSub basis_o) := hcommV
  have hFFM : IsFFModule (autOn Mo (eSub basis_o)) :=
    FFn.isFFModule_autOn_of_sum (n := 3) (k := 1) (by decide) le_rfl (by norm_num) hsum
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub basis_o : Set G₀))
      (eSub basis_o)) :=
    isFFModule_of_le (autOn_mono' Mo_le) hFFM
  have hbin : BinaryNaturalSL (V := ↥(eSub basis_o)) (autOn Mo (eSub basis_o)) ⊤ ⊥ 4 1 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
    exact T4213N.realizes_of_equiv Mo_le (FFModel.nat (StatedSL 4 (ZMod 2)))
      (fun _ => trivial) (fun x => Subgroup.mem_bot)
      (fun _ => rfl)
      α hsurj
      (fun a ha => by
        have hmem : (a : G₀) ∈ eSub basis_o := by
          have : a ∈ α.ker := ha
          rwa [hker₀, Subgroup.mem_subgroupOf] at this
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_o _ _ hy hmem)
      (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
      (fun a w w' hw => by
        show β w' = (FFModel.nat (StatedSL 4 (ZMod 2))).act (α a) (β w)
        apply Multiplicative.toAdd.injective
        show Multiplicative.toAdd (β w') = (((α a : ↥(StatedSL 4 (ZMod 2))) :
          Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (β w)
        rw [E16.eNHom_coe]
        exact ecoords_conj basis_o ⟨a, Mo_le a.2⟩ w w' hw)
  have hnat : IsNaturalSumUnder 4 Mo (eSub basis_o) := by
    refine ⟨1, fun _ => eSub basis_o, by norm_num, ?_, ?_, iSupIndep_subsingleton _, ?_⟩
    · intro i
      exact ⟨le_rfl, Mo_le, ⟨hcommV, hbin⟩⟩
    · intro i j
      exact isXSectionIso₂_of_isLEquiv (φ := MulEquiv.refl _) (fun l hl a a' ha' => ha')
    · rw [iSup_const]
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro h3
    have h1 := LieModel.card_psl_three_two h3
    rw [hcardX] at h1
    norm_num at h1
  ·
    intro _
    exact Or.inl hnat
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
