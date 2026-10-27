module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFn
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Quasithin.Vol2.Ch4Sec4L446Nat
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Vol2.KGFactC31M24Oct

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24
open scoped IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G] {v : Fin 4 → G} (hv : EBasis v)

theorem cent_eq_of_le16 (hcent : Subgroup.centralizer (eSub hv : Set G) ≤ eSub hv) :
    Subgroup.centralizer (eSub hv : Set G) = eSub hv :=
  le_antisymm hcent fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hv y x hy hx

theorem conclK_of_normalizer16 (hcardN : Nat.card (eNorm hv) = 322560)
    (hcent : Subgroup.centralizer (eSub hv : Set G) ≤ eSub hv) (MK : Subgroup G) :
    ConclK G (eNorm hv) (eSub hv) MK := by
  have hcent_eq := cent_eq_of_le16 hv hcent
  unfold ConclK
  let α := E16.eNHom hv (le_refl (eNorm hv))
  have hker_le : α.ker ≤ (eSub hv).subgroupOf (eNorm hv) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    have h := (E16.eNHom_eq_one_iff hv (le_refl (eNorm hv)) x).mp hx
    rwa [hcent_eq] at h
  have hker_card_le : Nat.card α.ker ≤ 16 := by
    have hinj : Function.Injective fun x : ↥α.ker =>
        (⟨((x : ↥(eNorm hv)) : G),
          Subgroup.mem_subgroupOf.mp (hker_le x.2)⟩ : ↥(eSub hv)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(eSub hv) => (z : G)) hxy))
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
  have hcard : Nat.card α.range * Nat.card α.ker = Nat.card ↥(eNorm hv) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv] at h
    exact h.symm
  have hprod : Nat.card α.range * Nat.card α.ker = 20160 * 16 := by
    rw [hcard, hcardN]
  have hsurj_card : Nat.card α.range = 20160 := by
    have h1 : 20160 * 16 ≤ Nat.card α.range * 16 := by
      rw [← hprod]
      exact Nat.mul_le_mul_left _ hker_card_le
    exact le_antisymm hrange_card_le (Nat.le_of_mul_le_mul_right h1 (by norm_num))
  have hker_card : Nat.card α.ker = 16 := by
    rw [hsurj_card] at hprod
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hprod
  have hinf_card_ge : 16 ≤ Nat.card ↥(eSub hv ⊓ (eNorm hv)) := by
    have hinj : Function.Injective fun x : ↥α.ker =>
        (⟨((x : ↥(eNorm hv)) : G),
          ⟨Subgroup.mem_subgroupOf.mp (hker_le x.2), (x : ↥(eNorm hv)).2⟩⟩ :
          ↥(eSub hv ⊓ (eNorm hv))) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(eSub hv ⊓ (eNorm hv)) => (z : G)) hxy))
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [hker_card] at h
  have hinf_card_le : Nat.card ↥(eSub hv ⊓ (eNorm hv)) ≤ 16 := by
    have h := Nat.card_le_card_of_injective
      (fun x : ↥(eSub hv ⊓ (eNorm hv)) => (⟨(x : G), x.2.1⟩ : ↥(eSub hv)))
      (fun x y hxy => Subtype.ext
        (congrArg (fun z : ↥(eSub hv) => (z : G)) hxy))
    rw [card_eSub] at h
    norm_num at h
    exact h
  have hRM : eSub hv ≤ (eNorm hv) := by
    have hcard_eSub_le : Nat.card ↥(eSub hv) ≤ Nat.card ↥(eSub hv ⊓ (eNorm hv)) := by
      rw [card_eSub]
      norm_num
      exact hinf_card_ge
    exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left hcard_eSub_le)
  have hE2 : IsPGroup 2 ↥(eSub hv) := IsPGroup.of_card (n := 4) (card_eSub hv)
  haveI : IsSimpleGroup ↥(StatedSL 4 (ZMod 2)) := E16.isSimpleGroup_statedSL4
  have hNo : NoNormalTwo ↥(StatedSL 4 (ZMod 2)) :=
    noNormalTwo_of_simple not_isPGroup_sl4
  have hsurj : Function.Surjective α := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _
      (by rw [E16.card_statedSL4]; exact hsurj_card)
  have hC : (eNorm hv) ⊓ Subgroup.centralizer (eSub hv : Set G) = eSub hv := by
    rw [hcent_eq, inf_eq_right.mpr hRM]
  have hker₀ : α.ker = (eSub hv).subgroupOf (eNorm hv) := ker_eNHom hv (le_refl (eNorm hv)) hC
  have hO : pCoreOf 2 (eNorm hv) = eSub hv :=
    pCoreOf_eq_of_surj hRM hE2 α hsurj hker₀ hNo
  have hpk : CFSG.pCore 2 ↥(eNorm hv) = α.ker := by
    rw [← Hex.pCoreOf_subgroupOf' (eNorm hv), hO, hker₀]
  let eQ : ↥(eNorm hv) ⧸ CFSG.pCore 2 ↥(eNorm hv) ≃* ↥(StatedSL 4 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj)
  have hpsl : IsPSL 4 2 1 (↥(eNorm hv) ⧸ CFSG.pCore 2 ↥(eNorm hv)) := E16.isPSL_of_equiv4 eQ
  have hcardX : Nat.card (↥(eNorm hv) ⧸ CFSG.pCore 2 ↥(eNorm hv)) = 20160 := by
    rw [Nat.card_congr eQ.toEquiv, E16.card_statedSL4]
  have hq : CFSG.IsQuasisimple (↥(eNorm hv) ⧸ CFSG.pCore 2 ↥(eNorm hv)) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥(eNorm hv) ⧸ CFSG.pCore 2 ↥(eNorm hv)) .PSL 4 2 1 := Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥(eNorm hv) ⧸ CFSG.pCore 2 ↥(eNorm hv)) := Or.inr (Or.inr (Or.inl hLM))
  let β : ↥(eSub hv) →* Multiplicative (Fin 4 → ZMod 2) := (ecoords hv).toMonoidHom
  have hβinj : Function.Injective β := (ecoords hv).injective
  have hβsurj : Function.Surjective β := (ecoords hv).surjective
  have hsec : IsNaturalSection (eNorm hv) (eSub hv) ⊥ ((eSub hv).subgroupOf (eNorm hv))
      (StatedSL 4 (ZMod 2)) := by
    refine ⟨(le_refl (eNorm hv)), α, hsurj, hker₀, β, hβsurj, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr hβinj
    · intro a u w hw
      rw [E16.eNHom_coe]
      exact ecoords_conj hv ⟨a, (le_refl (eNorm hv)) a.2⟩ u w hw
  have hsum : IsSumOfNaturalModules (eNorm hv) (eSub hv) ⊥ ((eSub hv).subgroupOf (eNorm hv))
      (StatedSL 4 (ZMod 2)) false 1 :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  have hcommV : IsMulCommutative ↥(eSub hv) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm hv x y hx hy
  letI : IsMulCommutative ↥(eSub hv) := hcommV
  have hFFM : IsFFModule (autOn (eNorm hv) (eSub hv)) :=
    FFn.isFFModule_autOn_of_sum (n := 3) (k := 1) (by decide) le_rfl (by norm_num) hsum
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub hv : Set G))
      (eSub hv)) :=
    isFFModule_of_le (autOn_mono' (le_refl (eNorm hv))) hFFM
  have hbin : BinaryNaturalSL (V := ↥(eSub hv)) (autOn (eNorm hv) (eSub hv)) ⊤ ⊥ 4 1 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
    exact T4213N.realizes_of_equiv (le_refl (eNorm hv)) (FFModel.nat (StatedSL 4 (ZMod 2)))
      (fun _ => trivial) (fun x => Subgroup.mem_bot)
      (fun _ => rfl)
      α hsurj
      (fun a ha => by
        have hmem : (a : G) ∈ eSub hv := by
          have : a ∈ α.ker := ha
          rwa [hker₀, Subgroup.mem_subgroupOf] at this
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hv _ _ hy hmem)
      (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
      (fun a w w' hw => by
        show β w' = (FFModel.nat (StatedSL 4 (ZMod 2))).act (α a) (β w)
        apply Multiplicative.toAdd.injective
        show Multiplicative.toAdd (β w') = (((α a : ↥(StatedSL 4 (ZMod 2))) :
          Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (β w)
        rw [E16.eNHom_coe]
        exact ecoords_conj hv ⟨a, (le_refl (eNorm hv)) a.2⟩ w w' hw)
  have hnat : IsNaturalSumUnder 4 (eNorm hv) (eSub hv) := by
    refine ⟨1, fun _ => eSub hv, by norm_num, ?_, ?_, iSupIndep_subsingleton _, ?_⟩
    · intro i
      exact ⟨le_rfl, (le_refl (eNorm hv)), ⟨hcommV, hbin⟩⟩
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

theorem normalizer16_facts (hcardN : Nat.card (eNorm hv) = 322560)
    (hcent : Subgroup.centralizer (eSub hv : Set G) ≤ eSub hv) :
    Function.Surjective (E16.eNHom hv (le_refl (eNorm hv))) ∧
      (E16.eNHom hv (le_refl (eNorm hv))).ker = (eSub hv).subgroupOf (eNorm hv) := by
  have hcent_eq := cent_eq_of_le16 hv hcent
  let α := E16.eNHom hv (le_refl (eNorm hv))
  have hker_le : α.ker ≤ (eSub hv).subgroupOf (eNorm hv) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    have h := (E16.eNHom_eq_one_iff hv (le_refl (eNorm hv)) x).mp hx
    rwa [hcent_eq] at h
  have hker_card_le : Nat.card α.ker ≤ 16 := by
    have hinj : Function.Injective fun x : ↥α.ker =>
        (⟨((x : ↥(eNorm hv)) : G),
          Subgroup.mem_subgroupOf.mp (hker_le x.2)⟩ : ↥(eSub hv)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(eSub hv) => (z : G)) hxy))
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
  have hcard : Nat.card α.range * Nat.card α.ker = Nat.card ↥(eNorm hv) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv] at h
    exact h.symm
  have hprod : Nat.card α.range * Nat.card α.ker = 20160 * 16 := by
    rw [hcard, hcardN]
  have hsurj_card : Nat.card α.range = 20160 := by
    have h1 : 20160 * 16 ≤ Nat.card α.range * 16 := by
      rw [← hprod]
      exact Nat.mul_le_mul_left _ hker_card_le
    exact le_antisymm hrange_card_le (Nat.le_of_mul_le_mul_right h1 (by norm_num))
  have hker_card : Nat.card α.ker = 16 := by
    rw [hsurj_card] at hprod
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hprod
  have hinf_card_ge : 16 ≤ Nat.card ↥(eSub hv ⊓ (eNorm hv)) := by
    have hinj : Function.Injective fun x : ↥α.ker =>
        (⟨((x : ↥(eNorm hv)) : G),
          ⟨Subgroup.mem_subgroupOf.mp (hker_le x.2), (x : ↥(eNorm hv)).2⟩⟩ :
          ↥(eSub hv ⊓ (eNorm hv))) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(eSub hv ⊓ (eNorm hv)) => (z : G)) hxy))
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [hker_card] at h
  have hinf_card_le : Nat.card ↥(eSub hv ⊓ (eNorm hv)) ≤ 16 := by
    have h := Nat.card_le_card_of_injective
      (fun x : ↥(eSub hv ⊓ (eNorm hv)) => (⟨(x : G), x.2.1⟩ : ↥(eSub hv)))
      (fun x y hxy => Subtype.ext
        (congrArg (fun z : ↥(eSub hv) => (z : G)) hxy))
    rw [card_eSub] at h
    norm_num at h
    exact h
  have hRM : eSub hv ≤ (eNorm hv) := by
    have hcard_eSub_le : Nat.card ↥(eSub hv) ≤ Nat.card ↥(eSub hv ⊓ (eNorm hv)) := by
      rw [card_eSub]
      norm_num
      exact hinf_card_ge
    exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left hcard_eSub_le)
  have hE2 : IsPGroup 2 ↥(eSub hv) := IsPGroup.of_card (n := 4) (card_eSub hv)
  haveI : IsSimpleGroup ↥(StatedSL 4 (ZMod 2)) := E16.isSimpleGroup_statedSL4
  have hNo : NoNormalTwo ↥(StatedSL 4 (ZMod 2)) :=
    noNormalTwo_of_simple not_isPGroup_sl4
  have hsurj : Function.Surjective α := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _
      (by rw [E16.card_statedSL4]; exact hsurj_card)
  have hC : (eNorm hv) ⊓ Subgroup.centralizer (eSub hv : Set G) = eSub hv := by
    rw [hcent_eq, inf_eq_right.mpr hRM]
  have hker₀ : α.ker = (eSub hv).subgroupOf (eNorm hv) := ker_eNHom hv (le_refl (eNorm hv)) hC
  exact ⟨hsurj, hker₀⟩

theorem refData_normalizer16 (hcardN : Nat.card (eNorm hv) = 322560)
    (hcent : Subgroup.centralizer (eSub hv : Set G) ≤ eSub hv) :
    CFSG.Quasithin.KGC31.RefData (eSub hv) (eNorm hv) where
  cent := hcent
  comm := fun a ha b hb => eSub_comm hv a b ha hb
  le := fun x hx => Subgroup.mem_normalizer_iff.mpr fun y => by
    constructor
    · intro hy
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx)
    · intro hy
      have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy) hx
      simpa [mul_assoc] using h1
  norm := le_rfl
  perf := fun _ hK _ => hK
  simple := by
    haveI : IsSimpleGroup ↥(StatedSL 4 (ZMod 2)) := E16.isSimpleGroup_statedSL4
    obtain ⟨hsurj, hker⟩ := normalizer16_facts hv hcardN hcent
    exact simple_of_surj _ hsurj hker

theorem KConfig.conclK_of_e16 {L V' MK : Subgroup G} (h : KConfig G L V' MK)
    (hcardN : Nat.card (eNorm hv) = 322560)
    (hcent : Subgroup.centralizer (eSub hv : Set G) ≤ eSub hv) (hVV : eSub hv ≤ V') :
    ConclK G L V' MK := by
  obtain ⟨rfl, rfl⟩ := h.eq_of_refData_of_le (refData_normalizer16 hv hcardN hcent) hVV
  exact conclK_of_normalizer16 hv hcardN hcent MK

end CFSG.SectionRank.QTK.Insp443

end
