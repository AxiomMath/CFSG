module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFn
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.KGFactC31E16
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat
public import CFSG.Quasithin.Vol2.Ch4Sec4L446Nat
public import CFSG.Quasithin.Vol2.KGFactC31E8

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix

theorem conclK_of_natural3 {G : Type} [Group G] [Finite G] {v : Fin 3 → G} (hv : EBasis v)
    {L : Subgroup G} (hLN : L ≤ eNorm hv) (hsurj₀ : Function.Surjective (E16.eNHom hv hLN))
    (hpk : CFSG.pCore 2 ↥L = (E16.eNHom hv hLN).ker) (MK : Subgroup G) :
    ConclK G L (eSub hv) MK := by
  unfold ConclK
  let α := E16.eNHom hv hLN
  let eQ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj₀)
  have hpsl : IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) := E8.isPSL_of_equiv3 eQ
  have hcardX : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hpsl
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥L ⧸ CFSG.pCore 2 ↥L) := Or.inr (Or.inl hLM)
  let β : ↥(eSub hv) →* Multiplicative (Fin 3 → ZMod 2) := (ecoords hv).toMonoidHom
  have hβinj : Function.Injective β := (ecoords hv).injective
  have hβsurj : Function.Surjective β := (ecoords hv).surjective
  have hcommV : IsMulCommutative ↥(eSub hv) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm hv x y hx hy
  letI : IsMulCommutative ↥(eSub hv) := hcommV
  have hNs : Function.Surjective (E16.eNHom hv (le_refl (eNorm hv))) := by
    intro s
    obtain ⟨k, hk⟩ := hsurj₀ s
    refine ⟨⟨k, hLN k.2⟩, Subtype.ext (Units.ext ?_)⟩
    rw [← hk]
    rfl
  have hsecN : IsNaturalSection (eNorm hv) (eSub hv) ⊥
      ((Subgroup.centralizer (eSub hv : Set G)).subgroupOf (eNorm hv))
      (StatedSL 3 (ZMod 2)) := by
    refine ⟨le_rfl, E16.eNHom hv le_rfl, hNs, ?_, β, hβsurj, ?_, ?_⟩
    · ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E16.eNHom_eq_one_iff]
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr hβinj
    · intro a u w hw
      rw [E16.eNHom_coe]
      exact ecoords_conj hv a u w hw
  have hsumN := (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsecN
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub hv : Set G)) (eSub hv)) :=
    FFn.isFFModule_autOn_of_sum (n := 2) (k := 1) (by decide) le_rfl (by norm_num) hsumN
  have hbin : BinaryNaturalSL (V := ↥(eSub hv)) (autOn L (eSub hv)) ⊤ ⊥ 3 1 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
    exact T4213N.realizes_of_equiv hLN (FFModel.nat (StatedSL 3 (ZMod 2)))
      (fun _ => trivial) (fun x => Subgroup.mem_bot)
      (fun _ => rfl)
      α hsurj₀
      (fun a ha => by
        have : a ∈ α.ker := ha
        rw [MonoidHom.mem_ker, E16.eNHom_eq_one_iff] at this
        exact this)
      (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
      (fun a w w' hw => by
        show β w' = (FFModel.nat (StatedSL 3 (ZMod 2))).act (α a) (β w)
        apply Multiplicative.toAdd.injective
        show Multiplicative.toAdd (β w') = (((α a : ↥(StatedSL 3 (ZMod 2))) :
          Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (β w)
        rw [E16.eNHom_coe]
        exact ecoords_conj hv ⟨a, hLN a.2⟩ w w' hw)
  have hnat : IsNaturalSumUnder 3 L (eSub hv) := by
    refine ⟨1, fun _ => eSub hv, by norm_num, ?_, ?_, iSupIndep_subsingleton _, ?_⟩
    · intro i
      exact ⟨le_rfl, hLN, ⟨hcommV, hbin⟩⟩
    · intro i j
      exact isXSectionIso₂_of_isLEquiv (φ := MulEquiv.refl _) (fun l hl a a' ha' => ha')
    · rw [iSup_const]
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  · intro _
    exact hnat
  · intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  · rintro ⟨-, hc, -⟩
    rw [F420.center_eq_bot_of_statedPSL hpsl] at hc
    rw [Subgroup.card_bot] at hc
    norm_num at hc
  · intro _ h64
    rw [card_eSub] at h64
    norm_num at h64

end CFSG.SectionRank.QTK.Insp443
