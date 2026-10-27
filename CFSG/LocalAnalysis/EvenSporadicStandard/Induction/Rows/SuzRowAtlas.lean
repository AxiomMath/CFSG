module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.PinnedPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONStage3
public import CFSG.RankThree.GroupTheory.SteinbergBYCentralCoverRank
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.TwoPart
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SuzCenterInputs
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.SmallActionData

public section

set_option linter.unusedSectionVars false

open scoped commutatorElement

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore Cover


theorem suz_card_centralizer {S : Type*} [Group S] (f : S ≃* suzM) {a : S} (ha : orderOf a = 2)
    (hdvd : 20160 ∣ Nat.card (centralizer ({a} : Set S))) :
    Nat.card (centralizer ({a} : Set S)) = 161280 := by
  obtain ⟨c, hc, h0⟩ := suz_conj_zero f a ha hdvd
  set a' : Equiv.Perm (Fin 1782) := ((f a : suzM) : Equiv.Perm (Fin 1782)) with ha'
  have hinj : Function.Injective (suzM.subtype.comp f.toMonoidHom) :=
    suzM.subtype_injective.comp f.injective
  have g1 : centralizer ({a} : Set S) ≃*
      (suzM ⊓ Subgroup.centralizer {a'} : Subgroup (Equiv.Perm (Fin 1782))) :=
    ((centralizer ({a} : Set S)).equivMapOfInjective _ hinj).trans
      (MulEquiv.subgroupCongr (centralizer_map_equiv f a))
  have hmap := map_conj_inf_centralizer (Γ := suzM) (c := c) (suzM_conj_iff hc) (suzInv 0)
  rw [h0] at hmap
  have e2 := (Subgroup.equivMapOfInjective (suzM ⊓ Subgroup.centralizer {suzInv 0})
    (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap)
  have e3 : invE 0 = suzM ⊓ Subgroup.centralizer {suzInv 0} := by
    rw [invE_eq_centM (by norm_num : 0 < 4), centM, inf_comm]
  have e4 := (g1.trans e2.symm).trans (MulEquiv.subgroupCongr e3.symm)
  rw [Nat.card_congr e4.toEquiv, card_invE (by norm_num : 0 < 4)]
  simp [invInnerOrders]

theorem suz_rowExists (H : Type) [Group H] (L : Subgroup H) (hcov : OddCover .Suz L) :
    ∃ (K : Subgroup H) (u : H), SuzQ H L K u := by
  obtain ⟨e⟩ := suz_equiv_of_isSporadic hcov.2.2
  obtain ⟨ut, Kt, hut, hut1, hKtu, hKt, hcard, -⟩ := suz_pinned_pair
  obtain ⟨K, u, hu, hu2, hKL, hKu, hKperf, hmap⟩ :=
    exists_pair_of_pinned_pair hcov.2.1 e hut hut1 hKtu hKt
  refine ⟨K, u, hu, hu2, hKL, hKu, hKperf, ?_⟩
  rw [hmap, Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem suz_rowFit (H : Type) [Group H] (L K : Subgroup H) (hcov : OddCover .Suz L) (hKL : K ≤ L)
    (hKq : CFSG.IsQuasisimple ↥K) (hK : IsOddCentralExt ↥suzD (↥K ⧸ CFSG.oddCore ↥K))
    (hstd : SolStd (K.subgroupOf L)) : ∃ u : H, SuzQ H L K u := by
  have : Finite ↥L := hcov.finite (by decide : TauCeti.SporadicName.Suz ≠ .M)
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hKL)
  obtain ⟨t, ht2, hcomp⟩ := hstd.exists_involution
  have hKt : ∀ k ∈ K, k * (t : H) = (t : H) * k := fun k hk => by
    have h1 : (⟨k, hKL hk⟩ : ↥L) ∈ centralizer ({t} : Set ↥L) := hcomp.1 (mem_subgroupOf.2 hk)
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 h1)
  have ht2' : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe]; exact ht2
  have hqt : orderOf (q ↥L ⟨(t : H), t.2⟩) = 2 := hcov.orderOf_q_involution t.2 ht2'
  have hle : (K.subgroupOf L).map (q ↥L) ≤ centralizer ({q ↥L ⟨(t : H), t.2⟩} : Set _) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKt k (Subgroup.mem_subgroupOf.1 hk))
  have hdvd := Subgroup.card_dvd_of_le hle
  obtain ⟨hKq', π, hπs, hπc, hπo⟩ := hK
  have hqcard : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 20160 * Nat.card π.ker := by
    rw [← card_suzD, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  obtain ⟨r, hr, hcard⟩ := exists_odd_card_map_q hKL hcov.2.1
  have h20160 : 20160 ∣ Nat.card (centralizer ({q ↥L ⟨(t : H), t.2⟩} : Set _)) := by
    refine Dvd.dvd.trans ?_ hdvd
    rw [hcard, hqcard, mul_assoc]
    exact dvd_mul_right _ _
  obtain ⟨f⟩ := suz_equiv_of_isSporadic hcov.2.2
  rw [suz_card_centralizer f hqt h20160] at hdvd
  have hcard' : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 20160 :=
    card_map_q_eq hKL hcov.2.1 (a := 3) (by norm_num) hπo hqcard (by simpa using hdvd)
  exact ⟨(t : H), t.2, ht2', hKL, hKt, hKq.1, hcard'⟩

theorem three_le_pRank_suzD : 3 ≤ CFSG.pRank 2 ↥suzD := by
  obtain ⟨K, hKM, hKc, hKp, hKcard, hKrank⟩ := suz_pinned_data
  have hperf : Group.IsPerfect ↥K := isPerfect_iff.mpr hKp
  have ht0 : suzInv 0 ∈ suzM := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ht0M, -⟩ := suz_row_facts
    exact ht0M
  have hP : SuzPair (Equiv.Perm (Fin 1782)) suzM K (suzInv 0) :=
    ⟨ht0, orderOf_eq_two_of_mul_self (suzInv_sq (by norm_num))
      (suzInv_ne_one (by norm_num)), hKM, hKc, hperf, hKcard⟩
  obtain ⟨e⟩ := suz_K_equiv hP suzM.subtype suzM.subtype_injective (fun x => x.2) rfl
  rw [← pRank_two_eq_of_mulEquiv' e]
  exact hKrank

theorem suz_pRank_K (X : Type) [Group X] (hX : IsOddCentralExt ↥suzD X) : 3 ≤ CFSG.pRank 2 X :=
  three_le_pRank_of_oddCentralExt three_le_pRank_suzD hX

theorem suz_pRank_L (X : Type) [Group X] (hX : IsLS [.Suz] X) : 3 ≤ CFSG.pRank 2 X := by
  refine three_le_pRank_of_isLS suz_pinned.1 (fun Y _ h => ?_) hX
  obtain ⟨f⟩ := suz_equiv_of_isSporadic h
  obtain ⟨ut, Kt, -, -, -, -, -, hrank⟩ := suz_pinned_pair
  rw [pRank_two_eq_of_mulEquiv' f]
  exact hrank.trans (CFSG.RankThree.GroupTheory.SteinbergBY.pRank_subgroup_le_pRank
    (by norm_num) Kt)

theorem suz_involutionPerfect : SuzInvolutionPerfect := by
  intro Y _ hY K u hQ
  obtain ⟨f⟩ := suz_equiv_of_isSporadic hY
  obtain ⟨hu, hu2, hKY, hKu, hKperf, hKcard⟩ := hQ
  have hdvd : 20160 ∣ Nat.card (centralizer ({u} : Set Y)) := by
    have hle : K ≤ centralizer ({u} : Set Y) := fun k hk =>
      mem_centralizer_singleton_iff.2 (hKu k hk)
    have := Subgroup.card_dvd_of_le hle
    rwa [hKcard] at this
  obtain ⟨Ψ, hΨ, hΨM, hΨR, hΨu⟩ := suz_exists_model_aux f u hu2 hdvd
  obtain ⟨e, x, heM, hxM, hec, hxc, hex⟩ := suz_commutator_data
  obtain ⟨e', he'⟩ := hΨR e heM
  obtain ⟨x', hx'⟩ := hΨR x hxM
  have hmem : ∀ y : Y, Ψ y * suzInv 0 = suzInv 0 * Ψ y → y ∈ centralizer ({u} : Set Y) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    apply hΨ
    rw [map_mul, map_mul, hΨu]
    exact hy
  have he'c : e' ∈ centralizer ({u} : Set Y) := hmem e' (by rw [he']; exact hec)
  have hx'c : x' ∈ centralizer ({u} : Set Y) := hmem x' (by rw [hx']; exact hxc)
  have hu' : u = ⁅e', x'⁆ := by
    apply hΨ
    simp only [commutatorElement_def, map_mul, map_inv, he', hx']
    rw [hex, hΨu]
  have := Subgroup.commutator_mem_commutator he'c hx'c
  rwa [← hu'] at this

theorem suz_rowAtlasFacts : RowAtlasFacts [.Suz] (fun _ => SuzQ) IsKSuz where
  pRank_K X _ hX := suz_pRank_K X hX
  pRank_L X _ hX := suz_pRank_L X hX
  rowExists s hs H _ _ L hcov := by
    rcases List.mem_singleton.1 hs with rfl
    exact suz_rowExists H L hcov
  rowFit s hs H _ _ L K hcov hKL hKq hK hstd _ := by
    rcases List.mem_singleton.1 hs with rfl
    exact suz_rowFit H L K hcov hKL hKq hK hstd

def stage3Row_suz_proved (haut : SuzAutFix) (hfix : SuzFixedNotLam)
    (h25 : Finkelstein77.Asc76Lemma25) : Stage3Row [.Suz] (fun _ => SuzQ) :=
  stage3Row_suz suz_rowAtlasFacts haut suz_involutionPerfect hfix h25

end CFSG.EvenSporadicStandard.Induction
