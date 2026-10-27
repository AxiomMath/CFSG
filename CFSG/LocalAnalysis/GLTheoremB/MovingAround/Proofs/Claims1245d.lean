module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1245c
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.FinalV2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1245d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

@[expose] def Input14_17L : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → y ^ 3 = 1 →
    ∀ J : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) J →
      Subgroup.center (barOf 3 J) = ⊥ → IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
      IsChevSimple 2 (barOf 3 L ⧸ Subgroup.center (barOf 3 L))

@[expose] def Input14_17SL : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → y ^ 3 = 1 →
    ∀ J : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) J →
      Subgroup.center (barOf 3 J) ≠ ⊥ → IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
      IsChevSimple 2 (barOf 3 L ⧸ Subgroup.center (barOf 3 L))

theorem isChevSimple_of_isChevTwo {Q : Type} [Group Q]
    (h : CFSG.HardMathSupport.Solomon.Coordinator.IsChevTwo Q) : IsChevSimple 2 Q := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  refine CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨d, hv⟩ ?_ e
  cases d <;> simp_all [CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex]

theorem isChevSimple_of_isChevOfChar_two {Q : Type} [Group Q]
    (h : CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar 2 Q) : IsChevSimple 2 Q := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  rcases CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.isChevIndexOfChar_two_cases d hd with
    hch | ⟨r, rfl, hr⟩ | ⟨r, rfl, hr⟩
  · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨d, hv⟩
      (CFSG.LieType.ChevTwo.characteristic_two_of_isChevIndexTwo hch) e
  · exfalso
    exact ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
      ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inl ⟨rfl, Or.inr (Or.inr hr)⟩))
  · exact Or.inr ⟨TauCeti.CFSGIndex.lie ⟨_, hv⟩, ⟨hr, rfl⟩, ⟨e⟩⟩

theorem isKGroup_of_le {G : Type} [Group G] {X L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (h : L ≤ X) :
    CFSG.Open.IsKGroup ↥L :=
  CFSG.KCore.KGroupNonab.of_injective isoInvariant_isCatalogGroup hX (Subgroup.inclusion h)
    (Subgroup.inclusion_injective h)

theorem chevSimple_of_reduction {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hL : GLAPComponent 3 X L) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hy3 : y ^ 3 = 1) {J : Subgroup G}
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (H : ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
      CFSG.Open.IsKGroup ↥K → GLAPPrimeCore 3 ↥K = ⊥ → ∀ b : Y, b ∈ Subgroup.normalizer (K : Set Y) →
      b ^ 3 ∈ Subgroup.centralizer (K : Set Y) → ∀ J' : Subgroup Y,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) J' →
      (barOf 3 J ≃* (↥J' ⧸ GLAPPrimeCore 3 ↥J')) → IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)) :
    IsChevSimple 2 (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) := by
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hLN : L ≤ L ⊔ Subgroup.zpowers y := le_sup_left
  have hyN : y ∈ L ⊔ Subgroup.zpowers y :=
    (le_sup_right : Subgroup.zpowers y ≤ L ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
  have hNnorm : L ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hyL)
  have hsn : IsSubnormal L (L ⊔ Subgroup.zpowers y) :=
    IsSubnormal.step hLN ((Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 hNnorm)
      (IsSubnormal.refl _)
  let e : barOf 3 L ≃* ↥(barX 3 (L ⊔ Subgroup.zpowers y) L) := quotEquivBarX hp3 hLN hsn
  have hKq : CFSG.Open.IsQuasisimple ↥(barX 3 (L ⊔ Subgroup.zpowers y) L) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e (l119_isQuasisimple_barOf hp3 hL)
  have hKK : CFSG.Open.IsKGroup ↥(barX 3 (L ⊔ Subgroup.zpowers y) L) :=
    CFSG.KCore.KGroupNonab.of_mulEquiv isoInvariant_isCatalogGroup
      (CFSG.KCore.KGroupNonab.quotient isoInvariant_isCatalogGroup (isKGroup_of_le hX hL.1) _) e.symm
  have hKO : GLAPPrimeCore 3 ↥(barX 3 (L ⊔ Subgroup.zpowers y) L) = ⊥ := by
    rw [← glaPPrimeCore_map_iso 3 e, glaPPrimeCore_quotient_eq_bot hp3, Subgroup.map_bot]
  have hbK : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(L ⊔ Subgroup.zpowers y)) ⟨y, hyN⟩ ∈
      Subgroup.normalizer (barX 3 (L ⊔ Subgroup.zpowers y) L : Set _) :=
    barX_le_normalizer hNnorm (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hyN))
  have hb3 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(L ⊔ Subgroup.zpowers y)) ⟨y, hyN⟩ ^ 3 ∈
      Subgroup.centralizer (barX 3 (L ⊔ Subgroup.zpowers y) L : Set _) := by
    have h1 : (⟨y, hyN⟩ : ↥(L ⊔ Subgroup.zpowers y)) ^ 3 = 1 := Subtype.ext (by simp [hy3])
    rw [← map_pow, h1, map_one]
    exact Subgroup.one_mem _
  have hJ' := Prop126b.glaPComponent_barX_inf_centralizer hp3 hyN hLN hyL (l119_isPGroup_zpowers hy3) hJ
  have hJN : J ≤ L ⊔ Subgroup.zpowers y := hJ.1.trans (inf_le_left.trans hLN)
  have hK := H _ _ hKq hKK hKO _ hbK hb3 _ hJ' (Prop126b.barOfBarX hp3 hJN)
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hK

theorem input14_17L_of_narrow (F : CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input25_2FactsNarrow) :
    Input14_17L := by
  intro G _ _ X L hX hL y hyL hy3 J hJ hZ hJt
  refine chevSimple_of_reduction hX hL hyL hy3 hJ ?_
  intro Y _ _ K hKq hKK hKO b hbK hb3 J' hJ' eJ
  have h1 : IsLThreeFour (barOf 3 J) :=
    Lemma1245.isLThreeFour_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hJt
  exact isChevSimple_of_isChevTwo
    (F.chevTwo Y K hKq hKK hKO b hbK hb3 J' hJ' (Lemma1245.isLThreeFour_congr eJ h1))

theorem input14_17SL_of_facts (F3 : CFSG.HardMathSupport.Solomon.Coordinator.Input25_3FactsNo38)
    (hC : CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover) : Input14_17SL := by
  intro G _ _ X L hX hL y hyL hy3 J hJ hZ hJt
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hJq : CFSG.Open.IsQuasisimple (barOf 3 J) := l119_isQuasisimple_barOf hp3 hJ
  have hpc := CFSG.HardMathSupport.Solomon.Coordinator.i271h_pCore_three_eq_center hJq
    (glaPPrimeCore_quotient_eq_bot hp3)
  rcases hC (barOf 3 J) hJq
      (Lemma1245.isLThreeFour_congr (QuotientGroup.quotientMulEquivOfEq hpc.symm) hJt) with hL34 | hSL
  · exfalso
    obtain ⟨hs, a, c, hac⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour hL34
    haveI := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (barOf 3 J)) with h | h
    · exact hZ h
    · exact hac ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top c)) a)
  · refine chevSimple_of_reduction hX hL hyL hy3 hJ ?_
    intro Y _ _ K hKq hKK _ b hbK hb3 J' hJ' eJ
    obtain ⟨E, hE, hEfin, hcard, ⟨f⟩⟩ := hSL
    have hchar : CharP E 2 := by
      haveI : Fintype E := Fintype.ofFinite E
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    exact isChevSimple_of_isChevOfChar_two (F3.chev Y K hKq hKK b hbK hb3 J' hJ' 2 Nat.prime_two
      (Or.inl ⟨E, hE, hEfin, hchar, by rw [hcard], ⟨eJ.symm.trans f⟩⟩))

theorem input14_17_of_narrow_SL
    (F : CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input25_2FactsNarrow) (hSL : Input14_17SL) :
    Claims1245c.Input14_17 := by
  intro G _ _ X L hX hL y hyL hy3 J hJ hJt
  by_cases hZ : Subgroup.center (barOf 3 J) = ⊥
  · exact input14_17L_of_narrow F X L hX hL y hyL hy3 J hJ hZ hJt
  · exact hSL X L hX hL y hyL hy3 J hJ hZ hJt

section Certified

set_option linter.unusedSectionVars false

theorem input14_17_of_SL
    (hSL : Input14_17SL) : Claims1245c.Input14_17 :=
  input14_17_of_narrow_SL CFSG.HardMathSupport.Solomon.Coordinator.YS08.lThreeFourComponentFacts_holds.input25_2
    hSL

theorem input14_17SL_holds
    : Input14_17SL :=
  input14_17SL_of_facts CFSG.HardMathSupport.Solomon.Coordinator.YS08.lThreeFourComponentFacts_holds.input25_3
    CFSG.HardMathSupport.Solomon.Proving.inputL34Cover_holds

theorem input14_17_holds
    : Claims1245c.Input14_17 :=
  input14_17_of_SL input14_17SL_holds

end Certified

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1245d

end
