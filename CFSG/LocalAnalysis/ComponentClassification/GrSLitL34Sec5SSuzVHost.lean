module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzFacts
public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.Constrained
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceTypes

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (conjSub swapDiag swapDiag_mem_sup)
open scoped commutatorElement

theorem exists_component_suz_of_twoComponent (hcat : SuzONanNotProperFixedCatalog)
    {H : Type} [Group H] [Finite H] (hK : SectionRank.IsKGroupCat H) {s : H}
    (hs : orderOf s = 2) {Λ : Subgroup H} (hΛs : Λ ≤ centralizer ({s} : Set H))
    (hΛ : IsPComponent 2 (Λ.subgroupOf (centralizer ({s} : Set H))))
    (hΛS : IsSporadic (↥Λ ⧸ Open.fusionZStar ↥Λ) .Suz) :
    ∃ L : Subgroup (H ⧸ pPrimeCore 2 H), IsComponent L ∧
      IsSporadic (↥L ⧸ Subgroup.center ↥L) .Suz ∧
      Nat.card (Subgroup.center ↥L) ≤ 2 ∧
      (L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom = L →
        Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)) = L ∧
          ∀ x ∈ L, QuotientGroup.mk' (pPrimeCore 2 H) s * x =
            x * QuotientGroup.mk' (pPrimeCore 2 H) s) ∧
      (L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom ≠ L →
        Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤
            L ⊔ L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom ∧
          Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊓ L ≤
            (Subgroup.center ↥L).map L.subtype ∧
          Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊓
            L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom ≤
              (Subgroup.center ↥(L.map
                (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom)).map
                (L.map
                  (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom).subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbound : CFSG.ComponentClassification.RankTwoSporadic.Suz.SuzCentralTwoGroupOrderBound :=
    suzCentralTwoGroupOrderBound_holds
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set u := π s with hu
  have hu2 : orderOf u = 2 := GH74.GLS.TwoThin.orderOf_barMk hs
  have huu : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at h
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hOX : pPrimeCore 2 (H ⧸ pPrimeCore 2 H) = ⊥ := GH74.pPrimeCore_quotient_pPrimeCore_eq_bot H 2
  have hΛ2 : TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({s} : Set H))) :=
    (CatalogueBAlternating.pComponent_two_iff _).mp hΛ
  obtain ⟨-, -, L, hL, hcases, -⟩ := GH74.GLS.TwoThin.pumpupY_structure hs hΛs hΛ2
  set Λb := Λ.map π with hΛb
  have hΛbC : Λb ≤ centralizer ({u} : Set (H ⧸ pPrimeCore 2 H)) :=
    (Subgroup.map_mono hΛs).trans (GH74.GLS.TwoThin.map_centralizer_barMk hs).le
  have hΛbp : IsPComponent 2 (Λb.subgroupOf (centralizer ({u} : Set (H ⧸ pPrimeCore 2 H)))) :=
    (CatalogueBAlternating.pComponent_two_iff _).mpr
      (GH74.GLS.TwoThin.isTwoComponent_map_barMk hs hΛs hΛ2)
  have hΛbS : IsSporadic (↥Λb ⧸ Open.fusionZStar ↥Λb) .Suz := by
    set f : ↥Λ →* ↥Λb := π.subgroupMap Λ with hf
    have hfs : Function.Surjective f := π.subgroupMap_surjective Λ
    have hfk : ¬ 2 ∣ Nat.card f.ker := by
      have hle : f.ker.map Λ.subtype ≤ pPrimeCore 2 H := by
        rintro _ ⟨x, hx, rfl⟩
        have h1 : (f x : H ⧸ pPrimeCore 2 H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        rw [← QuotientGroup.ker_mk' (pPrimeCore 2 H)]
        exact h1
      have hdvd : Nat.card f.ker ∣ Nat.card (pPrimeCore 2 H) := by
        rw [← Subgroup.card_map_of_injective Λ.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      intro h2
      have hc := (pPrimeCore_coprime_card (p := 2) (G := H))
      exact absurd (Nat.dvd_gcd (dvd_refl 2) (h2.trans hdvd)) (by rw [hc]; norm_num)
    obtain ⟨e⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective f hfs hfk
    obtain ⟨eΛ⟩ := hΛS
    exact ⟨e.symm.trans eΛ⟩
  have hOL : pPrimeCore 2 ↥L = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hOX hL.2
  have hZL : Open.fusionZStar ↥L = center ↥L := by
    refine CatLeaf.fusionZStar_eq_center_of_quasisimple hL.1 ?_
    rw [hOL]
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    exact bot_ne_top
  have hZ2 : IsPGroup 2 ↥(center ↥L) := Sol78.center_isPGroup_two hOL
  have hLq : CFSG.Assembly.IsQuasisimple ↥L :=
    ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hconj : conjSub u⁻¹ L = L.map (MulAut.conj u).toMonoidHom := by rw [huinv]
  set L2 : Subgroup (H ⧸ pPrimeCore 2 H) := L.map (MulAut.conj u).toMonoidHom with hL2def
  have hconj2 : conjSub u⁻¹ L = L2 := hconj.trans hL2def.symm
  rcases hcases with ⟨hinv, hΛbL'⟩ | ⟨hne, hAB, hdiag⟩
  ·
    have hinv' : L2 = L := hconj2.symm.trans hinv
    by_cases heq : Λb = L
    ·
      have hLSq : IsSporadic (↥L ⧸ center ↥L) .Suz := by
        obtain ⟨eΛb⟩ := hΛbS
        have e2 := Sol78.fusionZStarQuotCongr (MulEquiv.subgroupCongr heq)
        exact ⟨(e2.trans (QuotientGroup.quotientMulEquivOfEq hZL)).symm.trans eΛb⟩
      have hZcard : Nat.card (center ↥L) ≤ 2 := hbound ↥L hLq hZ2 hLSq
      refine ⟨L, hL, hLSq, hZcard, fun _ => ⟨heq, fun x hx => ?_⟩,
        fun hmap => absurd hinv' hmap⟩
      have hxΛb : x ∈ Λb := by rw [heq]; exact hx
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hΛbC hxΛb)).symm
    ·
      exfalso
      have hlt : Λb < L := lt_of_le_of_ne hΛbL' heq
      have huN : u ∈ normalizer (L : Set (H ⧸ pPrimeCore 2 H)) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hL2def.symm.trans hinv')
      set c : MulAut ↥L := L.normalizerMonoidHom ⟨u, huN⟩ with hcdef
      have hcapp : ∀ x : ↥L, ((c x : ↥L) : H ⧸ pPrimeCore 2 H) = u * x * u⁻¹ := fun x => rfl
      have hc : ∀ x, c (c x) = x := by
        intro x
        apply Subtype.ext
        rw [hcapp, hcapp]
        calc u * (u * (x : H ⧸ pPrimeCore 2 H) * u⁻¹) * u⁻¹ =
            (u * u) * x * (u * u)⁻¹ := by group
          _ = x := by rw [huu]; group
      have hfixC : fixedSubgroup c =
          (L ⊓ centralizer ({u} : Set (H ⧸ pPrimeCore 2 H))).subgroupOf L := by
        ext x
        rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
          mem_centralizer_singleton_iff]
        constructor
        · intro hx
          have h1 := congrArg Subtype.val hx
          rw [hcapp] at h1
          refine ⟨x.2, ?_⟩
          calc (x : H ⧸ pPrimeCore 2 H) * u = u * x * u⁻¹ * u := by rw [h1]
            _ = u * x := by group
        · rintro ⟨-, hx⟩
          apply Subtype.ext
          rw [hcapp]
          calc u * (x : H ⧸ pPrimeCore 2 H) * u⁻¹ = x * u * u⁻¹ := by rw [hx]
            _ = x := by group
      set T' := Λb.subgroupOf L with hT'def
      have hT'C : T' ≤ fixedSubgroup c := by
        rw [hfixC]
        intro x hx
        rw [mem_subgroupOf] at hx ⊢
        exact ⟨hΛbL' hx, hΛbC hx⟩
      have hTp' : IsPComponent 2
          (Λb.subgroupOf (L ⊓ centralizer ({u} : Set (H ⧸ pPrimeCore 2 H)))) :=
        Burgoyne.C.isPComponent_subgroupOf_of_le (le_inf hΛbL' hΛbC) inf_le_right hΛbp
      have hT'p : IsPComponent 2 (T'.subgroupOf (fixedSubgroup c)) := by
        rw [hfixC]
        exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := Λb) inf_le_left 2
          Nat.prime_two).mpr hTp'
      have hlt' : (pPrimeCore 2 ↥T').index < (pPrimeCore 2 ↥L).index := by
        rw [hOL, Subgroup.index_bot]
        calc (pPrimeCore 2 ↥T').index ≤ Nat.card ↥T' :=
              Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
          _ = Nat.card ↥Λb := Nat.card_congr (subgroupOfEquivOfLe hΛbL').toEquiv
          _ < Nat.card ↥L := Subgroup.card_lt_of_lt hlt
      have hMq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          ((QuotientGroup.quotientMulEquivOfEq hOL).trans QuotientGroup.quotientBot).symm hL.1
      obtain ⟨σ, P', hσ, hPF, hP, hPne, ⟨e⟩⟩ :=
        exists_simple_fixed_component hMq c hc hT'C hT'p hlt'
      obtain ⟨-, hS, hnab⟩ := hMq
      have hKL : SectionRank.IsKGroupCat ↥L := (hK.quotient (pPrimeCore 2 H)).subgroup L
      have hcatS : Blueprint.Catalog
          ((↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L)) := by
        have := hS
        refine SectionRank.catalog_of_isKGroupCat_of_surjective hKL ⊤
          (((QuotientGroup.mk' _).comp (QuotientGroup.mk' _)).comp (⊤ : Subgroup ↥L).subtype) ?_
        intro y
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
        exact ⟨⟨y, mem_top y⟩, rfl⟩
      have hT'S : IsSporadic (↥T' ⧸ Open.fusionZStar ↥T') .Suz := by
        obtain ⟨eΛb⟩ := hΛbS
        exact ⟨(Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hΛbL').symm).symm.trans eΛb⟩
      obtain ⟨eT'⟩ := hT'S
      have hPS : IsSporadic (↥P' ⧸ Open.fusionZStar ↥P') .Suz := ⟨e.symm.trans eT'⟩
      exact (hcat _ hS hnab hcatS σ hσ P' hPF hP hPne).1 hPS
  ·
    have hcj : conjSub u⁻¹ L = conjugate L u := rfl
    have hconjL2 : conjugate L u = L2 := by rw [← hcj, hconj2]
    have hne' : L ≠ conjugate L u := fun h => hne (by rw [hcj, ← h])
    have hL2 : IsComponent L2 := by
      rw [hL2def]
      exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj u) hL
    have hne2 : L ≠ L2 := by
      intro h
      apply hne
      rw [hconj2, h]
    have hcomm : ⁅L, L2⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hL hL2 with heq | hbot
      · exact absurd heq hne2
      · exact hbot
    have hTC : Λb ≤ (L ⊔ conjugate L u) ⊓
        centralizer ({u} : Set (H ⧸ pPrimeCore 2 H)) := by
      refine le_inf ?_ hΛbC
      refine hdiag.trans ?_
      rintro _ ⟨x, rfl⟩
      exact hcj ▸ swapDiag_mem_sup hAB x
    have hT := Burgoyne.C.isPComponent_subgroupOf_of_le hTC inf_le_right hΛbp
    obtain ⟨e⟩ := CatLeaf.swap_case_type hu2 L (CatLeafProof.isPComponent_two_of_isComponent hL)
      hne' Λb hTC hT
    have hLSq : IsSporadic (↥L ⧸ center ↥L) .Suz := by
      obtain ⟨eΛb⟩ := hΛbS
      exact ⟨(e.trans (QuotientGroup.quotientMulEquivOfEq hZL)).symm.trans eΛb⟩
    have hZcard : Nat.card (center ↥L) ≤ 2 := hbound ↥L hLq hZ2 hLSq
    have hcentL : L ≤ Subgroup.centralizer (L2 : Set (H ⧸ pPrimeCore 2 H)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hlink : Λb ≤ L ⊔ L2 := by
      have h := hTC.trans inf_le_left
      rwa [hconjL2] at h
    have hΛbLcent : Λb ⊓ L ≤ (Subgroup.center ↥L).map L.subtype := by
      rintro x ⟨hxΛb, hxL⟩
      have hxcomm : x * u = u * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hΛbC hxΛb)
      have hxu : MulAut.conj u x = x := by
        rw [MulAut.conj_apply]
        calc u * x * u⁻¹ = x * u * u⁻¹ := by rw [← hxcomm]
          _ = x := by group
      have hxL2 : x ∈ L2 := by
        rw [hL2def]
        exact Subgroup.mem_map.mpr ⟨x, hxL, hxu⟩
      have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hcentL y.2) x hxL2).symm
      exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hxZ, rfl⟩
    have hΛbL2cent : Λb ⊓ L2 ≤ (Subgroup.center ↥L2).map L2.subtype := by
      rintro x ⟨hxΛb, hxL2⟩
      have hxcomm : x * u = u * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hΛbC hxΛb)
      have hxL : x ∈ L := by
        obtain ⟨y, hyL, hyx⟩ := Subgroup.mem_map.mp (hL2def ▸ hxL2)
        have hyx' : u * y * u⁻¹ = x := by
          simpa [MulAut.conj_apply] using hyx
        have hxeq : u⁻¹ * x * u = x := by
          calc u⁻¹ * x * u = u⁻¹ * (x * u) := by group
            _ = u⁻¹ * (u * x) := by rw [hxcomm]
            _ = x := by group
        have hyx2 : y = x := by
          calc y = u⁻¹ * (u * y * u⁻¹) * u := by group
            _ = u⁻¹ * x * u := by rw [hyx']
            _ = x := hxeq
        rw [← hyx2]
        exact hyL
      have hxZ : (⟨x, hxL2⟩ : ↥L2) ∈ Subgroup.center ↥L2 := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp (hcentL hxL) y y.2
      exact Subgroup.mem_map.mpr ⟨⟨x, hxL2⟩, hxZ, rfl⟩
    refine ⟨L, hL, hLSq, hZcard, fun hmap => absurd hmap.symm hne2,
      fun _ => ⟨hlink, hΛbLcent, hΛbL2cent⟩⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
