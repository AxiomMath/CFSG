module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKFixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RCenterTrivial
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34ProperFixedSimple

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace HeK

theorem properFixed_data_of_pump {G : Type} [Group G]
    [Finite G]
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} {M T : Subgroup G}
    (ha : orderOf a = 2) (hbtop : centralizer ({b} : Set G) ≠ ⊤)
    (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hMa : conjugate M a = M) (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index)
    (htype : IsL34Type (T ⧸ Open.fusionZStar T)) {z₁ z₂ : G}
    (hz₁ : z₁ ∈ (Open.fusionZStar T).map T.subtype)
    (hz₂ : z₂ ∈ (Open.fusionZStar T).map T.subtype) (hs₁ : z₁ * z₁ = 1) (hs₂ : z₂ * z₂ = 1)
    (hn₁ : z₁ ≠ 1) (hn₂ : z₂ ≠ 1) (hne : z₁ ≠ z₂) (hc : z₁ * z₂ = z₂ * z₁) :
    IsQuasisimple (M ⧸ pPrimeCore 2 M) ∧
      Blueprint.Catalog ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) ∧
      ∃ σ : MulAut (M ⧸ pPrimeCore 2 M), (∀ y, σ (σ y) = y) ∧
        ∃ P : Subgroup (M ⧸ pPrimeCore 2 M), P ≤ fixedSubgroup σ ∧
          IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) ∧ P ≠ ⊤ ∧
          IsL34Type (P ⧸ Open.fusionZStar P) ∧ 2 ≤ pRank 2 ↥(Open.fusionZStar P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haN : a ∈ normalizer (M : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [← UnbalancedLayer.mem_conjugate_iff, hMa]
  set c : MulAut M := M.normalizerMonoidHom ⟨a, haN⟩ with hcdef
  have hcapp : ∀ x : M, ((c x : M) : G) = a * x * a⁻¹ := fun x => rfl
  have hc2 : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc a * (a * (x : G) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [haa]; group
  have hfixC : fixedSubgroup c = (M ⊓ centralizer ({a} : Set G)).subgroupOf M := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      refine ⟨x.2, ?_⟩
      calc (x : G) * a = a * x * a⁻¹ * a := by rw [h1]
        _ = a * x := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [hcapp]
      calc a * (x : G) * a⁻¹ = x * a * a⁻¹ := by rw [hx]
        _ = x := by group
  set T' := T.subgroupOf M with hT'def
  have hTM' : T ≤ M := hTM.trans inf_le_left
  have hT'C : T' ≤ fixedSubgroup c := by
    rw [hfixC]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact hTM hx
  have hT'p : IsPComponent 2 (T'.subgroupOf (fixedSubgroup c)) := by
    rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTp
  let eT : T ≃* T' := (subgroupOfEquivOfLe hTM').symm
  have hlt' : (pPrimeCore 2 T').index < (pPrimeCore 2 M).index := by
    rw [index_eq_card, index_eq_card,
      ← UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr eT, ← index_eq_card,
      ← index_eq_card]
    exact hlt
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMb).1 hMp).2.2
  obtain ⟨σ, P, hσ, hPF, hP, hPne, f, hf, hfk, -⟩ :=
    exists_quasisimple_fixed_component c hc2 hT'C hT'p hlt'
  set F : T →* P := f.comp eT.toMonoidHom with hFdef
  have hF : Function.Surjective F := hf.comp eT.surjective
  have hFk : ¬ 2 ∣ Nat.card F.ker := by
    let g : F.ker →* f.ker := (eT.toMonoidHom.comp F.ker.subtype).codRestrict f.ker fun k => k.2
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : f.ker => (x : T')) h
      exact Subtype.ext (eT.injective h')
    exact fun h2 => hfk (h2.trans (Subgroup.card_dvd_of_injective g hg))
  obtain ⟨eTP⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective F hF hFk
  have htypeP : IsL34Type (P ⧸ Open.fusionZStar P) :=
    LieType.CurtisTits.lieModel_of_mulEquiv eTP htype
  have hcomap := GSThmB.OddQuot.comap_fusionZStar_of_surjective F hF hFk
  obtain ⟨w₁, hw₁, rfl⟩ := hz₁
  obtain ⟨w₂, hw₂, rfl⟩ := hz₂
  have hw₁P : F w₁ ∈ Open.fusionZStar P := by
    rw [← hcomap] at hw₁
    exact hw₁
  have hw₂P : F w₂ ∈ Open.fusionZStar P := by
    rw [← hcomap] at hw₂
    exact hw₂
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pair_map_of_odd_ker F hFk (z₁ := w₁) (z₂ := w₂)
    (Subtype.ext hs₁) (Subtype.ext hs₂) (fun h => hn₁ (congrArg Subtype.val h))
    (fun h => hn₂ (congrArg Subtype.val h)) (fun h => hne (congrArg Subtype.val h))
    (Subtype.ext hc)
  have hrank : 2 ≤ pRank 2 ↥(Open.fusionZStar P) :=
    HeEnd.two_le_pRank_of_pair hw₁P hw₂P h1 h2 h3 h4 h5 h6
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar M
  have hcat : Blueprint.Catalog ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) :=
    SectionRank.catalog_of_mulEquiv eS (catalog_fusionZStar_of_isPComponent hK hbtop hMb hMp)
  exact ⟨hMq, hcat, σ, hσ, P, hPF, hP, hPne, htypeP, hrank⟩

theorem held_of_proper_fixed_l34 (hD : L34ProperFixedCenterTrivial)
    (hH : L34ProperFixedSimpleRank) {G : Type} [Group G] [Finite G]
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} {M T : Subgroup G}
    (ha : orderOf a = 2) (hbtop : centralizer ({b} : Set G) ≠ ⊤)
    (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hMa : conjugate M a = M) (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index)
    (htype : IsL34Type (T ⧸ Open.fusionZStar T)) {z₁ z₂ : G}
    (hz₁ : z₁ ∈ (Open.fusionZStar T).map T.subtype)
    (hz₂ : z₂ ∈ (Open.fusionZStar T).map T.subtype) (hs₁ : z₁ * z₁ = 1) (hs₂ : z₂ * z₂ = 1)
    (hn₁ : z₁ ≠ 1) (hn₂ : z₂ ≠ 1) (hne : z₁ ≠ z₂) (hc : z₁ * z₂ = z₂ * z₁) :
    Nonempty ((M ⧸ pPrimeCore 2 M) ≃* Blueprint.NativeSporadic.He) := by
  obtain ⟨hMq, hcat, σ, hσ, P, hPF, hP, hPne, htypeP, hrank⟩ :=
    properFixed_data_of_pump hK ha hbtop hMb hMp hMa hTM hTp hlt htype hz₁ hz₂ hs₁ hs₂ hn₁ hn₂
      hne hc
  have hZ := hD _ hMq (isPGroup_center_quotient M) hcat σ hσ P hPF hP hPne htypeP hrank
  let e : (M ⧸ pPrimeCore 2 M) ≃* (M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hsimp : IsSimpleGroup (M ⧸ pPrimeCore 2 M) := (MulEquiv.isSimpleGroup_congr e).mpr hMq.2.1
  have hna : ∃ x y : M ⧸ pPrimeCore 2 M, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hMq.2.2
    exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  rcases hH _ hsimp hna (SectionRank.catalog_of_mulEquiv e hcat) σ hσ P hPF hP hPne htypeP with
    hHe | hle
  · exact hHe
  · exact absurd hrank (by omega)

end HeK

end CFSG.ComponentClassification.GrSLit
