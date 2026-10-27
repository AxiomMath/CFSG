module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEnd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace HeK

theorem isPGroup_center_quotient (A : Type*) [Group A] [Finite A] :
    IsPGroup 2 (center (A ⧸ pPrimeCore 2 A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (A ⧸ pPrimeCore 2 A) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  intro x
  obtain ⟨a, m, hm, hn⟩ :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : A ⧸ pPrimeCore 2 A)).ne'
  have hy : (x : A ⧸ pPrimeCore 2 A) ^ 2 ^ a ∈ center (A ⧸ pPrimeCore 2 A) := pow_mem x.2 _
  have hord : orderOf ((x : A ⧸ pPrimeCore 2 A) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hn⟩, hn]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos a)
  have hnorm : (zpowers ((x : A ⧸ pPrimeCore 2 A) ^ 2 ^ a)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnc : n ∈ center (A ⧸ pPrimeCore 2 A) := zpowers_le.mpr hy hn
    rw [mem_center_iff.mp hnc g, mul_inv_cancel_right]
    exact hn
  have hbot := (pPrimeCore_eq_bot_iff.mp hO) _ hnorm
    (by rw [Nat.card_zpowers, hord]; exact Nat.coprime_two_left.mpr hm)
  rw [zpowers_eq_bot] at hbot
  exact ⟨a, Subtype.ext (by rw [Subgroup.coe_pow, hbot, OneMemClass.coe_one])⟩

theorem pair_map_of_odd_ker {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (hker : ¬ 2 ∣ Nat.card f.ker) {z₁ z₂ : X} (hs₁ : z₁ * z₁ = 1) (hs₂ : z₂ * z₂ = 1)
    (hn₁ : z₁ ≠ 1) (hn₂ : z₂ ≠ 1) (hne : z₁ ≠ z₂) (hc : z₁ * z₂ = z₂ * z₁) :
    f z₁ * f z₁ = 1 ∧ f z₂ * f z₂ = 1 ∧ f z₁ ≠ 1 ∧ f z₂ ≠ 1 ∧ f z₁ ≠ f z₂ ∧
      f z₁ * f z₂ = f z₂ * f z₁ := by
  have hinv : ∀ z : X, z * z = 1 → z ≠ 1 → f z ≠ 1 := by
    intro z hz hz1 h
    apply hker
    have hmem : z ∈ f.ker := h
    have h2 : orderOf (⟨z, hmem⟩ : f.ker) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [sq]; exact hz) hz1
    rw [← h2]
    exact orderOf_dvd_natCard _
  refine ⟨by rw [← map_mul, hs₁, map_one], by rw [← map_mul, hs₂, map_one], hinv z₁ hs₁ hn₁,
    hinv z₂ hs₂ hn₂, fun h => ?_, by rw [← map_mul, ← map_mul, hc]⟩
  have h12 : (z₁ * z₂) * (z₁ * z₂) = 1 := by
    calc (z₁ * z₂) * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [hc]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [hs₁, hs₂, one_mul]
  have h12' : z₁ * z₂ ≠ 1 := fun h' => hne (by
    calc z₁ = z₁ * z₂ * z₂ := by rw [mul_assoc, hs₂, mul_one]
      _ = z₂ := by rw [h', one_mul])
  apply hinv _ h12 h12'
  rw [map_mul, h, ← map_mul, hs₂, map_one]

theorem exists_quasisimple_fixed_component {A : Type*} [Group A] [Finite A] (c : MulAut A)
    (hc : ∀ x, c (c x) = x) {T : Subgroup A} (hTC : T ≤ fixedSubgroup c)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup c)))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 A).index) :
    ∃ (σ : MulAut (A ⧸ pPrimeCore 2 A)) (P : Subgroup (A ⧸ pPrimeCore 2 A)),
      (∀ y, σ (σ y) = y) ∧ P ≤ fixedSubgroup σ ∧ IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) ∧
        P ≠ ⊤ ∧ ∃ f : T →* P, Function.Surjective f ∧ ¬ 2 ∣ Nat.card f.ker ∧
          ∀ t : T, (f t : A ⧸ pPrimeCore 2 A) = QuotientGroup.mk' (pPrimeCore 2 A) t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 A with hO
  set π := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOmap : O.map c.toMonoidHom = O :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance c
  have hcO : ∀ n ∈ O, c n ∈ O := fun n hn => hOmap ▸ mem_map_of_mem c.toMonoidHom hn
  set cbar : MulAut (A ⧸ O) := QuotientGroup.congr O O c hOmap with hcbardef
  have hcbar : ∀ x, cbar (π x) = π (c x) := fun x => rfl
  have hcbar2 : ∀ y, cbar (cbar y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [hcbar, hcbar, hc]
  set C := fixedSubgroup c with hCdef
  set Cbar := fixedSubgroup cbar with hCbardef
  have hfix : C.map π = Cbar := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change cbar (π x) = π x
      rw [hcbar]
      exact congrArg π hx
    · intro y hy
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective O y
      have hy' : π (c w) = π w := (hcbar w).symm.trans hy
      have hw : w⁻¹ * c w ∈ O := (QuotientGroup.eq (s := O)).mp hy'.symm
      obtain ⟨n, hn, hfixed⟩ := exists_fixed_mul_of_inv_mul_mem c hc hcO hOodd hw
      refine ⟨w * n, hfixed, ?_⟩
      have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul, h1, mul_one]
  set Tbar := T.map π with hTbardef
  have hTbarC : Tbar ≤ Cbar := by
    rw [← hfix]
    exact map_mono hTC
  let r₁ : C →* Cbar := (π.comp C.subtype).codRestrict Cbar fun x => by
    rw [← hfix]
    exact mem_map_of_mem π x.2
  have hr₁s : Function.Surjective r₁ := by
    rintro ⟨y, hy⟩
    rw [← hfix] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hr₁k : Odd (Nat.card r₁.ker) := by
    let g : r₁.ker →* O := (C.subtype.comp r₁.ker.subtype).codRestrict O fun k => by
      have h1 : r₁ (k : C) = 1 := k.2
      have h2 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : O => (x : A)) h
      exact Subtype.ext (Subtype.ext h')
    exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)
  have hTbar : IsPComponent 2 (Tbar.subgroupOf Cbar) := by
    have h1 := OddKernelTwoComponents.image r₁ hr₁s hr₁k (T.subgroupOf C)
      ((CatalogueBAlternating.pComponent_two_iff _).mp hT)
    have h2 : (T.subgroupOf C).map r₁ = Tbar.subgroupOf Cbar := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · intro hy
        obtain ⟨x, hx, hxy⟩ := mem_subgroupOf.mp hy
        exact ⟨⟨x, hTC hx⟩, hx, Subtype.ext hxy⟩
    rw [← h2]
    exact (CatalogueBAlternating.pComponent_two_iff _).mpr h1
  have hne : Tbar ≠ ⊤ := fun htop =>
    absurd (index_pPrimeCore_le_of_map_eq_top htop) (not_le.mpr hlt)
  let f : T →* Tbar := (π.comp T.subtype).codRestrict Tbar fun t => mem_map_of_mem π t.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨⟨t, ht⟩, rfl⟩
  have hfk : ¬ 2 ∣ Nat.card f.ker := by
    let g : f.ker →* O := (T.subtype.comp f.ker.subtype).codRestrict O fun k => by
      have h1 : f (k : T) = 1 := k.2
      have h2 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : O => (x : A)) h
      exact Subtype.ext (Subtype.ext h')
    exact Nat.not_even_iff_odd.mpr (hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)) ∘
      even_iff_two_dvd.mpr
  exact ⟨cbar, Tbar, hcbar2, hTbarC, hTbar, hne, f, hf, hfk, fun t => rfl⟩

theorem false_of_proper_fixed_l34 (hD : L34RankTwoCentralFixedInput) {G : Type} [Group G]
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
    (hn₁ : z₁ ≠ 1) (hn₂ : z₂ ≠ 1) (hne : z₁ ≠ z₂) (hc : z₁ * z₂ = z₂ * z₁) (hbT : b ∈ T)
    (hb : orderOf b = 2) : False := by
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
  obtain ⟨σ, P, hσ, hPF, hP, hPne, f, hf, hfk, hfπ⟩ :=
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
  have hbM : b ∈ M := hTM' hbT
  set z : M ⧸ pPrimeCore 2 M := QuotientGroup.mk' (pPrimeCore 2 M) ⟨b, hbM⟩ with hz
  have hzP : z ∈ P := by
    have h := (f (eT ⟨b, hbT⟩)).2
    rwa [hfπ] at h
  have hzZ : z ∈ center (M ⧸ pPrimeCore 2 M) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hMb m.2))
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have hodd : Odd (Nat.card (pPrimeCore 2 M)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have h2 : orderOf (⟨⟨b, hbM⟩, h⟩ : pPrimeCore 2 M) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hb]
    have h3 := orderOf_dvd_natCard (⟨⟨b, hbM⟩, h⟩ : pPrimeCore 2 M)
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar M
  have hcat : Blueprint.Catalog ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) :=
    SectionRank.catalog_of_mulEquiv eS (catalog_fusionZStar_of_isPComponent hK hbtop hMb hMp)
  exact hD _ hMq (isPGroup_center_quotient M) hcat σ hσ P hPF hP hPne htypeP hrank z hzP hzZ hz1

end HeK

end CFSG.ComponentClassification.GrSLit
