module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerCorrespondenceTransfer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBComponentRecovery

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_normalizer_subgroupOf_of_mem {M C : Subgroup G} {g : C}
    (hg : (g : G) ∈ normalizer (M : Set G)) : g ∈ normalizer (M.subgroupOf C : Set C) := by
  rw [mem_normalizer_iff]
  intro y
  exact mem_normalizer_iff.mp hg y

theorem map_pPrimeCore_centralizer_of_mulAut (e : MulAut G) (x : G) :
    ((pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype).map
        e.toMonoidHom =
      (pPrimeCore 2 (centralizer ({e x} : Set G))).map (centralizer ({e x} : Set G)).subtype := by
  have hC : (centralizer ({x} : Set G)).map e.toMonoidHom = centralizer ({e x} : Set G) := by
    ext z
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hz
      have h1 := congrArg e hz
      rwa [map_mul, map_mul, e.apply_symm_apply] at h1
    · intro hz
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hz]
  let e' : centralizer ({x} : Set G) ≃* centralizer ({e x} : Set G) :=
    ((centralizer ({x} : Set G)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hC)
  have hcomm : e.toMonoidHom.comp (centralizer ({x} : Set G)).subtype =
      (centralizer ({e x} : Set G)).subtype.comp e'.toMonoidHom := by
    ext c
    rfl
  rw [map_map, hcomm, ← map_map, pPrimeCore_map_iso 2 e']

theorem gsUnbalancingTriple_conj {a x h : G} {J : Subgroup G} (hU : GSUnbalancingTriple a x J)
    (hha : h ∈ centralizer ({a} : Set G)) (hhJ : h ∈ normalizer (J : Set G)) :
    GSUnbalancingTriple a (h⁻¹ * x * h) J := by
  obtain ⟨ha, hx, hax, hJa, hJ, hJx, hJF⟩ := gsUnbalancingTriple_iff.mp hU
  set f := (MulAut.conj h⁻¹).toMonoidHom with hf
  have hfx : f x = h⁻¹ * x * h := by
    rw [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hfinj : Function.Injective f := (MulAut.conj h⁻¹).injective
  have hJf : J.map f = J := conjugate_eq_of_mem_normalizer hhJ
  have hCaf : (centralizer ({a} : Set G)).map f = centralizer ({a} : Set G) :=
    conjugate_eq_of_mem_normalizer (le_normalizer hha)
  have hOf : ((pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype).map f =
      (pPrimeCore 2 (centralizer ({h⁻¹ * x * h} : Set G))).map
        (centralizer ({h⁻¹ * x * h} : Set G)).subtype := by
    rw [← hfx]
    exact map_pPrimeCore_centralizer_of_mulAut (MulAut.conj h⁻¹) x
  have hah : h⁻¹ * a * h = a := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hha, inv_mul_cancel_left]
  refine gsUnbalancingTriple_iff.mpr ⟨ha, ?_, ?_, hJa, hJ, ?_, ?_⟩
  · rw [← hfx, hf, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hx]
  · calc a * (h⁻¹ * x * h) = (h⁻¹ * a * h) * (h⁻¹ * x * h) := by rw [hah]
      _ = h⁻¹ * (a * x) * h := by group
      _ = h⁻¹ * (x * a) * h := by rw [hax]
      _ = (h⁻¹ * x * h) * (h⁻¹ * a * h) := by group
      _ = (h⁻¹ * x * h) * a := by rw [hah]
  · have h1 := congrArg (Subgroup.map f) hJx
    rw [map_commutator, hJf, MonoidHom.map_zpowers, hfx] at h1
    exact h1
  · have h1 := congrArg (Subgroup.map f) hJF
    rw [map_commutator, hJf, Subgroup.map_inf _ _ _ hfinj, hOf, hCaf] at h1
    exact h1

variable [Finite G]

theorem exists_conjugate_le_of_sylow {H S E : Subgroup G}
    (hS : ∃ P : Sylow 2 H, (P : Subgroup H) = S.subgroupOf H) (hEH : E ≤ H)
    (hE : IsPGroup 2 E) : ∃ h ∈ H, conjugate E h ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hS
  have hE' : IsPGroup 2 (E.subgroupOf H) := hE.comap_subtype
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P₀ Q
  refine ⟨g, g.2, fun y hy => ?_⟩
  rw [mem_conjugate_iff] at hy
  have h1 : (⟨g * y * (g : G)⁻¹, hEH hy⟩ : H) ∈ (Q : Subgroup H) :=
    hQ (show (⟨g * y * (g : G)⁻¹, hEH hy⟩ : H) ∈ E.subgroupOf H from hy)
  rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.inv_def, MulAut.conj_symm_apply, hP₀, mem_subgroupOf] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  rwa [show (g : G)⁻¹ * (g * y * (g : G)⁻¹) * g = y by group] at h1

theorem restriction_quotient_mulEquiv {T X : Subgroup G} (hTX : T ≤ X)
    (hsup : T ⊔ (pPrimeCore 2 X).map X.subtype = X) :
    (pPrimeCore 2 T).map T.subtype = T ⊓ (pPrimeCore 2 X).map X.subtype ∧
      ∃ e : T ⧸ pPrimeCore 2 T ≃* X ⧸ pPrimeCore 2 X,
        ∀ (t : T) (ht : (t : G) ∈ X), e t = ((⟨(t : G), ht⟩ : X) : X ⧸ pPrimeCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : T.subgroupOf X ⊔ pPrimeCore 2 X = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hTX, ← MonoidHom.range_eq_map, range_subtype]
    exact hsup
  have hTmap : (T.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 X)) = ⊤ := by
    have h := congrArg (map (QuotientGroup.mk' (pPrimeCore 2 X))) hT'
    have hbot : (pPrimeCore 2 X).map (QuotientGroup.mk' (pPrimeCore 2 X)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [Subgroup.map_sup, hbot, sup_bot_eq, ← MonoidHom.range_eq_map,
      QuotientGroup.range_mk'] at h
  let φ : T →* X ⧸ pPrimeCore 2 X := (QuotientGroup.mk' (pPrimeCore 2 X)).comp (inclusion hTX)
  have hφ : ∀ t : T, φ t = ((inclusion hTX t : X) : X ⧸ pPrimeCore 2 X) := fun t => rfl
  have hsurj : Function.Surjective φ := by
    intro q
    have hq : q ∈ (T.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
      rw [hTmap]
      exact mem_top q
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hq
    exact ⟨⟨y, hy⟩, rfl⟩
  have hkerφ : φ.ker = (pPrimeCore 2 X).comap (inclusion hTX) := by
    ext t
    rw [MonoidHom.mem_ker, hφ, QuotientGroup.eq_one_iff, mem_comap]
  have hker : pPrimeCore 2 T = φ.ker := by
    apply le_antisymm
    · have hnorm : ((pPrimeCore 2 T).map φ).Normal :=
        (pPrimeCore_normal (p := 2) (G := T)).map φ hsurj
      have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 T).map φ)) :=
        Nat.Coprime.coprime_dvd_right (card_map_dvd _ _) (pPrimeCore_coprime_card (p := 2) (G := T))
      have hbot := pPrimeCore_eq_bot_iff.mp (pPrimeCore_quotient_pPrimeCore_eq_bot (G := X) 2) _
        hnorm hcop
      rwa [Subgroup.map_eq_bot_iff] at hbot
    · refine le_sSup ⟨φ.normal_ker, ?_⟩
      rw [hkerφ]
      exact Nat.Coprime.coprime_dvd_right
        (card_comap_dvd_of_injective _ _ (inclusion_injective hTX))
        (pPrimeCore_coprime_card (p := 2) (G := X))
  refine ⟨?_, (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj), fun t ht => rfl⟩
  rw [hker, hkerφ]
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact mem_inf.mpr ⟨t.2, ⟨inclusion hTX t, ht, rfl⟩⟩
  · intro hy
    obtain ⟨hyT, hyN⟩ := mem_inf.mp hy
    obtain ⟨n, hn, hny⟩ := mem_map.mp hyN
    refine ⟨⟨y, hyT⟩, ?_, rfl⟩
    show inclusion hTX ⟨y, hyT⟩ ∈ pPrimeCore 2 X
    have : inclusion hTX ⟨y, hyT⟩ = n := Subtype.ext hny.symm
    rw [this]
    exact hn

theorem isomorphic_correspondence_sylow_growth {a b : G} {J L : Subgroup G}
    (hC : UnbalancedGS.GSIsoCorr a J b L) {T A HJ HL : Subgroup G}
    (hT : T = UnbalancedGS.gsFixedLayer J b)
    (hA : A = centralizer ({b} : Set G) ⊓ normalizer (J : Set G))
    (hHJ : HJ = centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hHL : HL = centralizer ({b} : Set G) ⊓ normalizer (L : Set G)) :
    A ≤ normalizer (L : Set G) ∧ T ≤ J ∧ T ≤ L ∧ A ≤ normalizer (T : Set G) ∧
    (∃ e : T ⧸ pPrimeCore 2 T ≃* J ⧸ pPrimeCore 2 J,
      (∀ (t : T) (ht : (t : G) ∈ J), e t = ((⟨(t : G), ht⟩ : J) : J ⧸ pPrimeCore 2 J)) ∧
      ∀ g ∈ A, ∀ (t : T) (j : J) (ht : g * t * g⁻¹ ∈ T) (hj : g * j * g⁻¹ ∈ J),
        e t = (j : J ⧸ pPrimeCore 2 J) →
          e (⟨g * t * g⁻¹, ht⟩ : T) = ((⟨g * j * g⁻¹, hj⟩ : J) : J ⧸ pPrimeCore 2 J)) ∧
    (∃ e : T ⧸ pPrimeCore 2 T ≃* L ⧸ pPrimeCore 2 L,
      (∀ (t : T) (ht : (t : G) ∈ L), e t = ((⟨(t : G), ht⟩ : L) : L ⧸ pPrimeCore 2 L)) ∧
      ∀ g ∈ A, ∀ (t : T) (l : L) (ht : g * t * g⁻¹ ∈ T) (hl : g * l * g⁻¹ ∈ L),
        e t = (l : L ⧸ pPrimeCore 2 L) →
          e (⟨g * t * g⁻¹, ht⟩ : T) = ((⟨g * l * g⁻¹, hl⟩ : L) : L ⧸ pPrimeCore 2 L)) ∧
    (pPrimeCore 2 J).index = (pPrimeCore 2 L).index ∧
    {g | g ∈ A ∧ ∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype} =
      {g | g ∈ A ∧ ∀ l ∈ L, l⁻¹ * g⁻¹ * l * g ∈ (pPrimeCore 2 L).map L.subtype} ∧
    ∀ S : Subgroup G, S ≤ HJ → (∃ P : Sylow 2 HJ, (P : Subgroup HJ) = S.subgroupOf HJ) →
      S ≤ centralizer ({b} : Set G) →
      S ≤ HL ∧ pRank 2 ↥(HJ ⊓ coreActionKernel J) ≤ pRank 2 ↥(HL ⊓ coreActionKernel L) ∧
      2 ^ (Nat.card HJ).factorization 2 ≤ 2 ^ (Nat.card HL).factorization 2 ∧
      ((¬ ∃ P : Sylow 2 HL, (P : Subgroup HL) = S.subgroupOf HL) →
        2 ^ (Nat.card HJ).factorization 2 < 2 ^ (Nat.card HL).factorization 2) ∧
      ∀ x : G, GSUnbalancingTriple a x J →
        ∃ h ∈ HJ, h⁻¹ * x * h ∈ S ∧ GSUnbalancingTriple b (h⁻¹ * x * h) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hA hHJ hHL
  obtain ⟨hcorr, hLa, hsupL⟩ := UnbalancedGS.gsIsoCorr_iff_sup.mp hC
  have hTL : T ≤ L := by
    rw [hT]
    exact hcorr.gsFixedLayer_le hLa
  obtain ⟨-, hbo, -, hJa, hJ, hLb, hL, hbN, hcomm, -⟩ := hcorr
  rw [← hT] at hsupL
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
  have hsupJ : T ⊔ (pPrimeCore 2 J).map J.subtype = J := by
    rw [hT]
    exact gsFixedLayer_sup_map_pPrimeCore hbo hJq hbN hcomm
  have hTJ : T ≤ J := le_sup_left.trans hsupJ.le
  obtain ⟨hcoreJ, eJ, heJ⟩ := restriction_quotient_mulEquiv hTJ hsupJ
  obtain ⟨hcoreL, eL, heL⟩ := restriction_quotient_mulEquiv hTL hsupL
  have hcoreJL : T ⊓ (pPrimeCore 2 J).map J.subtype = T ⊓ (pPrimeCore 2 L).map L.subtype :=
    hcoreJ.symm.trans hcoreL
  have hNX : ∀ {X : Subgroup G} {g : G}, g ∈ normalizer (X : Set G) →
      g ∈ normalizer ((pPrimeCore 2 X).map X.subtype : Set G) := fun hg =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ (pPrimeCore 2 _) hg
  have hcoreg : ∀ {X : Subgroup G} {g : G}, g ∈ normalizer (X : Set G) →
      ∀ n ∈ (pPrimeCore 2 X).map X.subtype,
        n⁻¹ * g⁻¹ * n * g ∈ (pPrimeCore 2 X).map X.subtype := by
    intro X g hg n hn
    have h := (mem_normalizer_iff.mp (inv_mem (hNX hg)) n).mp hn
    rw [inv_inv] at h
    rw [show n⁻¹ * g⁻¹ * n * g = n⁻¹ * (g⁻¹ * n * g) by group]
    exact mul_mem (inv_mem hn) h
  have hAT : centralizer ({b} : Set G) ⊓ normalizer (J : Set G) ≤ normalizer (T : Set G) := by
    intro g hg
    obtain ⟨hgb, hgJ⟩ := mem_inf.mp hg
    have : (pLayer ↥(J ⊓ centralizer ({b} : Set G)) 2).Characteristic :=
      CatalogueBPrimeJoin.pLayer_characteristic
    rw [hT]
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic
      (J ⊓ centralizer ({b} : Set G)) (pLayer ↥(J ⊓ centralizer ({b} : Set G)) 2)
      (normalizer_inf_mem hgJ (le_normalizer hgb))
  have hAL : centralizer ({b} : Set G) ⊓ normalizer (J : Set G) ≤ normalizer (L : Set G) := by
    set Cb := centralizer ({b} : Set G) with hCb
    have hT'L' : T.subgroupOf Cb ≤ L.subgroupOf Cb := fun y hy =>
      (show (y : G) ∈ L from hTL (show (y : G) ∈ T from hy))
    have hsup' : T.subgroupOf Cb ⊔ (pPrimeCore 2 (L.subgroupOf Cb)).map (L.subgroupOf Cb).subtype =
        L.subgroupOf Cb := by
      apply map_injective Cb.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (hTL.trans hLb),
        pPrimeCore_map_subgroupOf 2 L Cb hLb, map_subgroupOf_eq_of_le hLb]
      exact hsupL
    have hcover : (T.subgroupOf Cb : Set Cb) *
        ((pPrimeCore 2 (L.subgroupOf Cb)).map (L.subgroupOf Cb).subtype : Set Cb) =
          L.subgroupOf Cb := by
      rw [← UnbalancedGS.coe_sup_pPrimeCore_eq_mul 2 hT'L', hsup']
    obtain ⟨-, -, -, hrec⟩ :=
      UnbalancedGS.component_recovery_from_covering_subgroup Nat.prime_two hL hT'L' hcover
    intro g hg
    have hgb : g ∈ Cb := (mem_inf.mp hg).1
    have hgT : (⟨g, hgb⟩ : Cb) ∈ normalizer (T.subgroupOf Cb : Set Cb) :=
      mem_normalizer_subgroupOf_of_mem (hAT hg)
    have hL' := hrec (MulAut.conj (⟨g, hgb⟩ : Cb)) (mem_normalizer_iff_map_conj_eq.mp hgT)
    exact mem_normalizer_of_subgroupOf hLb (mem_normalizer_iff_map_conj_eq.mpr hL')
  have hker : ∀ g ∈ centralizer ({b} : Set G) ⊓ normalizer (J : Set G),
      (∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype) ↔
        (∀ l ∈ L, l⁻¹ * g⁻¹ * l * g ∈ (pPrimeCore 2 L).map L.subtype) := by
    intro g hg
    have hgJ : g ∈ normalizer (J : Set G) := (mem_inf.mp hg).2
    have hgL := hAL hg
    have hTg : ∀ t ∈ T, t⁻¹ * g⁻¹ * t * g ∈ T := by
      intro t ht
      have h := (mem_normalizer_iff.mp (inv_mem (hAT hg)) t).mp ht
      rw [inv_inv] at h
      rw [show t⁻¹ * g⁻¹ * t * g = t⁻¹ * (g⁻¹ * t * g) by group]
      exact mul_mem (inv_mem ht) h
    constructor
    · intro h l hl
      refine commutator_mem_of_mem_sup (fun y hy => hNX (le_normalizer hy)) hTL (map_subtype_le _)
        (fun t ht => ?_) (hcoreg hgL) (by rw [hsupL]; exact hl)
      have h1 : t⁻¹ * g⁻¹ * t * g ∈ T ⊓ (pPrimeCore 2 J).map J.subtype :=
        mem_inf.mpr ⟨hTg t ht, h t (hTJ ht)⟩
      rw [hcoreJL] at h1
      exact (mem_inf.mp h1).2
    · intro h j hj
      refine commutator_mem_of_mem_sup (fun y hy => hNX (le_normalizer hy)) hTJ (map_subtype_le _)
        (fun t ht => ?_) (hcoreg hgJ) (by rw [hsupJ]; exact hj)
      have h1 : t⁻¹ * g⁻¹ * t * g ∈ T ⊓ (pPrimeCore 2 L).map L.subtype :=
        mem_inf.mpr ⟨hTg t ht, h t (hTL ht)⟩
      rw [← hcoreJL] at h1
      exact (mem_inf.mp h1).2
  refine ⟨hAL, hTJ, hTL, hAT, ⟨eJ, heJ, ?_⟩, ⟨eL, heL, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg t j ht hj hte
    rw [heJ ⟨g * t * g⁻¹, ht⟩ (hTJ ht)]
    rw [heJ t (hTJ t.2), QuotientGroup.eq] at hte
    rw [QuotientGroup.eq]
    apply (mem_map_iff_mem J.subtype_injective).mp
    have h1 : (t : G)⁻¹ * j ∈ (pPrimeCore 2 J).map J.subtype := mem_map_of_mem J.subtype hte
    have h2 := (mem_normalizer_iff.mp (hNX (mem_inf.mp hg).2) _).mp h1
    show (g * (t : G) * g⁻¹)⁻¹ * (g * (j : G) * g⁻¹) ∈ (pPrimeCore 2 J).map J.subtype
    rwa [show (g * (t : G) * g⁻¹)⁻¹ * (g * (j : G) * g⁻¹) = g * ((t : G)⁻¹ * j) * g⁻¹ by group]
  · intro g hg t l ht hl hte
    rw [heL ⟨g * t * g⁻¹, ht⟩ (hTL ht)]
    rw [heL t (hTL t.2), QuotientGroup.eq] at hte
    rw [QuotientGroup.eq]
    apply (mem_map_iff_mem L.subtype_injective).mp
    have h1 : (t : G)⁻¹ * l ∈ (pPrimeCore 2 L).map L.subtype := mem_map_of_mem L.subtype hte
    have h2 := (mem_normalizer_iff.mp (hNX (hAL hg)) _).mp h1
    show (g * (t : G) * g⁻¹)⁻¹ * (g * (l : G) * g⁻¹) ∈ (pPrimeCore 2 L).map L.subtype
    rwa [show (g * (t : G) * g⁻¹)⁻¹ * (g * (l : G) * g⁻¹) = g * ((t : G)⁻¹ * l) * g⁻¹ by group]
  · rw [index_eq_card, index_eq_card, ← Nat.card_congr eJ.toEquiv, Nat.card_congr eL.toEquiv]
  · ext g
    exact and_congr_right (hker g)
  intro S hSH hSsyl hSb
  obtain ⟨P₀, hP₀⟩ := hSsyl
  have hSA : S ≤ centralizer ({b} : Set G) ⊓ normalizer (J : Set G) := fun s hs =>
    mem_inf.mpr ⟨hSb hs, (mem_inf.mp (hSH hs)).2⟩
  have hSHL : S ≤ centralizer ({b} : Set G) ⊓ normalizer (L : Set G) := fun s hs =>
    mem_inf.mpr ⟨hSb hs, hAL (hSA hs)⟩
  have hbr : ∀ Q : Subgroup G, pRank 2 ↥Q = Open.pRank 2 Q := fun Q =>
    (SectionRank.pRank_eq_open_pRank_top 2 Q).trans (SectionRank.pRank_eq_pRank_top_subgroup Q).symm
  have hrank : pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J) ≤
      pRank 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (L : Set G) ⊓ coreActionKernel L) := by
    rw [hbr, hbr]
    obtain ⟨E, hEQ, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) one_lt_two
      (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J)
    obtain ⟨h, hh, hEh⟩ := exists_conjugate_le_of_sylow ⟨P₀, hP₀⟩ (hEQ.trans inf_le_left)
      (IsPGroup.of_card hcard)
    have hhQ : h ∈ normalizer ((centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓
        coreActionKernel J : Subgroup G) : Set G) :=
      normalizer_inf_mem (le_normalizer hh)
        (normalizer_le_normalizer_coreActionKernel J (mem_inf.mp hh).2)
    have hEhL : conjugate E h ≤
        centralizer ({b} : Set G) ⊓ normalizer (L : Set G) ⊓ coreActionKernel L := by
      intro y hy
      have hyS := hEh hy
      have hyQ : y ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J := by
        rw [mem_conjugate_iff] at hy
        have h1 := (mem_normalizer_iff.mp (inv_mem hhQ) _).mp (hEQ hy)
        rwa [show h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y by group] at h1
      have hyK := (mem_coreActionKernel.mp (mem_inf.mp hyQ).2).2
      exact mem_inf.mpr ⟨hSHL hyS,
        mem_coreActionKernel.mpr ⟨hAL (hSA hyS), (hker y (hSA hyS)).mp hyK⟩⟩
    refine SectionRank.le_pRank one_lt_two hEhL
      (SectionRank.isElemAbelian_map hE (MulAut.conj h⁻¹).toMonoidHom) ?_
    unfold conjugate
    rw [card_map_of_injective (MulAut.conj h⁻¹).injective, hcard]
  have hScard : Nat.card S =
      2 ^ (Nat.card ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G))).factorization 2 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv, ← hP₀]
    exact Sylow.card_eq_multiplicity P₀
  have hS2 : IsPGroup 2 (S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (L : Set G))) :=
    IsPGroup.of_card (by rw [Nat.card_congr (subgroupOfEquivOfLe hSHL).toEquiv, hScard])
  obtain ⟨Q, hQ⟩ := hS2.exists_le_sylow
  have hQcard := Sylow.card_eq_multiplicity Q
  have hle : 2 ^ (Nat.card ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G))).factorization 2 ≤
      2 ^ (Nat.card ↥(centralizer ({b} : Set G) ⊓ normalizer (L : Set G))).factorization 2 := by
    rw [← hScard, ← Nat.card_congr (subgroupOfEquivOfLe hSHL).toEquiv, ← hQcard]
    exact card_le_of_le hQ
  refine ⟨hSHL, hrank, hle, fun hnot => lt_of_le_of_ne hle fun heq => hnot ⟨Q, ?_⟩, ?_⟩
  · symm
    apply eq_of_le_of_card_ge hQ
    refine le_of_eq ?_
    rw [hQcard, ← heq, ← hScard, Nat.card_congr (subgroupOfEquivOfLe hSHL).toEquiv]
  · intro x hU
    obtain ⟨-, hxo, hax, -, -, hJx, -⟩ := gsUnbalancingTriple_iff.mp hU
    have hxN : x ∈ normalizer (J : Set G) := by
      have h := le_normalizer_commutator (zpowers x) J
      rw [commutator_comm, hJx] at h
      exact h (mem_zpowers x)
    have hxH : x ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) :=
      mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hax.symm, hxN⟩
    have hx2 : IsPGroup 2 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
    obtain ⟨h, hh, hxS⟩ := exists_conjugate_le_of_sylow ⟨P₀, hP₀⟩ (zpowers_le.mpr hxH) hx2
    have hxhS : h⁻¹ * x * h ∈ S := hxS (conj_mem_conjugate (mem_zpowers x) h)
    refine ⟨h, hh, hxhS, ?_⟩
    have hU' := gsUnbalancingTriple_conj hU (mem_inf.mp hh).1 (mem_inf.mp hh).2
    exact unbalancing_triple_correspondence_transfer hU' hC.1
      (mem_centralizer_singleton_iff.mp (hSb hxhS)).symm

end CFSG.ComponentClassification.UnbalancedLayer
