module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceSwap

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup CFSG.ComponentClassification.UnbalancedGS

variable {G : Type*} [Group G]

abbrev CorrQuotient (b : G) : Type _ :=
  centralizer ({b} : Set G) ⧸ pPrimeCore 2 (centralizer ({b} : Set G))

@[expose] def corrImage (b : G) (X : Subgroup G) : Subgroup (CorrQuotient b) :=
  (X.subgroupOf (centralizer ({b} : Set G))).map (QuotientGroup.mk' _)

namespace Correspondence

theorem gsFixedLayer_subgroupOf [Finite G] {H K : Subgroup G} (hKH : K ≤ H) {t : G}
    (ht : t ∈ H) :
    (gsFixedLayer K t).subgroupOf H = gsFixedLayer (K.subgroupOf H) (⟨t, ht⟩ : H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥(K.subgroupOf H ⊓ centralizer ({(⟨t, ht⟩ : H)} : Set H)) ≃*
      ↥(K ⊓ centralizer ({t} : Set G)) :=
    { toFun := fun x => ⟨((x : H) : G), Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp x.2).1, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2))⟩⟩
      invFun := fun y => ⟨⟨y, hKH (Subgroup.mem_inf.mp y.2).1⟩, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp y.2).1, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2))⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hcomp : H.subtype.comp (K.subgroupOf H ⊓ centralizer ({(⟨t, ht⟩ : H)} : Set H)).subtype =
      (K ⊓ centralizer ({t} : Set G)).subtype.comp φ.toMonoidHom := by
    ext x
    rfl
  have hmap : (gsFixedLayer (K.subgroupOf H) (⟨t, ht⟩ : H)).map H.subtype = gsFixedLayer K t := by
    rw [gsFixedLayer, gsFixedLayer, Subgroup.map_map, hcomp, ← Subgroup.map_map,
      FixedLayerPComponent.map_pLayer_mulEquiv 2 φ]
  rw [← hmap]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem fixed_case [Finite G] {a b : G} {J L : Subgroup G} (h : GSCorr a J b L)
    (hLa : conjugate L a = L) :
    Nat.card (J ⧸ pPrimeCore 2 J) ≤ Nat.card (L ⧸ pPrimeCore 2 L) ∧
      (Nat.card (J ⧸ pPrimeCore 2 J) = Nat.card (L ⧸ pPrimeCore 2 L) ↔ GSIsoCorr a J b L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : L ⊔ conjugate L a = L := by rw [hLa, sup_idem]
  have hTL := h.gsFixedLayer_le hK
  set Y := (gsFixedLayer J b).subgroupOf L with hY
  have hsrc := card_gsFixedLayer_quotient h
  have hYT : Nat.card (Y ⧸ pPrimeCore 2 Y) = Nat.card (J ⧸ pPrimeCore 2 J) := by
    rw [card_quotient_pPrimeCore_congr (Subgroup.subgroupOfEquivOfLe hTL), hsrc]
  have hker : ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 L)).domRestrict Y).ker :=
    not_two_dvd_card_ker_restrict Y
  obtain ⟨e, -⟩ := CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv (p := 2)
    (QuotientGroup.mk' (pPrimeCore 2 L)) Y hker
  have hle1 : Nat.card (Y ⧸ pPrimeCore 2 Y) ≤
      Nat.card (Y.map (QuotientGroup.mk' (pPrimeCore 2 L))) := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have hle2 : Nat.card (Y.map (QuotientGroup.mk' (pPrimeCore 2 L))) ≤
      Nat.card (L ⧸ pPrimeCore 2 L) := Subgroup.card_le_card_group _
  refine ⟨hYT ▸ hle1.trans hle2, ?_⟩
  rw [gsIsoCorr_iff_map_eq_top, ← hYT]
  constructor
  · intro heq
    refine ⟨h, hK, hTL, ?_⟩
    apply Subgroup.eq_top_of_card_eq
    exact le_antisymm hle2 (heq ▸ hle1)
  · rintro ⟨-, -, -, htop⟩
    rw [Nat.card_congr e.toEquiv]
    have hcore : pPrimeCore 2 (Y.map (QuotientGroup.mk' (pPrimeCore 2 L))) = ⊥ := by
      have hiso : (Y.map (QuotientGroup.mk' (pPrimeCore 2 L))) ≃* L ⧸ pPrimeCore 2 L :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      have h1 := pPrimeCore_map_iso 2 hiso
      rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ hiso.injective).mp h1
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcore).trans
      QuotientGroup.quotientBot).toEquiv, htop, Subgroup.card_top]

theorem swap_case [Finite G] {a b : G} {J L : Subgroup G} (h : GSCorr a J b L)
    (hne : conjugate L a ≠ L) (ha : a ∈ centralizer ({b} : Set G)) :
    ∃ α : ↥(corrImage b L ⊔ corrImage b (conjugate L a)) ≃*
        ↥(corrImage b L ⊔ corrImage b (conjugate L a)),
      (∀ k, (α k : CorrQuotient b) =
        ((⟨a, ha⟩ : centralizer ({b} : Set G)) : CorrQuotient b) * k *
          ((⟨a, ha⟩ : centralizer ({b} : Set G)) : CorrQuotient b)⁻¹) ∧
      corrImage b L ≠ corrImage b (conjugate L a) ∧
      (∀ x ∈ corrImage b L, ∀ y ∈ corrImage b (conjugate L a), x * y = y * x) ∧
      IsQuasisimple (corrImage b L) ∧ IsQuasisimple (corrImage b (conjugate L a)) ∧
      (∀ d ∈ corrImage b L ⊓ corrImage b (conjugate L a),
        ∀ k ∈ corrImage b L ⊔ corrImage b (conjugate L a), d * k = k * d) ∧
      IsPGroup 2 ↥(corrImage b L ⊓ corrImage b (conjugate L a)) ∧
      (∀ x, x ∈ corrImage b (gsFixedLayer J b) ↔
        ∃ u : ↥(corrImage b L ⊔ corrImage b (conjugate L a)),
          (u : CorrQuotient b) ∈ corrImage b L ∧ x = ((u * α u : ↥(corrImage b L ⊔
            corrImage b (conjugate L a))) : CorrQuotient b)) ∧
      (∃ e : gsFixedLayer J b ⧸ pPrimeCore 2 (gsFixedLayer J b) ≃*
          ↥(corrImage b (gsFixedLayer J b)),
        ∀ (t : gsFixedLayer J b) (ht : (t : G) ∈ centralizer ({b} : Set G)),
          (e t : CorrQuotient b) = ((⟨t, ht⟩ : centralizer ({b} : Set G)) : CorrQuotient b)) ∧
      Nat.card (J ⧸ pPrimeCore 2 J) = Nat.card (L ⧸ pPrimeCore 2 L) /
        Nat.card {d : ↥(corrImage b L ⊔ corrImage b (conjugate L a)) //
          (d : CorrQuotient b) ∈ corrImage b L ⊓ corrImage b (conjugate L a) ∧ α d = d⁻¹} ∧
      (Nat.card (J ⧸ pPrimeCore 2 J) = Nat.card (L ⧸ pPrimeCore 2 L) ↔
        corrImage b L ⊓ corrImage b (conjugate L a) = ⊥) ∧
      (corrImage b L ⊓ corrImage b (conjugate L a) = ⊥ →
        (∃ e : ↥(corrImage b L) × ↥(corrImage b (conjugate L a)) ≃*
            ↥(corrImage b L ⊔ corrImage b (conjugate L a)),
          ∀ x y, (e (x, y) : CorrQuotient b) = x * y) ∧
        ∀ x, x ∈ corrImage b (gsFixedLayer J b) ↔
          ∃ k : ↥(corrImage b L ⊔ corrImage b (conjugate L a)), α k = k ∧ x = k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsrc := card_gsFixedLayer_quotient h
  obtain ⟨hao, -, -, -, -, hLb, hLcomp, -, -, hfix⟩ := h
  set H := centralizer ({b} : Set G) with hHdef
  set a' : H := ⟨a, ha⟩ with ha'def
  have haa : a * a = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
  have ha2 : a' * a' = 1 := Subtype.ext haa
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hconjle : conjugate L a ≤ H := by
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem (inv_mem ha) (hLb hl)) (inv_mem (inv_mem ha))
  have hL₂eq : (conjugate L a).subgroupOf H =
      (L.subgroupOf H).map (MulAut.conj a').toMonoidHom := by
    have hconj : ∀ g : G, (MulAut.conj a⁻¹).toMonoidHom g = a * g * a⁻¹ := fun g => by
      change a⁻¹ * g * a⁻¹⁻¹ = a * g * a⁻¹
      rw [inv_inv, hainv]
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨l, hl, hx⟩
      refine ⟨⟨l, hLb hl⟩, hl, Subtype.ext ?_⟩
      rw [← hx, hconj]
      rfl
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, hconj l⟩
  have hL₂comp : IsPComponent 2 ((conjugate L a).subgroupOf H) := by
    rw [hL₂eq]
    exact ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
      (MulAut.conj a')).1 _).mp hLcomp
  have hne₁₂ : L.subgroupOf H ≠ (conjugate L a).subgroupOf H := by
    intro heq
    apply hne
    have h2 := congrArg (Subgroup.map H.subtype) heq
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hLb, inf_of_le_left hconjle, eq_comm] at h2
  have hKH : L ⊔ conjugate L a ≤ H := sup_le hLb hconjle
  have hK₀ : (L ⊔ conjugate L a).subgroupOf H = L.subgroupOf H ⊔ (conjugate L a).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hKH, Subgroup.map_sup,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLb,
      inf_of_le_left hconjle]
  have hT : (gsFixedLayer J b).subgroupOf H =
      gsFixedLayer (L.subgroupOf H ⊔ (conjugate L a).subgroupOf H) a' := by
    rw [hfix, gsFixedLayer_subgroupOf hKH ha, hK₀]
  have hTH : gsFixedLayer J b ≤ H := by
    rw [hfix]
    exact (gsFixedLayer_le_inf _ _).trans (inf_le_left.trans hKH)
  have himg : corrImage b (gsFixedLayer J b) =
      (gsFixedLayer (L.subgroupOf H ⊔ (conjugate L a).subgroupOf H) a').map
        (QuotientGroup.mk' (pPrimeCore 2 H)) := by
    rw [corrImage, hT]
  obtain ⟨α, hαk, hAB, hcomm, hAq, hBq, hDcent, hD2, hmemT, ⟨e₀, he₀⟩, hcardT, hiff, hcase⟩ :=
    swap_layer_analysis hLcomp hL₂comp hne₁₂ ha2 hL₂eq (corrImage b L)
      (corrImage b (conjugate L a)) rfl rfl _ rfl
  let eT : gsFixedLayer J b ≃*
      gsFixedLayer (L.subgroupOf H ⊔ (conjugate L a).subgroupOf H) a' :=
    (Subgroup.subgroupOfEquivOfLe hTH).symm.trans (MulEquiv.subgroupCongr hT)
  have hcardTT := card_quotient_pPrimeCore_congr (p := 2) eT
  have hcardL := card_quotient_pPrimeCore_congr (p := 2) (Subgroup.subgroupOfEquivOfLe hLb)
  refine ⟨α, hαk, hAB, hcomm, hAq, hBq, hDcent, hD2, fun x => himg ▸ hmemT x, ?_, ?_, ?_, ?_⟩
  · refine ⟨((quotientPPrimeCoreCongr 2 eT).trans e₀).trans
      (MulEquiv.subgroupCongr himg.symm), fun t ht => ?_⟩
    change ((e₀ (quotientPPrimeCoreCongr 2 eT t) : CorrQuotient b)) = _
    rw [quotientPPrimeCoreCongr_mk, he₀]
    rfl
  · rw [← hsrc, hcardTT, hcardT, hcardL]
  · rw [← hsrc, hcardTT, ← hcardL]
    exact hiff
  · intro hD
    obtain ⟨eAB, hmemC⟩ := hcase hD
    exact ⟨eAB, fun x => himg ▸ hmemC x⟩

end Correspondence

open Correspondence

theorem correspondence_quotient_order_comparison [Finite G] {a b : G} {J L : Subgroup G}
    (h : GSCorr a J b L) :
    Nat.card (J ⧸ pPrimeCore 2 J) ≤ Nat.card (L ⧸ pPrimeCore 2 L) ∧
    (conjugate L a = L →
      (Nat.card (J ⧸ pPrimeCore 2 J) = Nat.card (L ⧸ pPrimeCore 2 L) ↔ GSIsoCorr a J b L)) ∧
    (conjugate L a ≠ L → ∀ ha : a ∈ centralizer ({b} : Set G),
      ∃ α : ↥(corrImage b L ⊔ corrImage b (conjugate L a)) ≃*
          ↥(corrImage b L ⊔ corrImage b (conjugate L a)),
        (∀ k, (α k : CorrQuotient b) =
          ((⟨a, ha⟩ : centralizer ({b} : Set G)) : CorrQuotient b) * k *
            ((⟨a, ha⟩ : centralizer ({b} : Set G)) : CorrQuotient b)⁻¹) ∧
        corrImage b L ≠ corrImage b (conjugate L a) ∧
        (∀ x ∈ corrImage b L, ∀ y ∈ corrImage b (conjugate L a), x * y = y * x) ∧
        IsQuasisimple (corrImage b L) ∧ IsQuasisimple (corrImage b (conjugate L a)) ∧
        (∀ d ∈ corrImage b L ⊓ corrImage b (conjugate L a),
          ∀ k ∈ corrImage b L ⊔ corrImage b (conjugate L a), d * k = k * d) ∧
        IsPGroup 2 ↥(corrImage b L ⊓ corrImage b (conjugate L a)) ∧
        (∀ x, x ∈ corrImage b (gsFixedLayer J b) ↔
          ∃ u : ↥(corrImage b L ⊔ corrImage b (conjugate L a)),
            (u : CorrQuotient b) ∈ corrImage b L ∧ x = ((u * α u : ↥(corrImage b L ⊔
              corrImage b (conjugate L a))) : CorrQuotient b)) ∧
        (∃ e : gsFixedLayer J b ⧸ pPrimeCore 2 (gsFixedLayer J b) ≃*
            ↥(corrImage b (gsFixedLayer J b)),
          ∀ (t : gsFixedLayer J b) (ht : (t : G) ∈ centralizer ({b} : Set G)),
            (e t : CorrQuotient b) = ((⟨t, ht⟩ : centralizer ({b} : Set G)) : CorrQuotient b)) ∧
        Nat.card (J ⧸ pPrimeCore 2 J) = Nat.card (L ⧸ pPrimeCore 2 L) /
          Nat.card {d : ↥(corrImage b L ⊔ corrImage b (conjugate L a)) //
            (d : CorrQuotient b) ∈ corrImage b L ⊓ corrImage b (conjugate L a) ∧ α d = d⁻¹} ∧
        (Nat.card (J ⧸ pPrimeCore 2 J) = Nat.card (L ⧸ pPrimeCore 2 L) ↔
          corrImage b L ⊓ corrImage b (conjugate L a) = ⊥) ∧
        (corrImage b L ⊓ corrImage b (conjugate L a) = ⊥ →
          (∃ e : ↥(corrImage b L) × ↥(corrImage b (conjugate L a)) ≃*
              ↥(corrImage b L ⊔ corrImage b (conjugate L a)),
            ∀ x y, (e (x, y) : CorrQuotient b) = x * y) ∧
          ∀ x, x ∈ corrImage b (gsFixedLayer J b) ↔
            ∃ k : ↥(corrImage b L ⊔ corrImage b (conjugate L a)), α k = k ∧ x = k)) ∧
    (conjugate L a = L → ¬ GSIsoCorr a J b L →
      Nat.card (J ⧸ pPrimeCore 2 J) < Nat.card (L ⧸ pPrimeCore 2 L)) := by
  by_cases hLa : conjugate L a = L
  · obtain ⟨hle, hiff⟩ := fixed_case h hLa
    exact ⟨hle, fun _ => hiff, fun hne => absurd hLa hne,
      fun _ hnot => lt_of_le_of_ne hle fun heq => hnot (hiff.mp heq)⟩
  · have ha : a ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.mpr h.2.2.1
    obtain ⟨α, -, -, -, -, -, -, -, -, -, hcard, -⟩ := swap_case h hLa ha
    refine ⟨?_, fun h' => absurd h' hLa, fun _ ha' => swap_case h hLa ha',
      fun h' => absurd h' hLa⟩
    rw [hcard]
    exact Nat.div_le_self _ _

end CFSG.ComponentClassification.UnbalancingLocal
