module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalOrbits

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nested_le_normalizer_map_pPrimeCore (T : Subgroup G) :
    T ≤ normalizer (((pPrimeCore 2 ↥T).map T.subtype : Subgroup G) : Set G) := by
  have hle : (pPrimeCore 2 ↥T).map T.subtype ≤ T := map_subtype_le _
  rw [← normal_subgroupOf_iff_le_normalizer hle]
  have h : ((pPrimeCore 2 ↥T).map T.subtype).subgroupOf T = pPrimeCore 2 ↥T :=
    comap_map_eq_self_of_injective T.subtype_injective _
  rw [h]
  infer_instance

theorem map_primeResidual_eq_closure (X : Subgroup G) :
    (CatalogueBPrimeJoin.primeResidual 2 ↥X).map X.subtype =
      closure {x : G | x ∈ X ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CatalogueBPrimeJoin.primeResidual_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, (Subgroup.orderOf_coe y).trans hk⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, (Subgroup.orderOf_mk x hx).trans hk⟩, rfl⟩

theorem map_map_pLayer_subgroupOf {K H : Subgroup G} (hKH : K ≤ H) :
    ((pLayer ↥(K.subgroupOf H) 2).map (K.subgroupOf H).subtype).map H.subtype =
      (pLayer ↥K 2).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := subgroupOfEquivOfLe hKH
  have hhom : K.subtype.comp e.toMonoidHom = H.subtype.comp (K.subgroupOf H).subtype := by
    ext x
    rfl
  rw [Subgroup.map_map, ← hhom, ← Subgroup.map_map,
    UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 e]

theorem primeResidual_le_sup_of_commutator_le {U O R : Subgroup G}
    (hUO : U ≤ normalizer (O : Set G)) (hO : Nat.Coprime 2 (Nat.card O))
    (hXR : U ⊔ O ≤ normalizer (R : Set G)) (hc : ⁅U, O⁆ ≤ R) :
    (CatalogueBPrimeJoin.primeResidual 2 ↥(U ⊔ O)).map (U ⊔ O).subtype ≤ U ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := U ⊔ O with hXdef
  have hconj : ∀ o ∈ O, ∀ y ∈ U ⊔ R, o * y * o⁻¹ ∈ U ⊔ R := by
    intro o ho y hy
    have hmap : (U ⊔ R).map (MulAut.conj o).toMonoidHom ≤ U ⊔ R := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        have h1 := hc (commutator_mem_commutator (inv_mem hu) ho)
        rw [commutatorElement_def] at h1
        have h2 : (MulAut.conj o).toMonoidHom u = u * (u⁻¹ * o * u⁻¹⁻¹ * o⁻¹) := by
          show o * u * o⁻¹ = _
          group
        rw [h2]
        exact mul_mem (mem_sup_left hu) (mem_sup_right h1)
      · rintro _ ⟨r, hr, rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp (hXR (mem_sup_right ho)) r).mp hr)
    exact hmap ⟨y, hy, rfl⟩
  have hON : O ≤ normalizer ((U ⊔ R : Subgroup G) : Set G) := by
    intro o ho
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hconj o ho y, fun hy => ?_⟩
    have h1 := hconj o⁻¹ (inv_mem ho) _ hy
    rwa [show o⁻¹ * (o * y * o⁻¹) * o⁻¹⁻¹ = y by group] at h1
  have hUN : U ≤ normalizer ((U ⊔ R : Subgroup G) : Set G) := fun u hu =>
    mem_normalizer_sup (le_normalizer hu) (hXR (mem_sup_left hu))
  have hXN : X ≤ normalizer ((U ⊔ R : Subgroup G) : Set G) := sup_le hUN hON
  set N := (U ⊔ R).subgroupOf X with hNdef
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNdef, mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.mp (hXN g.2) n).mp hn
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (O.subgroupOf X).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : (x : G) ∈ (O : Set G) * (U : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left O U hUO, sup_comm]
      exact x.2
    obtain ⟨o, ho, u, hu, hou⟩ := Set.mem_mul.mp hx
    refine ⟨⟨⟨o, mem_sup_right ho⟩, ho⟩, ?_⟩
    show ((⟨o, mem_sup_right ho⟩ : X) : ↥X ⧸ N) = (x : ↥X ⧸ N)
    rw [QuotientGroup.eq, hNdef, mem_subgroupOf]
    show o⁻¹ * (x : G) ∈ U ⊔ R
    rw [← hou, inv_mul_cancel_left]
    exact mem_sup_left hu
  have hdvd : Nat.card (↥X ⧸ N) ∣ Nat.card ↥(O.subgroupOf X) :=
    Subgroup.card_dvd_of_surjective hsurj
  have hcardO : Nat.card ↥(O.subgroupOf X) = Nat.card O :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  have hindex : Nat.Coprime 2 N.index := by
    show Nat.Coprime 2 (Nat.card (↥X ⧸ N))
    rw [hcardO] at hdvd
    exact Nat.Coprime.coprime_dvd_right hdvd hO
  have hres := CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index 2 N hindex
  calc (CatalogueBPrimeJoin.primeResidual 2 ↥X).map X.subtype ≤ N.map X.subtype := map_mono hres
    _ ≤ U ⊔ R := by
      rw [hNdef, subgroupOf_map_subtype]
      exact inf_le_left

theorem commutator_pLayer_pPrimeCore_le_of_inputs
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {H D : Subgroup G} (hKH : SectionRank.IsKGroupCat ↥H) (hDH : D ≤ H) (hD1 : D ≠ ⊥)
    (hD2 : IsPGroup 2 D) :
    ⁅(pLayer ↥(H ⊓ normalizer (D : Set G)) 2).map (H ⊓ normalizer (D : Set G)).subtype,
      (pPrimeCore 2 ↥(H ⊓ normalizer (D : Set G))).map (H ⊓ normalizer (D : Set G)).subtype⁆ ≤
      (pPrimeCore 2 ↥H).map H.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hloc⟩ := ProperSectionB.kGroupBConclusion_of_inputs hS hU hheld hKH
  have hD'1 : D.subgroupOf H ≠ ⊥ := by
    intro h
    apply hD1
    have h1 := congrArg (Subgroup.map H.subtype) h
    rwa [map_subgroupOf_eq_of_le hDH, Subgroup.map_bot] at h1
  have hD'2 : IsPGroup 2 (D.subgroupOf H) := hD2.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨h1, -, -⟩ := hloc (D.subgroupOf H) hD'1 hD'2
  have hoc : ∀ (Y : Type) [Group Y], CFSG.Assembly.oddCore Y = pPrimeCore 2 Y := by
    intro Y _
    show sSup _ = sSup _
    congr 1
    ext L
    simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
  set K := H ⊓ normalizer (D : Set G) with hKdef
  have hV : normalizer ((D.subgroupOf H : Subgroup H) : Set H) = K.subgroupOf H := by
    rw [normalizer_subgroupOf_eq hDH, hKdef, inf_subgroupOf_left]
  simp only [hoc] at h1
  rw [hV] at h1
  have h2 := map_mono (f := H.subtype) h1
  rw [map_commutator, map_map_pLayer_subgroupOf (inf_le_left : K ≤ H),
    pPrimeCore_map_subgroupOf 2 K H inf_le_left] at h2
  exact h2

theorem nested_fixed_layer_le {J P B D T_B T_D : Subgroup G}
    (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J)) (hP2 : IsPGroup 2 P)
    (hPK : P ≤ UnbalancedLayer.coreActionKernel J) (hBD : B ≤ D) (hDP : D ≤ P)
    (hTB : T_B = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hTD : T_D = (pLayer ↥(J ⊓ centralizer (D : Set G)) 2).map
      (J ⊓ centralizer (D : Set G)).subtype) :
    T_D ≤ T_B ∧ T_D ⊔ (pPrimeCore 2 ↥T_B).map T_B.subtype = T_B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : P ≤ normalizer (J : Set G) := fun x hx =>
    (UnbalancedLayer.mem_coreActionKernel.mp (hPK hx)).1
  let α : P →* MulAut J := J.normalizerMonoidHom.comp (inclusion hPN)
  have hα : ∀ (c : P) (j : J), ((α c j : J) : G) = (c : G) * j * (c : G)⁻¹ :=
    fun c j => Subgroup.normalizerMonoidHom_apply_apply_coe J _ j
  have htriv : ∀ (c : P) (j : J),
      ((α c j : J) : J ⧸ pPrimeCore 2 J) = (j : J ⧸ pPrimeCore 2 J) := by
    intro c j
    rw [eq_comm, QuotientGroup.eq]
    apply (mem_map_iff_mem J.subtype_injective).mp
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem (hPK c.2))).2 j j.2
    rw [inv_inv] at h1
    show (j : G)⁻¹ * ((α c j : J) : G) ∈ (pPrimeCore 2 J).map J.subtype
    rw [hα]
    rwa [show (j : G)⁻¹ * ((c : G) * j * (c : G)⁻¹) = (j : G)⁻¹ * c * j * (c : G)⁻¹ by group]
  set C : Subgroup P → Subgroup J := fun B =>
    (centralizer ((B.map P.subtype : Subgroup G) : Set G)).subgroupOf J with hCdef
  have hC : ∀ (B : Subgroup P) (x : J), x ∈ C B ↔ ∀ c ∈ B, α c x = x := by
    intro B x
    show (x : G) ∈ centralizer ((B.map P.subtype : Subgroup G) : Set G) ↔ _
    rw [mem_centralizer_iff]
    constructor
    · intro h1 c hc
      apply Subtype.ext
      rw [hα, h1 (c : G) ⟨c, hc, rfl⟩, mul_inv_cancel_right]
    · intro h1 g hg
      obtain ⟨c, hc, rfl⟩ := mem_map.mp hg
      have h2 := congrArg Subtype.val (h1 c hc)
      rw [hα] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
  set Tf : Subgroup P → Subgroup J := fun B => (pLayer (C B) 2).map (C B).subtype with hTfdef
  obtain ⟨-, hnest⟩ :=
    UnbalancedGS.nested_fixed_prime_layer_covering 2 hP2 α hJq htriv C hC Tf (fun B => rfl)
  have hTfY : ∀ (B : Subgroup P) (Y : Subgroup G),
      centralizer ((B.map P.subtype : Subgroup G) : Set G) = Y →
      (Tf B).map J.subtype = (pLayer ↥(J ⊓ Y) 2).map (J ⊓ Y).subtype := by
    intro B Y hY
    subst hY
    exact map_pLayer_subgroupOf_eq J _
  have hTBm : (Tf (B.subgroupOf P)).map J.subtype = T_B := by
    rw [hTB]
    exact hTfY _ _ (by rw [map_subgroupOf_eq_of_le (hBD.trans hDP)])
  have hTDm : (Tf (D.subgroupOf P)).map J.subtype = T_D := by
    rw [hTD]
    exact hTfY _ _ (by rw [map_subgroupOf_eq_of_le hDP])
  obtain ⟨hle, hsup, -⟩ := hnest (B.subgroupOf P) (D.subgroupOf P) (fun x hx => hBD hx)
  refine ⟨?_, ?_⟩
  · rw [← hTBm, ← hTDm]
    exact map_mono hle
  · have h1 := congrArg (Subgroup.map J.subtype) hsup
    rw [Subgroup.map_sup, map_map_pPrimeCore_subtype, hTBm, hTDm] at h1
    exact h1

theorem nested_two_local_full_core_residual_identities_of_inputs
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S P : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)))
    (hP : P = S ⊓ UnbalancedLayer.coreActionKernel J)
    (H R T X : Subgroup G → Subgroup G) (hH : ∀ B, H B = normalizer (B : Set G))
    (hR : ∀ B, R B = (pPrimeCore 2 ↥(H B)).map (H B).subtype)
    (hT : ∀ B, T B = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hX : ∀ B, X B = T B ⊔ R B) :
    (∀ B D : Subgroup G, B ≠ ⊥ → B ≤ D → D ≤ P →
      T D ≤ T B ∧ T D ⊔ (pPrimeCore 2 ↥(T B)).map (T B).subtype = T B ∧ X B = T D ⊔ R B) ∧
    (∀ B D : Subgroup G, B ≠ ⊥ → B ≤ D → D ≤ P → D ≤ normalizer (B : Set G) →
      X B = closure {x : G | x ∈ X D ∧ ∃ k : ℕ, orderOf x = 2 ^ k} ⊔ R B) ∧
    ∀ B : Subgroup G, B ≠ ⊥ → B ≤ P →
      X (P ⊓ normalizer (B : Set G)) =
        X B ⊓ centralizer ((P ⊓ normalizer (B : Set G) : Subgroup G) : Set G) ⊔
          R (P ⊓ normalizer (B : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 (S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
      hP₀ ▸ P₀.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hSX)
  subst hP
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
  have hP2 : IsPGroup 2 ↥(S ⊓ UnbalancedLayer.coreActionKernel J) := hS2.to_le inf_le_left
  have hRf : ∀ C : Subgroup G, R C = (pPrimeCore 2 ↥(normalizer (C : Set G))).map
      (normalizer (C : Set G)).subtype := fun C => by rw [hR, hH]
  have hRN : ∀ C : Subgroup G, normalizer (C : Set G) ≤ normalizer (R C : Set G) := fun C => by
    rw [hRf]
    exact nested_le_normalizer_map_pPrimeCore _
  have hRodd : ∀ C : Subgroup G, Nat.Coprime 2 (Nat.card (R C)) := fun C => by
    rw [hRf, card_map_of_injective (subtype_injective _)]
    exact pPrimeCore_coprime_card
  have partA : ∀ B D : Subgroup G, B ≠ ⊥ → B ≤ D → D ≤ S ⊓ UnbalancedLayer.coreActionKernel J →
      T D ≤ T B ∧ T D ⊔ (pPrimeCore 2 ↥(T B)).map (T B).subtype = T B ∧
        X B = T D ⊔ R B := by
    intro B D hB1 hBD hDP
    have hBP := hBD.trans hDP
    obtain ⟨hTDB, hsupDB⟩ := nested_fixed_layer_le hJq hP2 inf_le_right hBD hDP (hT B) (hT D)
    obtain ⟨-, haN, -, hKH, -, -, -, -, -, hTaN, hpcN, -⟩ :=
      two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2 hB1 hBP (hT B)
    have ha1 : a ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ha
      exact absurd ha (by norm_num)
    have hza2 : IsPGroup 2 (zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    have hcomm0 := commutator_pLayer_pPrimeCore_le_of_inputs hS hU hheld hKH
      (zpowers_le.mpr haN) (zpowers_ne_bot.mpr ha1) hza2
    rw [normalizer_zpowers_eq_centralizer ha,
      inf_comm (normalizer (B : Set G)) (centralizer ({a} : Set G)), ← hRf] at hcomm0
    have hTE : T B ≤ (pLayer ↥(centralizer ({a} : Set G) ⊓ normalizer (B : Set G)) 2).map
        (centralizer ({a} : Set G) ⊓ normalizer (B : Set G)).subtype := by
      have h1 : (T B).subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (B : Set G)) ≤
          pLayer ↥(centralizer ({a} : Set G) ⊓ normalizer (B : Set G)) 2 := le_sSup hpcN
      intro t ht
      exact ⟨⟨t, hTaN ht⟩, h1 ht, rfl⟩
    have hOle : (pPrimeCore 2 ↥(T B)).map (T B).subtype ≤
        (pPrimeCore 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (B : Set G))).map
          (centralizer ({a} : Set G) ⊓ normalizer (B : Set G)).subtype := by
      obtain ⟨-, -, hs, -, -⟩ := id hpcN
      rw [map_pPrimeCore_eq_inf_of_subgroupOf hTaN hs]
      exact inf_le_right
    have hcomm : ⁅T B, (pPrimeCore 2 ↥(T B)).map (T B).subtype⁆ ≤ R B :=
      (commutator_mono hTE hOle).trans hcomm0
    have hTres : CatalogueBPrimeJoin.primeResidual 2 ↥(T B) = ⊤ :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 (T B) _ hTaN).mp hpcN).2.1
    have hUO : T D ≤ normalizer (((pPrimeCore 2 ↥(T B)).map (T B).subtype : Subgroup G) :
        Set G) := hTDB.trans (nested_le_normalizer_map_pPrimeCore (T B))
    have hO : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥(T B)).map (T B).subtype)) := by
      rw [card_map_of_injective (subtype_injective _)]
      exact pPrimeCore_coprime_card
    have hXR : T D ⊔ (pPrimeCore 2 ↥(T B)).map (T B).subtype ≤ normalizer (R B : Set G) := by
      rw [hsupDB]
      exact (hTaN.trans inf_le_right).trans (hRN B)
    have hres := primeResidual_le_sup_of_commutator_le hUO hO hXR
      ((commutator_mono hTDB le_rfl).trans hcomm)
    rw [hsupDB, hTres, ← MonoidHom.range_eq_map, range_subtype] at hres
    refine ⟨hTDB, hsupDB, ?_⟩
    rw [hX B]
    exact le_antisymm (sup_le hres le_sup_right) (sup_le_sup_right hTDB _)
  refine ⟨partA, ?_, ?_⟩
  ·
    intro B D hB1 hBD hDP hDN
    obtain ⟨-, -, hXB⟩ := partA B D hB1 hBD hDP
    have hBP := hBD.trans hDP
    have hD1 : D ≠ ⊥ := fun h => hB1 (le_bot_iff.mp (h ▸ hBD))
    obtain ⟨-, haN, hHtop, hKH, -, -, -, -, -, -, -, -⟩ :=
      two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2 hB1 hBP (hT B)
    obtain ⟨hD2, haND, -, -, -, -, -, hTaBD, -, hTaND, hpcND, -⟩ :=
      two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2 hD1 hDP (hT D)
    set K := normalizer (B : Set G) ⊓ normalizer (D : Set G) with hKdef
    have hCDB : centralizer (D : Set G) ≤ centralizer (B : Set G) := centralizer_le hBD
    have hCDH : centralizer (D : Set G) ≤ normalizer (B : Set G) :=
      hCDB.trans (centralizer_le_normalizer' B)
    have hCDK : centralizer (D : Set G) ≤ K := le_inf hCDH (centralizer_le_normalizer' D)
    have hKtop : K ≠ ⊤ := fun h => hHtop (top_unique (h ▸ inf_le_left))
    have hKK := isKGroupCat_of_ne_top hK hKtop
    have hTDK : T D ≤ centralizer ({a} : Set G) ⊓ K := fun t ht =>
      ⟨(hTaBD ht).1, hCDK (hTaBD ht).2⟩
    have hpcK : IsPComponent 2 ((T D).subgroupOf (centralizer ({a} : Set G) ⊓ K)) :=
      isPComponent_subgroupOf_of_le hTDK (inf_le_inf_left _ inf_le_right) hpcND
    have hTDE := le_pLayer_of_isPComponent_centralizer hS hKK ⟨haN, haND⟩ ha hTDK hpcK
    have hRDC : R D ≤ centralizer (D : Set G) := by
      rw [hRf]
      exact pPrimeCore_normalizer_le_centralizer hD2
    have hRDK : R D ≤ K := hRDC.trans hCDK
    have hRDO : R D ≤ (pPrimeCore 2 ↥K).map K.subtype := by
      have hn : ((R D).subgroupOf K).Normal :=
        (normal_subgroupOf_iff_le_normalizer hRDK).mpr (inf_le_right.trans (hRN D))
      have hcop : Nat.Coprime 2 (Nat.card ((R D).subgroupOf K)) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hRDK).toEquiv]
        exact hRodd D
      have h1 := le_pPrimeCore_of_isSubnormal hn.isSubnormal hcop
      intro r hr
      exact ⟨⟨r, hRDK hr⟩, h1 (show (⟨r, hRDK hr⟩ : K) ∈ (R D).subgroupOf K from hr), rfl⟩
    have hcomm0 := commutator_pLayer_pPrimeCore_le_of_inputs hS hU hheld hKH hDN hD1 hD2
    rw [← hRf] at hcomm0
    have hcommD : ⁅T D, R D⁆ ≤ R B := (commutator_mono hTDE hRDO).trans hcomm0
    have hUO : T D ≤ normalizer (R D : Set G) :=
      ((hTaND.trans inf_le_right).trans (hRN D))
    have hXR : T D ⊔ R D ≤ normalizer (R B : Set G) :=
      sup_le ((hTaBD.trans inf_le_right).trans (hCDH.trans (hRN B)))
        (hRDC.trans (hCDH.trans (hRN B)))
    have hres := primeResidual_le_sup_of_commutator_le hUO (hRodd D) hXR hcommD
    rw [← hX D, map_primeResidual_eq_closure] at hres
    have hTresD : CatalogueBPrimeJoin.primeResidual 2 ↥(T D) = ⊤ :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 (T D) _ hTaND).mp hpcND).2.1
    have h1 := map_primeResidual_eq_closure (T D)
    rw [hTresD, ← MonoidHom.range_eq_map, range_subtype] at h1
    have hTX : T D ≤ X D := hX D ▸ le_sup_left
    have hTD2 : T D ≤ closure {x : G | x ∈ X D ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := by
      rw [h1]
      exact closure_mono fun x hx => ⟨hTX hx.1, hx.2⟩
    rw [hXB]
    exact le_antisymm (sup_le_sup_right hTD2 _) (sup_le hres le_sup_right)
  ·
    intro B hB1 hBP
    set Tn := S ⊓ UnbalancedLayer.coreActionKernel J ⊓ normalizer (B : Set G) with hTndef
    have hBTn : B ≤ Tn := le_inf hBP le_normalizer
    have hTnP : Tn ≤ S ⊓ UnbalancedLayer.coreActionKernel J := inf_le_left
    have hTn1 : Tn ≠ ⊥ := fun h => hB1 (le_bot_iff.mp (h ▸ hBTn))
    obtain ⟨-, -, hXB⟩ := partA B Tn hB1 hBTn hTnP
    obtain ⟨hTn2, -, -, -, hRTnC, -, -, hTaTn, -, -, -, -⟩ :=
      two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2 hTn1 hTnP (hT Tn)
    have hCB : centralizer (Tn : Set G) ≤ normalizer (B : Set G) :=
      (centralizer_le hBTn).trans (centralizer_le_normalizer' B)
    have hTTnC : T Tn ≤ centralizer (Tn : Set G) := hTaTn.trans inf_le_right
    have hTTnXB : T Tn ≤ X B := hXB ▸ le_sup_left
    have hCX : X B ⊓ centralizer (Tn : Set G) ≤ T Tn ⊔ (R B ⊓ centralizer (Tn : Set G)) := by
      intro x hx
      obtain ⟨hxX, hxC⟩ := mem_inf.mp hx
      rw [hXB, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (T Tn) (R B)
        (hTTnC.trans (hCB.trans (hRN B)))] at hxX
      obtain ⟨u, hu, r, hr, rfl⟩ := Set.mem_mul.mp hxX
      have hrC : r ∈ centralizer (Tn : Set G) := by
        have h1 := mul_mem (inv_mem (hTTnC hu)) hxC
        rwa [inv_mul_cancel_left] at h1
      exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_inf.mpr ⟨hr, hrC⟩))
    have hRR : R B ⊓ centralizer (Tn : Set G) ≤ R Tn := by
      rw [hRf Tn, hRTnC]
      have hle : R B ⊓ centralizer (Tn : Set G) ≤ centralizer (Tn : Set G) := inf_le_right
      have hn : ((R B ⊓ centralizer (Tn : Set G)).subgroupOf (centralizer (Tn : Set G))).Normal :=
        (normal_subgroupOf_iff_le_normalizer hle).mpr fun g hg =>
          UnbalancedLayer.normalizer_inf_mem (hRN B (hCB hg)) (le_normalizer hg)
      have hcop : Nat.Coprime 2 (Nat.card ((R B ⊓ centralizer (Tn : Set G)).subgroupOf
          (centralizer (Tn : Set G)))) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) (hRodd B)
      have h1 := le_pPrimeCore_of_isSubnormal hn.isSubnormal hcop
      intro r hr
      exact ⟨⟨r, hle hr⟩, h1 (show (⟨r, hle hr⟩ : centralizer (Tn : Set G)) ∈
        (R B ⊓ centralizer (Tn : Set G)).subgroupOf (centralizer (Tn : Set G)) from hr), rfl⟩
    rw [hX Tn]
    apply le_antisymm
    · exact sup_le_sup_right (le_inf hTTnXB hTTnC) _
    · exact sup_le (hCX.trans (sup_le le_sup_left (hRR.trans le_sup_right))) le_sup_right

end CFSG.ComponentClassification.UnbalancedCorr
