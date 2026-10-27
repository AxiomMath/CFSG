module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCriticalAt
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBAssembly

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

section Assembly

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

@[expose] def CriticalAt {G : Type} [Group G] [Finite G] (a x : G) (J S P : Subgroup G)
    (H R T X E V : Subgroup G → Subgroup G) (B : Subgroup G) : Prop :=
  GSUnbalancingTriple a x J ∧
    B ≠ ⊥ ∧ B ≤ P ∧ ∃ haH : a ∈ H B,
      let θ := QuotientGroup.mk' (criticalOddTwoCore ↥(H B))
      let ā := θ ⟨a, haH⟩
      let L := ((T B).subgroupOf (H B)).map θ
      let W := ((V B).subgroupOf (H B)).map θ
      ((criticalOddTwoCore ↥(H B)).map (H B).subtype = R B ⊔ B ∧ R B ⊓ B = ⊥ ∧
        ⁅R B, B⁆ = ⊥ ∧ orderOf ā = 2 ∧ V B = E B ∧ ⁅V B, zpowers a⁆ = V B ∧
        B ≤ H B ⊓ UnbalancedLayer.coreActionKernel (V B) ∧
        (∃ P₀ : Sylow 2 ↥(H B ⊓ UnbalancedLayer.coreActionKernel (V B)),
          (P₀ : Subgroup _) = B.subgroupOf (H B ⊓ UnbalancedLayer.coreActionKernel (V B))) ∧
        S ⊓ normalizer (B : Set G) ≤ normalizer (B : Set G) ⊓ normalizer (X B : Set G) ∧
        ∃ P₀ : Sylow 2 ↥(normalizer (B : Set G) ⊓ normalizer (X B : Set G)),
          (P₀ : Subgroup _) = (S ⊓ normalizer (B : Set G)).subgroupOf
            (normalizer (B : Set G) ⊓ normalizer (X B : Set G))) ∧
      (L ≤ centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) ∧
        IsComponent (L.subgroupOf (centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))))) ∧
        2 ≤ pRank 2 ↥L ∧ IsStandardSubgroup L) ∧
      ((∃ e : ↥L ⧸ center ↥L ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J,
          ∀ (x : ↥((T B).subgroupOf (H B))) (hx : ((x : ↥(H B)) : G) ∈ J),
            e ((θ.subgroupMap ((T B).subgroupOf (H B)) x : ↥L) : ↥L ⧸ center ↥L) =
              ((⟨_, hx⟩ : J) : J ⧸ CFSG.Open.fusionZStar ↥J)) ∧
        (⨆ e ∈ layer (↥(H B) ⧸ criticalOddTwoCore ↥(H B)), conjugate L e) = W ∧
        ⁅W, zpowers ā⁆ = W ∧
        V B ⊓ (criticalOddTwoCore ↥(H B)).map (H B).subtype =
          (CFSG.Open.fusionZStar ↥(V B)).map (V B).subtype) ∧
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ P →
        (Nat.card B < Nat.card C ∨ (Nat.card B = Nat.card C ∧
          Nat.card ↥(S ⊓ normalizer (B : Set G)) < Nat.card ↥(S ⊓ normalizer (C : Set G)))) →
        V C ≤ H C ∧ IsPComponent 2 ((V C).subgroupOf (H C)) ∧ conjugate (V C) a = V C ∧
          (T C : Set G) * ((pPrimeCore 2 ↥(V C)).map (V C).subtype : Set G) = V C ∧
          T C = UnbalancedGS.gsFixedLayer (V C) a) ∧
      ∀ (Y : Type) [Group Y], Nonempty (↥J ⧸ CFSG.Open.fusionZStar ↥J ≃* Y) →
        Nonempty (↥L ⧸ center ↥L ≃* Y)

theorem hyp52_of_criticalAt (hS : SchreierFor Blueprint.Catalog)
    (hRS : RestrictedStandardInput) [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X)
    {a x : X} {J : Subgroup X} (hmax : GSMaximalUnbalancingTriple a x J)
    (hiso : GSIsoAt a J)
    (hsmall : SmallType J)
    {S : Subgroup X} (hSX : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hxS : x ∈ S)
    (horbit : ∀ B : Subgroup X, B ≠ ⊥ → B ≤ S ⊓ coreActionKernel J →
      ∃ K : Subgroup X, K ≤ normalizer (B : Set X) ∧
        IsPComponent 2 (K.subgroupOf (normalizer (B : Set X))) ∧
        conjClosure (GSLit.fixedLayer J B) (layerIn (normalizer (B : Set X))) =
          K ⊔ conjugate K a)
    {B : Subgroup X} (hcrit : CriticalAt a x J S (S ⊓ coreActionKernel J)
      (fun B => normalizer (B : Set X)) (fun B => oddCoreIn (normalizer (B : Set X)))
      (fun B => GSLit.fixedLayer J B)
      (fun B => GSLit.fixedLayer J B ⊔ oddCoreIn (normalizer (B : Set X)))
      (fun B => layerIn (normalizer (B : Set X)))
      (fun B => conjClosure (GSLit.fixedLayer J B) (layerIn (normalizer (B : Set X)))) B) :
    ∃ h : Hyp52 X, h.a = a ∧ h.J = J ∧ h.S = S ∧ h.x = x ∧ h.B = B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hU, hB, hBP, haH, h1, h2, h3, h4, -⟩ := hcrit
  obtain ⟨hN, -, -, -, hVE, hcommV, hBD, hBsyl, hQle, hQsyl⟩ := h1
  obtain ⟨hLa, hLc, hrank, hstd⟩ := h2
  obtain ⟨⟨e, he⟩, hcl, hcomm, -⟩ := h3
  obtain ⟨ha, hx, -, hJa, hJpc, -, -⟩ := gsUnbalancingTriple_iff.mp hU
  beta_reduce at hN hVE hcommV hBD hBsyl hQle hQsyl hLa hLc hrank hstd e he hcl hcomm h4 haH
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 (S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) :=
      hP₀ ▸ P₀.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hSX)
  have hB2 : IsPGroup 2 B := hS2.to_le (hBP.trans inf_le_left)
  have hWne := normalizer_ne_top_of_simple hnonab hB hB2
  have hWK := isKGroupCat_of_ne_top' hK hWne
  obtain ⟨K, hKW, hKpc, hKV⟩ := horbit B hB hBP
  rw [hVE] at hKV hcommV hBD hBsyl hcl hcomm
  have hTV : GSLit.fixedLayer J B ≤ layerIn (normalizer (B : Set X)) := by
    rw [← hVE]
    exact le_iSup₂_of_le 1 (one_mem _) fun t ht => ⟨t, ht, by simp⟩
  have hTJ : GSLit.fixedLayer J B ≤ J := (GSLit.fixedLayer_le_inf J B).trans inf_le_left
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hJa)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hJpc)
  have h9 := exists_sylow_inf_of_le_normalizer
    (M := normalizer (B : Set X) ⊓
      normalizer ((GSLit.fixedLayer J B ⊔ oddCoreIn (normalizer (B : Set X)) : Subgroup X) :
        Set X))
    (K := layerIn (normalizer (B : Set X)) ⊓
      normalizer ((GSLit.fixedLayer J B ⊔ oddCoreIn (normalizer (B : Set X)) : Subgroup X) :
        Set X))
    (inf_le_inf_right _ (map_subtype_le _))
    (fun g hg => mem_normalizer_inf (le_normalizer_layerIn_self _ (mem_inf.mp hg).1)
      (le_normalizer (mem_inf.mp hg).2)) hQle hQsyl
  obtain ⟨R', hR'⟩ := h9
  refine ⟨⟨a, J, S, B, K, x, hK, hWK, hWne, ha, hJa, hJpc, hsmall, hSX, hSsyl, hBP, hB, haH,
    ⟨hLa, hLc⟩, hstd, hVE, hcommV, hBD, hBsyl, ?_, hxS, ?_, ?_,
    ⟨_, inf_le_left, inf_le_right, R', hR'⟩, ⟨hKW, hKpc⟩, hKV.symm, Or.inl ?_⟩,
    rfl, rfl, rfl, rfl, rfl⟩
  ·
    intro E hE hlt
    have hE1 : E ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hlt
      rcases hlt with hlt | ⟨hlt, -⟩
      · exact absurd hlt (by have := Nat.card_pos (α := B); omega)
      · exact hB (Subgroup.card_eq_one.mp hlt.symm)
    obtain ⟨hVle, hVpc, hVa, hTO, hTfix⟩ := h4 E hE1 hE (hlt.imp id fun h => ⟨h.1.symm, h.2⟩)
    refine ⟨_, hVle, hVpc, hVa, ?_, hTfix⟩
    apply le_antisymm
    · refine sup_le (fun t ht => ?_) (map_subtype_le _)
      set VE := conjClosure (GSLit.fixedLayer J E) (layerIn (normalizer (E : Set X)))
      have h5 : t ∈ ((GSLit.fixedLayer J E : Set X) *
          ((pPrimeCore 2 ↥VE).map VE.subtype : Set X)) :=
        ⟨t, ht, 1, one_mem _, mul_one t⟩
      rw [hTO] at h5
      exact h5
    · intro v hv
      have hv' : v ∈ (conjClosure (GSLit.fixedLayer J E) (layerIn (normalizer (E : Set X))) :
          Set X) := hv
      rw [← hTO] at hv'
      obtain ⟨t, ht, o, ho, rfl⟩ := hv'
      exact mul_mem (mem_sup_left ht) (mem_sup_right ho)
  ·
    exact inf_conjugate_eq_bot hS hnonab hK hmax hiso hB2
      ((hBP.trans inf_le_left).trans (hSX.trans inf_le_left)) (hBP.trans inf_le_right) hVE hcommV
  · rw [show x ^ 2 = 1 by rw [← hx]; exact pow_orderOf_eq_one x]
    exact one_mem _
  · exact gsRestricted_of_criticalLayer hRS haH hWK hKW hKpc hKV.symm hN hBD hBsyl hTV hTJ hJq
      hsmall hLa hrank hstd e he hcl hcomm

omit [Finite X] in
theorem mem_normalizer_of_conjugate_eq' {L : Subgroup X} {a : X} (h : conjugate L a = L) :
    a ∈ normalizer (L : Set X) := by
  rw [mem_normalizer_iff]
  intro y
  have h1 : y ∈ conjugate L a ↔ y ∈ L := by rw [h]
  rw [mem_conjugate_iff] at h1
  exact h1.symm

theorem commutator_ne_of_isoCorrSub {a : X} {J E L : Subgroup X} (hL : IsoCorrSub a J E L) :
    ⁅conjClosure (GSLit.fixedLayer J E) (layerIn (normalizer (E : Set X))), zpowers a⁆ ≠
      conjClosure (GSLit.fixedLayer J E) (layerIn (normalizer (E : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLN, hLpc, hLa, hsup, hfix⟩ := hL
  set V := conjClosure (GSLit.fixedLayer J E) (layerIn (normalizer (E : Set X))) with hV
  set O := oddCoreIn L with hO
  have hJL : GSLit.fixedLayer J E ≤ L := hsup ▸ le_sup_left
  have hLnorm : layerIn (normalizer (E : Set X)) ≤ normalizer (L : Set X) :=
    UGSChain.map_pLayer_le_normalizer hLN hLpc
  have hVL : V ≤ L := by
    rw [hV, conjClosure]
    refine iSup₂_le fun e he => ?_
    intro y hy
    rw [mem_conjugate_iff] at hy
    have h2 := (mem_normalizer_iff.mp (inv_mem (hLnorm he)) _).mp (hJL hy)
    convert h2 using 1
    group
  have hJV : GSLit.fixedLayer J E ≤ V := by
    rw [hV, conjClosure]
    refine le_iSup₂_of_le (1 : X) (one_mem _) fun t ht => ?_
    rw [mem_conjugate_iff, one_mul, inv_one, mul_one]
    exact ht
  have haL : a ∈ normalizer (L : Set X) := mem_normalizer_of_conjugate_eq' hLa
  have haO : a ∈ normalizer (O : Set X) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 ↥L) haL
  have hLO : ∀ l ∈ L, l ∈ normalizer (O : Set X) := fun l hl =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 ↥L)
      (le_normalizer hl)
  have hJa : ∀ j ∈ GSLit.fixedLayer J E, j * a = a * j := by
    intro j hj
    rw [hfix] at hj
    have := (mem_inf.mp ((map_subtype_le _) hj)).2
    exact mem_centralizer_singleton_iff.mp this
  have hLmul : (L : Set X) = (GSLit.fixedLayer J E : Set X) * (O : Set X) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ fun j hj => hLO j (hJL hj), hsup]
  have hcomm : ⁅V, zpowers a⁆ ≤ O := by
    rw [commutator_le]
    intro v hv w hw
    have hvL : v ∈ (L : Set X) := hVL hv
    rw [hLmul] at hvL
    obtain ⟨j, hj, o, ho, rfl⟩ := Set.mem_mul.mp hvL
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have hjk : j⁻¹ * (a ^ k)⁻¹ = (a ^ k)⁻¹ * j⁻¹ := by
      have h1 : Commute j (a ^ k) := Commute.zpow_right (hJa j hj) k
      rw [← mul_inv_rev, ← mul_inv_rev, h1.eq]
    have haOk : a ^ k ∈ normalizer (O : Set X) := zpow_mem haO k
    have h1 : a ^ k * o⁻¹ * (a ^ k)⁻¹ ∈ O := (mem_normalizer_iff.mp haOk _).mp (inv_mem ho)
    have h2 : o * (a ^ k * o⁻¹ * (a ^ k)⁻¹) ∈ O := mul_mem ho h1
    have h3 := (mem_normalizer_iff.mp (hLO j (hJL hj)) _).mp h2
    rw [commutatorElement_def]
    have e : j * o * a ^ k * (j * o)⁻¹ * (a ^ k)⁻¹ = j * (o * (a ^ k * o⁻¹ * (a ^ k)⁻¹)) * j⁻¹ :=
      calc j * o * a ^ k * (j * o)⁻¹ * (a ^ k)⁻¹ = j * o * a ^ k * o⁻¹ * (j⁻¹ * (a ^ k)⁻¹) := by
            group
        _ = j * o * a ^ k * o⁻¹ * ((a ^ k)⁻¹ * j⁻¹) := by rw [hjk]
        _ = j * (o * (a ^ k * o⁻¹ * (a ^ k)⁻¹)) * j⁻¹ := by group
    rw [e]
    exact h3
  intro heq
  have hJO : GSLit.fixedLayer J E ≤ O := hJV.trans (heq ▸ hcomm)
  have hLO' : L = O := by
    rw [← hsup]
    exact le_antisymm (sup_le hJO le_rfl) le_sup_right
  have hq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLN).1 hLpc).2.2
  have htop : pPrimeCore 2 ↥L = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (y : X) ∈ O := hLO' ▸ y.2
    obtain ⟨y', hy', hyy'⟩ := mem_map.mp hy
    have : y' = y := Subtype.ext hyy'
    exact this ▸ hy'
  obtain ⟨-, -, u, v, huv⟩ := hq
  apply huv
  have h1 : ∀ w : ↥L ⧸ pPrimeCore 2 ↥L, w = 1 := by
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    rw [QuotientGroup.eq_one_iff, htop]
    exact mem_top w
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  rw [h1 u, h1 v]

theorem Hyp52.exists_of_sameLex (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hCTI : LayerGeneratedUniversalComponentStandard) (hRS : RestrictedStandardInput)
    [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X) (h : Hyp52 X)
    (hmax : GSMaximalUnbalancingTriple h.a h.x h.J)
    (hiso : GSIsoAt h.a h.J)
    (hnB2a : ¬ ConclusionB2a h.a h.J) {B₂ : Subgroup X} (hB₂ : B₂ ≠ ⊥) (hB₂P : B₂ ≤ h.P)
    (hcard : Nat.card B₂ = Nat.card h.B)
    (hQ : Nat.card ↥(h.S ⊓ normalizer (B₂ : Set X)) = Nat.card ↥h.Q)
    (hbad : ∀ L : Subgroup X, ¬ IsoCorrSub h.a h.J B₂ L) :
    ∃ h₂ : Hyp52 X, h₂.a = h.a ∧ h₂.x = h.x ∧ h₂.J = h.J ∧ h₂.S = h.S ∧ h₂.B = B₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha := h.orderOf_a
  have hJa := h.J_le
  have hJpc := h.isPComponent_J
  have hSX := h.S_le
  have hSsyl := h.S_sylow
  have hQ' : Nat.card ↥(h.S ⊓ normalizer (B₂ : Set X)) =
      Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) := hQ
  set d : Subgroup X → ℕ := fun W =>
    Nat.card ((↥W ⧸ pPrimeCore 2 ↥W) ⧸ center (↥W ⧸ pPrimeCore 2 ↥W)) with hd
  have hA2 := actual_two_local_fixed_layer_orbits_of_inputs hS hU hheld hnonab hK ha hJa hJpc hSX
    hSsyl rfl
    (fun B => normalizer (B : Set X)) (fun B => oddCoreIn (normalizer (B : Set X)))
    (fun B => GSLit.fixedLayer h.J B)
    (fun B => GSLit.fixedLayer h.J B ⊔ oddCoreIn (normalizer (B : Set X)))
    (fun B => layerIn (normalizer (B : Set X)))
    (fun B => conjClosure (GSLit.fixedLayer h.J B) (layerIn (normalizer (B : Set X))))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    d (fun _ => rfl)
  have hbad₂ : d h.J < d (conjClosure (GSLit.fixedLayer h.J B₂)
      (layerIn (normalizer (B₂ : Set X)))) := by
    obtain ⟨-, -, -, -, -, -, -, ⟨M, hMH, hM, hMa, hVM, hVE, -, hdle, hdiff, hdeq, -, -⟩, -⟩ :=
      hA2.1 B₂ hB₂ hB₂P
    by_contra hnot
    have heq : d (conjClosure (GSLit.fixedLayer h.J B₂) (layerIn (normalizer (B₂ : Set X)))) =
        d h.J := le_antisymm (not_lt.mp hnot) hdle
    obtain ⟨hVpc, hTO, hTfix⟩ := hdeq heq
    obtain ⟨hMMa, -⟩ := hdiff.mp heq
    set V₂ := conjClosure (GSLit.fixedLayer h.J B₂) (layerIn (normalizer (B₂ : Set X)))
    have hVle : V₂ ≤ normalizer (B₂ : Set X) := hVE.trans (map_subtype_le _)
    have hVM' : V₂ = M := by rw [hVM, ← hMMa, sup_idem]
    have hVa : conjugate V₂ h.a = V₂ := by rw [hVM', ← hMMa]
    apply hbad V₂
    refine ⟨hVle, hVpc, hVa, ?_, hTfix⟩
    apply le_antisymm
    · refine sup_le (fun t ht => ?_) (map_subtype_le _)
      have h5 : t ∈ ((GSLit.fixedLayer h.J B₂ : Set X) *
          ((pPrimeCore 2 ↥V₂).map V₂.subtype : Set X)) :=
        ⟨t, ht, 1, one_mem _, mul_one t⟩
      rw [hTO] at h5
      exact h5
    · intro v hv
      have hv' : v ∈ (V₂ : Set X) := hv
      rw [← hTO] at hv'
      obtain ⟨t, ht, o, ho, rfl⟩ := hv'
      exact mul_mem (mem_sup_left ht) (mem_sup_right ho)
  have hlex : ∀ C : Subgroup X, C ≠ ⊥ → C ≤ h.S ⊓ coreActionKernel h.J →
      d h.J < d (conjClosure (GSLit.fixedLayer h.J C) (layerIn (normalizer (C : Set X)))) →
      Nat.card C < Nat.card B₂ ∨ (Nat.card C = Nat.card B₂ ∧
        Nat.card ↥(h.S ⊓ normalizer (C : Set X)) ≤
          Nat.card ↥(h.S ⊓ normalizer (B₂ : Set X))) := by
    intro C hC hCP hCbad
    by_contra hcon
    push Not at hcon
    obtain ⟨hle, hlt⟩ := hcon
    have hlex' : Nat.card h.B < Nat.card C ∨ (Nat.card C = Nat.card h.B ∧
        Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) <
          Nat.card ↥(h.S ⊓ normalizer (C : Set X))) := by
      rcases Nat.lt_or_ge (Nat.card B₂) (Nat.card C) with h1 | h1
      · left
        omega
      · right
        have hCeq : Nat.card C = Nat.card B₂ := le_antisymm h1 hle
        refine ⟨by omega, ?_⟩
        have := hlt hCeq
        rwa [hQ'] at this
    obtain ⟨L, hL⟩ := h.isoCorr_of_lt C hCP hlex'
    obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, -, -, hltiff, -⟩, -⟩ :=
      hA2.1 C hC hCP
    exact commutator_ne_of_isoCorrSub hL (hltiff.mp hCbad)
  have hb : ∃ b : X, orderOf b = 2 ∧ b ∈ h.S ⊓ coreActionKernel h.J ∧
      ∀ M : Subgroup X, ¬ UnbalancedGS.GSIsoCorr h.a h.J b M := by
    by_contra hcon
    push Not at hcon
    exact hnB2a (conclusionB2a_of_sylow hSsyl fun b hb hb2 => hcon b hb2 hb)
  have hJ2 : 2 ≤ pRank 2 ↥h.J := by
    have htype' : 2 ≤ pRank 2 ↥h.J ∨
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
          Assembly.LowTwoRank.StatedClassicalModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f) ∨
        Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin 7)) ∨
        Assembly.LowTwoRank.StatedClassicalModel (h.J ⧸ Open.fusionZStar h.J) .PSL 3 2 2 := by
      rcases h.smallType with h7 | ⟨p, f, hp, hp2, hf, -, hm⟩ | h34
      · exact Or.inr (Or.inr (Or.inl h7))
      · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, GSLit.statedClassicalModel_of_lieModel_psl_two hm⟩)
      · exact Or.inr (Or.inr (Or.inr (GSLit.statedClassicalModel_of_lieModel_psl_three h34)))
    rcases htype' with h2 | hsmall
    · exact h2
    let e : h.J ⧸ oddCore h.J ≃* h.J ⧸ pPrimeCore 2 h.J :=
      QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two h.J)
    have hq : IsQuasisimple (h.J ⧸ pPrimeCore 2 h.J) :=
      CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hJa)
        (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hJpc)
    have hA : IsQuasisimple (h.J ⧸ oddCore h.J) := LocalCores.isQuasisimple_of_mulEquiv e.symm hq
    refine UnbalancedGS.small_source_models_force_rank_at_least_two hA ?_
    rcases hsmall with ⟨p, f, hp, hp2, hf, hm⟩ | h7 | h34
    · exact Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf,
        SectionRank.statedClassicalModel_of_mulEquiv e hm⟩
    · obtain ⟨e7⟩ := h7
      exact Or.inr (Or.inl ⟨e.trans e7⟩)
    · exact Or.inr (Or.inr h34)
  obtain ⟨haH, h1, h2, ⟨⟨e, he⟩, h3⟩, h4⟩ :=
    critical_local_quotient_standard_component_at_of_inputs hS hU hheld hCTI hnonab hK ha hJa
      hJpc hSX hSsyl rfl
      (fun B => normalizer (B : Set X)) (fun B => oddCoreIn (normalizer (B : Set X)))
      (fun B => GSLit.fixedLayer h.J B)
      (fun B => GSLit.fixedLayer h.J B ⊔ oddCoreIn (normalizer (B : Set X)))
      (fun B => layerIn (normalizer (B : Set X)))
      (fun B => conjClosure (GSLit.fixedLayer h.J B) (layerIn (normalizer (B : Set X))))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      d (fun _ => rfl)
      (fun z hz hzP hzS => (sylow_fixed_core_of_central hmax hiso hSX hSsyl hz
        (mem_inf.mp hzP).1 (mem_inf.mp hzP).2 (fun s hs => mem_centralizer_iff.mp hzS s hs) _
        rfl).2)
      hb hJ2 B₂ hB₂ hB₂P hbad₂ hlex
  have horbit := orbitLayerStatement_of_inputs hS hU hheld X hnonab hK h.a h.J h.S ha hJa hJpc
    hSX hSsyl
  obtain ⟨h₂, h2a, h2J, h2S, h2x, h2B⟩ := hyp52_of_criticalAt hS hRS hnonab hK hmax hiso
    h.smallType hSX hSsyl h.x_mem horbit
    ⟨hmax.1, hB₂, hB₂P, haH, h1, h2, ⟨⟨e, he⟩, h3⟩, h4, fun Y _ ⟨φ⟩ => ⟨e.trans φ⟩⟩
  exact ⟨h₂, h2a, h2x, h2J, h2S, h2B⟩

end Assembly

end CFSG.ComponentClassification.GSThmB
