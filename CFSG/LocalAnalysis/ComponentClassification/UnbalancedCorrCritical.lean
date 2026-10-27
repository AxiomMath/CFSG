module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalGrowth
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalSylowRep

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

@[expose] def criticalOddTwoCore (Y : Type*) [Group Y] : Subgroup Y :=
  (pCore 2 (Y ⧸ pPrimeCore 2 Y)).comap (QuotientGroup.mk' (pPrimeCore 2 Y))

instance criticalOddTwoCore_normal (Y : Type*) [Group Y] : (criticalOddTwoCore Y).Normal := by
  unfold criticalOddTwoCore
  infer_instance

variable {G : Type} [Group G] [Finite G]

theorem commutator_map_sup_eq_bot_of_solvable {H M₁ M₂ : Subgroup G} (hM₁H : M₁ ≤ H)
    (hM₁ : IsPComponent 2 (M₁.subgroupOf H)) (hM₂H : M₂ ≤ H)
    (hM₂ : IsPComponent 2 (M₂.subgroupOf H)) {Y : Subgroup (↥H ⧸ pPrimeCore 2 ↥H)}
    (hYn : Y.Normal) (hYs : Group.IsSolvable ↥Y) :
    ⁅((M₁ ⊔ M₂).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)), Y⁆ = ⊥ := by
  obtain ⟨K₁, hK₁, -, hmap₁, -⟩ := id hM₁
  obtain ⟨K₂, hK₂, -, hmap₂, -⟩ := id hM₂
  have hc := (LocalCores.component_solvable_centralizer hYs hYn.isSubnormal).1
  have h1 := hc K₁ hK₁
  have h2 := hc K₂ hK₂
  rw [subgroupOf_sup hM₁H hM₂H, Subgroup.map_sup, hmap₁, hmap₂]
  rw [commutator_eq_bot_iff_le_centralizer] at h1 h2 ⊢
  exact sup_le h1 h2

omit [Finite G] in
theorem commutator_le_of_map_eq_bot {H V K : Subgroup G} (hVH : V ≤ H) (hKH : K ≤ H)
    (h : ⁅(V.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)),
      (K.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H))⁆ = ⊥) :
    ⁅V, K⁆ ≤ (pPrimeCore 2 ↥H).map H.subtype := by
  rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  have h1 := map_mono (f := H.subtype) h
  rwa [map_commutator, map_subgroupOf_eq_of_le hVH, map_subgroupOf_eq_of_le hKH] at h1

omit [Finite G] in
theorem le_coreActionKernel_of_commutator_le {O V K : Subgroup G}
    (hKV : K ≤ normalizer (V : Set G)) (hOV : (pPrimeCore 2 ↥V).map V.subtype = V ⊓ O)
    (hc : ⁅V, K⁆ ≤ O) : K ≤ UnbalancedLayer.coreActionKernel V := by
  intro k hk
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨hKV hk, fun v hv => ?_⟩
  rw [hOV]
  refine mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : k⁻¹ * v * k ∈ V := by
      have h2 := (mem_normalizer_iff.mp (inv_mem (hKV hk)) v).mp hv
      rwa [inv_inv] at h2
    rw [show v⁻¹ * k⁻¹ * v * k = v⁻¹ * (k⁻¹ * v * k) by group]
    exact mul_mem (inv_mem hv) h1
  · have h1 := hc (commutator_mem_commutator (inv_mem hv) (inv_mem hk))
    rwa [commutatorElement_def, inv_inv, inv_inv] at h1

omit [Finite G] in
theorem conj_mem_sup_of_commutator {U R : Subgroup G} {h : G}
    (hU : ∀ u ∈ U, u⁻¹ * h * u * h⁻¹ ∈ R) (hR : h ∈ normalizer (R : Set G)) :
    ∀ y ∈ U ⊔ R, h * y * h⁻¹ ∈ U ⊔ R := by
  intro y hy
  have hmap : (U ⊔ R).map (MulAut.conj h).toMonoidHom ≤ U ⊔ R := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      have h2 : (MulAut.conj h).toMonoidHom u = u * (u⁻¹ * h * u * h⁻¹) := by
        show h * u * h⁻¹ = _
        group
      rw [h2]
      exact mul_mem (mem_sup_left hu) (mem_sup_right (hU u hu))
    · rintro _ ⟨r, hr, rfl⟩
      exact mem_sup_right ((mem_normalizer_iff.mp hR r).mp hr)
  exact hmap ⟨y, hy, rfl⟩

theorem commutator_map_eq_bot_of_ne {H : Type*} [Group H] [Finite H] {K₁ K₂ : Subgroup H}
    (h₁ : IsPComponent 2 K₁) (h₂ : IsPComponent 2 K₂) (hne : K₁ ≠ K₂) :
    ⁅K₁.map (QuotientGroup.mk' (pPrimeCore 2 H)), K₂.map (QuotientGroup.mk' (pPrimeCore 2 H))⁆ =
      ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hc, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two K₁ K₂ h₁ h₂).2 hne
  have hO : (pPrimeCore 2 ↥K₁).map K₁.subtype ≤ pPrimeCore 2 H := by
    obtain ⟨-, -, hs, -, -⟩ := id h₁
    rw [map_pPrimeCore_eq_inf_of_isSubnormal hs]
    exact inf_le_right
  rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact (hc.trans inf_le_left).trans hO

omit [Finite G] in
theorem isSimpleGroup_of_surjective_ker_eq_center {A Y : Type*} [Group A] [Group Y]
    (hA : IsQuasisimple A) (f : A →* Y) (hf : Function.Surjective f) (hker : f.ker = center A) :
    IsSimpleGroup Y ∧ ∃ x y : Y, x * y ≠ y * x := by
  have e : A ⧸ center A ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have : IsSimpleGroup (A ⧸ center A) := hA.2.1
  have hs : IsSimpleGroup Y := e.symm.isSimpleGroup
  refine ⟨hs, ?_⟩
  obtain ⟨x, y, hxy⟩ := hA.2.2
  refine ⟨e x, e y, fun h => hxy ?_⟩
  apply e.injective
  rw [map_mul, map_mul, h]

theorem critical_two_subgroup_full_layer_and_odd_two_core_of_inputs
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
    (H R T X E V : Subgroup G → Subgroup G) (hH : ∀ B, H B = normalizer (B : Set G))
    (hR : ∀ B, R B = (pPrimeCore 2 ↥(H B)).map (H B).subtype)
    (hT : ∀ B, T B = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hX : ∀ B, X B = T B ⊔ R B) (hE : ∀ B, E B = (pLayer ↥(H B) 2).map (H B).subtype)
    (hV : ∀ B, V B = ⨆ e ∈ E B, conjugate (T B) e) (d : Subgroup G → ℕ)
    (hd : ∀ W : Subgroup G,
      d W = Nat.card ((↥W ⧸ pPrimeCore 2 ↥W) ⧸ center (↥W ⧸ pPrimeCore 2 ↥W)))
    (hz : ∀ z : G, orderOf z = 2 → z ∈ P → z ∈ centralizer (S : Set G) →
      ∃ P₀ : Sylow 2 ↥(centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G)),
        (P₀ : Subgroup _) =
          S.subgroupOf (centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G)))
    (hb : ∃ b : G, orderOf b = 2 ∧ b ∈ P ∧ ∀ M : Subgroup G, ¬ UnbalancedGS.GSIsoCorr a J b M) :
    (∃ B : Subgroup G, B ≠ ⊥ ∧ B ≤ P ∧ d J < d (V B)) ∧
    ∀ B : Subgroup G, B ≠ ⊥ → B ≤ P → d J < d (V B) →
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ P → d J < d (V C) →
        Nat.card C < Nat.card B ∨ (Nat.card C = Nat.card B ∧
          Nat.card ↥(S ⊓ normalizer (C : Set G)) ≤ Nat.card ↥(S ⊓ normalizer (B : Set G)))) →
      (S ⊓ normalizer (B : Set G) ≤ normalizer (B : Set G) ⊓ normalizer (X B : Set G) ∧
        ∃ P₀ : Sylow 2 ↥(normalizer (B : Set G) ⊓ normalizer (X B : Set G)),
          (P₀ : Subgroup _) = (S ⊓ normalizer (B : Set G)).subgroupOf
            (normalizer (B : Set G) ⊓ normalizer (X B : Set G))) ∧
      V B = E B ∧ ⁅V B, zpowers a⁆ = V B ∧
      B ≤ H B ⊓ UnbalancedLayer.coreActionKernel (V B) ∧
      (∃ P₀ : Sylow 2 ↥(H B ⊓ UnbalancedLayer.coreActionKernel (V B)),
        (P₀ : Subgroup _) = B.subgroupOf (H B ⊓ UnbalancedLayer.coreActionKernel (V B))) ∧
      (criticalOddTwoCore ↥(H B)).map (H B).subtype = R B ⊔ B ∧ R B ⊓ B = ⊥ ∧ ⁅R B, B⁆ = ⊥ ∧
      a ∉ (criticalOddTwoCore ↥(H B)).map (H B).subtype ∧
      V B ⊓ (criticalOddTwoCore ↥(H B)).map (H B).subtype =
        (CFSG.Open.fusionZStar ↥(V B)).map (V B).subtype ∧
      ((IsSimpleGroup ↥(((V B).subgroupOf (H B)).map
          (QuotientGroup.mk' (criticalOddTwoCore ↥(H B)))) ∧
        ∃ x y : ↥(((V B).subgroupOf (H B)).map (QuotientGroup.mk' (criticalOddTwoCore ↥(H B)))),
          x * y ≠ y * x) ∨
       ∃ L₁ L₂ : Subgroup (↥(H B) ⧸ criticalOddTwoCore ↥(H B)),
        (IsSimpleGroup ↥L₁ ∧ ∃ x y : ↥L₁, x * y ≠ y * x) ∧
        (IsSimpleGroup ↥L₂ ∧ ∃ x y : ↥L₂, x * y ≠ y * x) ∧ ⁅L₁, L₂⁆ = ⊥ ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₁ ⊔ L₂ = ((V B).subgroupOf (H B)).map (QuotientGroup.mk' (criticalOddTwoCore ↥(H B)))) ∧
      ∀ C : Subgroup G, C ≠ ⊥ → C ≤ P →
        (Nat.card B < Nat.card C ∨ (Nat.card B = Nat.card C ∧
          Nat.card ↥(S ⊓ normalizer (B : Set G)) < Nat.card ↥(S ⊓ normalizer (C : Set G)))) →
        V C ≤ H C ∧ IsPComponent 2 ((V C).subgroupOf (H C)) ∧ conjugate (V C) a = V C ∧
          (T C : Set G) * ((pPrimeCore 2 ↥(V C)).map (V C).subtype : Set G) = V C ∧
          T C = UnbalancedGS.gsFixedLayer (V C) a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 (S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
      hP₀ ▸ P₀.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hSX)
  have hA2 := actual_two_local_fixed_layer_orbits_of_inputs hS hU hheld hnonab hK ha hJa hJ hSX
    hSsyl hP H R T X E V hH hR hT hX hE hV d hd
  have hA4 := two_local_pair_full_sylow_representative_of_inputs hS hU hheld hnonab hK ha hJa hJ
    hSX hSsyl hP H R T X hH hR hT hX hz
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨b, hb2, hbP, hbno⟩ := hb
    have hb1 : zpowers b ≠ ⊥ := by
      rw [Ne, zpowers_eq_bot]
      intro h
      rw [h, orderOf_one] at hb2
      exact absurd hb2 (by norm_num)
    obtain ⟨-, -, -, -, -, -, -, ⟨M, -, -, -, -, -, -, hdle, -, -, -, hiso⟩, -⟩ :=
      hA2.1 (zpowers b) hb1 (zpowers_le.mpr hbP)
    exact ⟨zpowers b, hb1, zpowers_le.mpr hbP,
      lt_of_le_of_ne hdle fun h => hbno _ (hiso b rfl hb2 h.symm)⟩
  intro B hB1 hBP hbad hmax
  obtain ⟨-, -, -, -, hTaH, hpcT, hTE, ⟨M, hMH, hM, hMa, hVM, hVE, hVEn, hdle, hdeq, hdeqc, hdlt,
    -⟩, hOX, -, hQact, hNV⟩ := hA2.1 B hB1 hBP
  have hVa : ⁅V B, zpowers a⁆ = V B := hdlt.mp hbad
  have hRf : ∀ C : Subgroup G, R C = (pPrimeCore 2 ↥(normalizer (C : Set G))).map
      (normalizer (C : Set G)).subtype := fun C => by rw [hR, hH]
  have hBP' : B ≤ S ⊓ UnbalancedLayer.coreActionKernel J := hBP.trans hP.le
  have hB2 : IsPGroup 2 B := hS2.to_le (hBP'.trans inf_le_left)
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  set HB := H B with hHBdef
  set VB := V B with hVBdef
  set RB := R B with hRBdef
  set Q := S ⊓ normalizer (B : Set G) with hQdef
  set L := normalizer (B : Set G) ⊓ normalizer (X B : Set G) with hLdef
  set D := HB ⊓ UnbalancedLayer.coreActionKernel VB with hDdef
  have hHB : HB = normalizer (B : Set G) := hH B
  have hBH : B ≤ HB := hHB ▸ le_normalizer
  have hEB : E B = (pLayer ↥HB 2).map HB.subtype := hE B
  have hVE' : VB ≤ (pLayer ↥HB 2).map HB.subtype := hEB ▸ hVE
  have hEV : (pLayer ↥HB 2).map HB.subtype ≤ normalizer (VB : Set G) :=
    hEB ▸ (normal_subgroupOf_iff_le_normalizer hVE).mp hVEn
  have hVH : VB ≤ HB := hVE'.trans (map_subtype_le _)
  have hVsub : (VB.subgroupOf HB).IsSubnormal := isSubnormal_of_le_pLayer hVE' hEV
  have hOV : (pPrimeCore 2 ↥VB).map VB.subtype = VB ⊓ RB := by
    rw [hRBdef, hR B]
    exact map_pPrimeCore_eq_inf_of_subgroupOf hVH hVsub
  have hMaH : conjugate M a ≤ HB := by
    have h1 := hVH
    rw [hVM] at h1
    exact le_sup_right.trans h1
  have hRBH : RB ≤ HB := by rw [hRBdef, hR B]; exact map_subtype_le _
  have hHR : HB ≤ normalizer (RB : Set G) := by
    rw [hRBdef, hR B]
    exact nested_le_normalizer_map_pPrimeCore HB
  have hRodd : Nat.Coprime 2 (Nat.card RB) := by
    rw [hRBdef, hR B, card_map_of_injective (subtype_injective _)]
    exact pPrimeCore_coprime_card
  have hTB : T B ≤ J ⊓ centralizer (B : Set G) := by rw [hT B]; exact map_subtype_le _
  have hTV : T B ≤ VB := by
    obtain ⟨-, -, h, -, -, -⟩ := two_local_conj_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2
      hB1 hBP' (hT B) (hRf B) (hX B) (by rw [hE, hH]) (hV B)
    exact h
  have hQL : Q ≤ L := fun q hq => mem_inf.mpr ⟨(mem_inf.mp hq).2, (hQact q hq).1⟩
  have hQsyl : ∃ P₀ : Sylow 2 ↥L, (P₀ : Subgroup ↥L) = Q.subgroupOf L := by
    obtain ⟨g, hg1, hg2, hg3, hg4, ⟨P₁, hP₁⟩⟩ := hA4 B hB1 hBP
    have hcardB' : Nat.card ↥(conjugate B g) = Nat.card B :=
      card_map_of_injective (MulAut.conj g⁻¹).injective
    have hB'1 : conjugate B g ≠ ⊥ := by
      intro h
      apply hB1
      rw [← Subgroup.card_eq_one, ← hcardB', h, Subgroup.card_bot]
    obtain ⟨-, hdg⟩ := hA2.2 B (conjugate B g) g hB1 hBP rfl hg1 hg2
    have hbad' : d J < d (V (conjugate B g)) := hdg ▸ hbad
    have hNS : Nat.card ↥(S ⊓ normalizer (conjugate B g : Set G)) = Nat.card ↥Q := by
      rcases hmax (conjugate B g) hB'1 hg1 hbad' with h | ⟨-, h⟩
      · omega
      · exact le_antisymm h hg3
    have hL' : normalizer (conjugate B g : Set G) ⊓ normalizer (X (conjugate B g) : Set G) =
        conjugate L g := by
      rw [← hg2, ← conjugate_normalizer, ← conjugate_normalizer]
      exact (Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective).symm
    have hcardL : Nat.card ↥(normalizer (conjugate B g : Set G) ⊓
        normalizer (X (conjugate B g) : Set G)) = Nat.card ↥L := by
      rw [hL']
      exact card_map_of_injective (MulAut.conj g⁻¹).injective
    have h1 := Sylow.card_eq_multiplicity P₁
    have h2 : Nat.card ↥(P₁ : Subgroup ↥(normalizer (conjugate B g : Set G) ⊓
        normalizer (X (conjugate B g) : Set G))) =
        Nat.card ↥(S ⊓ normalizer (conjugate B g : Set G)) := by
      rw [hP₁]
      exact Nat.card_congr (subgroupOfEquivOfLe hg4).toEquiv
    apply exists_sylow_of_card_eq hQL
    rw [← hNS, ← h2, h1, hcardL]
  have hBX : B ≤ normalizer (X B : Set G) := by
    intro b hb
    rw [hX B]
    refine mem_normalizer_sup ?_ (hHR (hBH hb))
    apply centralizer_le_normalizer' (T B)
    rw [mem_centralizer_iff]
    intro t ht
    exact (mem_centralizer_iff.mp (hTB ht).2 b hb).symm
  have hBV : B ≤ normalizer (VB : Set G) := fun b hb => hNV b (mem_inf.mpr ⟨hBH hb, hBX hb⟩)
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥HB) with hπdef
  have hVsup : VB.subgroupOf HB = (M ⊔ conjugate M a).subgroupOf HB := by rw [hVM]
  have hcommBot : ∀ {Y : Subgroup (↥HB ⧸ pPrimeCore 2 ↥HB)}, Y.Normal → Group.IsSolvable ↥Y →
      ⁅(VB.subgroupOf HB).map π, Y⁆ = ⊥ := by
    intro Y hYn hYs
    rw [hVsup]
    exact commutator_map_sup_eq_bot_of_solvable hMH hM hMaH hMa hYn hYs
  have hBn : (B.subgroupOf HB).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBH).mpr hHB.le
  have hBbs : Group.IsSolvable ↥((B.subgroupOf HB).map π) := by
    have h1 : IsPGroup 2 ((B.subgroupOf HB).map π) :=
      (hB2.comap_of_injective HB.subtype HB.subtype_injective).map π
    have : Group.IsNilpotent ↥((B.subgroupOf HB).map π) := h1.isNilpotent
    infer_instance
  have hVBc : ⁅VB, B⁆ ≤ RB := by
    rw [hRBdef, hR B]
    exact commutator_le_of_map_eq_bot hVH hBH
      (hcommBot (hBn.map π (QuotientGroup.mk'_surjective _)) hBbs)
  have hBD : B ≤ D :=
    le_inf hBH (le_coreActionKernel_of_commutator_le hBV hOV hVBc)
  have hQV : Q ≤ normalizer (VB : Set G) := fun q hq =>
    hNV q (mem_inf.mpr ⟨hHB ▸ (mem_inf.mp hq).2, (hQact q hq).1⟩)
  have hQDP : Q ⊓ D ≤ P := by
    intro t ht
    obtain ⟨htQ, htD⟩ := mem_inf.mp ht
    obtain ⟨htH, htK⟩ := mem_inf.mp htD
    have htriv : ∀ x ∈ X B, x⁻¹ * t⁻¹ * x * t ∈ (pPrimeCore 2 ↥(X B)).map (X B).subtype := by
      intro x hx
      rw [hX B, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (T B) RB
        ((hTV.trans hVH).trans hHR)] at hx
      obtain ⟨u, hu, r, hr, rfl⟩ := Set.mem_mul.mp hx
      rw [hOX]
      apply mem_sup_left
      have hcu : u⁻¹ * t⁻¹ * u * t ∈ RB := by
        have h1 := (UnbalancedLayer.mem_coreActionKernel.mp htK).2 u (hTV hu)
        rw [hOV] at h1
        exact (mem_inf.mp h1).2
      have htr : t⁻¹ * r * t ∈ RB := by
        have h1 := (mem_normalizer_iff.mp (inv_mem (hHR htH)) r).mp hr
        rwa [inv_inv] at h1
      rw [show (u * r)⁻¹ * t⁻¹ * (u * r) * t = r⁻¹ * (u⁻¹ * t⁻¹ * u * t) * (t⁻¹ * r * t) by group]
      exact mul_mem (mul_mem (inv_mem hr) hcu) htr
    exact (mem_inf.mp (((hQact t htQ).2.2).mp htriv)).1
  have hBQ : B ≤ Q := le_inf (hBP'.trans inf_le_left) le_normalizer
  have hBQD : B ≤ Q ⊓ D := le_inf hBQ hBD
  have hQDeq : Q ⊓ D = B := by
    by_contra hne
    have hlt : B < Q ⊓ D := lt_of_le_of_ne hBQD (Ne.symm hne)
    have hgrow := critical_growth_le hS hU hheld hnonab hK ha hJa hJ hSX hSsyl hP H R T X E V
      hH hR hT hX hE hV d hd hB1 hBQD hQDP (inf_le_left.trans hQV)
      (inf_le_right.trans inf_le_right)
    have hbadT : d J < d (V (Q ⊓ D)) := lt_of_lt_of_le hbad hgrow
    have hQD1 : Q ⊓ D ≠ ⊥ := fun h => hB1 (le_bot_iff.mp (h ▸ hBQD))
    have hcard := card_lt_of_lt hlt
    rcases hmax (Q ⊓ D) hQD1 hQDP hbadT with h | ⟨h, -⟩
    · omega
    · omega
  have hDL : D ≤ L := by
    intro h hh
    obtain ⟨hhH, hhK⟩ := mem_inf.mp hh
    refine mem_inf.mpr ⟨hHB ▸ hhH, ?_⟩
    apply mem_normalizer_of_forall_conj_mem
    intro x hx
    rw [hX B] at hx ⊢
    refine conj_mem_sup_of_commutator (fun u hu => ?_) (hHR hhH) x hx
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hhK)).2 u (hTV hu)
    rw [inv_inv, hOV] at h1
    exact (mem_inf.mp h1).2
  have hLD : L ≤ normalizer (D : Set G) := by
    intro g hg
    obtain ⟨hgB, hgX⟩ := mem_inf.mp hg
    have hgH : g ∈ HB := hHB ▸ hgB
    have hgV : g ∈ normalizer (VB : Set G) := hNV g (mem_inf.mpr ⟨hgH, hgX⟩)
    exact UnbalancedLayer.normalizer_inf_mem (le_normalizer hgH)
      (UnbalancedLayer.normalizer_le_normalizer_coreActionKernel VB hgV)
  have hBsylD : ∃ P₀ : Sylow 2 ↥D, (P₀ : Subgroup ↥D) = B.subgroupOf D := by
    obtain ⟨Ps, hPs⟩ := (hB2.comap_of_injective D.subtype D.subtype_injective).exists_le_sylow
    refine ⟨Ps, ?_⟩
    set PsG := (Ps : Subgroup ↥D).map D.subtype with hPsGdef
    have hPsG2 : IsPGroup 2 PsG := Ps.isPGroup'.map _
    have hPsGL : PsG ≤ L := (map_subtype_le _).trans hDL
    obtain ⟨c, hcL, hcQ⟩ := UnbalancedLayer.exists_conjugate_le_of_sylow hQsyl hPsGL hPsG2
    have hcD : conjugate PsG c ≤ D := by
      have h1 : conjugate D c = D := UnbalancedLayer.conjugate_eq_of_mem_normalizer (hLD hcL)
      rw [← h1]
      exact map_mono (map_subtype_le _)
    have hle : conjugate PsG c ≤ B := hQDeq ▸ le_inf hcQ hcD
    have hcard : Nat.card ↥PsG ≤ Nat.card ↥B := by
      have h1 := Subgroup.card_le_of_le hle
      rwa [show Nat.card ↥(conjugate PsG c) = Nat.card ↥PsG from
        card_map_of_injective (MulAut.conj c⁻¹).injective] at h1
    have hcard' : Nat.card ↥(Ps : Subgroup ↥D) ≤ Nat.card ↥(B.subgroupOf D) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBD).toEquiv]
      rwa [hPsGdef, card_map_of_injective D.subtype_injective] at hcard
    exact (Subgroup.eq_of_le_of_card_ge hPs hcard').symm
  have hBDn : (B.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBD).mpr (inf_le_left.trans hHB.le)
  have hDBodd : Odd (Nat.card (↥D ⧸ B.subgroupOf D)) := by
    obtain ⟨P₀, hP₀⟩ := hBsylD
    have h1 : Nat.card ↥D = Nat.card (↥D ⧸ B.subgroupOf D) * Nat.card ↥(B.subgroupOf D) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    set v := (Nat.card ↥D).factorization 2 with hvdef
    have h2 : Nat.card ↥(B.subgroupOf D) = 2 ^ v := by
      rw [← hP₀]
      exact Sylow.card_eq_multiplicity P₀
    have h1' : Nat.card ↥D = Nat.card (↥D ⧸ B.subgroupOf D) * 2 ^ v := by
      rw [← h2]
      exact h1
    have h3 : Nat.card (↥D ⧸ B.subgroupOf D) = Nat.card ↥D / 2 ^ v :=
      (Nat.div_eq_of_eq_mul_left (pow_pos two_pos v) h1').symm
    have h4 := Nat.coprime_ordCompl Nat.prime_two (Nat.card_pos (α := ↥D)).ne'
    rw [h3]
    exact Nat.coprime_two_left.mp h4
  have hDsolv : Group.IsSolvable ↥D := by
    have : Group.IsSolvable (↥D ⧸ B.subgroupOf D) := CFSG.Milestones.odd_order_solvable hDBodd
    have hB2' : IsPGroup 2 ↥(B.subgroupOf D) :=
      hB2.comap_of_injective D.subtype D.subtype_injective
    have : Group.IsNilpotent ↥(B.subgroupOf D) := hB2'.isNilpotent
    exact Group.isSolvable_of_subgroup_quotient (B.subgroupOf D)
  have hEVeq : E B = VB := by
    apply le_antisymm _ hVE
    rw [hEB, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K' hK' => ?_
    by_cases h1 : K' = M.subgroupOf HB
    · rw [h1]
      intro x hx
      rw [mem_comap, hVM]
      exact mem_sup_left (mem_subgroupOf.mp hx)
    by_cases h2 : K' = (conjugate M a).subgroupOf HB
    · rw [h2]
      intro x hx
      rw [mem_comap, hVM]
      exact mem_sup_right (mem_subgroupOf.mp hx)
    exfalso
    set K := K'.map HB.subtype with hKdef
    have hKK' : K.subgroupOf HB = K' := comap_map_eq_self_of_injective HB.subtype_injective K'
    have hKH : K ≤ HB := map_subtype_le _
    have hKpc : IsPComponent 2 (K.subgroupOf HB) := hKK' ▸ hK'
    have hc1 := commutator_map_eq_bot_of_ne hM hK' (Ne.symm h1)
    have hc2 := commutator_map_eq_bot_of_ne hMa hK' (Ne.symm h2)
    have hcV : ⁅(VB.subgroupOf HB).map π, (K.subgroupOf HB).map π⁆ = ⊥ := by
      rw [hKK', hVsup, subgroupOf_sup hMH hMaH, Subgroup.map_sup]
      rw [commutator_eq_bot_iff_le_centralizer] at hc1 hc2 ⊢
      exact sup_le hc1 hc2
    have hKc : ⁅VB, K⁆ ≤ RB := by
      rw [hRBdef, hR B]
      exact commutator_le_of_map_eq_bot hVH hKH hcV
    have hKE : K ≤ (pLayer ↥HB 2).map HB.subtype := map_mono (le_sSup hK')
    have hKD : K ≤ D :=
      le_inf hKH (le_coreActionKernel_of_commutator_le (hKE.trans hEV) hOV hKc)
    have hKs : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKD)
    have hKbot := eq_bot_of_commutator_eq_of_isSolvable (commutator_eq_of_isPComponent hKH hKpc)
      hKs
    have hcop : Nat.Coprime 2 (Nat.card (⊥ : Subgroup G)) := by
      rw [card_bot]
      exact Nat.coprime_one_right 2
    exact not_le_of_isPComponent_of_coprime hKH hKpc hcop hKbot.le
  have hHV : HB ≤ normalizer (VB : Set G) := by
    rw [← hEVeq, hEB]
    have : (pLayer ↥HB 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    intro h hh
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic HB (pLayer ↥HB 2)
      (le_normalizer hh)
  set K₂ := criticalOddTwoCore ↥HB with hK₂def
  set N := K₂.map HB.subtype with hNdef
  have hObn : (pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB)).Normal := inferInstance
  have hObs : Group.IsSolvable ↥(pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB)) := by
    have : Group.IsNilpotent ↥(pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB)) := pCore_isNilpotent
    infer_instance
  have hK₂map : K₂.map π = pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hNK : N.subgroupOf HB = K₂ := comap_map_eq_self_of_injective HB.subtype_injective K₂
  have hNH : N ≤ HB := map_subtype_le _
  have hcent : ⁅(VB.subgroupOf HB).map π, pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB)⁆ = ⊥ :=
    hcommBot hObn hObs
  have hND : N ≤ D := by
    have hcN : ⁅(VB.subgroupOf HB).map π, (N.subgroupOf HB).map π⁆ = ⊥ := by
      rw [hNK, hK₂map]
      exact hcent
    have hNc : ⁅VB, N⁆ ≤ RB := by
      rw [hRBdef, hR B]
      exact commutator_le_of_map_eq_bot hVH hNH hcN
    exact le_inf hNH (le_coreActionKernel_of_commutator_le (hNH.trans hHV) hOV hNc)
  have hRN : RB ≤ N := by
    intro r hr
    rw [hRBdef, hR B] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    refine ⟨r', ?_, rfl⟩
    show π r' ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB)
    rw [show π r' = 1 from (QuotientGroup.eq_one_iff r').mpr hr']
    exact one_mem _
  have hBN : B ≤ N := by
    intro b hb
    refine ⟨⟨b, hBH hb⟩, ?_, rfl⟩
    show π ⟨b, hBH hb⟩ ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB)
    have hBb2 : IsPGroup 2 ((B.subgroupOf HB).map π) :=
      (hB2.comap_of_injective HB.subtype HB.subtype_injective).map π
    have hle : (B.subgroupOf HB).map π ≤ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB) :=
      le_sSup ⟨hBn.map π (QuotientGroup.mk'_surjective _), hBb2⟩
    exact hle (mem_map_of_mem π (show (⟨b, hBH hb⟩ : HB) ∈ B.subgroupOf HB from hb))
  have hNRB : N ≤ RB ⊔ B := by
    have hidxR : ∃ k : ℕ, RB.relIndex N = 2 ^ k := by
      let ψ : ↥N →* ↥HB ⧸ pPrimeCore 2 ↥HB := π.comp (inclusion hNH)
      have hkerψ : ψ.ker = RB.subgroupOf N := by
        ext x
        rw [MonoidHom.mem_ker, mem_subgroupOf]
        show π (inclusion hNH x) = 1 ↔ (x : G) ∈ RB
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRBdef, hR B]
        constructor
        · intro h
          exact ⟨_, h, rfl⟩
        · rintro ⟨y, hy, hyx⟩
          have hyx' : y = inclusion hNH x := Subtype.ext hyx
          rwa [← hyx']
      have hrange : ψ.range ≤ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB) := by
        rintro _ ⟨x, rfl⟩
        obtain ⟨y, hy, hyx⟩ := x.2
        have hxy : inclusion hNH x = y := Subtype.ext hyx.symm
        show π (inclusion hNH x) ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB)
        rw [hxy]
        exact hy
      have h2 : IsPGroup 2 ψ.range := pCore_isPGroup.to_le hrange
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      refine ⟨k, ?_⟩
      rw [Subgroup.relIndex, ← hkerψ, index_ker, hk]
    obtain ⟨k, hk⟩ := hidxR
    have hBodd : Odd (B.relIndex N) := by
      have h1 := Subgroup.relIndex_mul_relIndex B N D hBN hND
      have h2 : Odd (B.relIndex D) := hDBodd
      rw [← h1] at h2
      exact (Nat.odd_mul.mp h2).1
    have hd1 : (RB ⊔ B).relIndex N ∣ RB.relIndex N :=
      Subgroup.relIndex_dvd_of_le_left (L := N) le_sup_left
    have hd2 : (RB ⊔ B).relIndex N ∣ B.relIndex N :=
      Subgroup.relIndex_dvd_of_le_left (L := N) le_sup_right
    rw [hk] at hd1
    obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
    have hodd' : Odd ((RB ⊔ B).relIndex N) := Odd.of_dvd_nat hBodd hd2
    have hj0 : j = 0 := by
      by_contra hj0
      rw [hj'] at hodd'
      exact (Nat.not_odd_iff_even.mpr ((Nat.even_pow' hj0).mpr even_two)) hodd'
    rw [hj0, pow_zero] at hj'
    exact Subgroup.relIndex_eq_one.mp hj'
  have hNeq : N = RB ⊔ B := le_antisymm hNRB (sup_le hRN hBN)
  have hRBbot : RB ⊓ B = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup_two hB2 hRodd
  have hRBc : ⁅RB, B⁆ = ⊥ := by
    have h1 : ⁅RB, B⁆ ≤ RB := UnbalancedLayer.commutator_le_left_of_le_normalizer (hBH.trans hHR)
    have h2 : ⁅RB, B⁆ ≤ B := by
      rw [commutator_comm]
      exact UnbalancedLayer.commutator_le_left_of_le_normalizer (hRBH.trans hHB.le)
    rw [← le_bot_iff, ← hRBbot]
    exact le_inf h1 h2
  have hMV : M ≤ VB := hVM ▸ le_sup_left
  have hOVodd : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥VB).map VB.subtype)) := by
    rw [card_map_of_injective (subtype_injective _)]
    exact pPrimeCore_coprime_card
  have haN : a ∉ N := by
    intro haN
    have haD := hND haN
    have hle : ⁅VB, zpowers a⁆ ≤ (pPrimeCore 2 ↥VB).map VB.subtype := by
      rw [commutator_le]
      intro v hv x hx
      have hxK : x ∈ UnbalancedLayer.coreActionKernel VB :=
        (zpowers_le.mpr (mem_inf.mp haD).2) hx
      have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hxK)).2 _ (inv_mem hv)
      rw [inv_inv, inv_inv] at h1
      rwa [commutatorElement_def]
    rw [hVa] at hle
    exact not_le_of_isPComponent_of_coprime hMH hM hOVodd (hMV.trans hle)
  set Ub := (VB.subgroupOf HB).map π with hUbdef
  have hUbn : Ub.Normal :=
    ((normal_subgroupOf_iff_le_normalizer hVH).mpr hHV).map π (QuotientGroup.mk'_surjective _)
  set Zb := (center ↥Ub).map Ub.subtype with hZbdef
  have hZbn : Zb.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff]
    have h1 := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Ub (center ↥Ub)
    rw [normalizer_eq_top_iff.mpr hUbn] at h1
    exact h1
  have hZbc : ∀ x ∈ Zb, ∀ y ∈ Zb, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, -, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hx y).symm
  have hZb2 : IsPGroup 2 Zb :=
    isPGroup_two_of_abelian_normal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hZbn hZbc
  have hZbO : Zb ≤ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB) := le_sSup ⟨hZbn, hZb2⟩
  have hOc : ∀ x ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB), ∀ y ∈ Ub, y * x = x * y := by
    intro x hx y hy
    have h1 := commutator_mem_commutator hy hx
    rw [hcent, mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hcomm_iff : ∀ v ∈ VB, (∀ w ∈ VB, (w * v)⁻¹ * (v * w) ∈ RB) ↔ v ∈ N := by
    intro v hv
    have hvH := hVH hv
    have hvU : π ⟨v, hvH⟩ ∈ Ub :=
      mem_map_of_mem π (show (⟨v, hvH⟩ : HB) ∈ VB.subgroupOf HB from hv)
    have hcomm : ∀ w : HB, (w : G) ∈ VB → (π w * π ⟨v, hvH⟩ = π ⟨v, hvH⟩ * π w ↔
        ((w : G) * v)⁻¹ * (v * w) ∈ RB) := by
      intro w hw
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, hRBdef, hR B]
      constructor
      · intro h
        exact ⟨_, h, rfl⟩
      · rintro ⟨y, hy, hyeq⟩
        have hyeq' : y = (w * ⟨v, hvH⟩)⁻¹ * (⟨v, hvH⟩ * w) := Subtype.ext hyeq
        rwa [← hyeq']
    constructor
    · intro h
      have hc : (⟨π ⟨v, hvH⟩, hvU⟩ : Ub) ∈ center ↥Ub := by
        rw [mem_center_iff]
        rintro ⟨_, w, hw, rfl⟩
        apply Subtype.ext
        exact (hcomm w hw).mpr (h w hw)
      exact ⟨⟨v, hvH⟩, hZbO ⟨_, hc, rfl⟩, rfl⟩
    · intro hvN w hw
      obtain ⟨y, hy, hyeq⟩ := hvN
      have hyv : y = ⟨v, hvH⟩ := Subtype.ext hyeq
      rw [hyv] at hy
      exact (hcomm ⟨w, hVH hw⟩ hw).mp
        (hOc _ hy _ (mem_map_of_mem π (show (⟨w, hVH hw⟩ : HB) ∈ VB.subgroupOf HB from hw)))
  have hfo : CFSG.Open.fusionOddCore ↥VB = pPrimeCore 2 ↥VB := by
    show sSup _ = sSup _
    congr 1
    ext J'
    simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
  have hzstar : ∀ v : ↥VB, v ∈ CFSG.Open.fusionZStar ↥VB ↔
      ∀ w : ↥VB, (w * v)⁻¹ * (v * w) ∈ pPrimeCore 2 ↥VB := by
    intro v
    rw [← hfo]
    show QuotientGroup.mk' _ v ∈ center _ ↔ _
    rw [mem_center_iff]
    constructor
    · intro h w
      have h1 := h (QuotientGroup.mk' _ w)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h1
      exact h1
    · intro h q
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ q
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      exact h w
  have hZ : VB ⊓ N = (CFSG.Open.fusionZStar ↥VB).map VB.subtype := by
    ext x
    constructor
    · rintro ⟨hxV, hxN⟩
      refine ⟨⟨x, hxV⟩, (hzstar _).mpr fun w => ?_, rfl⟩
      have h1 := (hcomm_iff x hxV).mpr hxN w w.2
      have h3 : (((w * ⟨x, hxV⟩)⁻¹ * (⟨x, hxV⟩ * w) : VB) : G) ∈
          (pPrimeCore 2 ↥VB).map VB.subtype := by
        rw [hOV]
        exact mem_inf.mpr ⟨((w * ⟨x, hxV⟩)⁻¹ * (⟨x, hxV⟩ * w) : VB).2, h1⟩
      obtain ⟨y, hy, hyeq⟩ := h3
      rwa [← Subtype.ext hyeq]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.2, (hcomm_iff v v.2).mp fun w hw => ?_⟩
      have h1 := (hzstar v).mp hv ⟨w, hw⟩
      have h2 := mem_map_of_mem VB.subtype h1
      rw [hOV] at h2
      exact (mem_inf.mp h2).2
  set θ := QuotientGroup.mk' K₂ with hθdef
  have hRK₂ : pPrimeCore 2 ↥HB ≤ K₂.comap (MonoidHom.id ↥HB) := by
    intro r hr
    show π r ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB)
    rw [show π r = 1 from (QuotientGroup.eq_one_iff r).mpr hr]
    exact one_mem _
  set φ : (↥HB ⧸ pPrimeCore 2 ↥HB) →* (↥HB ⧸ K₂) :=
    QuotientGroup.map _ _ (MonoidHom.id ↥HB) hRK₂ with hφdef
  have hφπ : φ.comp π = θ := by
    ext h
    rfl
  have hkerφ : ∀ x, φ x = 1 ↔ x ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB) := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ x
    show θ h = 1 ↔ π h ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hθmap : ∀ Y : Subgroup HB, Y.map θ = (Y.map π).map φ := fun Y => by
    rw [← hφπ, ← Subgroup.map_map]
  have hsimple : ∀ A : Subgroup (↥HB ⧸ pPrimeCore 2 ↥HB), IsQuasisimple ↥A →
      (∀ x ∈ A, x ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB) ↔ ∀ y ∈ A, y * x = x * y) →
      IsSimpleGroup ↥(A.map φ) ∧ ∃ x y : ↥(A.map φ), x * y ≠ y * x := by
    intro A hAq hAZ
    refine isSimpleGroup_of_surjective_ker_eq_center hAq (φ.subgroupMap A)
      (φ.subgroupMap_surjective A) ?_
    ext x
    rw [MonoidHom.mem_ker, mem_center_iff]
    constructor
    · intro hx y
      have h1 : φ x = 1 := congrArg Subtype.val hx
      exact Subtype.ext (((hAZ x x.2).mp ((hkerφ x).mp h1)) y y.2)
    · intro hx
      apply Subtype.ext
      show φ x = 1
      rw [hkerφ]
      exact (hAZ x x.2).mpr fun y hy => congrArg Subtype.val (hx ⟨y, hy⟩)
  have hcenter : ∀ {Y : Type} [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      center Y = ⊥ := by
    intro Y _ hY hnab
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      have hy : y ∈ center Y := by rw [h]; exact mem_top y
      exact hxy (mem_center_iff.mp hy x)
  obtain ⟨Kc, hKc, -, hmapc, -⟩ := id hM
  obtain ⟨Kc', hKc', -, hmapc', -⟩ := id hMa
  set Ab := (M.subgroupOf HB).map π with hAbdef
  set Ab' := ((conjugate M a).subgroupOf HB).map π with hAb'def
  have hAbq : IsQuasisimple ↥Ab := by
    have h := hKc.1
    rw [← hmapc] at h
    exact h
  have hAb'q : IsQuasisimple ↥Ab' := by
    have h := hKc'.1
    rw [← hmapc'] at h
    exact h
  have hUbAb : Ub = Ab ⊔ Ab' := by
    rw [hUbdef, hVsup, subgroupOf_sup hMH hMaH, Subgroup.map_sup]
  have hAbU : Ab ≤ Ub := hUbAb ▸ le_sup_left
  have hAb'U : Ab' ≤ Ub := hUbAb ▸ le_sup_right
  have hcentO : ∀ x ∈ Ub, (∀ y ∈ Ub, y * x = x * y) → x ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB) := by
    intro x hx hc
    have h1 : (⟨x, hx⟩ : Ub) ∈ center ↥Ub := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (hc y y.2)
    exact hZbO ⟨_, h1, rfl⟩
  have hθV : ((VB.subgroupOf HB).map θ) = Ub.map φ := hθmap _
  have hθ : (IsSimpleGroup ↥((VB.subgroupOf HB).map θ) ∧
        ∃ x y : ↥((VB.subgroupOf HB).map θ), x * y ≠ y * x) ∨
      ∃ L₁ L₂ : Subgroup (↥HB ⧸ K₂),
        (IsSimpleGroup ↥L₁ ∧ ∃ x y : ↥L₁, x * y ≠ y * x) ∧
        (IsSimpleGroup ↥L₂ ∧ ∃ x y : ↥L₂, x * y ≠ y * x) ∧ ⁅L₁, L₂⁆ = ⊥ ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₁ ⊔ L₂ = (VB.subgroupOf HB).map θ := by
    by_cases hMM : M = conjugate M a
    ·
      left
      have hUA : Ub = Ab := by
        rw [hUbdef, hVsup, ← hMM, sup_idem]
      rw [hθV, hUA]
      refine hsimple Ab hAbq fun x hx => ⟨fun hxO y hy => hOc x hxO y (hAbU hy), fun hc => ?_⟩
      exact hcentO x (hAbU hx) fun y hy => hc y (hUA ▸ hy)
    ·
      right
      have hne' : M.subgroupOf HB ≠ (conjugate M a).subgroupOf HB := fun h =>
        hMM (UGSChain.eq_of_subgroupOf_eq hMH hMaH h)
      have hcAb : ⁅Ab, Ab'⁆ = ⊥ := commutator_map_eq_bot_of_ne hM hMa hne'
      have hAbAb' : ∀ x ∈ Ab, ∀ y ∈ Ab', y * x = x * y := by
        intro x hx y hy
        have h1 := commutator_mem_commutator hx hy
        rw [hcAb, mem_bot] at h1
        exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
      have hcentU : ∀ x ∈ Ub, (∀ y ∈ Ab, y * x = x * y) → (∀ y ∈ Ab', y * x = x * y) →
          x ∈ pCore 2 (↥HB ⧸ pPrimeCore 2 ↥HB) := by
        intro x hx h1 h2
        refine hcentO x hx fun y hy => ?_
        have hle : Ab ⊔ Ab' ≤ centralizer ({x} : Set (↥HB ⧸ pPrimeCore 2 ↥HB)) :=
          sup_le (fun z hz => mem_centralizer_singleton_iff.mpr (h1 z hz))
            (fun z hz => mem_centralizer_singleton_iff.mpr (h2 z hz))
        rw [← hUbAb] at hle
        exact mem_centralizer_singleton_iff.mp (hle hy)
      have hs1 := hsimple Ab hAbq fun x hx =>
        ⟨fun hxO y hy => hOc x hxO y (hAbU hy), fun hc =>
          hcentU x (hAbU hx) hc fun y hy => (hAbAb' x hx y hy)⟩
      have hs2 := hsimple Ab' hAb'q fun x hx =>
        ⟨fun hxO y hy => hOc x hxO y (hAb'U hy), fun hc =>
          hcentU x (hAb'U hx) (fun y hy => (hAbAb' y hy x hx).symm) hc⟩
      refine ⟨Ab.map φ, Ab'.map φ, hs1, hs2, ?_, ?_, ?_⟩
      · rw [← map_commutator, hcAb, Subgroup.map_bot]
      · rw [eq_bot_iff]
        intro x hx
        obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
        have hc : (⟨x, hx1⟩ : Ab.map φ) ∈ center ↥(Ab.map φ) := by
          rw [mem_center_iff]
          rintro ⟨_, y, hy, rfl⟩
          apply Subtype.ext
          obtain ⟨z, hz, rfl⟩ := hx2
          show φ y * φ z = φ z * φ y
          rw [← map_mul, ← map_mul, (hAbAb' y hy z hz).symm]
        rw [hcenter hs1.1 hs1.2, mem_bot] at hc
        exact mem_bot.mpr (congrArg Subtype.val hc)
      · rw [hθV, hUbAb, Subgroup.map_sup]
  have hlarger : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ P →
      (Nat.card B < Nat.card C ∨ (Nat.card B = Nat.card C ∧
        Nat.card ↥Q < Nat.card ↥(S ⊓ normalizer (C : Set G)))) →
      V C ≤ H C ∧ IsPComponent 2 ((V C).subgroupOf (H C)) ∧ conjugate (V C) a = V C ∧
        (T C : Set G) * ((pPrimeCore 2 ↥(V C)).map (V C).subtype : Set G) = V C ∧
        T C = UnbalancedGS.gsFixedLayer (V C) a := by
    intro C hC1 hCP hlex
    obtain ⟨-, -, -, -, -, -, -, ⟨MC, -, -, -, hVMC, hVEC, -, hdleC, hdeqC, hdeqcC, -, -⟩, -⟩ :=
      hA2.1 C hC1 hCP
    have hnotbad : ¬ d J < d (V C) := by
      intro hbadC
      rcases hmax C hC1 hCP hbadC with h | ⟨h, h'⟩
      · rcases hlex with h'' | ⟨h'', -⟩ <;> omega
      · rcases hlex with h'' | ⟨-, h''⟩ <;> omega
    have hdeqJ : d (V C) = d J := le_antisymm (not_lt.mp hnotbad) hdleC
    obtain ⟨hMCeq, -⟩ := hdeqC.mp hdeqJ
    obtain ⟨hpcV, hmulV, hfixV⟩ := hdeqcC hdeqJ
    have hVCM : V C = MC := by rw [hVMC, ← hMCeq, sup_idem]
    refine ⟨hVEC.trans (by rw [hE C]; exact map_subtype_le _), hpcV, ?_, hmulV, hfixV⟩
    rw [hVCM]
    exact hMCeq.symm
  exact ⟨⟨hQL, hQsyl⟩, hEVeq.symm, hVa, hBD, hBsylD, hNeq, hRBbot, hRBc, haN, hZ, hθ, hlarger⟩

end CFSG.ComponentClassification.UnbalancedCorr
