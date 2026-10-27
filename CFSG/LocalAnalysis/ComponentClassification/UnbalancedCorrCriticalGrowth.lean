module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalTools

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem pLayer_quotient_eq_top_of_sup {V M M' : Subgroup G} (hMV : M ≤ V) (hM'V : M' ≤ V)
    (hV : V = M ⊔ M') (hM : IsPComponent 2 (M.subgroupOf V))
    (hM' : IsPComponent 2 (M'.subgroupOf V)) : pLayer (↥V ⧸ pPrimeCore 2 ↥V) 2 = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥V) with hπdef
  have hker : ¬ 2 ∣ Nat.card π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  have hbij := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection π
    (QuotientGroup.mk'_surjective _) hker
  have h1 : IsPComponent 2 ((M.subgroupOf V).map π) := hbij.1.mapsTo hM
  have h2 : IsPComponent 2 ((M'.subgroupOf V).map π) := hbij.1.mapsTo hM'
  have htop : M.subgroupOf V ⊔ M'.subgroupOf V = ⊤ := by
    rw [← subgroupOf_sup hMV hM'V, ← hV, subgroupOf_self]
  rw [eq_top_iff]
  calc (⊤ : Subgroup (↥V ⧸ pPrimeCore 2 ↥V)) = (M.subgroupOf V ⊔ M'.subgroupOf V).map π := by
        rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    _ = (M.subgroupOf V).map π ⊔ (M'.subgroupOf V).map π := Subgroup.map_sup _ _ _
    _ ≤ pLayer _ 2 := sup_le (le_sSup h1) (le_sSup h2)

theorem normalClosure_map_eq_top_of_orbit {H V M W : Subgroup G} {a : G} (ha : a * a = 1)
    (hMH : M ≤ H) (hM : IsPComponent 2 (M.subgroupOf H)) (hV : V = M ⊔ conjugate M a)
    (hVM : V ≤ normalizer (M : Set G)) (haV : a ∈ normalizer (V : Set G)) (hWV : W ≤ V)
    (hWa : W ≤ centralizer ({a} : Set G)) (hWperf : ⁅W, W⁆ = W)
    (hWodd : ¬ W ≤ (pPrimeCore 2 ↥V).map V.subtype) :
    normalClosure (((W.subgroupOf V).map (QuotientGroup.mk' (pPrimeCore 2 ↥V)) :
      Subgroup (↥V ⧸ pPrimeCore 2 ↥V)) : Set (↥V ⧸ pPrimeCore 2 ↥V)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥V) with hπdef
  have hMV : M ≤ V := hV ▸ le_sup_left
  have hMaV : conjugate M a ≤ V := hV ▸ le_sup_right
  have hMn : (M.subgroupOf V).Normal := (normal_subgroupOf_iff_le_normalizer hMV).mpr hVM
  obtain ⟨eM, -⟩ := exists_restriction_quotient_equiv_of_subnormal hMV hMn.isSubnormal
  have hAq : IsQuasisimple ↥((M.subgroupOf V).map π) :=
    LocalCores.isQuasisimple_of_mulEquiv eM
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hM).2.2
  have hAn : ((M.subgroupOf V).map π).Normal := hMn.map π (QuotientGroup.mk'_surjective _)
  let φ : MulAut ↥V := V.normalizerMonoidHom ⟨a, haV⟩
  have hφ : ∀ v : V, ((φ v : V) : G) = a * v * a⁻¹ := fun v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V _ v
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hφsymm : ∀ v : V, ((φ.symm v : V) : G) = a * v * a⁻¹ := by
    intro v
    have h1 := hφ (φ.symm v)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : ((φ.symm v : V) : G) = a⁻¹ * v * a := by
      rw [h1]
      group
    rw [h2, hainv]
  let σ : (↥V ⧸ pPrimeCore 2 ↥V) ≃* (↥V ⧸ pPrimeCore 2 ↥V) :=
    QuotientGroup.congr (pPrimeCore 2 ↥V) (pPrimeCore 2 ↥V) φ (pPrimeCore_map_iso 2 φ)
  have hσ : ∀ v : V, σ (π v) = π (φ v) := fun v => QuotientGroup.congr_mk _ _ _ _ v
  have hφM : (M.subgroupOf V).map φ.toMonoidHom = (conjugate M a).subgroupOf V := by
    ext x
    rw [mem_map_equiv, mem_subgroupOf, mem_subgroupOf, UnbalancedLayer.mem_conjugate_iff,
      hφsymm]
  have hσA : ((M.subgroupOf V).map π).map σ.toMonoidHom = ((conjugate M a).subgroupOf V).map π := by
    rw [← hφM, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have htop : (M.subgroupOf V).map π ⊔ ((M.subgroupOf V).map π).map σ.toMonoidHom = ⊤ := by
    rw [hσA, ← Subgroup.map_sup, ← subgroupOf_sup hMV hMaV, ← hV, subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hσW : ∀ x ∈ (W.subgroupOf V).map π, σ x = x := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hσ]
    congr 1
    apply Subtype.ext
    rw [hφ, show a * (w : G) = w * a from (mem_centralizer_singleton_iff.mp (hWa hw)).symm,
      mul_inv_cancel_right]
  have hW'perf : ⁅W.subgroupOf V, W.subgroupOf V⁆ = W.subgroupOf V := by
    apply map_injective V.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hWV, hWperf]
  have hWbperf : ⁅(W.subgroupOf V).map π, (W.subgroupOf V).map π⁆ = (W.subgroupOf V).map π := by
    rw [← map_commutator, hW'perf]
  have hWb1 : (W.subgroupOf V).map π ≠ ⊥ := by
    intro h
    apply hWodd
    rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk'] at h
    intro w hw
    exact ⟨⟨w, hWV hw⟩, h (show (⟨w, hWV hw⟩ : V) ∈ W.subgroupOf V from hw), rfl⟩
  exact normalClosure_eq_top_of_quasisimple hAq σ htop hσW hWbperf hWb1

omit [Finite G] in
theorem commutator_eq_of_isPComponent {H M : Subgroup G} (hMH : M ≤ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) : ⁅M, M⁆ = M := by
  have h1 : Group.IsPerfect ↥(M.subgroupOf H) := CatalogueBAlternating.pComponent_perfect hM
  have h2 : Group.IsPerfect ↥M :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hMH).toMonoidHom)
      (subgroupOfEquivOfLe hMH).surjective
  exact Subgroup.isPerfect_iff.mp h2

theorem not_le_of_isPComponent_of_coprime {H M Y : Subgroup G} (hMH : M ≤ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) (hY : Nat.Coprime 2 (Nat.card Y)) : ¬ M ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hMY
  apply CatalogueBPrimeJoin.core_ne_top 2 _ hM
  have hcop : Nat.Coprime 2 (Nat.card ↥(M.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hMH).toEquiv]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hMY) hY
  refine top_unique (le_sSup ⟨inferInstance, ?_⟩)
  rwa [card_top]

theorem isSubnormal_of_le_pLayer {H V : Subgroup G}
    (hVE : V ≤ (pLayer ↥H 2).map H.subtype)
    (hEV : (pLayer ↥H 2).map H.subtype ≤ normalizer (V : Set G)) :
    (V.subgroupOf H).IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEn : (pLayer ↥H 2).Normal := by
    have : (pLayer ↥H 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    infer_instance
  have hV'E : V.subgroupOf H ≤ pLayer ↥H 2 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := mem_map.mp (hVE (mem_subgroupOf.mp hx))
    rwa [← Subtype.ext hyx]
  refine IsSubnormal.step _ _ hV'E hEn.isSubnormal ?_
  rw [normal_subgroupOf_iff_le_normalizer hV'E]
  intro e he
  exact UnbalancedLayer.mem_normalizer_subgroupOf_of_mem (hEV (mem_map_of_mem H.subtype he))

theorem critical_growth_le
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
    {B Tn : Subgroup G} (hB1 : B ≠ ⊥) (hBTn : B ≤ Tn) (hTnP : Tn ≤ P)
    (hTnV : Tn ≤ normalizer (V B : Set G))
    (hTnK : Tn ≤ UnbalancedLayer.coreActionKernel (V B)) :
    d (V B) ≤ d (V Tn) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 (S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
      hP₀ ▸ P₀.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hSX)
  have hBP : B ≤ P := hBTn.trans hTnP
  have hTn1 : Tn ≠ ⊥ := fun h => hB1 (le_bot_iff.mp (h ▸ hBTn))
  have hTn2 : IsPGroup 2 Tn := hS2.to_le (hTnP.trans (hP.le.trans inf_le_left))
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hA2 := actual_two_local_fixed_layer_orbits_of_inputs hS hU hheld hnonab hK ha hJa hJ hSX
    hSsyl hP H R T X E V hH hR hT hX hE hV d hd
  obtain ⟨-, -, -, -, -, -, -, ⟨M, hMH, hM, hMa, hVM, hVE, hVEn, -⟩, -⟩ := hA2.1 B hB1 hBP
  obtain ⟨-, -, -, -, hTaH', hpcT', -, ⟨M', hM'H, hM', hM'a, hVM', hVE', hVEn', -⟩, -⟩ :=
    hA2.1 Tn hTn1 hTnP
  obtain ⟨hA3, -, -⟩ := nested_two_local_full_core_residual_identities_of_inputs hS hU hheld
    hnonab hK ha hJa hJ hSX hSsyl hP H R T X hH hR hT hX
  obtain ⟨hTTnB, -, -⟩ := hA3 B Tn hB1 hBTn hTnP
  have hRf : ∀ C : Subgroup G, R C = (pPrimeCore 2 ↥(normalizer (C : Set G))).map
      (normalizer (C : Set G)).subtype := fun C => by rw [hR, hH]
  have hEf : ∀ C : Subgroup G, E C = (pLayer ↥(normalizer (C : Set G)) 2).map
      (normalizer (C : Set G)).subtype := fun C => by rw [hE, hH]
  have hBP' : B ≤ S ⊓ UnbalancedLayer.coreActionKernel J := hBP.trans hP.le
  have hTnP' : Tn ≤ S ⊓ UnbalancedLayer.coreActionKernel J := hTnP.trans hP.le
  obtain ⟨-, -, hTBV, -, -, -⟩ := two_local_conj_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2
    hB1 hBP' (hT B) (hRf B) (hX B) (hEf B) (hV B)
  obtain ⟨-, -, hTTnV, -, -, -⟩ := two_local_conj_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2
    hTn1 hTnP' (hT Tn) (hRf Tn) (hX Tn) (hEf Tn) (hV Tn)
  rw [hH] at hMH hM hMa hM'H hM' hM'a hTaH' hpcT'
  rw [hEf] at hVE hVEn hVE' hVEn'
  set Vb := V B with hVbdef
  set NB := normalizer (B : Set G) with hNBdef
  have hVbE : Vb ≤ (pLayer ↥NB 2).map NB.subtype := hVE
  have hEVb : (pLayer ↥NB 2).map NB.subtype ≤ normalizer (Vb : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hVE).mp hVEn
  have hVbH : Vb ≤ NB := hVE.trans (map_subtype_le _)
  have hVbsub : (Vb.subgroupOf NB).IsSubnormal := isSubnormal_of_le_pLayer hVbE hEVb
  have hVbM : Vb ≤ normalizer (M : Set G) :=
    hVbE.trans (UGSChain.map_pLayer_le_normalizer hMH hM)
  have haVb : a ∈ normalizer (Vb : Set G) := by
    rw [hVM]
    exact mem_normalizer_orbit haa
  have hMVb : M ≤ Vb := hVM ▸ le_sup_left
  have hMaVb : conjugate M a ≤ Vb := hVM ▸ le_sup_right
  set W := T Tn with hWdef
  have hWJC : W ≤ J ⊓ centralizer (Tn : Set G) := by
    rw [hWdef, hT Tn]
    exact map_subtype_le _
  have hWVb : W ≤ Vb := hTTnB.trans hTBV
  have hWa : W ≤ centralizer ({a} : Set G) := fun w hw => hJa (hWJC hw).1
  have hWC : W ≤ Vb ⊓ centralizer (Tn : Set G) := fun w hw => ⟨hWVb hw, (hWJC hw).2⟩
  have hWperf : ⁅W, W⁆ = W := commutator_eq_of_isPComponent hTaH' hpcT'
  have hOVb : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥Vb).map Vb.subtype)) := by
    rw [card_map_of_injective (subtype_injective _)]
    exact pPrimeCore_coprime_card
  have hWodd : ¬ W ≤ (pPrimeCore 2 ↥Vb).map Vb.subtype :=
    not_le_of_isPComponent_of_coprime hTaH' hpcT' hOVb
  have hW2 : CatalogueBPrimeJoin.primeResidual 2 ↥W = ⊤ :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 W _ hTaH').mp hpcT').2.1
  have hEQ : pLayer (↥Vb ⧸ pPrimeCore 2 ↥Vb) 2 = ⊤ :=
    pLayer_quotient_eq_top_of_sup hMVb hMaVb hVM (isPComponent_subgroupOf_of_le hMVb hVbH hM)
      (isPComponent_subgroupOf_of_le hMaVb hVbH hMa)
  have hNC := normalClosure_map_eq_top_of_orbit haa hMH hM hVM hVbM haVb hWVb hWa hWperf hWodd
  set F := (pLayer ↥(Vb ⊓ centralizer (Tn : Set G)) 2).map
    (Vb ⊓ centralizer (Tn : Set G)).subtype with hFdef
  obtain ⟨hFC, hdF, hgen⟩ := core_trivial_fixed_layer_facts hTn2 hTnV hTnK hEQ hFdef
  obtain ⟨hWF, hWFn⟩ := hgen W hWC hW2 hNC
  set C := Vb ⊓ centralizer (Tn : Set G) with hCdef
  set NT := normalizer (Tn : Set G) with hNTdef
  have hCT : centralizer (Tn : Set G) ≤ NB :=
    (centralizer_le hBTn).trans (centralizer_le_normalizer' B)
  have hCTN : centralizer (Tn : Set G) ≤ NT := centralizer_le_normalizer' Tn
  have hCC : C ≤ centralizer (Tn : Set G) := inf_le_right
  have hCsub : (C.subgroupOf (centralizer (Tn : Set G))).IsSubnormal := by
    rw [hCdef, inf_subgroupOf_right]
    exact CatalogueBPrimeJoin.subgroupOf_isSubnormal_of_le hCT hVbsub
  have hCTsub : ((centralizer (Tn : Set G)).subgroupOf NT).IsSubnormal :=
    (centralizer_normal_normalizer Tn).isSubnormal
  have hCN : C ≤ NT := hCC.trans hCTN
  have hCNsub : (C.subgroupOf NT).IsSubnormal :=
    (CatalogueBPrimeJoin.subgroupOf_isSubnormal_iff hCC hCTN hCTsub).mpr hCsub
  have hFE : F ≤ (pLayer ↥NT 2).map NT.subtype := by
    rw [hFdef, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hKc => ?_
    have hK' : IsPComponent 2 ((K.map C.subtype).subgroupOf C) := by
      rwa [show (K.map C.subtype).subgroupOf C = K from
        comap_map_eq_self_of_injective C.subtype_injective K]
    have hK'' := isPComponent_subgroupOf_of_isSubnormal (map_subtype_le K) hCN hCNsub hK'
    have h1 : (K.map C.subtype).subgroupOf NT ≤ pLayer ↥NT 2 := le_sSup hK''
    intro k hk
    exact ⟨⟨(k : G), hCN k.2⟩, h1 (show (⟨(k : G), hCN k.2⟩ : NT) ∈
      (K.map C.subtype).subgroupOf NT from ⟨k, hk, rfl⟩), rfl⟩
  have hFN : F ≤ NT := hFE.trans (map_subtype_le _)
  have hFsub : (F.subgroupOf NT).IsSubnormal := by
    have hFC' : F.subgroupOf C = pLayer ↥C 2 :=
      comap_map_eq_self_of_injective C.subtype_injective _
    have hn : (F.subgroupOf C).Normal := by
      rw [hFC']
      have : (pLayer ↥C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
      infer_instance
    exact (CatalogueBPrimeJoin.subgroupOf_isSubnormal_iff hFC hCN hCNsub).mpr hn.isSubnormal
  have hVTE : V Tn ≤ (pLayer ↥NT 2).map NT.subtype := hVE'
  have hEVT : (pLayer ↥NT 2).map NT.subtype ≤ normalizer (V Tn : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hVE').mp hVEn'
  have hFVT : F ≤ V Tn := by
    have hn : ((V Tn).subgroupOf F).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      exact (mem_normalizer_iff.mp (hEVT (hFE g.2)) n).mp hn
    have h1 : normalClosure ((W.subgroupOf F : Subgroup ↥F) : Set ↥F) ≤ (V Tn).subgroupOf F :=
      normalClosure_le_normal fun x hx => hTTnV hx
    rw [hWFn] at h1
    intro f hf
    exact h1 (mem_top (⟨f, hf⟩ : F))
  have hVTsub : ((V Tn).subgroupOf NT).IsSubnormal := isSubnormal_of_le_pLayer hVTE hEVT
  have hVTN : V Tn ≤ NT := hVTE.trans (map_subtype_le _)
  have hVTperf : ⁅V Tn, V Tn⁆ = V Tn := by
    have h1 := commutator_eq_of_isPComponent hM'H hM'
    have h2 : ⁅conjugate M' a, conjugate M' a⁆ = conjugate M' a := by
      unfold conjugate
      rw [← map_commutator, h1]
    rw [hVM']
    apply le_antisymm (commutator_le_self _)
    refine sup_le ?_ ?_
    · calc M' = ⁅M', M'⁆ := h1.symm
        _ ≤ ⁅M' ⊔ conjugate M' a, M' ⊔ conjugate M' a⁆ :=
          commutator_mono le_sup_left le_sup_left
    · calc conjugate M' a = ⁅conjugate M' a, conjugate M' a⁆ := h2.symm
        _ ≤ ⁅M' ⊔ conjugate M' a, M' ⊔ conjugate M' a⁆ :=
          commutator_mono le_sup_right le_sup_right
  set π' := QuotientGroup.mk' (pPrimeCore 2 ↥NT) with hπ'def
  have hVTperf' : Group.IsPerfect ↥(((V Tn).subgroupOf NT).map π') := by
    apply Subgroup.isPerfect_iff.mpr
    rw [← map_commutator]
    congr 1
    apply map_injective NT.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hVTN, hVTperf]
  have hle := (card_center_quotient_le (map_mono (fun x hx => hFVT hx :
    F.subgroupOf NT ≤ (V Tn).subgroupOf NT)) hVTperf').1
  rw [hd, hd, ← hdF, card_centerQuotient_eq_of_subnormal hFN hFsub,
    card_centerQuotient_eq_of_subnormal hVTN hVTsub]
  exact hle

end CFSG.ComponentClassification.UnbalancedCorr
