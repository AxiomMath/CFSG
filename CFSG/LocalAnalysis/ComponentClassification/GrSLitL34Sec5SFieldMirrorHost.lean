module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldHost

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem exists_field_host_component (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3) {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G}
    (hset : L34FieldNormalSetting G t P) (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hPW : normalizer (P : Set G) ≤ normalizer (W : Set G)) (hM : normalizer (W : Set G) = M)
    {m : ℕ} (hm : 4 ≤ m) (hme : Even m)
    (hPm : Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 m) :
    ∃ (htM : t ∈ M) (L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) (n : ℕ), IsComponent L ∧
      center ↥L = ⊥ ∧ (n = m ∨ n = 2 * m) ∧ Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 n ∧
      ((L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom = L ∧
          (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = L ∧ n = m) ∨
        (L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom = L ∧
          (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤ L ∧ n = 2 * m) ∨
        (L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom ≠ L ∧
          (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤
            L ⊔ L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom)) :=
  by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, ht2, hPt, hPp, hPn, -⟩ := hset
  have hCM : centralizer ({t} : Set G) ≤ M :=
    (((normal_subgroupOf_iff_le_normalizer hPt).mp hPn).trans hPW).trans (le_of_eq hM)
  have htM : t ∈ M := hCM (mem_centralizer_singleton_iff.mpr rfl)
  have hPM : P ≤ M := hPt.trans hCM
  have hMtop : M ≠ ⊤ := by
    intro hMt
    have hWn : W.Normal := ⟨fun n hn g => by
      have hg : g ∈ M := hMt ▸ mem_top g
      rw [← hM] at hg
      exact (mem_normalizer_iff.mp hg n).mp hn⟩
    have := hbase.1
    have := hWn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · exact hW1 h
    · have h2 : 2 ∣ Nat.card W := by
        rw [h, card_top, ← ht2]
        exact orderOf_dvd_natCard t
      exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h2)
  have hKM : SectionRank.IsKGroupCat ↥M :=
    UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
      (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hbase.2.2.1 M hMtop
  have hs : orderOf (⟨t, htM⟩ : ↥M) = 2 := by
    rw [Subgroup.orderOf_mk]; exact ht2
  set Λ : Subgroup ↥M := P.subgroupOf M with hΛdef
  have hΛs : Λ ≤ centralizer ({(⟨t, htM⟩ : ↥M)} : Set ↥M) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hPt (mem_subgroupOf.mp hx))
  have hΛ : IsPComponent 2 (Λ.subgroupOf (centralizer ({(⟨t, htM⟩ : ↥M)} : Set ↥M))) := by
    rw [FooteLit.centralizer_mk_eq htM,
      UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two,
      inf_of_le_left hCM]
    exact hPp
  have hΛL : Blueprint.LieModel (↥Λ ⧸ Open.fusionZStar ↥Λ) .PSL 3 2 m :=
    Blueprint.LieModel.of_mulEquiv (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hPM).symm) hPm
  obtain ⟨L, n, hL, hlink, hn, hLn, hcent⟩ :=
    exists_component_l3_of_twoComponent hcat hKM hs hΛs hΛ hm hme hΛL
  have hOX : pPrimeCore 2 (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ :=
    GH74.pPrimeCore_quotient_pPrimeCore_eq_bot _ 2
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl <;> omega
  have hZ : center ↥L = ⊥ := center_eq_bot_of_isComponent_l3 hmult hOX hL (by omega) hLn
  set u := QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ with hu
  set Λb := Λ.map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) with hΛb
  have hΛ2 : TwoComponents.IsTwoComponent
      (Λ.subgroupOf (centralizer ({(⟨t, htM⟩ : ↥M)} : Set ↥M))) :=
    (CatalogueBAlternating.pComponent_two_iff _).mp hΛ
  have hΛbC : Λb ≤ centralizer ({u} : Set (↥M ⧸ pPrimeCore 2 ↥M)) :=
    (Subgroup.map_mono hΛs).trans (GH74.GLS.TwoThin.map_centralizer_barMk hs).le
  have hΛbp : IsPComponent 2
      (Λb.subgroupOf (centralizer ({u} : Set (↥M ⧸ pPrimeCore 2 ↥M)))) :=
    (CatalogueBAlternating.pComponent_two_iff _).mpr
      (GH74.GLS.TwoThin.isTwoComponent_map_barMk hs hΛs hΛ2)
  by_cases hLfix : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M)
    ⟨t, htM⟩)).toMonoidHom = L
  · rcases hn with hnm | hn2m
    ·
      have hLfix' : L.map (MulAut.conj u).toMonoidHom = L := hLfix
      have hΛbL : Λb ≤ L := by
        have h := hlink
        rw [hLfix', sup_idem] at h
        exact h
      have hcentL : L ≤ centralizer ({u} : Set (↥M ⧸ pPrimeCore 2 ↥M)) := by
        intro x hx
        rw [mem_centralizer_singleton_iff]
        exact (hcent hnm hLfix' x hx).symm
      have hΛbL' : IsPComponent 2 (Λb.subgroupOf L) :=
        CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hΛbL hcentL hΛbp
      have hΛbEq : Λb = L := by
        have hne : Λb.subgroupOf L ≠ ⊥ := CatalogueBPrimeJoin.pComponent_ne_bot hΛbL'
        obtain ⟨-, -, hsub, -, -⟩ := hΛbL'
        rcases CFSG.Quasithin.A3.eq_top_or_le_center_of_subnormal hL.1 hsub with htop | hcen
        · exact le_antisymm hΛbL (Subgroup.subgroupOf_eq_top.mp htop)
        · exact absurd (le_bot_iff.mp (hcen.trans (le_of_eq hZ))) hne
      exact ⟨htM, L, n, hL, hZ, Or.inl hnm, hLn, Or.inl ⟨hLfix, hΛbEq, hnm⟩⟩
    ·
      have hLfix' : L.map (MulAut.conj u).toMonoidHom = L := hLfix
      have hΛbL : Λb ≤ L := by
        have h := hlink
        rw [hLfix', sup_idem] at h
        exact h
      exact ⟨htM, L, n, hL, hZ, Or.inr hn2m, hLn, Or.inr (Or.inl ⟨hLfix, hΛbL, hn2m⟩)⟩
  ·
    exact ⟨htM, L, n, hL, hZ, hn, hLn, Or.inr (Or.inr ⟨hLfix, hlink⟩)⟩

theorem exists_sylow_fusion_of_field (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3) {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G}
    (hset : L34FieldNormalSetting G t P) (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hPW : normalizer (P : Set G) ≤ normalizer (W : Set G))
    (hWE : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = W) :
    ∃ S : Sylow 2 G, t ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ normalizer (W : Set G) ∧
      (∃ A : Subgroup G, A ≤ S ∧ (S : Subgroup G) ≤ normalizer (A : Set G) ∧
        Open.IsElemAbelian 2 A ∧ 32 ≤ Nat.card A) ∧
      ∀ x ∈ (S : Subgroup G), ∀ g : G, g⁻¹ * x * g ∈ (S : Subgroup G) →
        3 ≤ pRank 2 ↥((S : Subgroup G) ⊓ centralizer ({x} : Set G)) →
        3 ≤ pRank 2 ↥((S : Subgroup G) ⊓ centralizer ({g⁻¹ * x * g} : Set G)) →
        ∃ m ∈ normalizer (W : Set G), g⁻¹ * x * g = m⁻¹ * x * m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbase : L34BaseSetting G := hset.1
  have ht2 : orderOf t = 2 := hset.2.1
  have hPt : P ≤ centralizer ({t} : Set G) := hset.2.2.1
  have hPn : (P.subgroupOf (centralizer ({t} : Set G))).Normal := hset.2.2.2.2.1
  have htM : t ∈ normalizer (W : Set G) :=
    (((normal_subgroupOf_iff_le_normalizer hPt).mp hPn).trans hPW)
      (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨S, -, hSyl, -, -, -, -, -, hAex, -⟩ :=
    l34FieldNormalUTSection_of_inputs hcat hmult G t P W hset hWodd hW1 hPW hWE
  obtain ⟨A, hAS, hAn, hA, hA32, hWA⟩ := hAex
  obtain ⟨St, hSylt, htSt⟩ := exists_isSylowTwoIn_mem htM ht2
  have hSylP := hSyl
  have hSyltQ := hSylt
  obtain ⟨-, P, hP⟩ := hSylP
  obtain ⟨-, Q, hQ⟩ := hSyltQ
  have hPQ : Nat.card ↥(P : Subgroup ↥(normalizer (W : Set G))) =
      Nat.card ↥(Q : Subgroup ↥(normalizer (W : Set G))) :=
    Nat.card_congr (Sylow.equiv P Q).toEquiv
  rw [hP, hQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSyl.1).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSylt.1).toEquiv] at hPQ
  obtain ⟨c, hcM, hSc⟩ :=
    GrS4.exists_eq_map_conj_of_isSylowTwoIn hSyl hSylt.1
      (GrSLit.IsSylowTwoIn.isPGroup hSylt) hPQ.symm
  set S1 : Subgroup G := S.map (MulAut.conj c).toMonoidHom with hS1
  set A1 : Subgroup G := A.map (MulAut.conj c).toMonoidHom with hA1
  have hSc' : St = S1 := hSc.trans hS1.symm
  have hSyl1 : IsSylowTwoIn S1 (normalizer (W : Set G)) := hSc' ▸ hSylt
  have htS1 : t ∈ S1 := hSc' ▸ htSt
  have hAe : IsElemTwo A :=
    isElemTwo_of_sq fun a ha => by rw [← pow_two]; exact hA.2 a ha
  have hA1e : IsElemTwo A1 := by rw [hA1]; exact hAe.map_conj c
  have hA132 : 32 ≤ Nat.card A1 := by
    rw [hA1, card_map_of_injective (MulAut.conj c).injective]
    exact hA32
  have hA1S : A1 ≤ S1 := by rw [hA1, hS1]; exact Subgroup.map_mono hAS
  have hS1N : S1 ≤ normalizer (A1 : Set G) := by
    rw [hS1, hA1]
    exact (Subgroup.map_mono hAn).trans (Subgroup.le_normalizer_map _)
  have hS12 : IsPGroup 2 S1 := by
    obtain ⟨Q1, hQ1⟩ := hSyl1.2
    have hQ2 : IsPGroup 2 (S1.subgroupOf (normalizer (W : Set G))) := hQ1 ▸ Q1.isPGroup'
    have := hQ2.map (normalizer (W : Set G)).subtype
    rwa [subgroupOf_map_subtype, inf_of_le_left hSyl1.1] at this
  have h3 : IsThreeConnected S1 :=
    isThreeConnected_of_normal hS12 hA1S hS1N hA1e hA132
  have hWA1 : GrSLit.wGroup A1 = W := by
    rw [hA1, GrSLit.wGroup_map_conj c A, hWA]
    simpa using mem_normalizer_iff_map_conj_eq.mp hcM
  have hGW : GWTwoBalanced G :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hbase.2.2.2.2.2.1
  have hSylA : IsSylowTwoIn S1 (normalizer (GrSLit.wGroup A1 : Set G)) := by
    rw [hWA1]
    exact hSyl1
  obtain ⟨⟨T, hT⟩, hfus⟩ :=
    sylow_and_fusion_of_threeConnected hGW hA1e (by omega) hSylA h3
  rw [hWA1] at hfus
  have hfuse : ∀ x ∈ S1, ∀ g : G, g⁻¹ * x * g ∈ S1 →
      3 ≤ pRank 2 ↥(S1 ⊓ centralizer ({x} : Set G)) →
      3 ≤ pRank 2 ↥(S1 ⊓ centralizer ({g⁻¹ * x * g} : Set G)) →
      ∃ m ∈ normalizer (W : Set G), g⁻¹ * x * g = m⁻¹ * x * m := by
    intro x hx g hy hrx hry
    obtain ⟨c', hc'⟩ := exists_extremal_conj ⟨T, hT⟩ hx
    obtain ⟨m1, hm1, h1⟩ := hfus _ x hx hc' ⟨c', rfl⟩ hrx
    obtain ⟨m2, hm2, h2⟩ := hfus _ (g⁻¹ * x * g) hy hc' ⟨g⁻¹ * c', by group⟩ hry
    refine ⟨m1⁻¹ * m2, mul_mem (inv_mem hm1) hm2, ?_⟩
    rw [h2]
    conv_rhs => rw [h1]
    group
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · rw [hT]; exact htS1
  · rw [hT]; exact hSyl1.1
  · refine ⟨A1, ?_, ?_, ?_, ?_⟩
    · rw [hT]; exact hA1S
    · rw [hT]; exact hS1N
    · exact hA1e.isElemAbelian
    · exact hA132
  · rw [hT]
    exact hfuse

theorem hom_eq_one_of_field_signalizer (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3) {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G}
    (hset : L34FieldNormalSetting G t P) (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hPW : normalizer (P : Set G) ≤ normalizer (W : Set G))
    (hWE : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = W)
    (htM : t ∈ normalizer (W : Set G)) {B : Type} [CommGroup B]
    (χ : ↥(normalizer (W : Set G)) →* B) : χ ⟨t, htM⟩ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hsimple : IsSimpleGroup G := hset.1.1
  haveI hperf : Group.IsPerfect G :=
    Group.IsPerfect.mk
      (CFSG.SignalizerFunctorTheorem.IsSectionOf.commutator_eq_top_of_simple hset.1.2.1)
  obtain ⟨S, -, hSM, ⟨A, hAS, hSnA, hA, hA32⟩, hfus⟩ :=
    exists_sylow_fusion_of_field hcat hmult hset hWodd hW1 hPW hWE
  have hidx : Odd (normalizer (W : Set G)).index :=
    CFSG.ComponentClassification.AschbacherStrongEmbedding.Lemma34.odd_index_of_sylow_le hSM
  refine hom_eq_one_of_involution_fusion (M := normalizer (W : Set G)) hidx ?_ χ ?_
  · intro x hxM hxord g hyM
    have hx2 : x * x = 1 := by
      rw [← pow_two, ← hxord, pow_orderOf_eq_one]
    have hyord : orderOf (g⁻¹ * x * g) = 2 := by
      rw [show g⁻¹ * x * g = g⁻¹ * x * (g⁻¹)⁻¹ by group,
        CFSG.BenderGlauberman.orderOf_conj_eq, hxord]
    have hy2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
      rw [← pow_two, ← hyord, pow_orderOf_eq_one]
    obtain ⟨h1, h1M, h1c⟩ :=
      CFSG.ComponentClassification.AschbacherStrongEmbedding.Lemma34.exists_conj_le_sylow
        (S := S) (H := normalizer (W : Set G)) (P := Subgroup.zpowers x)
        hSM (Subgroup.zpowers_le.mpr hxM)
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord, pow_one]))
    obtain ⟨h2, h2M, h2c⟩ :=
      CFSG.ComponentClassification.AschbacherStrongEmbedding.Lemma34.exists_conj_le_sylow
        (S := S) (H := normalizer (W : Set G)) (P := Subgroup.zpowers (g⁻¹ * x * g))
        hSM (Subgroup.zpowers_le.mpr hyM)
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord, pow_one]))
    set a : G := h1⁻¹ * x * h1 with ha
    set b : G := h2⁻¹ * (g⁻¹ * x * g) * h2 with hb
    have haS : a ∈ (S : Subgroup G) := by
      rw [ha]; exact h1c x (Subgroup.mem_zpowers x)
    have hbS : b ∈ (S : Subgroup G) := by
      rw [hb]; exact h2c (g⁻¹ * x * g) (Subgroup.mem_zpowers _)
    have ha2 : a * a = 1 := by
      rw [ha]
      calc (h1⁻¹ * x * h1) * (h1⁻¹ * x * h1) = h1⁻¹ * (x * x) * h1 := by group
        _ = 1 := by rw [hx2]; group
    have hb2 : b * b = 1 := by
      rw [hb]
      calc (h2⁻¹ * (g⁻¹ * x * g) * h2) * (h2⁻¹ * (g⁻¹ * x * g) * h2)
          = h2⁻¹ * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * h2 := by group
        _ = 1 := by rw [hy2]; group
    have hAe : IsElemTwo A :=
      isElemTwo_of_sq fun a ha => by rw [← pow_two]; exact hA.2 a ha
    have hrank : ∀ y ∈ (S : Subgroup G), y * y = 1 →
        3 ≤ pRank 2 ↥((S : Subgroup G) ⊓ centralizer ({y} : Set G)) := by
      intro y hy hy2
      exact three_le_pRank_of_sq_centralizes hAS hAe hA32 (hSnA hy)
        (fun e _ => by rw [hy2, one_mul, mul_one])
    have hk : (h1⁻¹ * g * h2)⁻¹ * a * (h1⁻¹ * g * h2) = b := by
      rw [ha, hb]; group
    obtain ⟨m, hmM, hm⟩ := hfus a haS (h1⁻¹ * g * h2) (hk.symm ▸ hbS)
      (hrank a haS ha2) (hk.symm ▸ hrank b hbS hb2)
    have hbm : b = m⁻¹ * a * m := hk.symm.trans hm
    refine ⟨h1 * m * h2⁻¹, mul_mem (mul_mem h1M hmM) (inv_mem h2M), ?_⟩
    calc g⁻¹ * x * g = h2 * b * h2⁻¹ := by rw [hb]; group
      _ = h2 * (m⁻¹ * a * m) * h2⁻¹ := by rw [hbm]
      _ = (h1 * m * h2⁻¹)⁻¹ * x * (h1 * m * h2⁻¹) := by rw [ha]; group
  · rw [Subgroup.orderOf_mk]; exact hset.2.1

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
