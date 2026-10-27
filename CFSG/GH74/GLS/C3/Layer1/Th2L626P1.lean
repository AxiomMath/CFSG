module

public import CFSG.GH74.GLS.C3.Layer1.St1P41Cls

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpCalc

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.E2 (Shape2M12 Shape2Sz8 K0Shape)
open CFSG.Open (ordA)

variable {G : Type} [Group G] [Finite G] {z u : G} {J H Λ : Subgroup G}

theorem stable_pumpupC (hr4 : pRank 2 G = 4) (hgen4 : CFSG.GH74.Gen4 G) (hC2 : C2Facts)
    (hJU2 : InU2 (kBar J)) (hJno : ¬ IsL34Quotient (kBar J)) (hJs : IsSimpleGroup (kBar J))
    (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ)
    (hcls : center ↥(bar u H) = ⊥ ∨ InC2 ↥(bar u H)) : z ∈ normalizer (H : Set G) := by
  by_contra hdiag
  have hu2 : orderOf u = 2 := hlt.2.1.1
  have hH : IsPCompIn 2 (centralizer ({u} : Set G)) H := hlt.2.1.2.2
  have hzY : z ∈ centralizer ({u} : Set G) := mem_centralizer_symm hlt.2.2.1
  obtain ⟨e⟩ := kBar_equiv_bar hH
  by_cases hcen : center ↥(bar u H) = ⊥
  · have hq : CFSG.IsQuasisimple (kBar H) := isQuasisimple_hat hH
    have hcenH : center (kBar H) = ⊥ := by
      have h1 := Subgroup.map_center_eq e
      rw [hcen] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
    exact hdiag (PumpGen.mem_normalizer_of_centerless hr4 ⟨hu2, hH⟩ hq hcenH hzY)
  · have hC : InC2 ↥(bar u H) := hcls.resolve_left hcen
    have hP : TwoThin.Gen4Comp ↥(bar u H) :=
      TwoThin.gen4Comp_of_gen4Cen (TwoThin.gen4Cen_barQ hgen4 hu2) _
    obtain ⟨eq⟩ := kBar_equiv_quotient_of_diag hlt hΛ hzY hdiag hJs
    exact hC2.centre _ hP hC hcen (kBar J) hJU2 hJno ⟨eq⟩

theorem isSimpleGroup_of_inU2_not_l34
    {K : Type} [Group K] (hU2 : InU2 K) (hno : ¬ IsL34Quotient K) : IsSimpleGroup K := by
  obtain ⟨-, hcls⟩ := hU2
  rcases hcls with hA | hB | hC
  · obtain ⟨p, f, hp, hf, hodd, hL⟩ := hA
    exact (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hL).2.2
  · obtain ⟨e⟩ := hB
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · exact absurd hC.1 hno

theorem pumpup_rank4C (T : Rank4Tables) (hG : IsKProperSimple G)
    (hB2 : ∀ (X : Type) [Group X] [Finite X], CFSG.GH74.Gen4 X → IsKGroupNative X →
      pPrimeCore 2 X = ⊥ → ∀ y : X, orderOf y = 2 → ∀ K : Subgroup X,
        IsPCompIn 2 (centralizer ({y} : Set X)) K → IsCompIn (centralizer ({y} : Set X)) K)
    (hr4 : pRank 2 G = 4) (hgen4 : CFSG.GH74.Gen4 G) (hC2 : C2Facts)
    (hJU2 : InU2 (kBar J)) (hJno : ¬ IsL34Quotient (kBar J)) (hJs : IsSimpleGroup (kBar J))
    (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ) (hC : InC2 ↥(bar u H)) :
    z ∈ normalizer (H : Set G) ∧ (TrivialPumpup z u J H ∨ VerticalPumpup z u J H Λ) := by
  have hu2 : orderOf u = 2 := hlt.2.1.1
  have hH : IsPCompIn 2 (centralizer ({u} : Set G)) H := hlt.2.1.2.2
  have hJc : IsPCompIn 2 (centralizer ({z} : Set G)) J := hlt.1.2.2
  have hzY : z ∈ centralizer ({u} : Set G) := mem_centralizer_symm hlt.2.2.1
  have hzH : z ∈ normalizer (H : Set G) :=
    stable_pumpupC hr4 hgen4 hC2 hJU2 hJno hJs hlt hΛ (Or.inr hC)
  refine ⟨hzH, ?_⟩
  have hΛJ : Λ ≤ J := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({u} : Set G) := hΛ.le.trans inf_le_right
  have hΛL := bar_le_of_stable hlt hΛ hzH
  have hLc : CFSG.IsComponent (bar u H) := isComponent_bar hH
  have hP : Gen4Comp ↥(bar u H) := gen4Comp_of_gen4Cen (gen4Cen_barQ hgen4 hu2) _
  have hqH : CFSG.IsQuasisimple ↥(bar u H) := hLc.1
  have hs2 : sbar z hzY * sbar z hzY = 1 := by
    have := pow_orderOf_eq_one (sbar z hzY)
    rwa [orderOf_sbar hlt.1.1 hzY, pow_two] at this
  by_cases hcen : ∀ l ∈ bar u H, sbar z hzY * l * (sbar z hzY)⁻¹ = l
  ·
    have hEq := lam_eq_of_central hlt hΛ hzY hzH hcen
    by_cases hZ : center ↥(bar u H) = ⊥
    · exact Or.inl (stable_trivial hlt hΛ hzY hzH hcen (isSimple_of_quasisimple_center_bot hqH hZ))
    · exfalso
      obtain ⟨φ, hφs, -, -⟩ := exists_phi hΛJ hΛY hΛ.cover
      have hqΛ : CFSG.IsQuasisimple ↥(bar u Λ) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hqH
      obtain ⟨eJ⟩ := equiv_quotient_center_of_surjective hqΛ hJs φ hφs
      have e4 : kBar J ≃* ↥(bar u H) ⧸ center ↥(bar u H) :=
        eJ.trans (GH74.E2.centerQuotientEquiv (MulEquiv.subgroupCongr hEq))
      exact hC2.centre _ hP hC hZ (kBar J) hJU2 hJno ⟨e4⟩
  ·
    right
    have hMstab := map_conj_bar_of_normalizes (u := u) (X := H) hzY hzH
    have hN : sbar z hzY ∈ normalizer ((bar u H : Subgroup _) : Set _) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMstab
    let σ : MulAut ↥(bar u H) := conjAut hN
    have hσ : ∀ l, σ (σ l) = l := by
      intro l
      apply Subtype.ext
      show sbar z hzY * (sbar z hzY * (l : _) * (sbar z hzY)⁻¹) * (sbar z hzY)⁻¹ = l
      calc sbar z hzY * (sbar z hzY * (l : _) * (sbar z hzY)⁻¹) * (sbar z hzY)⁻¹
          = (sbar z hzY * sbar z hzY) * (l : _) * (sbar z hzY * sbar z hzY)⁻¹ := by group
        _ = l := by rw [hs2]; group
    have hσ2 : σ ^ 2 = 1 := by
      refine MulEquiv.ext fun l => ?_
      rw [pow_two, MulAut.mul_apply, hσ l]
      rfl
    have hσ1 : σ ≠ 1 := by
      push Not at hcen
      obtain ⟨l₀, hl₀, hne⟩ := hcen
      intro h
      apply hne
      have h1 : ((σ ⟨l₀, hl₀⟩ : ↥(bar u H)) : barQ ↥(centralizer ({u} : Set G))) = l₀ := by
        rw [h]; rfl
      exact h1
    have hΛq : CFSG.IsQuasisimple ↥(bar u Λ) := bar_lam_quasisimple hG hB2 hgen4 hlt hΛ
    set L' : Subgroup ↥(bar u H) := (bar u Λ).subgroupOf (bar u H) with hL'
    have hL'q : CFSG.IsQuasisimple ↥L' :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hΛL).symm hΛq
    have hF : ∀ x ∈ L', σ x = x := by
      intro l hl
      apply Subtype.ext
      exact bar_lam_le_centralizer hzY hΛ (l : _) (Subgroup.mem_subgroupOf.mp hl)
    have key : Shape2M12 ↥(bar u H) := by
      rcases T.c2shape _ hC hP with ⟨hc0, hsimple⟩ | h2M | h2S
      · exfalso
        rcases hsimple with ⟨p, f, hp, hp2, hfm, hlie⟩ | hL28 | hL33 | hU33 | hSz | hM11
        · have hf1 : 1 ≤ f := (CFSG.GH74.Generic.stated_of_lieModel_PSL hlie).1.2.1
          exact hcen (sbar_central hlt hΛ hzY hzH ⟨p, f, hp, hf1, hfm, hlie⟩)
        · exact false_of_shape2M12_of_center_bot
            (T.k0fixed _ (K0Shape.of_L28 hL28) σ hσ2 hσ1 L' hF hL'q) hc0
        · exact false_of_shape2M12_of_center_bot
            (T.k0fixed _ (K0Shape.of_L33 hL33) σ hσ2 hσ1 L' hF hL'q) hc0
        · exact false_of_shape2M12_of_center_bot
            (T.k0fixed _ (K0Shape.of_U33 hU33) σ hσ2 hσ1 L' hF hL'q) hc0
        · exact false_of_shape2M12_of_center_bot
            (T.k0fixed _ (K0Shape.of_Sz8 hSz) σ hσ2 hσ1 L' hF hL'q) hc0
        · exact false_of_shape2M12_of_center_bot
            (T.k0fixed _ (K0Shape.of_M11 hM11) σ hσ2 hσ1 L' hF hL'q) hc0
      · exact h2M
      · exfalso
        exact T.noBoth _ (T.k0fixed _ (K0Shape.of_2Sz8 h2S) σ hσ2 hσ1 L' hF hL'q) h2S
    have h60 : Nat.card ↥L' = 60 := T.fixed60 _ key σ hσ2 hσ1 L' hF hL'q
    have hΛ60 : Nat.card ↥(bar u Λ) = 60 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛL).toEquiv).symm.trans h60
    obtain ⟨φ, hφs, -, -⟩ := exists_phi hΛJ hΛY hΛ.cover
    have hJq : CFSG.IsQuasisimple (kBar J) := isQuasisimple_hat hJc
    have hle : Nat.card (kBar J) ≤ 60 := hΛ60 ▸ Nat.card_le_card_of_surjective φ hφs
    have hge : 60 ≤ Nat.card (kBar J) :=
      CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty hJs (exists_noncomm_of_isQuasisimple' hJq)
    have hJ60 : Nat.card (kBar J) = 60 := le_antisymm hle hge
    refine ⟨?_, hJs, key, hΛ60, hΛq, hzY, ?_⟩
    · rcases hJU2.2 with ⟨p, f, hp, hf, hodd, hLie⟩ | hA7 | hL34
      · have hcard : Nat.card (kBar J) = ordA 1 (p ^ f) := by
          simpa using card_of_lieModel_PSL (n := 2) (by norm_num) hLie
        exact ⟨p, f, hp, hf, eq_five_of_ordA_sixty hodd (hcard ▸ hJ60), hLie⟩
      · exfalso
        obtain ⟨e⟩ := hA7
        have : Nat.card (kBar J) = 2520 := by
          rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
            Fintype.card_fin]
          decide
        omega
      · exact absurd hL34.1 hJno
    · push Not at hcen
      obtain ⟨l, hl, hne⟩ := hcen
      exact ⟨l, hl, hne⟩

end CFSG.GH74.GLS.C3.Layer1.PumpCalc
