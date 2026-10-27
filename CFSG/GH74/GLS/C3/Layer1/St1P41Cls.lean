module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.GLS.C3.Layer1.St1PumpClass
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpCalc

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.E2 (Shape2M12 Shape2Sz8 K0Shape)
open CFSG.Open (ordA)

structure Rank4Tables : Prop where
  c2shape : ∀ (L : Type) [Group L] [Finite L], InC2 L → Gen4Comp L → C2Shape L
  k0fixed : ∀ (K : Type) [Group K] [Finite K], K0Shape K → ∀ α : MulAut K, α ^ 2 = 1 → α ≠ 1 →
    ∀ L : Subgroup K, (∀ x ∈ L, α x = x) → CFSG.IsQuasisimple ↥L → Shape2M12 K
  fixed60 : ∀ (K : Type) [Group K] [Finite K], Shape2M12 K → ∀ α : MulAut K, α ^ 2 = 1 → α ≠ 1 →
    ∀ L : Subgroup K, (∀ x ∈ L, α x = x) → CFSG.IsQuasisimple ↥L → Nat.card ↥L = 60
  noBoth : ∀ (K : Type) [Group K] [Finite K], Shape2M12 K → Shape2Sz8 K → False

variable {G : Type} [Group G] [Finite G] {z u : G} {J H Λ : Subgroup G}

theorem eq_five_of_ordA_sixty {q : ℕ} (hq : Odd q) (h : ordA 1 q = 60) : q = 5 := by
  obtain ⟨k, rfl⟩ := hq
  rw [PumpClass.ordA_one_odd] at h
  have hk : k ≤ 3 := by
    by_contra hk
    have hk4 : 4 ≤ k := by omega
    have : 2 * 4 * (4 + 1) * (2 * 4 + 1) ≤ 2 * k * (k + 1) * (2 * k + 1) := by gcongr
    omega
  interval_cases k <;> omega

theorem isSimple_of_quasisimple_center_bot {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (hc : center Q = ⊥) : IsSimpleGroup Q := by
  have e : Q ⧸ center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr e).mp hq.2.1

theorem false_of_shape2M12_of_center_bot {K : Type} [Group K] (h : Shape2M12 K) (hc : center K = ⊥) :
    False := by
  have h2 := h.2.1
  rw [hc] at h2
  simp at h2


theorem bar_lam_quasisimple (hG : IsKProperSimple G)
    (hB2 : ∀ (X : Type) [Group X] [Finite X], CFSG.GH74.Gen4 X → IsKGroupNative X →
      pPrimeCore 2 X = ⊥ → ∀ y : X, orderOf y = 2 → ∀ K : Subgroup X,
        IsPCompIn 2 (centralizer ({y} : Set X)) K → IsCompIn (centralizer ({y} : Set X)) K)
    (hgen4 : CFSG.GH74.Gen4 G) (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ) :
    CFSG.IsQuasisimple ↥(bar u Λ) := by
  have hu : orderOf u = 2 := hlt.2.1.1
  have hz : orderOf z = 2 := hlt.1.1
  have hzY : z ∈ centralizer ({u} : Set G) := mem_centralizer_symm hlt.2.2.1
  set Y' := centralizer ({u} : Set G) with hY'
  have hY'ne : Y' ≠ ⊤ := centralizer_involution_ne_top hG.1 hG.2.1 hu
  have hX : IsKGroupNative (barQ ↥Y') :=
    isKGroupNative_of_surjective (X := ↥Y') (isKGroupNative_of_kProper hG.2.2 hY'ne) ⊤
      ((barMk ↥Y').comp (⊤ : Subgroup ↥Y').subtype)
      (barMk_surjective.comp fun m => ⟨⟨m, trivial⟩, rfl⟩)
  have hso : orderOf (⟨z, hzY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hzY hz
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛ.pcW).1 hzY
  have hΛ2 := isTwoComponent_centralizer_mk hΛ.pcW hzY
  have hmap2 := isTwoComponent_map_barMk hso hΛC hΛ2
  have hle : bar u Λ ≤ centralizer ({sbar z hzY} : Set _) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (by
      have := bar_lam_le_centralizer hzY hΛ w hw
      calc w * sbar z hzY = sbar z hzY * w * (sbar z hzY)⁻¹ * sbar z hzY := by rw [this]
        _ = sbar z hzY * w := by group)
  have hpc : IsPCompIn 2 (centralizer ({sbar z hzY} : Set _)) (bar u Λ) :=
    isPCompIn_two_iff.mpr ⟨hle, hmap2⟩
  have hcore : pPrimeCore 2 (barQ ↥Y') = ⊥ := by
    have := oddCore_barQ (Y := ↥Y')
    rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hg4 : CFSG.GH74.Gen4 (barQ ↥Y') := CFSG.GH74.Gen4.quotient _ (CFSG.GH74.Gen4.subgroup Y' hgen4)
  have hcomp := hB2 _ hg4 hX hcore (sbar z hzY) (orderOf_sbar hz hzY) (bar u Λ) hpc
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hcomp.2.1

theorem lam_eq_of_central (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ)
    (hzY : z ∈ centralizer ({u} : Set G)) (hzH : z ∈ normalizer (H : Set G))
    (hcen : ∀ l ∈ bar u H, sbar z hzY * l * (sbar z hzY)⁻¹ = l) : bar u Λ = bar u H := by
  have hz : orderOf z = 2 := hlt.1.1
  have hH : IsPCompIn 2 (centralizer ({u} : Set G)) H := hlt.2.1.2.2
  set Y' := centralizer ({u} : Set G) with hY'
  have hΛL := bar_le_of_stable hlt hΛ hzH
  have hso : orderOf (⟨z, hzY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hzY hz
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛ.pcW).1 hzY
  have hΛ2 := isTwoComponent_centralizer_mk hΛ.pcW hzY
  have hmap2 := isTwoComponent_map_barMk hso hΛC hΛ2
  have hsubC : ((bar u Λ).subgroupOf (centralizer ({sbar z hzY} : Set _))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain hmap2.1 Subgroup.IsSubnormal.top
  have hHC : bar u H ≤ centralizer ({sbar z hzY} : Set _) := fun l hl =>
    mem_centralizer_singleton_iff.mpr (by
      have := hcen l hl
      calc l * sbar z hzY = sbar z hzY * l * (sbar z hzY)⁻¹ * sbar z hzY := by rw [this]
        _ = sbar z hzY * l := by group)
  have hsubH := isSubnormal_inf_subgroupOf hsubC hHC
  have hqs : CFSG.IsQuasisimple ↥(bar u H) :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).1
      (assembly_isQuasisimple_of_isComponent (isComponent_bar hH))
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hqs hsubH with
    htop | hcent
  · refine le_antisymm hΛL fun l hl => ?_
    have : (⟨l, hl⟩ : ↥(bar u H)) ∈ (bar u Λ).subgroupOf (bar u H) := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  · exfalso
    refine bar_lam_ne_bot hΛ ?_
    have hc : ⁅bar u Λ, bar u Λ⁆ = ⊥ := by
      rw [Subgroup.commutator_le.mpr (fun a ha b hb => ?_) |> fun h => (le_bot_iff.mp h)]
      have h1 := hcent (Subgroup.mem_subgroupOf.mpr ha : (⟨a, hΛL ha⟩ : ↥(bar u H)) ∈
        (bar u Λ).subgroupOf (bar u H))
      have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hΛL hb⟩
      have h3 : b * a = a * b := congrArg Subtype.val h2
      rw [Subgroup.mem_bot, commutatorElement_def]
      calc a * b * a⁻¹ * b⁻¹ = (a * b) * (b * a)⁻¹ := by group
        _ = 1 := by rw [h3]; group
    rw [← bar_lam_perfect hΛ, hc]


@[expose] def TrivialPumpup (z u : G) (J H : Subgroup G) : Prop :=
  Nonempty (kBar H ≃* kBar J) ∧ (∀ q ∈ CxK z J, u * q = q * u → q ∈ CxK u H) ∧ z ∈ CxK u H

@[expose] def VerticalPumpup (z u : G) (J H Λ : Subgroup G) : Prop :=
  HasL2Model (kBar J) (fun q => q = 5) ∧ IsSimpleGroup (kBar J) ∧ Shape2M12 ↥(bar u H) ∧
    Nat.card ↥(bar u Λ) = 60 ∧ CFSG.IsQuasisimple ↥(bar u Λ) ∧
    ∃ hzY : z ∈ centralizer ({u} : Set G), ∃ l ∈ bar u H, sbar z hzY * l * (sbar z hzY)⁻¹ ≠ l

theorem pumpup_rank4 (T : Rank4Tables) (hG : IsKProperSimple G)
    (hB2 : ∀ (X : Type) [Group X] [Finite X], CFSG.GH74.Gen4 X → IsKGroupNative X →
      pPrimeCore 2 X = ⊥ → ∀ y : X, orderOf y = 2 → ∀ K : Subgroup X,
        IsPCompIn 2 (centralizer ({y} : Set X)) K → IsCompIn (centralizer ({y} : Set X)) K)
    (hr4 : pRank 2 G = 4) (hgen4 : CFSG.GH74.Gen4 G) (T7 : St1Thm7 G) (hC2 : C2Facts)
    (hJU2 : InU2 (kBar J)) (hJno : ¬ IsL34Quotient (kBar J)) (hJs : IsSimpleGroup (kBar J))
    (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ) :
    z ∈ normalizer (H : Set G) ∧ (TrivialPumpup z u J H ∨ VerticalPumpup z u J H Λ) := by
  have hu2 : orderOf u = 2 := hlt.2.1.1
  have hH : IsPCompIn 2 (centralizer ({u} : Set G)) H := hlt.2.1.2.2
  have hJc : IsPCompIn 2 (centralizer ({z} : Set G)) J := hlt.1.2.2
  have hzY : z ∈ centralizer ({u} : Set G) := mem_centralizer_symm hlt.2.2.1
  have hzH : z ∈ normalizer (H : Set G) := stable_pumpup hr4 hgen4 T7 hC2 hJU2 hJno hJs hlt hΛ
  refine ⟨hzH, ?_⟩
  have hΛJ : Λ ≤ J := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({u} : Set G) := hΛ.le.trans inf_le_right
  have hΛL := bar_le_of_stable hlt hΛ hzH
  have hLc : CFSG.IsComponent (bar u H) := isComponent_bar hH
  have hC : InC2 ↥(bar u H) := T7 u hu2 (bar u H) hLc
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
