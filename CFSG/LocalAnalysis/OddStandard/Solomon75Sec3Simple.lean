module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Reduction
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Skeleton
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusAmbient
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Quot

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.ComponentClassification CFSG.GH74.GLS

open scoped commutatorElement

section Narrow

variable {X : Type} [Group X] [Finite X]

theorem le_pLayer_of_isPComponent_cen {t : X} (ht : orderOf t = 2) {L : Subgroup X}
    (hLC : L ≤ centralizer ({t} : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X)))) : L ≤ pLayer X 2 := by
  have h1 : L.subgroupOf (centralizer ({t} : Set X)) ≤ pLayer ↥(centralizer ({t} : Set X)) 2 :=
    le_sSup hL
  have h2 := Subgroup.map_mono (f := (centralizer ({t} : Set X)).subtype) h1
  rw [Subgroup.map_subgroupOf_eq_of_le hLC] at h2
  have hB : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  have h3 := layer_balance (zpowers t) hB
  rw [ComponentClassification.UnbalancedLayer.centralizer_zpowers_eq] at h3
  exact h2.trans h3

theorem isPComponent_of_isPComponent_subgroupOf_top {L : Subgroup X}
    (hL : IsPComponent 2 (L.subgroupOf (⊤ : Subgroup X))) : IsPComponent 2 L := by
  rw [isPComponent_two_iff] at hL ⊢
  exact ⟨Subgroup.IsSubnormal.trans le_top hL.1 Subgroup.IsSubnormal.top,
    (isTwoGenQuasi_subgroupOf_iff le_top).1 hL.2⟩

theorem IsAhatIntr.le_KProd_of_mem_center {t : X} {L : Subgroup X} (hL : IsAhatIntr X t L)
    (htZ : t ∈ center X) : L ≤ KProd X := by
  have htop : centralizer ({t} : Set X) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.2 (by simpa using htZ)
  have hpc := hL.2.2.1
  rw [htop] at hpc
  have hpc' : IsPComponent 2 L := isPComponent_of_isPComponent_subgroupOf_top hpc
  obtain ⟨n, hn, hcov⟩ := hL.2.2.2
  exact le_sSup ⟨hpc', hcov.1, Or.inl ⟨n, hn, hcov⟩⟩


variable {t : X} {L : Subgroup X}

theorem SolMinCEx.not_le_of_subnormal_of_isAhatIntr (h : SolMinCEx X) (ht : orderOf t = 2)
    (hL : IsAhatIntr X t L) (hnot : ¬ L ≤ KProd X) {N : Subgroup X} (hN : N.IsSubnormal)
    (hNtop : N ≠ ⊤) : ¬ L ≤ N :=
  fun hLN => hnot (h.le_KProd_of_le_subnormal hN hNtop ht (hLN hL.2.1) hLN (Or.inl hL))

theorem SolMinCEx.layer_eq_top_of_isAhatIntr (h : SolMinCEx X) (ht : orderOf t = 2)
    (hL : IsAhatIntr X t L) (hnot : ¬ L ≤ KProd X) : layer X = ⊤ := by
  have hLp : L ≤ pLayer X 2 := le_pLayer_of_isPComponent_cen ht hL.1 hL.2.2.1
  have hpl : pLayer X 2 = ⊤ := by
    by_contra hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar : (pLayer X 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic (p := 2)
    have hn : (pLayer X 2).Normal := inferInstance
    exact h.not_le_of_subnormal_of_isAhatIntr ht hL hnot hn.isSubnormal hne hLp
  rw [← ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot
    h.pPrimeCore_eq_bot]
  exact hpl

theorem SolMinCEx.isComponent_top_of_isAhatIntr (h : SolMinCEx X) (ht : orderOf t = 2)
    (hL : IsAhatIntr X t L) (hnot : ¬ L ≤ KProd X) : IsComponent (⊤ : Subgroup X) := by
  have hlayer := h.layer_eq_top_of_isAhatIntr ht hL hnot
  obtain ⟨K, hK⟩ : ∃ K : Subgroup X, IsComponent K := by
    by_contra hno
    push Not at hno
    have h1 : layer X = ⊥ := LocalCores.layer_eq_bot_of_forall hno
    have ht1 : t = 1 := by
      have : t ∈ layer X := hlayer ▸ Subgroup.mem_top t
      rw [h1] at this
      exact Subgroup.mem_bot.mp this
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hKn : K.Normal := LocalCores.component_normal_of_layer_eq_top hlayer hK
  set Y : Subgroup X := centralizer (K : Set X) with hYdef
  have hYn : Y.Normal := Subgroup.normal_centralizer
  have hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k := fun k hk y hy =>
    Subgroup.mem_centralizer_iff.mp hy k hk
  have hsup : Y ⊔ K = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hlayer]
    refine sSup_le fun K' hK' => ?_
    rcases LocalCores.distinct_components_commute hK' hK with rfl | hcomm
    · exact le_sup_right
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans le_sup_left
  have hdich : L ≤ K ∨ L ≤ Y := by
    set D : Subgroup X := centralizer ({t} : Set X) with hD
    have hc0 := commutator_centralizer_le_of_central_product hKY hsup t
    have hc1 : commutator ↥D ≤ ((Y ⊓ D) ⊔ (K ⊓ D)).subgroupOf D := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      exact hc0 (Subgroup.commutator_mem_commutator a.2 b.2)
    have hc2 : commutator ↥D ≤ K.subgroupOf D ⊔ Y.subgroupOf D := by
      refine hc1.trans ?_
      rw [Subgroup.subgroupOf_sup inf_le_right inf_le_right, Subgroup.inf_subgroupOf_right,
        Subgroup.inf_subgroupOf_right, sup_comm]
    have : (K.subgroupOf D).Normal := hKn.subgroupOf D
    have : (Y.subgroupOf D).Normal := hYn.subgroupOf D
    rcases isPComponent_le_or_le_of_commutator_le hc2 hL.2.2.1 with hLK | hLY
    · exact Or.inl fun x hx => hLK (show (⟨x, hL.1 hx⟩ : ↥D) ∈ L.subgroupOf D from hx)
    · exact Or.inr fun x hx => hLY (show (⟨x, hL.1 hx⟩ : ↥D) ∈ L.subgroupOf D from hx)
  have hYtop : Y ≠ ⊤ := by
    intro hYtop
    have hKK : K ≤ centralizer (K : Set X) := by
      show K ≤ Y
      rw [hYtop]
      exact le_top
    have hbot : ⁅K, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKK
    have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
    rw [hperf] at hbot
    have : Nontrivial ↥K := LocalCores.isQuasisimple_nontrivial hK.1
    exact (Subgroup.nontrivial_iff_ne_bot K).1 this hbot
  have hKtop : K = ⊤ := by
    rcases hdich with hLK | hLY
    · by_contra hne
      exact h.not_le_of_subnormal_of_isAhatIntr ht hL hnot hKn.isSubnormal hne hLK
    · exact absurd hLY (h.not_le_of_subnormal_of_isAhatIntr ht hL hnot hYn.isSubnormal hYtop)
  rwa [hKtop] at hK

theorem nonempty_equiv_of_ne_bot_KProd {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) (hne : KProd G ≠ ⊥) :
    Nonempty (G ≃* Blueprint.NativeSporadic.McL) ∨ Nonempty (G ≃* Blueprint.NativeSporadic.Ly) := by
  obtain ⟨J, hJ, hJne⟩ : ∃ J : Subgroup G, IsKComp J ∧ J ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hne (le_bot_iff.mp (sSup_le fun J hJ => (hcon J hJ).le))
  have hJtop : J = ⊤ := isKComp_top_of_ne_bot hJ hJne
  subst hJtop
  have : IsSimpleGroup ↥(⊤ : Subgroup G) := Subgroup.topEquiv.isSimpleGroup
  have hbot : pPrimeCore 2 ↥(⊤ : Subgroup G) = ⊥ := by
    rcases (inferInstance : (pPrimeCore 2 ↥(⊤ : Subgroup G)).Normal).eq_bot_or_eq_top with h1 | h1
    · exact h1
    · exfalso
      have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(⊤ : Subgroup G))) :=
        pPrimeCore_coprime_card
      rw [h1, Subgroup.card_top] at h2
      have h3 : 2 ∣ Nat.card ↥(⊤ : Subgroup G) := by
        rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
        exact hz ▸ orderOf_dvd_natCard z
      exact absurd (Nat.Coprime.eq_one_of_dvd h2 h3) (by norm_num)
  let e : (↥(⊤ : Subgroup G) ⧸ pPrimeCore 2 ↥(⊤ : Subgroup G)) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  exact nonempty_equiv_of_isKType_of_simple hnonab e hJ.2

theorem SolMinCEx.center_eq_bot_of_isAhatIntr (h : SolMinCEx X) (ht : orderOf t = 2)
    (hL : IsAhatIntr X t L) (hnot : ¬ L ≤ KProd X) : center X = ⊥ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp := h.isComponent_top_of_isAhatIntr ht hL hnot
  have hXq : IsQuasisimple X := LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv hcomp.1
  by_contra hZ
  have htZ : t ∉ center X := fun htZ => hnot (hL.le_KProd_of_mem_center htZ)
  have hπ := h.ihQuot (N := center X) hZ
  have ht2 : orderOf (QuotientGroup.mk t : X ⧸ center X) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, ← ht, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      exact htZ ((QuotientGroup.eq_one_iff t).1 h1)
  have hLbar := hL.map_center ht htZ
  have hKbar : L.map (QuotientGroup.mk' (center X)) ≤ KProd (X ⧸ center X) :=
    hπ _ ht2 _ (Or.inl hLbar)
  have hne : KProd (X ⧸ center X) ≠ ⊥ := by
    intro hbot
    have hmem : (QuotientGroup.mk t : X ⧸ center X) ∈ L.map (QuotientGroup.mk' (center X)) :=
      Subgroup.mem_map_of_mem _ hL.2.1
    have h1 := hKbar hmem
    rw [hbot, Subgroup.mem_bot] at h1
    exact htZ ((QuotientGroup.eq_one_iff t).1 h1)
  have : IsSimpleGroup (X ⧸ center X) := hXq.2.1
  have hKT := nonempty_equiv_of_ne_bot_KProd hXq.2.2 ht2 hne
  have hXK : IsKType X := ⟨hXq, Or.inr hKT⟩
  have hbot2 : pPrimeCore 2 X = ⊥ := h.pPrimeCore_eq_bot
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hPC : IsPComponent 2 (⊤ : Subgroup X) :=
    LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp (fun hle => by
      rw [hbot2] at hle
      exact ht1 (Subgroup.mem_bot.mp (hle (Subgroup.mem_top t))))
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X))
  let e1 : X ⧸ pPrimeCore 2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hbot2).trans QuotientGroup.quotientBot
  have hKT' : IsKType (↥(⊤ : Subgroup X) ⧸ pPrimeCore 2 ↥(⊤ : Subgroup X)) :=
    IsKType.congr (e1.symm.trans f) hXK
  exact hnot (le_top.trans (le_sSup ⟨hPC, hKT'⟩))

theorem SolMinCEx.isSimpleGroup_of_isAhatIntr (h : SolMinCEx X) (ht : orderOf t = 2)
    (hL : IsAhatIntr X t L) (hnot : ¬ L ≤ KProd X) : IsSimpleGroup X := by
  have hZ := h.center_eq_bot_of_isAhatIntr ht hL hnot
  have hcomp := h.isComponent_top_of_isAhatIntr ht hL hnot
  have hXq : IsQuasisimple X := LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv hcomp.1
  have : IsSimpleGroup (X ⧸ center X) := hXq.2.1
  let e : X ≃* X ⧸ center X :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact e.isSimpleGroup

end Narrow

end CFSG.OddStandard.Solomon75
