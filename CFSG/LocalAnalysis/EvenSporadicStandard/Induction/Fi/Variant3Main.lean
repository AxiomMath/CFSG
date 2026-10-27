module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Lemma33
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.LastProof
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.DiagProof
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Six
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Row
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Outer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLemma39N
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSTransport
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Walter.JRFacts

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def FiVariantThreeNM : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ¬ IsSporadic ↥N .Fi22 →
        ¬ IsSporadic ↥N .Fi23 → ¬ IsSporadic ↥N .Fi24Prime → NoBiggerFi H .Fi24Prime →
          (∃ L₀ : Subgroup H, SolStd L₀ ∧ OddCover .Fi24Prime L₀) →
            (∃ P : Subgroup H, InL P ∧ IsSporadic (↥P ⧸ center ↥P) .Fi23 ∧ ¬ Maximal P) →
              ∃ (s' : TauCeti.SporadicName) (L' : Subgroup H), s' ∈ fiTypes ∧ OddCover s' L' ∧
                FiOut H N L' s'

section Facts

variable {H : Type} [Group H] [Finite H]

theorem cqEq_isKFi23 : CqEq IsKFi23 := by
  intro X Y _ _ hX hY
  obtain ⟨-, -, ⟨e₁⟩⟩ := hX
  obtain ⟨-, -, ⟨e₂⟩⟩ := hY
  exact ⟨e₁.trans e₂.symm⟩

theorem isSporadic_cq_of_isKFi23 {K : Subgroup H} (hKq : CFSG.IsQuasisimple ↥K)
    (hK : IsKFi23 (↥K ⧸ CFSG.oddCore ↥K)) : IsSporadic (↥K ⧸ center ↥K) .Fi23 := by
  have : Group.IsPerfect ↥K := hKq.1
  obtain ⟨e⟩ := cqEquiv_of_central_cover (QuotientGroup.mk' (CFSG.oddCore ↥K))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact oddCore_le_center_of_isQuasisimple hKq)
  obtain ⟨-, -, ⟨f⟩⟩ := hK
  exact ⟨e.trans f⟩

omit [Finite H] in
theorem card_le_of_isKFi23 (ho : Fi23Order) {K : Subgroup H}
    (hK : IsKFi23 (↥K ⧸ CFSG.oddCore ↥K)) :
    4089470473293004800 ≤ Nat.card (↥K ⧸ CFSG.oddCore ↥K) := by
  obtain ⟨hfin, -, ⟨f⟩⟩ := hK
  have h1 : Nat.card ((↥K ⧸ CFSG.oddCore ↥K) ⧸ center (↥K ⧸ CFSG.oddCore ↥K)) ≤
      Nat.card (↥K ⧸ CFSG.oddCore ↥K) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (center (↥K ⧸ CFSG.oddCore ↥K)))
  rw [Nat.card_congr f.toEquiv, ho] at h1
  exact h1

theorem noFixedEmbeds_of_le {K : Type} [Group K] {G : Type} [Group G] {Λ Λ' : Subgroup G}
    (hle : Λ' ≤ Λ) (h : NoFixedEmbeds K ↥Λ) : NoFixedEmbeds K ↥Λ' := by
  intro α h1 h2
  obtain ⟨hA, hB⟩ := h α h1 h2
  refine ⟨fun ⟨f, hf⟩ => hA ⟨(Subgroup.inclusion hle).comp f, ?_⟩, fun hin ⟨f, hf⟩ =>
    hB hin ⟨(Subgroup.inclusion hle).comp f, ?_⟩⟩
  · exact (Subgroup.inclusion_injective hle).comp hf
  · exact (Subgroup.inclusion_injective hle).comp hf

end Facts

section Layers

open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

structure OuterLayer (K : Subgroup H) (v : H) (M : Subgroup H) : Prop where
  comp : IsCompIn M (centralizer ({v} : Set H))
  cover : OddCover .Fi24Prime M
  std : SolStd M
  le : K ≤ M

theorem typeL_facts (lit : Sol78Lit) (hH : Balance.UHered H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hN : FStarSimple N)
    (hyp : Hyp31NS H N IsKFi23 (IsLS [.Fi24Prime])) {M : Subgroup H} (hM : InL M)
    (hLS : IsLS [.Fi24Prime] ↥M) :
    SolStd M ∧ (∃ S : Sylow 2 (centralizer (M : Set H)), IsCyclic ↥S) ∧
      ∀ y : H, 3 ≤ CFSG.pRank 2 ↥(M.map (MulAut.conj y).toMonoidHom) := by
  have hmax := hyp.type_max M hM hLS
  have hrank0 : 3 ≤ CFSG.pRank 2 ↥M := (hyp.quasi_L ↥M hLS).2.2
  have hstd : StdBare M := lit.thm22 H hH hkp N hN hyp.index_le_two M hmax.1 hrank0
  exact ⟨solStd_of_inL_stdBare hM hstd, hmax.2, fun y =>
    (hyp.quasi_L _ (hyp.isL_inv _ _ (Subgroup.equivMapOfInjective M
      (MulAut.conj y).toMonoidHom (MulAut.conj y).injective) hLS)).2.2⟩

theorem commutatorElement_mul_central {G : Type*} [Group G] {k₁ k₂ z₁ z₂ : G}
    (h₁ : ∀ g : G, g * z₁ = z₁ * g) (h₂ : ∀ g : G, g * z₂ = z₂ * g) :
    ⁅k₁ * z₁, k₂ * z₂⁆ = ⁅k₁, k₂⁆ := by
  have cj₁ : ∀ g : G, z₁ * g * z₁⁻¹ = g := fun g => by rw [← h₁ g]; group
  have cj₂ : ∀ g : G, z₂ * g * z₂⁻¹ = g := fun g => by rw [← h₂ g]; group
  calc ⁅k₁ * z₁, k₂ * z₂⁆
      = k₁ * (z₁ * (k₂ * z₂) * z₁⁻¹) * k₁⁻¹ * (z₂⁻¹ * k₂⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = k₁ * (k₂ * z₂) * k₁⁻¹ * (z₂⁻¹ * k₂⁻¹) := by rw [cj₁]
    _ = k₁ * k₂ * (z₂ * k₁⁻¹ * z₂⁻¹) * k₂⁻¹ := by group
    _ = ⁅k₁, k₂⁆ := by rw [cj₂]; simp only [commutatorElement_def]

end Layers

section Unique

open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem eq_of_equiv_of_outer (hF : Fi24OuterFixed) {L K K' : Subgroup H} {u : H}
    (hq : CFSG.IsQuasisimple ↥L) (hodd : Odd (Nat.card ↥(center ↥L)))
    (hY : IsSporadic (↥L ⧸ center ↥L) .Fi24Prime) (huN : u ∈ normalizer (L : Set H))
    (hu2 : orderOf u = 2) (hunot : u ∉ L ⊔ centralizer (L : Set H)) (hKL : K ≤ L)
    (hKq : CFSG.IsQuasisimple ↥K) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcard : 4089470473293004800 ≤ Nat.card (↥K ⧸ CFSG.oddCore ↥K)) (hK'L : K' ≤ L)
    (hK'u : ∀ k ∈ K', k * u = u * k) (e : ↥K' ≃* ↥K) : K' = K := by
  have hbar := bar_eq_fix_of_outer hF hq hodd hY huN hu2 hunot hKL hKq hKu hcard
  have hle : Cover.bar (K'.subgroupOf L) ≤ Cover.bar (K.subgroupOf L) :=
    hbar ▸ bar_le_fix_of_commute huN hK'u
  have hK'q : CFSG.IsQuasisimple ↥K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hKq
  have hmem : ∀ (a : H) (ha : a ∈ K'), ∃ k z : ↥L, (k : H) ∈ K ∧ z ∈ center ↥L ∧
      (⟨a, hK'L ha⟩ : ↥L) = k * z := by
    intro a ha
    have hx : (⟨a, hK'L ha⟩ : ↥L) ∈ K'.subgroupOf L := Subgroup.mem_subgroupOf.2 ha
    have hy : ((⟨a, hK'L ha⟩ : ↥L) : ↥L ⧸ center ↥L) ∈ Cover.bar (K'.subgroupOf L) :=
      Cover.mem_bar.2 ⟨_, hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := Cover.mem_bar.1 (hle hy)
    exact ⟨k, k⁻¹ * ⟨a, hK'L ha⟩, Subgroup.mem_subgroupOf.1 hk, QuotientGroup.eq.1 hkx, by group⟩
  have hcomm : ⁅K', K'⁆ ≤ K := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨k₁, z₁, hk₁, hz₁, h₁⟩ := hmem a ha
    obtain ⟨k₂, z₂, hk₂, hz₂, h₂⟩ := hmem b hb
    have hc : (⁅(⟨a, hK'L ha⟩ : ↥L), (⟨b, hK'L hb⟩ : ↥L)⁆ : ↥L) = ⁅k₁, k₂⁆ := by
      rw [h₁, h₂]
      exact commutatorElement_mul_central (Subgroup.mem_center_iff.1 hz₁)
        (Subgroup.mem_center_iff.1 hz₂)
    have hab : ⁅a, b⁆ = ((⁅k₁, k₂⁆ : ↥L) : H) := by
      rw [← hc]
      rfl
    rw [hab]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
  have hperf : ⁅K', K'⁆ = K' := Cover.commutator_eq_self_of_isPerfect hK'q.1
  exact Subgroup.eq_of_le_of_card_ge (hperf ▸ hcomm) (Nat.card_congr e.toEquiv).ge

end Unique

section Dichotomy

variable {H : Type} [Group H] [Finite H] {N L K : Subgroup H} {t v : H}

theorem outer_dichotomy (lit : Sol78Lit) (hH : Balance.UHered H) (hpin : FiV3Pinned)
    (hN : FStarSimple N) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (hcov : OddCover .Fi24Prime L)
    (hSol : SolStd L) (ht2 : orderOf t = 2) (htL : t ∈ centralizer (L : Set H))
    (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K)
    (hcard : 4089470473293004800 ≤ Nat.card (↥K ⧸ CFSG.oddCore ↥K))
    (hv2 : orderOf v = 2) (hvN : v ∈ normalizer (L : Set H))
    (hvnot : v ∉ L ⊔ centralizer (L : Set H)) (hKv : ∀ k ∈ K, k * v = v * k)
    (hvt : v * t = t * v) (hΛs : Group.IsSolvable ↥(lam L K))
    (hemb : NoFixedEmbeds ↥K ↥(lam L K))
    (h33 : ∀ M : Subgroup H, InL M → Lt K M → M ≠ K → IsLS [.Fi24Prime] ↥M)
    (hty : ∀ M : Subgroup H, InL M → IsLS [.Fi24Prime] ↥M → SolStd M ∧
      (∃ S : Sylow 2 (centralizer (M : Set H)), IsCyclic ↥S) ∧
        ∀ y : H, 3 ≤ CFSG.pRank 2 ↥(M.map (MulAut.conj y).toMonoidHom)) :
    K = componentProduct K v ∨ ∃ M : Subgroup H, OuterLayer K v M := by
  have hCt := hSol.centralizer_le_normalizer htL ht2
  have hbar := bar_eq_fix_of_outer hpin.outerFixed hcov.1 hcov.2.1 hcov.2.2 hvN hv2 hvnot hKL hKq
    hKv hcard
  have hKn := normal_of_outer hvN hKL hKq hKv hbar htL hCt
  have hB : BTheoremAt v := lit.bthm H hH hkp hN.oddCore_eq_bot v hv2
  by_cases hex : NoOtherComponent K t v
  · left
    exact componentProduct_eq_of_noOther_out hkp hN.center_eq_bot hB hCt htL ht2 hvt hv2 hKL hKq
      (fun k hk => mem_centralizer_singleton_iff.2 (hKv k hk)) hKn hΛs hemb hex
  · right
    unfold NoOtherComponent at hex
    push Not at hex
    obtain ⟨M, hM, hKM, hMK, -⟩ := hex
    have hv1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hv2; omega
    have hinLM : InL M := ⟨zpowers v, fun hb => hv1 (Subgroup.mem_bot.1 (hb ▸ mem_zpowers v)),
      isPGroup_zpowers_of_orderOf_two hv2, by rw [centralizer_zpowers_eq]; exact hM⟩
    have hKcomp : IsCompIn K (centralizer ({v} : Set H) ⊓ centralizer ({t} : Set H)) :=
      isCompIn_of_normal (fun k hk => ⟨mem_centralizer_singleton_iff.2 (hKv k hk),
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL k (hKL hk))⟩) hKq hKn
    have hlt : Lt K M := lt_of_le_sup_conj hv2 ht2 hvt hKcomp hM hKM
    have hMLS := h33 M hinLM hlt hMK
    obtain ⟨hsol, hcyc, hrank⟩ := hty M hinLM hMLS
    obtain ⟨s'', hs'', hqq, hoo, hsp⟩ := hMLS
    obtain rfl : s'' = .Fi24Prime := List.mem_singleton.1 hs''
    have hMzp : IsCompIn M (centralizer ((zpowers v : Subgroup H) : Set H)) := by
      rw [centralizer_zpowers_eq]; exact hM
    have htv : t ∈ centralizer ({v} : Set H) := mem_centralizer_singleton_iff.2 hvt.symm
    have hnorm : centralizer ({v} : Set H) ≤ normalizer (M : Set H) :=
      le_normalizer_of_cyclic_centralizer hMzp (by rw [centralizer_zpowers_eq]) hrank hcyc
    have hconj : CFSG.conjugate M t = M :=
      Solomon78.mem_normalizer_iff_map_conj_eq.1 (Subgroup.inv_mem _ (hnorm htv))
    have hKM' : K ≤ M := by
      rw [hconj, sup_idem] at hKM
      exact hKM
    exact ⟨M, hM, ⟨hqq, hoo, hsp⟩, hsol, hKM'⟩

end Dichotomy

section Main

variable {H : Type} [Group H] [Finite H]

theorem fiVariantThree_of_nm (pf : FiPinned) (h : FiVariantThreeNM) : FiVariantThree := by
  intro lit H _ _ ih N hN hidx hkp hN22 hN23 hN24 hnb hL0 ⟨P, hPinL, hPcq⟩ hnostd
  refine h lit H ih N hN hidx hkp hN22 hN23 hN24 hnb hL0 ⟨P, hPinL, hPcq, fun hmax => ?_⟩
  have hPq : CFSG.IsQuasisimple ↥P := hPinL.isQuasisimple
  have hstd : StdBare P := fiStdBare_of_maximal (lit.thm22 H ih.uHered) hkp hN hidx hmax
    (inL_ne_of_fStarSimple' hN hPinL) (pf.rank23 ↥P hPq hPcq)
  have hodd : Odd (Nat.card ↥(center ↥P)) := by
    rw [pf.mult23 ↥P hPq hPcq, Subgroup.card_bot]
    exact odd_one
  exact hnostd ⟨P, solStd_of_inL_stdBare hPinL hstd, hPq, hodd, hPcq⟩

@[expose] def FiCoexistMax : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ¬ IsSporadic ↥N .Fi22 →
        ¬ IsSporadic ↥N .Fi23 → ¬ IsSporadic ↥N .Fi24Prime → NoBiggerFi H .Fi24Prime →
          (∃ L₀ : Subgroup H, SolStd L₀ ∧ OddCover .Fi24Prime L₀) →
            (∃ L₁ : Subgroup H, SolStd L₁ ∧ OddCover .Fi23 L₁) →
              (∀ P : Subgroup H, InL P → IsSporadic (↥P ⧸ center ↥P) .Fi23 → Maximal P) →
                ∃ (s' : TauCeti.SporadicName) (L' : Subgroup H), s' ∈ fiTypes ∧ OddCover s' L' ∧
                  FiOut H N L' s'

theorem fiCoexist_of_nm (hnm : FiVariantThreeNM) (hmax : FiCoexistMax) : FiCoexist := by
  intro lit H _ _ ih N hN hidx hkp hN22 hN23 hN24 hnb hL0 hL1
  by_cases h : ∃ P : Subgroup H, InL P ∧ IsSporadic (↥P ⧸ center ↥P) .Fi23 ∧ ¬ Maximal P
  · exact hnm lit H ih N hN hidx hkp hN22 hN23 hN24 hnb hL0 h
  · push Not at h
    exact hmax lit H ih N hN hidx hkp hN22 hN23 hN24 hnb hL0 hL1 h

end Main

end CFSG.EvenSporadicStandard.Induction.Fi.V3
