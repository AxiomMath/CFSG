module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCfg610
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Real2

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def Fi24Cfg610Comp : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ (N L : Subgroup H) (t u : H), CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
      OddCover .Fi24Prime L → Cfg610_2 H N L t u → ∀ (K : Subgroup H) (u₀ : H), K ≤ L →
        K ≤ centralizer ({u} : Set H) → IsSporadic ↥K .Fi23 → u₀ ∈ K → Fi23Transposition K u₀ →
          IsCompIn (K ⊓ centralizer ({u₀} : Set H)) (centralizer ({u₀} : Set H))

section Tail

variable {H : Type} [Group H] [Finite H]

theorem componentProduct_eq_of_isCompIn_Q {L K : Subgroup H} {t u : H} {b n : ℕ} (hbn : b < n)
    (hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H))
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (hu : u ∈ L) (hKL : K ≤ L)
    (hKq : CFSG.IsQuasisimple ↥K) (hKM : IsCompIn K (centralizer ({u} : Set H)))
    (hΛs : Group.IsSolvable ↥(normalizer (L : Set H) ⊓ centralizer (K : Set H)))
    (hΛr : ∀ E : Subgroup H, E ≤ normalizer (L : Set H) ⊓ centralizer (K : Set H) →
      (∀ x ∈ E, x * x = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ b)
    (hrank : InvolutionFixesElem ↥K n) : K = componentProduct K u := by
  classical
  set X : Subgroup H := centralizer ({u} : Set H) with hX
  have ht2' : t * t = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 ht2.dvd
  have htK : t ∈ centralizer (K : Set H) :=
    mem_centralizer_iff.2 fun k hk => mem_centralizer_iff.1 ht k (hKL hk)
  have htH : t ∈ X := mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht u hu).symm
  have hn : (K.subgroupOf X).Normal :=
    normal_of_component hbn hKM htH htK ht2' hCt hΛs hΛr hrank
  apply le_antisymm
  · exact le_sSup ⟨hKM.1, hn, ⟨MulEquiv.refl _⟩⟩
  · refine sSup_le ?_
    rintro N ⟨hNH, hNn, ⟨e⟩⟩
    by_cases hNK : N = K
    · exact hNK.le
    · exfalso
      have hNq : CFSG.IsQuasisimple ↥N := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hKq
      have hNcomp : IsCompIn N X := isCompIn_of_normal hNH hNq hNn
      have hcentK : N ≤ centralizer (K : Set H) := fun a ha =>
        mem_centralizer_iff.2 fun c hc => (hNcomp.commute_of_ne hKM hNK a ha c hc).symm
      have htN : t ∈ normalizer (N : Set H) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).1 hNn htH
      exact false_of_second_copy hbn ht2' hCt hKq hΛs hΛr hrank hcentK e htN

end Tail

section Certificates


theorem fiLoc_of_transposition {H : Type} [Group H] [Finite H] {K L : Subgroup H} {u : H}
    (hK : IsSporadic ↥K .Fi23) (hKL : K ≤ L) (hT : Fi23Transposition K u) :
    fiLoc (2 * 64561751654400) H L (K ⊓ centralizer ({u} : Set H)) u := by
  obtain ⟨huK, hu2, hcard⟩ := id hT
  have hq : CFSG.IsQuasisimple ↥(K ⊓ centralizer ({u} : Set H)) :=
    (Fi.V3.fi23Transpositions_real H K hK).2 u hT
  have hZ : Nat.card (center ↥(K ⊓ centralizer ({u} : Set H))) = 2 :=
    fi23_card_center_inf_centralizer hK huK hu2 hcard
  have hev : Even (Nat.card (↥(K ⊓ centralizer ({u} : Set H)) ⧸
      center ↥(K ⊓ centralizer ({u} : Set H)))) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center ↥(K ⊓ centralizer ({u} : Set H)))
    rw [hcard, hZ] at h1
    exact ⟨32280875827200, by omega⟩
  have hO := oddCore_eq_bot_of_quasisimple hq hZ hev
  refine ⟨hKL huK, hu2, inf_le_left.trans hKL, fun k hk => mem_centralizer_singleton_iff.1 hk.2,
    hq, ?_⟩
  rw [hO, Nat.card_congr QuotientGroup.quotientBot.toEquiv, hcard]

end Certificates

section CertificatesB


theorem fi24Cfg610Hyp35_of_comp (hfix : Fi24InFixesElem) (h : Fi24Cfg610Comp) :
    Fi24Cfg610Hyp35 := by
  intro lit H _ _ ih N L t u hKP hcov hcfg K u₀ hKL hKC hKs hu₀K hT
  have hloc := fiLoc_of_transposition hKs hKL hT
  have hcomp := h lit H ih N L t u hKP hcov hcfg K u₀ hKL hKC hKs hu₀K hT
  have hd := lemma36DataQ_fi24in hfix
  obtain ⟨-, huK₀, -, -, hKq, hAs, hA, hrank⟩ :=
    hd.data H L (K ⊓ centralizer ({u₀} : Set H)) u₀ hcov hloc
  obtain ⟨-, -, hK₀L, -⟩ := id hloc
  have hcycall := cyclic_sylow_all_of_exists hcfg.cyclicSylow
  have hCt := hcfg.standardL.centralizer_le_normalizer hcfg.t_mem hcfg.t_order
  exact componentProduct_eq_of_isCompIn_Q hd.bound hCt hcfg.t_mem hcfg.t_order (hK₀L huK₀) hK₀L
    hKq hcomp (lam_isSolvable hcycall hAs)
    (fun E hE h2 _ => lam_elemAbelian_card_le_pow hcycall hA hE h2) hrank

end CertificatesB

end CFSG.EvenSporadicStandard.Induction
