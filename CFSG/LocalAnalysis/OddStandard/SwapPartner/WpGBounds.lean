module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WPrimeShape
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdCentral
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGNum

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] [Finite G]

theorem card_centralizer_twoSec_le {x c : G} (hc : c ∈ centralizer ({x} : Set G)) :
    Nat.card (centralizer ({(QuotientGroup.mk ⟨c, hc⟩ : TwoSec x)} : Set (TwoSec x))) ≤
      pairOrder c x := by
  let C : Subgroup G := centralizer ({x} : Set G)
  haveI : Finite C := inferInstance
  have hle := card_centralizer_quotient_le (Z := zpowers (selfC x)) (c := (⟨c, hc⟩ : C))
  have hcard : Nat.card (centralizer ({(⟨c, hc⟩ : C)} : Set C)) =
      Nat.card ↥(centralizer ({c} : Set G) ⊓ C) := by
    refine Nat.card_congr ?_
    refine ⟨fun z => ⟨(z.1 : G), ?_, z.1.2⟩,
      fun g => ⟨⟨(g.1 : G), (Subgroup.mem_inf.mp g.2).2⟩, ?_⟩, ?_, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp z.2))
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).1)
    · intro z
      exact Subtype.ext (Subtype.ext rfl)
    · intro g
      exact Subtype.ext rfl
  refine le_trans hle ?_
  rw [hcard]
  simp only [pairOrder]
  exact le_of_eq rfl

private lemma wp_mk_mul_self_eq_one {x c : G} (hc : c ∈ centralizer ({x} : Set G))
    (hc2 : c * c = 1) :
    (QuotientGroup.mk ⟨c, hc⟩ : TwoSec x) * QuotientGroup.mk ⟨c, hc⟩ = 1 := by
  have hc2' : (⟨c, hc⟩ : ↥(centralizer ({x} : Set G))) * ⟨c, hc⟩ = 1 :=
    Subtype.ext (by simpa using hc2)
  rw [← QuotientGroup.mk_mul (zpowers (selfC x)), hc2', QuotientGroup.mk_one]

theorem two_mul_le_pairOrder_of_outer {x : G} {t : TwoSec x} {Sg V K : Subgroup (TwoSec x)}
    (H : WreathCase t Sg V K) {c : G} (hc : c ∈ centralizer ({x} : Set G)) (hc2 : c * c = 1)
    (hout : (QuotientGroup.mk ⟨c, hc⟩ : TwoSec x) ∉ normalizer (K : Set (TwoSec x))) :
    2 * 40320 ≤ pairOrder c x := by
  haveI : Finite (TwoSec x) := inferInstance
  calc 2 * 40320
      ≤ Nat.card (centralizer ({(QuotientGroup.mk ⟨c, hc⟩ : TwoSec x)} : Set (TwoSec x))) :=
        WreathCase.two_mul_le_card_centralizer_of_not_mem_normalizer H
          (wp_mk_mul_self_eq_one hc hc2) hout
    _ ≤ pairOrder c x := card_centralizer_twoSec_le hc

theorem allowedPair_of_inner {x : G} {t : TwoSec x} {Sg V K : Subgroup (TwoSec x)}
    (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) {c : G}
    (hc : c ∈ centralizer ({x} : Set G)) (hc2 : c * c = 1)
    (hcN : (QuotientGroup.mk ⟨c, hc⟩ : TwoSec x) ∈ normalizer (K : Set (TwoSec x))) {k : ℕ}
    (hk : pairOrder c x = N10 k) :
    AllowedPair (N10 k) (WreathCase.theta H e ⟨QuotientGroup.mk ⟨c, hc⟩, hcN⟩) := by
  haveI : Finite (TwoSec x) := inferInstance
  have hy : (⟨QuotientGroup.mk ⟨c, hc⟩, hcN⟩ : normalizer (K : Set (TwoSec x))) *
      ⟨QuotientGroup.mk ⟨c, hc⟩, hcN⟩ = 1 := Subtype.ext (wp_mk_mul_self_eq_one hc hc2)
  obtain ⟨h1, h2⟩ := WreathCase.theta_mul_self H e hy
  refine ⟨h1, h2, ?_⟩
  calc altCentCard8 (WreathCase.theta H e ⟨QuotientGroup.mk ⟨c, hc⟩, hcN⟩).1 *
        altCentCard8 (WreathCase.theta H e ⟨QuotientGroup.mk ⟨c, hc⟩, hcN⟩).2
      ≤ Nat.card (centralizer ({(QuotientGroup.mk ⟨c, hc⟩ : TwoSec x)} : Set (TwoSec x))) :=
        WreathCase.altCentCard8_mul_le_card_centralizer_of_mem_normalizer H e
          (wp_mk_mul_self_eq_one hc hc2) hcN
    _ ≤ pairOrder c x := card_centralizer_twoSec_le hc
    _ = N10 k := hk

theorem allowedPair_of_conj {x : G} {t : TwoSec x} {Sg V K : Subgroup (TwoSec x)}
    (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) {c : G}
    (hc : c ∈ centralizer ({x} : Set G)) (hc2 : c * c = 1) {k : ℕ} (hk : pairOrder c x = N10 k)
    (f : TwoSec x)
    (hf : f * (QuotientGroup.mk ⟨c, hc⟩ : TwoSec x) * f⁻¹ ∈ normalizer (K : Set (TwoSec x))) :
    AllowedPair (N10 k)
      (WreathCase.theta H e ⟨f * (QuotientGroup.mk ⟨c, hc⟩ : TwoSec x) * f⁻¹, hf⟩) := by
  obtain ⟨f', rfl⟩ := QuotientGroup.mk_surjective (s := zpowers (selfC x)) f
  let c' : G := (f' : G) * c * (f' : G)⁻¹
  have hc' : c' ∈ centralizer ({x} : Set G) :=
    mul_mem (mul_mem f'.2 hc) (inv_mem f'.2)
  have hc2' : c' * c' = 1 := by
    calc c' * c' = (f' : G) * (c * c) * (f' : G)⁻¹ := by
          simp only [c']; group
      _ = 1 := by rw [hc2]; group
  have hfx : (f' : G) * x * (f' : G)⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp f'.2]
    group
  have hfeq : (QuotientGroup.mk f' : TwoSec x) * QuotientGroup.mk ⟨c, hc⟩ *
      (QuotientGroup.mk f')⁻¹ = (QuotientGroup.mk ⟨c', hc'⟩ : TwoSec x) := by
    rw [← QuotientGroup.mk_mul (zpowers (selfC x)), ← QuotientGroup.mk_inv (zpowers (selfC x)),
      ← QuotientGroup.mk_mul (zpowers (selfC x))]
    rw [show f' * ⟨c, hc⟩ * f'⁻¹ = ⟨c', hc'⟩ from Subtype.ext rfl]
  have hcN' : (QuotientGroup.mk ⟨c', hc'⟩ : TwoSec x) ∈
      normalizer (K : Set (TwoSec x)) := hfeq ▸ hf
  have hk' : pairOrder c' x = N10 k := by
    rw [← hk]
    have hconj := pairOrder_conj (f' : G) c x
    rw [hfx] at hconj
    exact hconj
  have heq : (⟨(QuotientGroup.mk f' : TwoSec x) * QuotientGroup.mk ⟨c, hc⟩ *
        (QuotientGroup.mk f')⁻¹, hf⟩ : normalizer (K : Set (TwoSec x))) =
      ⟨QuotientGroup.mk ⟨c', hc'⟩, hcN'⟩ := Subtype.ext hfeq
  rw [heq]
  exact allowedPair_of_inner H e hc' hc2' hcN' hk'

end CFSG.OddStandard.AltStdSec.SwapPartner
