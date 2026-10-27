module

public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.GH74.KGroups.L34Tables
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.GH74.GLS
open scoped commutatorElement

private theorem mem_cSec_of_le_centralizer {X : Type} [Group X] (w : X) (J : Subgroup X)
    (hJC : J ≤ centralizer ({w} : Set X)) : w ∈ Stage1.Thm2.Recip.cSec J := by
  have hwc : w ∈ centralizer (J : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hJC hy))
  have hN : w ∈ normalizer (J : Set X) := Subgroup.centralizer_le_normalizer _ hwc
  refine ⟨hN, TwoThin.mem_normalizer_pPrimeCoreOf hN, fun k hk => ?_⟩
  have hkw : k * w = w * k := Subgroup.mem_centralizer_iff.mp hwc k hk
  rw [commutatorElement_def, hkw, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem theta1 {X : Type} [Group X] [Finite X] (w x : X) (J : Subgroup X)
    (hJ : IsPCompIn 2 (centralizer ({w} : Set X)) J)
    (hin : x ∈ zpowers w ⊔ pLayerOf 2 (centralizer ({w} : Set X))) :
    ∃ g ∈ J, ∀ y ∈ J, (x⁻¹ * y * x)⁻¹ * (g⁻¹ * y * g) ∈ pPrimeCoreOf 2 J := by
  have hle : zpowers w ⊔ pLayerOf 2 (centralizer ({w} : Set X)) ≤ Stage1.Thm2.Recip.innSub J :=
    sup_le ((zpowers_le.mpr (mem_cSec_of_le_centralizer w J hJ.1)).trans
      (Stage1.Thm2.Recip.cSec_le_innSub J)) (Stage1.Thm2.Recip.pLayerOf_le_innSub hJ)
  obtain ⟨k, hk, hc⟩ := Stage1.Thm2.Recip.mem_innSub_iff.mp (hle hin)
  have hcM : x * k⁻¹ ∈ normalizer (pPrimeCoreOf 2 J : Set X) := hc.2.1
  have hcc : ∀ y ∈ J, ⁅y, x * k⁻¹⁆ ∈ pPrimeCoreOf 2 J := hc.2.2
  refine ⟨k, hk, fun y hy => ?_⟩
  set c := x * k⁻¹ with hcdef
  have hx : x = c * k := by rw [hcdef]; group
  have hkM : k ∈ normalizer (pPrimeCoreOf 2 J : Set X) :=
    TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer hk)
  have h1 : ⁅y⁻¹, c⁆ ∈ pPrimeCoreOf 2 J := hcc _ (inv_mem hy)
  have h2 : c⁻¹ * ⁅y⁻¹, c⁆ * c⁻¹⁻¹ ∈ pPrimeCoreOf 2 J :=
    (mem_normalizer_iff.mp (inv_mem hcM) _).mp h1
  have h3 := (mem_normalizer_iff.mp (inv_mem hkM) _).mp h2
  have e : (x⁻¹ * y * x)⁻¹ * (k⁻¹ * y * k) = k⁻¹ * (c⁻¹ * ⁅y⁻¹, c⁆ * c⁻¹⁻¹) * k⁻¹⁻¹ := by
    rw [hx]; simp only [commutatorElement_def]; group
  rw [e]
  exact h3

theorem theta2
    {Q : Type} [Group Q] [Finite Q] (hL : IsL34Quotient Q)
    (hZ : Nat.card ↥(center Q) = 16) (g : Q) (hg : g ∉ center Q) (hg2 : g ^ 2 ∈ center Q) :
    ∀ y : Q, Commute y g → ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
  intro y hyg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Q ⧸ center Q
  obtain ⟨e⟩ := GH74.KGroups.L34.equiv_of_lieModel hL
  set gb : P := (g : P)
  have hgb1 : gb ≠ 1 := fun h => hg ((QuotientGroup.eq_one_iff g).mp h)
  have hgb2 : gb ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hg2
  have hord : orderOf gb = 2 := orderOf_eq_prime hgb2 hgb1
  obtain ⟨-, -, hcard⟩ := GH74.KGroups.L34.ki3_model (⊤ : Subgroup P) (le_top)
    (Subgroup.topEquiv.trans e) gb (Subgroup.mem_top _) hord
  set C := centralizer ({gb} : Set P) ⊓ ⊤
  have hyC : (y : P) ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_top _⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hyg.eq]
  have h64 : (y : P) ^ 64 = 1 := by
    have := pow_card_eq_one' (G := ↥C) (x := ⟨(y : P), hyC⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  have hyZ : y ^ 64 ∈ center Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h64
  refine ⟨10, ?_⟩
  have h16 := pow_card_eq_one' (G := ↥(center Q)) (x := ⟨y ^ 64, hyZ⟩)
  rw [hZ] at h16
  have h16' : (y ^ 64) ^ 16 = 1 := congrArg Subtype.val h16
  rw [← pow_mul] at h16'
  simpa using h16'

private theorem mk_eq_iff {X : Type} [Group X] {J : Subgroup X} {a b : X} (ha : a ∈ J)
    (hb : b ∈ J) :
    ((QuotientGroup.mk (⟨a, ha⟩ : ↥J) : kBar J) = QuotientGroup.mk (⟨b, hb⟩ : ↥J)) ↔
      a⁻¹ * b ∈ pPrimeCoreOf 2 J := by
  rw [QuotientGroup.eq, pPrimeCoreOf,
    ← Subgroup.mem_map_iff_mem (f := J.subtype) Subtype.val_injective]
  simp

theorem lemmaTheta
    {X : Type} [Group X] [Finite X] (w x : X) (hw : orderOf w = 2)
    (hx : orderOf x = 2) (hwx : w * x = x * w) (J : Subgroup X)
    (hJ : IsPCompIn 2 (centralizer ({w} : Set X)) J) (hxJ : x ∈ normalizer (J : Set X))
    (hL : IsL34Quotient (kBar J)) (hZ : Nat.card ↥(center (kBar J)) = 16)
    (hnt : ∃ y ∈ J, y⁻¹ * (x⁻¹ * y * x) ∉ pPrimeCoreOf 2 J)
    (hin : x ∈ zpowers w ⊔ pLayerOf 2 (centralizer ({w} : Set X))) :
    ∀ y ∈ J, y⁻¹ * (x⁻¹ * y * x) ∈ pPrimeCoreOf 2 J →
      ∃ k : ℕ, y ^ (2 ^ k) ∈ pPrimeCoreOf 2 J := by
  have hxc : ∀ y ∈ J, x⁻¹ * y * x ∈ J := fun y hy => by
    have := (mem_normalizer_iff.mp (inv_mem hxJ) y).mp hy
    simpa using this
  have hgc : ∀ g ∈ J, ∀ y ∈ J, g⁻¹ * y * g ∈ J := fun g hg y hy =>
    J.mul_mem (J.mul_mem (J.inv_mem hg) hy) hg
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  obtain ⟨g, hgJ, hg⟩ := theta1 w x J hJ hin
  let φ : ∀ a : X, a ∈ J → kBar J := fun a ha => QuotientGroup.mk (⟨a, ha⟩ : ↥J)
  set gb : kBar J := φ g hgJ with hgb
  have hconj : ∀ y (hy : y ∈ J), φ (x⁻¹ * y * x) (hxc y hy) = gb⁻¹ * φ y hy * gb := by
    intro y hy
    have h1 : φ (x⁻¹ * y * x) (hxc y hy) = φ (g⁻¹ * y * g) (hgc g hgJ y hy) :=
      (mk_eq_iff _ _).mpr (hg y hy)
    rw [h1]
    rfl
  have hsurj : ∀ h : kBar J, ∃ a, ∃ ha : a ∈ J, φ a ha = h := by
    intro h
    obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective h
    exact ⟨a, ha, rfl⟩
  have hgZ : gb ∉ center (kBar J) := by
    intro hc
    obtain ⟨y₀, hy₀, hn⟩ := hnt
    apply hn
    rw [← mk_eq_iff hy₀ (hxc y₀ hy₀)]
    change φ y₀ hy₀ = φ (x⁻¹ * y₀ * x) (hxc y₀ hy₀)
    rw [hconj y₀ hy₀, mul_assoc, mem_center_iff.mp hc (φ y₀ hy₀)]
    group
  have hg2 : gb ^ 2 ∈ center (kBar J) := by
    refine mem_center_iff.mpr fun h => ?_
    obtain ⟨a, ha, rfl⟩ := hsurj h
    have e : φ a ha = gb⁻¹ * (gb⁻¹ * φ a ha * gb) * gb := by
      rw [← hconj a ha, ← hconj (x⁻¹ * a * x) (hxc a ha)]
      congr 1
      simp only [hxinv, mul_assoc, hx2, mul_one]
      rw [← mul_assoc, hx2, one_mul]
    have : gb * gb * φ a ha = φ a ha * (gb * gb) := by
      nth_rewrite 1 [e]
      group
    rw [pow_two]
    exact this.symm
  intro y hy hyx
  have hcomm : Commute (φ y hy) gb := by
    have h1 : φ y hy = φ (x⁻¹ * y * x) (hxc y hy) := (mk_eq_iff _ _).mpr hyx
    rw [hconj y hy] at h1
    show φ y hy * gb = gb * φ y hy
    nth_rewrite 2 [h1]
    group
  obtain ⟨k, hk⟩ := theta2 hL hZ gb hgZ hg2 (φ y hy) hcomm
  refine ⟨k, ?_⟩
  have hyk : y ^ (2 ^ k) ∈ J := J.pow_mem hy _
  have h2 : φ (y ^ (2 ^ k)) hyk = φ 1 J.one_mem := by
    rw [show φ 1 J.one_mem = 1 from rfl, ← hk]
    rfl
  have := (mk_eq_iff hyk J.one_mem).mp h2
  simpa using this

end CFSG.ComponentClassification.GSThmB
