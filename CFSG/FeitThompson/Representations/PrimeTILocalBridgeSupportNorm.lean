module

public import CFSG.FeitThompson.Representations.PrimeTIDegreeSignCongruence
public import CFSG.FeitThompson.Representations.FrobeniusComplementPermutationCharacter
public import CFSG.FeitThompson.Representations.CoprimeAutomorphismCosetPartition
public import CFSG.FeitThompson.Representations.NonprincipalRowRestrictionsDetectCores
public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
public import CFSG.FeitThompson.Representations.ScalarEqualityPermutationTest
public import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
public import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup
open scoped Pointwise

variable {L : Type*} [Group L]

theorem card_map_mk'_of_disjoint {N S : Subgroup L} [N.Normal] (hd : Disjoint S N) :
    Nat.card (S.map (mk' N)) = Nat.card S := by
  set g : ↥S →* L ⧸ N := (mk' N).comp S.subtype with hg
  have hker : g.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxN : (x : L) ∈ N := by
      simpa [hg, MonoidHom.mem_ker, QuotientGroup.eq_one_iff] using hx
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.disjoint_def.1 hd x.2 hxN))
  have hrange : g.range = S.map (mk' N) := by
    ext y
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨(x : L), x.2, rfl⟩,
      by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff g).1 hker)).toEquiv).symm

theorem card_mul_card_map_mk' {N S : Subgroup L} [N.Normal] (hNS : N ≤ S) :
    Nat.card N * Nat.card (S.map (mk' N)) = Nat.card S := by
  set g : ↥S →* L ⧸ N := (mk' N).comp S.subtype with hg
  have hker : g.ker = N.subgroupOf S := by
    ext x
    simp [hg, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : g.range = S.map (mk' N) := by
    ext y
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨(x : L), x.2, rfl⟩,
      by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
  have h1 : Nat.card (↥S ⧸ g.ker) = Nat.card (S.map (mk' N)) := by
    rw [← hrange]; exact Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have h2 : Nat.card g.ker = Nat.card N := by
    rw [hker]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker, h1, h2]
  ring

theorem mem_map_mk'_iff_of_le {N S : Subgroup L} [N.Normal] (hNS : N ≤ S) (y : L) :
    mk' N y ∈ S.map (mk' N) ↔ y ∈ S := by
  refine ⟨fun hy => ?_, fun hy => Subgroup.mem_map_of_mem _ hy⟩
  have h := Subgroup.comap_map_eq (mk' N) S
  rw [QuotientGroup.ker_mk', sup_eq_left.2 hNS] at h
  rw [← h]
  exact hy

def cyclicTIsetConj (W₁ W₂ : Subgroup L) : Set L :=
  ⋃ t : L, (fun x => t⁻¹ * x * t) '' cyclicTIset W₁ W₂

theorem mem_cyclicTIsetConj {W₁ W₂ : Subgroup L} {x : L} :
    x ∈ cyclicTIsetConj W₁ W₂ ↔ ∃ t : L, ∃ v ∈ cyclicTIset W₁ W₂, t⁻¹ * v * t = x := by
  simp only [cyclicTIsetConj, Set.mem_iUnion, Set.mem_image]

theorem cyclicTIset_subset_cyclicTIsetConj (W₁ W₂ : Subgroup L) :
    cyclicTIset W₁ W₂ ⊆ cyclicTIsetConj W₁ W₂ :=
  fun v hv => mem_cyclicTIsetConj.2 ⟨1, v, hv, by group⟩

def bridgeSupport (A : Set L) (W₁ W₂ : Subgroup L) : Set L := A ∪ cyclicTIsetConj W₁ W₂

theorem bridgeSupport_eq (A : Set L) (W₁ W₂ : Subgroup L) :
    bridgeSupport A W₁ W₂ = A ∪ cyclicTIsetConj W₁ W₂ := (rfl)

theorem mem_bridgeSupport {A : Set L} {W₁ W₂ : Subgroup L} {x : L} :
    x ∈ bridgeSupport A W₁ W₂ ↔ x ∈ A ∨ x ∈ cyclicTIsetConj W₁ W₂ := Iff.rfl

theorem subset_bridgeSupport_left {A : Set L} {W₁ W₂ : Subgroup L} : A ⊆ bridgeSupport A W₁ W₂ :=
  Set.subset_union_left

theorem cyclicTIsetConj_subset_bridgeSupport {A : Set L} {W₁ W₂ : Subgroup L} :
    cyclicTIsetConj W₁ W₂ ⊆ bridgeSupport A W₁ W₂ := Set.subset_union_right

theorem bridgeSupport_subset {A : Set L} {W₁ W₂ : Subgroup L} {X : Set L} (hA : A ⊆ X)
    (hV : cyclicTIsetConj W₁ W₂ ⊆ X) : bridgeSupport A W₁ W₂ ⊆ X := Set.union_subset hA hV

theorem image_bridgeSupport {M : Type*} (f : L → M) (A : Set L) (W₁ W₂ : Subgroup L) :
    f '' bridgeSupport A W₁ W₂ = f '' A ∪ f '' cyclicTIsetConj W₁ W₂ := by
  rw [bridgeSupport_eq, Set.image_union]

theorem mul_mem_cyclicTIset {K W₁ W₂ : Subgroup L} (h : IsPrimeCyclicTIHyp K W₁ W₂) {y x : L}
    (hy : y ∈ W₂) (hy1 : y ≠ 1) (hx : x ∈ W₁) (hx1 : x ≠ 1) : y * x ∈ cyclicTIset W₁ W₂ := by
  refine mem_cyclicTIset.2 ⟨mul_mem (le_sup_right (a := W₁) hy) (le_sup_left (a := W₁) hx), ?_, ?_⟩
  · intro hmem
    have hyW : y ∈ W₁ := by
      rw [show y = (y * x) * x⁻¹ from by group]
      exact W₁.mul_mem hmem (W₁.inv_mem hx)
    have hb : y ∈ W₁ ⊓ W₂ := Subgroup.mem_inf.2 ⟨hyW, hy⟩
    rw [h.inf_left_right_eq_bot] at hb
    exact hy1 (Subgroup.mem_bot.1 hb)
  · intro hmem
    have hxW : x ∈ W₂ := by
      rw [show x = y⁻¹ * (y * x) from by group]
      exact W₂.mul_mem (W₂.inv_mem hy) hmem
    have hb : x ∈ W₁ ⊓ W₂ := Subgroup.mem_inf.2 ⟨hx, hxW⟩
    rw [h.inf_left_right_eq_bot] at hb
    exact hx1 (Subgroup.mem_bot.1 hb)

theorem exists_conj_eq_mul_of_notMem [Finite L] {K W₁ W₂ : Subgroup L}
    (h : IsPrimeCyclicTIHyp K W₁ W₂) {z : L} (hz : z ∉ K) :
    ∃ g : L, ∃ y ∈ W₂, ∃ x ∈ W₁, x ≠ 1 ∧ g⁻¹ * z * g = y * x := by
  classical
  have hKn := h.normal
  have _ : Finite K := Subtype.finite
  obtain ⟨k, hk, w, hw, rfl⟩ := h.exists_decomp z
  have hw1 : w ≠ 1 := by
    intro hcw
    rw [hcw, mul_one] at hz
    exact hz hk
  have hcop : (Nat.card K).Coprime (orderOf w) :=
    h.coprime_natCard.coprime_dvd_right (Subgroup.orderOf_dvd_natCard W₁ hw)
  have hfin : IsOfFinOrder w := isOfFinOrder_of_finite w
  have hnorm : w ∈ Subgroup.normalizer (K : Set L) := by
    rw [Subgroup.mem_set_normalizer_iff'']
    intro t
    refine ⟨fun ht => by simpa [mul_assoc] using hKn.conj_mem t ht w⁻¹, fun ht => ?_⟩
    simpa [mul_assoc] using hKn.conj_mem _ ht w
  have hmem : k * w ∈ (K : Set L) * ({w} : Set L) := by
    rw [Set.mul_singleton]
    exact ⟨k, hk, rfl⟩
  obtain ⟨S, ⟨hS, hzS⟩, -⟩ := existsUnique_mem_centralizerCosetConjugates hcop hfin hnorm hmem
  obtain ⟨g, -, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  rw [mem_conjAct_smul_set_iff] at hzS
  have hcc := mem_centralizerCoset_iff.1 hzS
  rw [h.centralizer_eq w hw hw1] at hcc
  exact ⟨g, g⁻¹ * (k * w) * g * w⁻¹, hcc, w, hw, hw1, by group⟩

noncomputable def bridgePermChar [Fintype L] (H W₁ : Subgroup L) : L → ℂ :=
  indClassFun (H ⊔ W₁) 1

theorem indClassFun_one_eq_frobeniusComplementChar [Fintype L] (C : Subgroup L) :
    indClassFun C (1 : ↥C → ℂ) = frobeniusComplementChar C := by
  classical
  funext x
  rw [frobeniusComplementChar_apply, indClassFun_apply]
  congr 1
  simp only [Pi.one_apply, dite_eq_ite]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem bridgePermChar_eq_frobeniusComplementChar [Fintype L] (H W₁ : Subgroup L) :
    bridgePermChar H W₁ = frobeniusComplementChar (H ⊔ W₁) := by
  rw [bridgePermChar, indClassFun_one_eq_frobeniusComplementChar]

theorem bridgePermChar_eq_character [Fintype L] (H W₁ : Subgroup L) :
    bridgePermChar H W₁
      = (Representation.ind (H ⊔ W₁).subtype
          (Representation.trivial ℂ ↥(H ⊔ W₁) ℂ)).character := by
  rw [bridgePermChar_eq_frobeniusComplementChar, frobeniusComplementChar_eq_character]

theorem conj_bridgePermChar_apply [Fintype L] (H W₁ : Subgroup L) (x : L) :
    (starRingEnd ℂ) (bridgePermChar H W₁ x) = bridgePermChar H W₁ x := by
  rw [bridgePermChar_eq_frobeniusComplementChar, frobeniusComplementChar_apply]
  simp

theorem cfInner_bridgePermChar_one [Fintype L] (H W₁ : Subgroup L) :
    cfInner (bridgePermChar H W₁) (1 : L → ℂ) = 1 := by
  rw [bridgePermChar_eq_frobeniusComplementChar]
  exact cfInner_frobeniusComplementChar_one _

theorem bridgePermChar_mem_virtualChars [Fintype L] (H W₁ : Subgroup L) :
    bridgePermChar H W₁ ∈ virtualChars L := by
  rw [bridgePermChar]
  exact indClassFun_one_mem_virtualChars _

theorem bridgePermChar_mem_classFun [Fintype L] (H W₁ : Subgroup L) :
    bridgePermChar H W₁ ∈ classFun L := by
  rw [bridgePermChar, mem_classFun]
  intro x y hxy
  obtain ⟨a, rfl⟩ := isConj_iff.1 hxy
  rw [indClassFun_conj]

theorem bridgePermChar_eq_comp_mk [Fintype L] {H : Subgroup L} [H.Normal] [Fintype (L ⧸ H)]
    (W₁ : Subgroup L) :
    bridgePermChar H W₁
      = frobeniusComplementChar (W₁.map (mk' H)) ∘ (QuotientGroup.mk : L → L ⧸ H) := by
  classical
  funext y
  have hIle : H ≤ H ⊔ W₁ := le_sup_left
  have hImap : (H ⊔ W₁).map (mk' H) = W₁.map (mk' H) := by rw [Subgroup.map_sup]; simp
  set S : Set (L ⧸ H) := {s | s⁻¹ * (QuotientGroup.mk y : L ⧸ H) * s ∈ W₁.map (mk' H)} with hS
  have hpre : (QuotientGroup.mk ⁻¹' S) = {t : L | t⁻¹ * y * t ∈ H ⊔ W₁} := by
    ext t
    simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [show (QuotientGroup.mk t : L ⧸ H)⁻¹ * (QuotientGroup.mk y) * (QuotientGroup.mk t)
        = (QuotientGroup.mk (t⁻¹ * y * t) : L ⧸ H) from by simp [mul_assoc], ← hImap]
    exact mem_map_mk'_iff_of_le hIle _
  have hcount := QuotientGroup.card_preimage_mk H S
  rw [hpre] at hcount
  rw [bridgePermChar, Function.comp_apply, frobeniusComplementChar_apply, indClassFun_apply]
  have hA : (Nat.card {t : L // t⁻¹ * y * t ∈ H ⊔ W₁} : ℂ)
      = (Nat.card H : ℂ) * (Nat.card {s : L ⧸ H // s⁻¹ * (QuotientGroup.mk y) * s
        ∈ W₁.map (mk' H)} : ℂ) := by
    have h3 : Nat.card {t : L // t⁻¹ * y * t ∈ H ⊔ W₁}
        = Nat.card H * Nat.card {s : L ⧸ H // s⁻¹ * (QuotientGroup.mk y) * s
          ∈ W₁.map (mk' H)} := hcount
    rw [h3]
    push_cast
    ring
  have hsum : (∑ t : L, if h : t⁻¹ * y * t ∈ H ⊔ W₁ then (1 : ↥(H ⊔ W₁) → ℂ) ⟨_, h⟩ else 0)
      = (Nat.card {t : L // t⁻¹ * y * t ∈ H ⊔ W₁} : ℂ) := by
    simp only [Pi.one_apply, dite_eq_ite]
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hsum, hA]
  have hcards : Nat.card H * Nat.card (W₁.map (mk' H)) = Nat.card (H ⊔ W₁ : Subgroup L) := by
    rw [← hImap]
    exact card_mul_card_map_mk' hIle
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hW0 : (Nat.card (W₁.map (mk' H)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [← hcards]
  push_cast
  field_simp

structure IsPrimeTIBridgeConfig (K W₁ W₂ H U : Subgroup L) [H.Normal] (A : Set L) : Prop where
  primeCyclicTI : IsPrimeCyclicTIHyp K W₁ W₂
  right_le_H : W₂ ≤ H
  H_le_K : H ≤ K
  A_subset : A ⊆ (K : Set L) \ {1}
  A_conj_mem : ∀ g : L, ∀ a ∈ A, g⁻¹ * a * g ∈ A
  centralizer_sdiff_subset : ∀ h ∈ H, h ≠ 1 →
    ((K ⊓ Subgroup.centralizer ({h} : Set L) : Subgroup L) : Set L) \ {1} ⊆ A
  U_ne_bot : U ≠ ⊥
  sup_H_U : H ⊔ U = K
  disjoint_H_U : Disjoint H U
  le_normalizer_U : W₁ ≤ Subgroup.normalizer (U : Set L)
  inf_centralizer_U_eq_bot : ∀ x ∈ W₁, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set L) = ⊥

namespace IsPrimeTIBridgeConfig

variable {K W₁ W₂ H U : Subgroup L} [H.Normal] {A : Set L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}
  (hc : IsPrimeTIBridgeConfig K W₁ W₂ H U A)

include hc

theorem disjoint_H_W₁ : Disjoint H W₁ := by
  rw [disjoint_iff, eq_bot_iff, ← hc.primeCyclicTI.inf_eq_bot]
  exact inf_le_inf_right _ hc.H_le_K

theorem sdiff_H_subset_A : ((H : Set L) \ {1}) ⊆ A := by
  intro x hx
  obtain ⟨hxH, hx1⟩ := hx
  refine hc.centralizer_sdiff_subset x hxH (by simpa using hx1) ⟨?_, hx1⟩
  exact Subgroup.mem_inf.2 ⟨hc.H_le_K hxH, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem sdiff_H_union_subset_bridgeSupport :
    ((H : Set L) \ {1}) ∪ cyclicTIsetConj W₁ W₂ ⊆ bridgeSupport A W₁ W₂ :=
  Set.union_subset_union_left _ hc.sdiff_H_subset_A

theorem index_sup_H_left [Finite L] : (H ⊔ W₁).index = Nat.card U := by
  have h1 : Nat.card H * Nat.card W₁ = Nat.card (H ⊔ W₁ : Subgroup L) :=
    card_sup_eq_mul_of_disjoint H W₁ hc.disjoint_H_W₁
  have h2 : Nat.card H * Nat.card U = Nat.card K := by
    rw [← hc.sup_H_U]
    exact card_sup_eq_mul_of_disjoint H U hc.disjoint_H_U
  have h3 : Nat.card W₁ * Nat.card K = Nat.card L :=
    hc.primeCyclicTI.isComplement'_left.card_mul_card
  have h4 := Subgroup.index_mul_card (H ⊔ W₁ : Subgroup L)
  have key : (H ⊔ W₁).index * Nat.card (H ⊔ W₁ : Subgroup L)
      = Nat.card U * Nat.card (H ⊔ W₁ : Subgroup L) := by
    rw [h4, ← h3, ← h2, ← h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos key

theorem bridgePermChar_one [Fintype L] : bridgePermChar H W₁ 1 = (Nat.card U : ℂ) := by
  rw [bridgePermChar, indClassFun_apply_one, hc.index_sup_H_left]
  simp

noncomputable def conjActionOn : ↥W₁ →* MulAut ↥U :=
  U.normalizerMonoidHom.comp (Subgroup.inclusion hc.le_normalizer_U)

theorem coe_conjActionOn_apply (x : ↥W₁) (v : ↥U) :
    ((hc.conjActionOn (U := U) x v : ↥U) : L) = (x : L) * (v : L) * (x : L)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe U _ v

theorem fixedPointFree_conjActionOn {x : ↥W₁} (hx : x ≠ 1) :
    MonoidHom.FixedPointFree (hc.conjActionOn (U := U) x : ↥U → ↥U) := by
  intro v hv
  have hx1 : (x : L) ≠ 1 := fun hcx => hx (Subtype.ext hcx)
  have hmem : (v : L) ∈ U ⊓ Subgroup.centralizer ({(x : L)} : Set L) := by
    refine Subgroup.mem_inf.2 ⟨v.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hfix : (x : L) * (v : L) * (x : L)⁻¹ = (v : L) := by
      rw [← hc.coe_conjActionOn_apply x v, hv]
    calc (v : L) * (x : L) = ((x : L) * (v : L) * (x : L)⁻¹) * (x : L) := by rw [hfix]
      _ = (x : L) * (v : L) := by group
  rw [hc.inf_centralizer_U_eq_bot (x : L) x.2 hx1] at hmem
  exact Subtype.ext (by simpa using hmem)

theorem natCard_left_dvd_natCard_sub_one [Finite U] : Nat.card W₁ ∣ Nat.card U - 1 :=
  card_dvd_card_sub_one_of_fixedPointFree (φ := hc.conjActionOn (U := U))
    fun _ hx => hc.fixedPointFree_conjActionOn hx

theorem map_K_eq_map_U : K.map (mk' H) = U.map (mk' H) := by
  rw [← hc.sup_H_U, Subgroup.map_sup]
  simp

theorem normal_map_U : (U.map (mk' H)).Normal := by
  rw [← hc.map_K_eq_map_U]
  exact hc.primeCyclicTI.normal.map _ (mk'_surjective H)

theorem isComplement'_map : (U.map (mk' H)).IsComplement' (W₁.map (mk' H)) := by
  have hnU : (U.map (mk' H)).Normal := hc.normal_map_U
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, eq_bot_iff]
    intro z hz
    obtain ⟨hzU, hzW⟩ := Subgroup.mem_inf.1 hz
    rw [← hc.map_K_eq_map_U] at hzU
    obtain ⟨w, hw, rfl⟩ := hzW
    have hwK : w ∈ K := (mem_map_mk'_iff_of_le hc.H_le_K w).1 hzU
    have hmem : w ∈ K ⊓ W₁ := Subgroup.mem_inf.2 ⟨hwK, hw⟩
    rw [hc.primeCyclicTI.inf_eq_bot] at hmem
    simp [Subgroup.mem_bot.1 hmem]
  · have hKn := hc.primeCyclicTI.normal
    have hKW : K ⊔ W₁ = ⊤ := by
      rw [← Subgroup.coe_eq_univ, Subgroup.normal_mul]
      exact hc.primeCyclicTI.mul_eq_univ
    have h1 : (H ⊔ (U ⊔ W₁)).map (mk' H) = (U ⊔ W₁).map (mk' H) := by
      rw [Subgroup.map_sup]; simp
    have h2 : (U ⊔ W₁).map (mk' H) = ⊤ := by
      rw [← h1, ← sup_assoc, hc.sup_H_U, hKW,
        Subgroup.map_top_of_surjective _ (mk'_surjective H)]
    rw [← Subgroup.normal_mul, ← Subgroup.map_sup, h2]
    exact Subgroup.coe_top

theorem inf_centralizer_map_eq_bot {c : L ⧸ H} (hcmem : c ∈ W₁.map (mk' H)) (hc1 : c ≠ 1) :
    U.map (mk' H) ⊓ Subgroup.centralizer ({c} : Set (L ⧸ H)) = ⊥ := by
  obtain ⟨x, hxW, rfl⟩ := hcmem
  have hx1 : x ≠ 1 := fun hcx => hc1 (by rw [hcx, map_one])
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzU, hzc⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨v, hvU, rfl⟩ := hzU
  have hconjU : x⁻¹ * v * x ∈ U :=
    (Subgroup.mem_set_normalizer_iff''.1 (hc.le_normalizer_U hxW) v).1 hvU
  have hcomm : (mk' H) v * (mk' H) x = (mk' H) x * (mk' H) v :=
    Subgroup.mem_centralizer_singleton_iff.1 hzc
  have hH : x⁻¹ * v * x * v⁻¹ ∈ H := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    have hval : (QuotientGroup.mk (x⁻¹ * v * x * v⁻¹) : L ⧸ H)
        = ((mk' H) x)⁻¹ * ((mk' H) v * (mk' H) x) * ((mk' H) v)⁻¹ := by
      change (mk' H) (x⁻¹ * v * x * v⁻¹) = _
      simp only [map_mul, map_inv]
      group
    rw [hval, hcomm]
    group
  have hmem : x⁻¹ * v * x * v⁻¹ ∈ H ⊓ U :=
    Subgroup.mem_inf.2 ⟨hH, U.mul_mem hconjU (U.inv_mem hvU)⟩
  rw [disjoint_iff.1 hc.disjoint_H_U] at hmem
  have hfix : x⁻¹ * v * x = v := mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem)
  have hvC : v ∈ U ⊓ Subgroup.centralizer ({x} : Set L) := by
    refine Subgroup.mem_inf.2 ⟨hvU, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc v * x = x * (x⁻¹ * v * x) := by group
      _ = x * v := by rw [hfix]
  rw [hc.inf_centralizer_U_eq_bot x hxW hx1] at hvC
  simp [Subgroup.mem_bot.1 hvC]

theorem card_map_U : Nat.card (U.map (mk' H)) = Nat.card U :=
  card_map_mk'_of_disjoint hc.disjoint_H_U.symm

theorem card_map_left : Nat.card (W₁.map (mk' H)) = Nat.card W₁ :=
  card_map_mk'_of_disjoint hc.disjoint_H_W₁.symm

theorem cfInner_bridgePermChar_self [Fintype L] :
    cfInner (bridgePermChar H W₁) (bridgePermChar H W₁)
      = 1 + ((Nat.card U : ℂ) - 1) / (Nat.card ↥W₁ : ℂ) := by
  have _ : Fintype (L ⧸ H) := Fintype.ofFinite _
  have _ : (U.map (mk' H)).Normal := hc.normal_map_U
  rw [bridgePermChar_eq_comp_mk, cfInner_comp_mk,
    cfInner_frobeniusComplementChar_self hc.isComplement'_map
      (fun c hcm hc1 => hc.inf_centralizer_map_eq_bot hcm hc1),
    hc.card_map_U, hc.card_map_left]

theorem bridgePermChar_eq_one_of_notMem [Fintype L] {z : L} (hz : z ∉ K) :
    bridgePermChar H W₁ z = 1 := by
  have _ : Fintype (L ⧸ H) := Fintype.ofFinite _
  have _ : (U.map (mk' H)).Normal := hc.normal_map_U
  rw [bridgePermChar_eq_comp_mk, Function.comp_apply]
  refine frobeniusComplementChar_eq_one_of_notMem hc.isComplement'_map
    (fun c hcm hc1 => hc.inf_centralizer_map_eq_bot hcm hc1) ?_
  rw [← hc.map_K_eq_map_U]
  exact fun hmem => hz ((mem_map_mk'_iff_of_le hc.H_le_K z).1 hmem)

theorem bridgePermChar_eq_zero_of_mem_sdiff [Fintype L] {z : L} (hzK : z ∈ K) (hzH : z ∉ H) :
    bridgePermChar H W₁ z = 0 := by
  have _ : Fintype (L ⧸ H) := Fintype.ofFinite _
  have _ : (U.map (mk' H)).Normal := hc.normal_map_U
  rw [bridgePermChar_eq_comp_mk, Function.comp_apply]
  refine frobeniusComplementChar_eq_zero hc.isComplement'_map ?_ ?_
  · rw [← hc.map_K_eq_map_U]
    exact Subgroup.mem_map_of_mem _ hzK
  · exact fun hcx => hzH ((QuotientGroup.eq_one_iff z).1 hcx)

section Characters

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]
  (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j : Irr ↥W₂}

include hσ

theorem primeTIirr_ne_one (hj : j ≠ principalIrr ↥W₂) :
    hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j ≠ 1 := by
  intro heq
  refine hc.primeCyclicTI.not_subset_charValueKernel_primeTIres hσ hc.right_le_H hj ?_
  intro y _
  have hy : hc.primeCyclicTI.primeTIres σ j y = 1 := by
    rw [hc.primeCyclicTI.primeTIres_apply, heq]
    rfl
  have h1 : hc.primeCyclicTI.primeTIres σ j 1 = 1 := by
    rw [hc.primeCyclicTI.primeTIres_one, heq]
    rfl
  rw [mem_charValueKernel, hy, h1]

theorem cfInner_primeTIirr_one_eq_zero (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j) (1 : L → ℂ) = 0 :=
  cfInner_eq_zero_of_mem_Irr (hc.primeCyclicTI.primeTIirr_principal_left_mem_Irr hσ j)
    one_mem_Irr (hc.primeTIirr_ne_one hσ hj)

theorem cfInner_bridgePermChar_primeTIirr (hj : j ≠ principalIrr ↥W₂) :
    cfInner (bridgePermChar H W₁)
      (hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j) = 0 := by
  classical
  have _ : Fintype ↥H := Fintype.ofFinite _
  have _ : Fintype ↥(H ⊔ W₁ : Subgroup L) := Fintype.ofFinite _
  have hIrr := hc.primeCyclicTI.primeTIirr_principal_left_mem_Irr hσ j
  rw [bridgePermChar]
  refine cfInner_indClassFun_one_eq_zero_of_sum (X := (H ⊔ W₁ : Subgroup L))
    (Irr_subset_classFun hIrr) ?_
  refine sum_subgroup_eq_zero_of_sum_coset (H := H) le_sup_left fun g => ?_
  refine sum_apply_mul_eq_zero (N := H) (by rw [irrChar_eq_Irr]; exact hIrr) ?_ g
  intro hsub
  refine hc.primeCyclicTI.not_subset_charValueKernel_primeTIres hσ hc.right_le_H hj ?_
  intro y hy
  have hval := hsub (Subgroup.mem_subgroupOf.1 hy)
  rw [mem_charValueKernel] at hval ⊢
  rw [hc.primeCyclicTI.primeTIres_apply, hc.primeCyclicTI.primeTIres_one, hval]

theorem primeTISign_eq_one
    (hchi1 : hc.primeCyclicTI.primeTIres σ j 1 = (Nat.card U : ℂ)) :
    hc.primeCyclicTI.primeTISign σ j = 1 := by
  have _ : Finite U := Subtype.finite
  have hupos : 1 ≤ Nat.card U := Nat.card_pos
  have hdvd : (Nat.card W₁ : ℤ) ∣ ((Nat.card U : ℤ) - 1) := by
    have hd := Int.natCast_dvd_natCast.2 hc.natCard_left_dvd_natCard_sub_one
    rwa [Nat.cast_sub hupos, Nat.cast_one] at hd
  have hmod : ((Nat.card U : ℤ)) ≡ 1 [ZMOD (Nat.card ↥W₁ : ℤ)] := by
    obtain ⟨cq, hcq⟩ := hdvd
    exact Int.modEq_iff_dvd.2 ⟨-cq, by linarith⟩
  refine hc.primeCyclicTI.primeTISign_eq_one_of_intCast_modEq_one hσ (principalIrr ↥W₁) j
    (m := (Nat.card U : ℤ)) ?_ hmod
  rw [← hc.primeCyclicTI.primeTIres_one (σ := σ) j, hchi1]
  push_cast
  ring

noncomputable def bridgeChar : L → ℂ :=
  bridgePermChar H W₁ - hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j

omit hσ in
theorem bridgeChar_apply (x : L) :
    hc.bridgeChar (σ := σ) (H := H) (j := j) x
      = bridgePermChar H W₁ x - hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j x := (rfl)

theorem bridgeChar_mem_virtualChars :
    hc.bridgeChar (σ := σ) (H := H) (j := j) ∈ virtualChars L := by
  rw [bridgeChar]
  refine sub_mem (bridgePermChar_mem_virtualChars H W₁) ?_
  rw [virtualChars_eq_span_Irr]
  exact Submodule.subset_span (hc.primeCyclicTI.primeTIirr_principal_left_mem_Irr hσ j)

theorem cfInner_bridgeChar_one (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hc.bridgeChar (σ := σ) (H := H) (j := j)) (1 : L → ℂ) = 1 := by
  rw [bridgeChar, cfInner_sub_left, cfInner_bridgePermChar_one,
    hc.cfInner_primeTIirr_one_eq_zero hσ hj, sub_zero]

theorem cfInner_bridgeChar_self (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hc.bridgeChar (σ := σ) (H := H) (j := j))
        (hc.bridgeChar (σ := σ) (H := H) (j := j))
      = ((Nat.card U : ℂ) - 1) / (Nat.card ↥W₁ : ℂ) + 2 := by
  have hgm := hc.cfInner_bridgePermChar_primeTIirr hσ hj
  have hmg : cfInner (hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j)
      (bridgePermChar H W₁) = 0 := by
    rw [← conj_cfInner, hgm, map_zero]
  rw [bridgeChar, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hgm, hmg,
    hc.cfInner_bridgePermChar_self (U := U),
    cfInner_self_of_mem_Irr (hc.primeCyclicTI.primeTIirr_principal_left_mem_Irr hσ j)]
  ring

theorem primeTIirr_apply_eq_one_of_mem_left
    (hchi1 : hc.primeCyclicTI.primeTIres σ j 1 = (Nat.card U : ℂ))
    {x : L} (hxW : x ∈ W₁) (hx1 : x ≠ 1) :
    hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j x = 1 := by
  have hx : (⟨x, hxW⟩ : ↥W₁) ≠ 1 := fun hcx => hx1 (by simpa using congrArg Subtype.val hcx)
  have hval := hc.primeCyclicTI.primeTIirr_apply_coe_left hσ (principalIrr ↥W₁) j hx
  rw [coe_principalIrr] at hval
  simpa [hc.primeTISign_eq_one hσ hchi1] using hval

theorem bridgeChar_eq_zero_of_notMem_sdiff_union
    (hchi1 : hc.primeCyclicTI.primeTIres σ j 1 = (Nat.card U : ℂ))
    (hchi0 : ∀ k : ↥K, (k : L) ∉ H → hc.primeCyclicTI.primeTIres σ j k = 0)
    {x : L} (hx : x ∉ ((H : Set L) \ {1}) ∪ cyclicTIsetConj W₁ W₂) :
    hc.bridgeChar (σ := σ) (H := H) (j := j) x = 0 := by
  have hmuIrr := hc.primeCyclicTI.primeTIirr_principal_left_mem_Irr hσ j
  have hmuCF : hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j ∈ classFun L :=
    Irr_subset_classFun hmuIrr
  have hgCF := bridgePermChar_mem_classFun (L := L) H W₁
  rw [bridgeChar_apply, sub_eq_zero]
  by_cases hxK : x ∈ K
  · by_cases hx1 : x = 1
    ·
      subst hx1
      rw [hc.bridgePermChar_one (U := U)]
      have h1 := hc.primeCyclicTI.primeTIres_one (σ := σ) j
      rw [hchi1] at h1
      exact h1
    ·
      have hxH : x ∉ H := fun hcx => hx (Or.inl ⟨hcx, by simpa using hx1⟩)
      rw [hc.bridgePermChar_eq_zero_of_mem_sdiff hxK hxH]
      have h0 := hchi0 ⟨x, hxK⟩ hxH
      rw [hc.primeCyclicTI.primeTIres_apply] at h0
      exact h0.symm
  ·
    have _ : Finite L := Finite.of_fintype L
    obtain ⟨g, y, hy, w, hw, hw1, hconj⟩ :=
      exists_conj_eq_mul_of_notMem hc.primeCyclicTI hxK
    rcases eq_or_ne y 1 with rfl | hy1
    ·
      rw [one_mul] at hconj
      have hIsConj : IsConj x w := by
        rw [isConj_comm, isConj_iff]
        exact ⟨g, by rw [← hconj]; group⟩
      have hwK : w ∉ K := by
        intro hcw
        refine hxK ?_
        have hKn := hc.primeCyclicTI.normal
        have hcx : x = g * w * g⁻¹ := by rw [← hconj]; group
        rw [hcx]
        exact hKn.conj_mem w hcw g
      rw [mem_classFun.1 hgCF x w hIsConj, mem_classFun.1 hmuCF x w hIsConj,
        hc.primeTIirr_apply_eq_one_of_mem_left hσ hchi1 hw hw1,
        hc.bridgePermChar_eq_one_of_notMem (U := U) hwK]
    ·
      exact absurd (Or.inr (mem_cyclicTIsetConj.2
        ⟨g⁻¹, y * w, mul_mem_cyclicTIset hc.primeCyclicTI hy hy1 hw hw1,
          by rw [← hconj]; group⟩)) hx

theorem bridgeChar_eq_zero_of_notMem_bridgeSupport
    (hchi1 : hc.primeCyclicTI.primeTIres σ j 1 = (Nat.card U : ℂ))
    (hchi0 : ∀ k : ↥K, (k : L) ∉ H → hc.primeCyclicTI.primeTIres σ j k = 0)
    {x : L} (hx : x ∉ bridgeSupport A W₁ W₂) :
    hc.bridgeChar (σ := σ) (H := H) (j := j) x = 0 :=
  hc.bridgeChar_eq_zero_of_notMem_sdiff_union hσ hchi1 hchi0
    fun hmem => hx (hc.sdiff_H_union_subset_bridgeSupport hmem)

end Characters

end IsPrimeTIBridgeConfig

end CFSG.FeitThompson
