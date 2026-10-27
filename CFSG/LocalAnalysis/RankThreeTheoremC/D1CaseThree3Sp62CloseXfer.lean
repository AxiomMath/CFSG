module

import CFSG.LocalAnalysis.AGLEmbedding.KlingenRouteAux
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

section Quotient

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (O : Subgroup Y) [O.Normal]

theorem le_of_map_quotient_le_of_isPGroup (hp : p.Prime) (hO : p.Coprime (Nat.card O))
    {S U V : Subgroup Y} (hS : IsPGroup p S) (hU : U ≤ S) (hV : V ≤ S)
    (h : U.map (QuotientGroup.mk' O) ≤ V.map (QuotientGroup.mk' O)) : U ≤ V := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h (Subgroup.mem_map_of_mem _ hx)
  have := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp O hO hS (hV hy) (hU hx) hxy
  exact this ▸ hy

theorem map_mk_normalizer_eq (hp : p.Prime) (hO : p.Coprime (Nat.card O)) {S : Subgroup Y}
    (hS : IsPGroup p S) :
    (Subgroup.normalizer (S : Set Y)).map (QuotientGroup.mk' O) =
      Subgroup.normalizer ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) := by
  refine le_antisymm (Subgroup.le_normalizer_map _) fun x hx => ?_
  obtain ⟨g, hg, rfl⟩ :=
    CFSG.AGLEmbedding.exists_mem_normalizer_mk_eq_of_mem_normalizer hp O hO hS hx
  exact ⟨g, hg, rfl⟩

theorem mem_normalizer_iff_quotient_mem_normalizer (hp : p.Prime) (hO : p.Coprime (Nat.card O))
    {S B : Subgroup Y} (hS : IsPGroup p S) (hBS : B ≤ S) {n : Y}
    (hn : n ∈ Subgroup.normalizer (S : Set Y)) :
    n ∈ Subgroup.normalizer (B : Set Y) ↔ QuotientGroup.mk' O n ∈
      Subgroup.normalizer ((B.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) := by
  refine ⟨fun h => Subgroup.le_normalizer_map _ ⟨n, h, rfl⟩, fun h => ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h ⊢
  have hnS : S.map (MulAut.conj n).toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have h1 : B.map (MulAut.conj n).toMonoidHom ≤ S := hnS ▸ Subgroup.map_mono hBS
  have hcomm : (QuotientGroup.mk' O).comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj (QuotientGroup.mk' O n)).toMonoidHom.comp (QuotientGroup.mk' O) :=
    MonoidHom.ext fun x => by simp [MulAut.conj_apply]
  have h2 : (B.map (MulAut.conj n).toMonoidHom).map (QuotientGroup.mk' O) =
      B.map (QuotientGroup.mk' O) := by
    rw [Subgroup.map_map, hcomm, ← Subgroup.map_map]
    exact h
  exact le_antisymm (le_of_map_quotient_le_of_isPGroup O hp hO hS h1 hBS h2.le)
    (le_of_map_quotient_le_of_isPGroup O hp hO hS hBS h1 h2.ge)

theorem relIndex_normalizer_eq_map_mk (hp : p.Prime) (hO : p.Coprime (Nat.card O))
    {S B : Subgroup Y} (hS : IsPGroup p S) (hBS : B ≤ S) :
    (Subgroup.normalizer (B : Set Y)).relIndex (Subgroup.normalizer (S : Set Y)) =
      (Subgroup.normalizer
        ((B.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))).relIndex
        (Subgroup.normalizer
          ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))) := by
  set N := Subgroup.normalizer (S : Set Y) with hN
  set NB' := Subgroup.normalizer ((B.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))
    with hNB'
  have hmap := map_mk_normalizer_eq O hp hO hS
  have key : Subgroup.normalizer (B : Set Y) ⊓ N = NB'.comap (QuotientGroup.mk' O) ⊓ N := by
    ext n
    simp only [Subgroup.mem_inf, Subgroup.mem_comap]
    refine and_congr_left fun hn => ?_
    exact mem_normalizer_iff_quotient_mem_normalizer O hp hO hS hBS hn
  calc (Subgroup.normalizer (B : Set Y)).relIndex N
      = (Subgroup.normalizer (B : Set Y) ⊓ N).relIndex N := (Subgroup.inf_relIndex_right _ _).symm
    _ = (NB'.comap (QuotientGroup.mk' O) ⊓ N).relIndex N := by rw [key]
    _ = (NB'.comap (QuotientGroup.mk' O)).relIndex N := Subgroup.inf_relIndex_right _ _
    _ = NB'.relIndex (N.map (QuotientGroup.mk' O)) := Subgroup.relIndex_comap _ _ _
    _ = _ := by rw [hmap]

theorem relIndex_centralizer_eq_map_mk (hp : p.Prime) (hO : p.Coprime (Nat.card O))
    {S : Subgroup Y} (hS : IsPGroup p S) :
    (Subgroup.centralizer (S : Set Y)).relIndex (Subgroup.normalizer (S : Set Y)) =
      (Subgroup.centralizer
        ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))).relIndex
        (Subgroup.normalizer
          ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))) := by
  set ρ := QuotientGroup.mk' O with hρ
  set N := Subgroup.normalizer (S : Set Y) with hN
  set N' := Subgroup.normalizer ((S.map ρ : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) with hN'
  set C' := Subgroup.centralizer ((S.map ρ : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) with hC'
  have hmap : N.map ρ = N' := map_mk_normalizer_eq O hp hO hS
  let ψ : ↥N →* ↥N' := (ρ.comp N.subtype).codRestrict N' fun n => hmap ▸ ⟨n, n.2, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn, rfl⟩ := hmap ▸ hx
    exact ⟨⟨n, hn⟩, rfl⟩
  have hC'n : (C'.subgroupOf N').Normal := by
    rw [hC', hN', ← Subgroup.normalizerMonoidHom_ker]
    infer_instance
  let φ : ↥N →* ↥N' ⧸ (C'.subgroupOf N') := (QuotientGroup.mk' (C'.subgroupOf N')).comp ψ
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hψ
  have hker : φ.ker = (Subgroup.centralizer (S : Set Y)).subgroupOf N := by
    ext n
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ψ, MonoidHom.codRestrict_apply,
      Subgroup.coe_subtype, hC', Subgroup.mem_centralizer_iff]
    constructor
    · intro h s hs
      have hs' : ρ s ∈ (S.map ρ : Subgroup (Y ⧸ O)) := Subgroup.mem_map_of_mem _ hs
      have hcomm := h (ρ s) hs'
      have hnS : (n : Y) * s * (n : Y)⁻¹ ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp n.2 s).mp hs
        exact this
      have h1 : ρ ((n : Y) * s * (n : Y)⁻¹) = ρ s := by
        have e : ρ (n : Y) * ρ s = ρ s * ρ (n : Y) := hcomm.symm
        rw [map_mul, map_mul, map_inv, e, mul_inv_cancel_right]
      have := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp O hO hS hnS hs h1
      calc s * (n : Y) = (n : Y) * s * (n : Y)⁻¹ * (n : Y) := by rw [this]
        _ = (n : Y) * s := by group
    · intro h x hx
      obtain ⟨s, hs, rfl⟩ := hx
      have := h s hs
      rw [← map_mul, ← map_mul, this]
  have h := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  rw [hker] at h
  exact h

end Quotient

section SubgroupOf

variable {G : Type*} [Group G] {A : Subgroup G}

theorem relIndex_centralizer_eq_subgroupOf {J : Subgroup G} (hJA : J ≤ A) :
    (Subgroup.centralizer (J : Set G)).relIndex (Subgroup.normalizer (J : Set G) ⊓ A) =
      (Subgroup.centralizer ((J.subgroupOf A : Subgroup A) : Set A)).relIndex
        (Subgroup.normalizer ((J.subgroupOf A : Subgroup A) : Set A)) := by
  have h1 : (Subgroup.normalizer (J : Set G) ⊓ A).subgroupOf A =
      Subgroup.normalizer ((J.subgroupOf A : Subgroup A) : Set A) := by
    rw [Subgroup.inf_subgroupOf_right, Subgroup.subgroupOf_normalizer_eq hJA]
  have h2 : (Subgroup.centralizer (J : Set G)).subgroupOf A =
      Subgroup.centralizer ((J.subgroupOf A : Subgroup A) : Set A) := by
    ext a
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h t ht
      exact Subtype.ext (h t ht)
    · intro h j hj
      exact congrArg Subtype.val (h ⟨j, hJA hj⟩ hj)
  rw [← Subgroup.relIndex_subgroupOf (H := Subgroup.centralizer (J : Set G)) (inf_le_right :
    Subgroup.normalizer (J : Set G) ⊓ A ≤ A), h1, h2]

theorem relIndex_normalizer_eq_subgroupOf {J B : Subgroup G} (hJA : J ≤ A) (hBJ : B ≤ J) :
    (Subgroup.normalizer (B : Set G)).relIndex (Subgroup.normalizer (J : Set G) ⊓ A) =
      (Subgroup.normalizer ((B.subgroupOf A : Subgroup A) : Set A)).relIndex
        (Subgroup.normalizer ((J.subgroupOf A : Subgroup A) : Set A)) := by
  have h1 : (Subgroup.normalizer (J : Set G) ⊓ A).subgroupOf A =
      Subgroup.normalizer ((J.subgroupOf A : Subgroup A) : Set A) := by
    rw [Subgroup.inf_subgroupOf_right, Subgroup.subgroupOf_normalizer_eq hJA]
  have h2 : (Subgroup.normalizer (B : Set G)).subgroupOf A =
      Subgroup.normalizer ((B.subgroupOf A : Subgroup A) : Set A) :=
    Subgroup.subgroupOf_normalizer_eq (hBJ.trans hJA)
  rw [← Subgroup.relIndex_subgroupOf (H := Subgroup.normalizer (B : Set G)) (inf_le_right :
    Subgroup.normalizer (J : Set G) ⊓ A ≤ A), h1, h2]

variable {p : ℕ}

theorem relIndex_centralizer_eq_of_quotient [Finite G] (hp : p.Prime) (O : Subgroup A) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {J : Subgroup G} (hJA : J ≤ A) (hJ : IsPGroup p J) :
    (Subgroup.centralizer (J : Set G)).relIndex (Subgroup.normalizer (J : Set G) ⊓ A) =
      (Subgroup.centralizer (((J.subgroupOf A).map (QuotientGroup.mk' O) :
        Subgroup (A ⧸ O)) : Set (A ⧸ O))).relIndex
        (Subgroup.normalizer (((J.subgroupOf A).map (QuotientGroup.mk' O) :
          Subgroup (A ⧸ O)) : Set (A ⧸ O))) :=
  (relIndex_centralizer_eq_subgroupOf hJA).trans
    (relIndex_centralizer_eq_map_mk O hp hO hJ.comap_subtype)

theorem relIndex_normalizer_eq_of_quotient [Finite G] (hp : p.Prime) (O : Subgroup A) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {J B : Subgroup G} (hJA : J ≤ A) (hBJ : B ≤ J)
    (hJ : IsPGroup p J) :
    (Subgroup.normalizer (B : Set G)).relIndex (Subgroup.normalizer (J : Set G) ⊓ A) =
      (Subgroup.normalizer (((B.subgroupOf A).map (QuotientGroup.mk' O) :
        Subgroup (A ⧸ O)) : Set (A ⧸ O))).relIndex
        (Subgroup.normalizer (((J.subgroupOf A).map (QuotientGroup.mk' O) :
          Subgroup (A ⧸ O)) : Set (A ⧸ O))) :=
  (relIndex_normalizer_eq_subgroupOf hJA hBJ).trans
    (relIndex_normalizer_eq_map_mk O hp hO hJ.comap_subtype
      (Subgroup.subgroupOf_mono A hBJ))

theorem map_mk_subgroupOf_zpowers (O : Subgroup A) [O.Normal] {b : G} (hb : b ∈ A) :
    ((Subgroup.zpowers b).subgroupOf A).map (QuotientGroup.mk' O) =
      Subgroup.zpowers (QuotientGroup.mk' O ⟨b, hb⟩) := by
  have e1 : (Subgroup.zpowers b).subgroupOf A = Subgroup.zpowers (⟨b, hb⟩ : A) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  rw [e1, MonoidHom.map_zpowers]

end SubgroupOf

end CFSG.LocalAnalysis.RankThreeTheoremC
