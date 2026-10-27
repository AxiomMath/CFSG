module

public import CFSG.RankThree.PartOne.K1214.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open scoped Pointwise

theorem relIndex_sup_eq_relIndex_inf {X : Type*} [Group X] [Finite X] (V N : Subgroup X) [N.Normal] :
    V.relIndex (V ⊔ N) = (V ⊓ N).relIndex N := by
  have hcs := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_normal V N
  have hr := Subgroup.relIndex_mul_card (H := V) (K := V ⊔ N)
  rw [inf_of_le_left (le_sup_left : V ≤ V ⊔ N)] at hr
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have key : V.relIndex (V ⊔ N) * Nat.card (V ⊓ N : Subgroup X) = Nat.card N := by
    have h : Nat.card V * (V.relIndex (V ⊔ N) * Nat.card (V ⊓ N : Subgroup X)) =
        Nat.card V * Nat.card N := by
      rw [← hcs, ← hr]
      ring
    exact Nat.eq_of_mul_eq_mul_left hVpos h
  have h2 := Subgroup.relIndex_mul_card (H := V ⊓ N) (K := N)
  rw [inf_of_le_left (inf_le_right : V ⊓ N ≤ N)] at h2
  have hpos : 0 < Nat.card (V ⊓ N : Subgroup X) := Nat.card_pos
  have : V.relIndex (V ⊔ N) * Nat.card (V ⊓ N : Subgroup X) =
      (V ⊓ N).relIndex N * Nat.card (V ⊓ N : Subgroup X) := by
    rw [key, ← h2]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem exists_sylow_ge {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {X Y : Subgroup G}
    (hX : IsPGroup p X) (hXY : X ≤ Y) :
    ∃ P : Subgroup G, X ≤ P ∧ P ≤ Y ∧ IsPGroup p P ∧ ¬ p ∣ (P.subgroupOf Y).index := by
  have hX' : IsPGroup p (X.subgroupOf Y) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXY).symm
  obtain ⟨Q, hQ⟩ := hX'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥Y).map Y.subtype, ?_, ?_, (Q.isPGroup').map _, ?_⟩
  · intro e he
    exact ⟨⟨e, hXY he⟩, hQ (show (⟨e, hXY he⟩ : ↥Y) ∈ X.subgroupOf Y from he), rfl⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · have : ((Q : Subgroup ↥Y).map Y.subtype).subgroupOf Y = (Q : Subgroup ↥Y) := by
      ext y
      simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact Q.not_dvd_index

theorem sylow_mod_of_maximal {M : Type} [Group M] [Finite M] (D L U A : Subgroup M) [D.Normal]
    [L.Normal] (hD3 : ¬ 3 ∣ Nat.card D) (hU2 : IsPGroup 2 U)
    (hAU : A ≤ Subgroup.normalizer (U : Set M))
    (hAc : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ D)
    (hmax : ∀ S : Subgroup M, IsPGroup 2 S → U ≤ S → A ≤ Subgroup.normalizer (S : Set M) →
      S ≤ U)
    (hinv : ∀ S X : Subgroup M, ¬ 3 ∣ Nat.card S → A ≤ Subgroup.normalizer (S : Set M) →
      X ≤ S → IsPGroup 2 X → A ≤ Subgroup.normalizer (X : Set M) →
      ∃ P : Subgroup M, P ≤ S ∧ IsPGroup 2 P ∧ ¬ 2 ∣ (P.subgroupOf S).index ∧ X ≤ P ∧
        A ≤ Subgroup.normalizer (P : Set M)) :
    ¬ 2 ∣ (((U.map (QuotientGroup.mk' D)) ⊓ (L.map (QuotientGroup.mk' D))).subgroupOf
      (L.map (QuotientGroup.mk' D))).index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : M →* M ⧸ D := QuotientGroup.mk' D with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : π.ker = D := QuotientGroup.ker_mk' D
  set Ub : Subgroup (M ⧸ D) := U.map π with hUb
  set Lb : Subgroup (M ⧸ D) := L.map π with hLb
  haveI : Lb.Normal := Subgroup.Normal.map ‹L.Normal› π hsurj
  intro heven
  have hUb2 : IsPGroup 2 Ub := hU2.map π
  obtain ⟨Tb, hUbT, hTbS, hTb2, hTbidx⟩ := exists_sylow_ge (p := 2) hUb2 (le_sup_left : Ub ≤ Ub ⊔ Lb)
  have hTL : ¬ 2 ∣ ((Tb ⊓ Lb).subgroupOf Lb).index := by
    have hsupeq : Tb ⊔ Lb = Ub ⊔ Lb := le_antisymm (sup_le hTbS le_sup_right)
      (sup_le_sup_right hUbT _)
    have h1 := relIndex_sup_eq_relIndex_inf Tb Lb
    rw [hsupeq] at h1
    have h2 : Tb.relIndex (Ub ⊔ Lb) = (Tb.subgroupOf (Ub ⊔ Lb)).index := rfl
    show ¬ 2 ∣ (Tb ⊓ Lb).relIndex Lb
    rw [← h1, h2]
    exact hTbidx
  have hTbne : Tb ≠ Ub := by
    intro h
    rw [h] at hTL
    exact hTL heven
  have hcomm : ∀ a ∈ A, ∀ l ∈ Lb, π a * l * (π a)⁻¹ = l := by
    intro a ha l hl
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    have h := hAc a ha l₀ hl₀
    have h1 : π (a * l₀ * a⁻¹ * l₀⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hker]; exact h
    simp only [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hnormU : ∀ a ∈ A, ∀ u ∈ Ub, π a * u * (π a)⁻¹ ∈ Ub := by
    intro a ha u hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    refine ⟨a * u₀ * a⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hAU ha) u₀).mp hu₀
  have hTinv : ∀ a ∈ A, ∀ t ∈ Tb, π a * t * (π a)⁻¹ ∈ Tb := by
    intro a ha t ht
    have htS : t ∈ ((Ub ⊔ Lb : Subgroup (M ⧸ D)) : Set (M ⧸ D)) := hTbS ht
    rw [Subgroup.mul_normal] at htS
    obtain ⟨u, hu, l, hl, rfl⟩ := Set.mem_mul.mp htS
    have hlT : l ∈ Tb := by
      have := Tb.mul_mem (Tb.inv_mem (hUbT hu)) ht
      simpa [mul_assoc] using this
    have e : π a * (u * l) * (π a)⁻¹ = (π a * u * (π a)⁻¹) * l := by
      have := hcomm a ha l hl
      calc π a * (u * l) * (π a)⁻¹ = (π a * u * (π a)⁻¹) * (π a * l * (π a)⁻¹) := by group
        _ = (π a * u * (π a)⁻¹) * l := by rw [this]
    rw [e]
    exact Tb.mul_mem (hUbT (hnormU a ha u hu)) hlT
  have hAnT : ∀ a ∈ A, π a ∈ Subgroup.normalizer (Tb : Set (M ⧸ D)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hTinv a ha g hg, fun hg => ?_⟩
    have := hTinv a⁻¹ (A.inv_mem ha) _ hg
    simpa [map_inv, mul_assoc] using this
  set Sh : Subgroup M := Tb.comap π with hSh
  have hUSh : U ≤ Sh := fun u hu => hUbT ⟨u, hu, rfl⟩
  have hSh3 : ¬ 3 ∣ Nat.card Sh := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Sh) 3 h3
    have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
    have hπx : π (x : M) ∈ Tb := x.2
    obtain ⟨k, hk⟩ := hTb2 ⟨π (x : M), hπx⟩
    have h2 : (π (x : M)) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h3' : (π (x : M)) ^ 3 = 1 := by rw [← map_pow]; exact congrArg (fun y : ↥Sh => π (y : M)) hx3 |>.trans (by simp)
    have hg : (π (x : M)) ^ (Nat.gcd 3 (2 ^ k)) = 1 := pow_gcd_eq_one.mpr ⟨h3', h2⟩
    have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    rw [hcop, pow_one] at hg
    have hxD : (x : M) ∈ D := by rw [← hker, MonoidHom.mem_ker]; exact hg
    have hord : orderOf (⟨(x : M), hxD⟩ : ↥D) = 3 := by
      have : orderOf (⟨(x : M), hxD⟩ : ↥D) = orderOf (x : M) := by
        rw [← Subgroup.orderOf_coe]
      rw [this, Subgroup.orderOf_coe, hx]
    exact hD3 (hord ▸ orderOf_dvd_natCard (⟨(x : M), hxD⟩ : ↥D))
  have hAnSh : A ≤ Subgroup.normalizer (Sh : Set M) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have := Subgroup.mem_normalizer_iff.mp (hAnT a ha) (π g)
    simp only [hSh, Subgroup.mem_comap, map_mul, map_inv]
    exact this
  obtain ⟨P, hPS, hP2, hPidx, hUP, hAP⟩ := hinv Sh U hSh3 hAnSh hUSh hU2 hAU
  have hPU : P ≤ U := hmax P hP2 hUP hAP
  have hPeq : P = U := le_antisymm hPU hUP
  rw [hPeq] at hPidx
  let f : ↥Sh →* ↥Tb := (π.comp Sh.subtype).codRestrict Tb (fun x => x.2)
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨m, hm⟩ := hsurj (t : M ⧸ D)
    exact ⟨⟨m, by show π m ∈ Tb; rw [hm]; exact t.2⟩, Subtype.ext hm⟩
  have hmapU : (U.subgroupOf Sh).map f = Ub.subgroupOf Tb := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : M), hx, rfl⟩
    · intro ht
      obtain ⟨u, hu, hut⟩ := ht
      exact ⟨⟨u, hUSh hu⟩, hu, Subtype.ext hut⟩
  have hdvd := Subgroup.index_map_dvd (U.subgroupOf Sh) hf
  rw [hmapU] at hdvd
  have hodd : ¬ 2 ∣ (Ub.subgroupOf Tb).index := fun h => hPidx (h.trans hdvd)
  obtain ⟨n, hn⟩ := hTb2.index (Ub.subgroupOf Tb)
  have hn0 : n = 0 := by
    by_contra h
    exact hodd (hn ▸ dvd_pow_self 2 h)
  have h1 : (Ub.subgroupOf Tb).index = 1 := by rw [hn, hn0, pow_zero]
  have htop : Ub.subgroupOf Tb = ⊤ := Subgroup.index_eq_one.mp h1
  apply hTbne
  apply le_antisymm
  · intro t ht
    have : (⟨t, ht⟩ : ↥Tb) ∈ Ub.subgroupOf Tb := by rw [htop]; trivial
    exact this
  · exact hUbT

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
