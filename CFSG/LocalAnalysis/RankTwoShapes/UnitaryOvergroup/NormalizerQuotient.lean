module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.Complement
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankTwoShapes

variable {G : Type*} [Group G]

theorem conj_mem_centralizer_of_mem_normalizer {Q : Subgroup G} {n c : G}
    (hn : n ∈ Subgroup.normalizer (Q : Set G)) (hc : c ∈ Subgroup.centralizer (Q : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro q hq
  have hq' : n⁻¹ * q * n ∈ Q := (Subgroup.mem_normalizer_iff''.mp hn q).mp hq
  have h := hc _ hq'
  calc q * (n * c * n⁻¹) = n * ((n⁻¹ * q * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * q * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * q := by group

@[expose] def centralizerConj {Q : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (Q : Set G)) :
    MulAut (Subgroup.centralizer (Q : Set G)) where
  toFun c := ⟨n * c * n⁻¹, conj_mem_centralizer_of_mem_normalizer hn c.2⟩
  invFun c := ⟨n⁻¹ * c * n, by
    have := conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ hn) c.2
    rwa [inv_inv] at this⟩
  left_inv c := Subtype.ext (by simp only; group)
  right_inv c := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] def centralizerOddPart (Q : Subgroup G) : Subgroup G :=
  (CFSG.pPrimeCore 2 (Subgroup.centralizer (Q : Set G))).map
    (Subgroup.centralizer (Q : Set G)).subtype

theorem centralizerOddPart_le_centralizer (Q : Subgroup G) :
    centralizerOddPart Q ≤ Subgroup.centralizer (Q : Set G) :=
  Subgroup.map_subtype_le _

theorem centralizerOddPart_subgroupOf (Q : Subgroup G) :
    (centralizerOddPart Q).subgroupOf (Subgroup.centralizer (Q : Set G)) =
      CFSG.pPrimeCore 2 (Subgroup.centralizer (Q : Set G)) :=
  Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

theorem conj_mem_centralizerOddPart {Q : Subgroup G} {n k : G}
    (hn : n ∈ Subgroup.normalizer (Q : Set G)) (hk : k ∈ centralizerOddPart Q) :
    n * k * n⁻¹ ∈ centralizerOddPart Q := by
  obtain ⟨k', hk', rfl⟩ := hk
  have hfix := Subgroup.characteristic_iff_map_eq.mp
    (CFSG.pPrimeCore_characteristic (p := 2) (G := Subgroup.centralizer (Q : Set G)))
    (centralizerConj hn)
  refine ⟨centralizerConj hn k', ?_, rfl⟩
  rw [← hfix]
  exact Subgroup.mem_map_of_mem _ hk'

instance centralizerOddPart_subgroupOf_normalizer_normal (Q : Subgroup G) :
    ((centralizerOddPart Q).subgroupOf (Subgroup.normalizer (Q : Set G))).Normal where
  conj_mem k hk n := by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact conj_mem_centralizerOddPart n.2 hk

instance centralizer_subgroupOf_normalizer_normal (Q : Subgroup G) :
    ((Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))).Normal where
  conj_mem c hc n := by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    exact conj_mem_centralizer_of_mem_normalizer n.2 hc

instance sup_centralizer_subgroupOf_normalizer_normal (Q : Subgroup G) :
    ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf
      (Subgroup.normalizer (Q : Set G))).Normal := by
  rw [Subgroup.subgroupOf_sup Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)]
  have := Subgroup.normal_in_normalizer (H := Q)
  infer_instance

theorem isComplement'_pPrimeCore_of_sylow_central {X : Type*} [Group X] [Finite X]
    (Z : Sylow 2 X) (hZ : ∀ z ∈ (Z : Subgroup X), ∀ x : X, z * x = x * z) :
    (CFSG.pPrimeCore 2 X).IsComplement' Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : Subgroup.normalizer ((Z : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((Z : Subgroup X) : Set X) := fun x _ =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => hZ z hz x
  have hT := MonoidHom.ker_transferSylow_isComplement' Z hP
  have hTodd := MonoidHom.not_dvd_card_ker_transferSylow Z hP
  have hTK : (MonoidHom.transferSylow Z hP).ker ≤ CFSG.pPrimeCore 2 X :=
    le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hTodd⟩
  have hKT : CFSG.pPrimeCore 2 X ≤ (MonoidHom.transferSylow Z hP).ker := by
    obtain ⟨a, ha⟩ := Z.isPGroup'.exists_card_eq
    have h1 : (MonoidHom.transferSylow Z hP).ker.relIndex (CFSG.pPrimeCore 2 X) ∣
        Nat.card (CFSG.pPrimeCore 2 X) := Subgroup.relIndex_dvd_card _ _
    have h2 : (MonoidHom.transferSylow Z hP).ker.relIndex (CFSG.pPrimeCore 2 X) ∣ 2 ^ a := by
      rw [← ha, ← hT.symm.index_eq_card]
      exact Subgroup.relIndex_dvd_index_of_le hTK
    have hcop : Nat.Coprime (Nat.card (CFSG.pPrimeCore 2 X)) (2 ^ a) :=
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := X)).symm.pow_right a
    exact Subgroup.relIndex_eq_one.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  rw [le_antisymm hKT hTK]
  exact hT

theorem not_two_dvd_relIndex_inf_centralizer [Finite G] (Q : Subgroup G)
    (P : Sylow 2 (Subgroup.normalizer (Q : Set G)))
    (hCP : (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
        (Subgroup.normalizer (Q : Set G)).subtype ⊓ Subgroup.centralizer (Q : Set G) =
      Q ⊓ Subgroup.centralizer (Q : Set G)) :
    ¬ 2 ∣ (Q ⊓ Subgroup.centralizer (Q : Set G)).relIndex (Subgroup.centralizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PC, hPC⟩ := CFSG.Glauberman.sylow_inf_normal P
    (N := (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))
  have h1 := PC.not_dvd_index
  rw [hPC] at h1
  have hPeq : (P : Subgroup (Subgroup.normalizer (Q : Set G))) =
      ((P : Subgroup (Subgroup.normalizer (Q : Set G))).map
        (Subgroup.normalizer (Q : Set G)).subtype).subgroupOf (Subgroup.normalizer (Q : Set G)) :=
    (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _).symm
  have h2 : (((P : Subgroup (Subgroup.normalizer (Q : Set G))) ⊓
      (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))).subgroupOf
        ((Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))).index =
      (Q ⊓ Subgroup.centralizer (Q : Set G)).relIndex (Subgroup.centralizer (Q : Set G)) := by
    change ((P : Subgroup (Subgroup.normalizer (Q : Set G))) ⊓
      (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))).relIndex
        ((Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))) = _
    rw [Subgroup.inf_relIndex_right, hPeq,
      Subgroup.relIndex_subgroupOf (Subgroup.centralizer_le_normalizer _),
      ← Subgroup.inf_relIndex_right, hCP]
  rwa [h2] at h1

theorem isComplement'_pPrimeCore_centralizer [Finite G] (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hodd : ¬ 2 ∣ (Q ⊓ Subgroup.centralizer (Q : Set G)).relIndex
      (Subgroup.centralizer (Q : Set G))) :
    (CFSG.pPrimeCore 2 (Subgroup.centralizer (Q : Set G))).IsComplement'
      ((Q ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.centralizer (Q : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZp : IsPGroup 2 ((Q ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf
      (Subgroup.centralizer (Q : Set G))) :=
    (hQ.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  exact isComplement'_pPrimeCore_of_sylow_central (hZp.toSylow hodd) fun z hz x =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2 z (Subgroup.mem_subgroupOf.mp hz).1)

theorem inf_sup_centralizerOddPart_eq (Q : Subgroup G)
    (hcomp : (CFSG.pPrimeCore 2 (Subgroup.centralizer (Q : Set G))).IsComplement'
      ((Q ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.centralizer (Q : Set G)))) :
    (Q ⊓ Subgroup.centralizer (Q : Set G)) ⊔ centralizerOddPart Q =
      Subgroup.centralizer (Q : Set G) := by
  have h := congrArg (Subgroup.map (Subgroup.centralizer (Q : Set G)).subtype) hcomp.sup_eq_top
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rw [sup_comm]
  exact h

abbrev centricQuotient (Q : Subgroup G) : Type _ :=
  Subgroup.normalizer (Q : Set G) ⧸
    (centralizerOddPart Q).subgroupOf (Subgroup.normalizer (Q : Set G))

abbrev centricQuotientMk (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) →* centricQuotient Q :=
  QuotientGroup.mk' _

theorem centralizerOddPart_le_normalizer (Q : Subgroup G) :
    centralizerOddPart Q ≤ Subgroup.normalizer (Q : Set G) :=
  (centralizerOddPart_le_centralizer Q).trans (Subgroup.centralizer_le_normalizer _)

theorem coprime_two_natCard_centralizerOddPart [Finite G] (Q : Subgroup G) :
    Nat.Coprime 2 (Nat.card (centralizerOddPart Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [centralizerOddPart, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact CFSG.pPrimeCore_coprime_card

theorem disjoint_centralizerOddPart_subgroupOf [Finite G] (Q : Subgroup G)
    {X : Subgroup (Subgroup.normalizer (Q : Set G))} (hX : IsPGroup 2 X) :
    Disjoint X ((centralizerOddPart Q).subgroupOf (Subgroup.normalizer (Q : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hn, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (centralizerOddPart_le_normalizer Q)).toEquiv]
  exact (coprime_two_natCard_centralizerOddPart Q).pow_left n

theorem injOn_centricQuotientMk [Finite G] (Q : Subgroup G)
    {X : Subgroup (Subgroup.normalizer (Q : Set G))} (hX : IsPGroup 2 X) :
    Set.InjOn (centricQuotientMk Q) (X : Set (Subgroup.normalizer (Q : Set G))) := by
  intro x hx y hy hxy
  have h : x⁻¹ * y ∈ (centralizerOddPart Q).subgroupOf (Subgroup.normalizer (Q : Set G)) :=
    QuotientGroup.eq.mp hxy
  have h' : x⁻¹ * y ∈ X := X.mul_mem (X.inv_mem hx) hy
  have h1 := (disjoint_centralizerOddPart_subgroupOf Q hX).le_bot ⟨h', h⟩
  rw [Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem exists_sylow_eq_map_centricQuotientMk [Finite G] (Q : Subgroup G)
    (P : Sylow 2 (Subgroup.normalizer (Q : Set G))) :
    ∃ P' : Sylow 2 (centricQuotient Q),
      (P' : Subgroup (centricQuotient Q)) = (P : Subgroup _).map (centricQuotientMk Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (centricQuotientMk Q) := QuotientGroup.mk'_surjective _
  have hidx : ¬ 2 ∣ ((P : Subgroup _).map (centricQuotientMk Q)).index := by
    rw [← Subgroup.index_comap_of_surjective _ hsurj, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk']
    intro h
    exact P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le le_sup_left))
  exact ⟨(P.isPGroup'.map _).toSylow hidx, rfl⟩

theorem pCore_centricQuotient [Finite G] (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hdecomp : (Q ⊓ Subgroup.centralizer (Q : Set G)) ⊔ centralizerOddPart Q =
      Subgroup.centralizer (Q : Set G))
    (hrad : CFSG.pCore 2 (Subgroup.normalizer (Q : Set G) ⧸
      (Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))) = ⊥) :
    CFSG.pCore 2 (centricQuotient Q) =
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (centricQuotientMk Q) := QuotientGroup.mk'_surjective _
  have hQC : (Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)) ≤
      Q.subgroupOf (Subgroup.normalizer (Q : Set G)) ⊔
        (centralizerOddPart Q).subgroupOf (Subgroup.normalizer (Q : Set G)) := by
    rw [← Subgroup.subgroupOf_sup Subgroup.le_normalizer (centralizerOddPart_le_normalizer Q)]
    apply Subgroup.comap_mono
    apply sup_le le_sup_left
    rw [← hdecomp]
    exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hQp' : IsPGroup 2 (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm
  apply le_antisymm
  · apply sSup_le
    rintro D ⟨hDn, hDp⟩
    let ψ := QuotientGroup.map ((centralizerOddPart Q).subgroupOf (Subgroup.normalizer (Q : Set G)))
      ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))
      (MonoidHom.id _) (fun k hk =>
        (le_sup_right : Subgroup.centralizer (Q : Set G) ≤ _)
          (centralizerOddPart_le_centralizer Q hk))
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
      exact ⟨QuotientGroup.mk x, rfl⟩
    have hDψ : D.map ψ ≤ CFSG.pCore 2 _ := le_sSup ⟨hDn.map ψ hψ, hDp.map ψ⟩
    have hker : ψ.ker = Subgroup.map (QuotientGroup.mk' _) (Subgroup.comap (MonoidHom.id _)
        ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))) :=
      QuotientGroup.ker_map _ _ _ _
    rw [hrad, le_bot_iff, Subgroup.map_eq_bot_iff, hker] at hDψ
    refine hDψ.trans ?_
    rw [Subgroup.comap_id, Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk']
    exact hQC
  · exact le_sSup ⟨(Subgroup.normal_in_normalizer).map _ hsurj, hQp'.map _⟩

theorem centralizer_map_centricQuotientMk [Finite G] (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hdecomp : (Q ⊓ Subgroup.centralizer (Q : Set G)) ⊔ centralizerOddPart Q =
      Subgroup.centralizer (Q : Set G)) :
    Subgroup.centralizer (((Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map
        (centricQuotientMk Q) : Subgroup (centricQuotient Q)) : Set (centricQuotient Q)) =
      ((Q ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf
        (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) := by
  have hQp' : IsPGroup 2 (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm
  apply le_antisymm
  · intro h hh
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ h
    have hnC : (n : G) ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqN : q ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hq
      let q' : Subgroup.normalizer (Q : Set G) := ⟨q, hqN⟩
      have hq'Q : q' ∈ Q.subgroupOf (Subgroup.normalizer (Q : Set G)) := hq
      have h1 := Subgroup.mem_centralizer_iff.mp hh (centricQuotientMk Q q')
        (Subgroup.mem_map_of_mem _ hq'Q)
      rw [← map_mul, ← map_mul] at h1
      have h2 : (q' * n)⁻¹ * (n * q') ∈
          (centralizerOddPart Q).subgroupOf (Subgroup.normalizer (Q : Set G)) :=
        QuotientGroup.eq.mp h1
      have h3 : (q' * n)⁻¹ * (n * q') ∈ Q.subgroupOf (Subgroup.normalizer (Q : Set G)) := by
        have hrw : (q' * n)⁻¹ * (n * q') = (n⁻¹ * q'⁻¹ * n⁻¹⁻¹) * q' := by group
        rw [hrw]
        exact Subgroup.mul_mem _ ((Subgroup.normal_in_normalizer).conj_mem _
          (Subgroup.inv_mem _ hq'Q) n⁻¹) hq'Q
      have h4 := (disjoint_centralizerOddPart_subgroupOf Q hQp').le_bot ⟨h3, h2⟩
      rw [Subgroup.mem_bot, inv_mul_eq_one] at h4
      exact congrArg Subtype.val h4
    have hCZ : (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)) ≤
        Subgroup.comap (centricQuotientMk Q) (((Q ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf
          (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q)) := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
        ← Subgroup.subgroupOf_sup (inf_le_left.trans Subgroup.le_normalizer)
          (centralizerOddPart_le_normalizer Q), hdecomp]
    exact hCZ hnC
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_subgroupOf.mp hz).2 q (Subgroup.mem_subgroupOf.mp hq))

theorem fourCenter_centricRadical_normalizerQuotient [Finite G] (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (_hZ : IsElementaryAbelian 2 (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) ∧
      Nat.card (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) = 4)
    (P : Sylow 2 (Subgroup.normalizer (Q : Set G)))
    (hQP : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) ≤ P)
    (hCP : (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
        (Subgroup.normalizer (Q : Set G)).subtype ⊓ Subgroup.centralizer (Q : Set G) =
      Q ⊓ Subgroup.centralizer (Q : Set G))
    (hrad : CFSG.pCore 2 (Subgroup.normalizer (Q : Set G) ⧸
      (Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))) = ⊥) :
    centralizerOddPart Q ≤ Subgroup.centralizer (Q : Set G) ∧
    ((centralizerOddPart Q).subgroupOf (Subgroup.centralizer (Q : Set G))).Characteristic ∧
    ((centralizerOddPart Q).subgroupOf (Subgroup.centralizer (Q : Set G))).Normal ∧
    Nat.Coprime 2 (Nat.card (centralizerOddPart Q)) ∧
    (∃ k : ℕ,
      ((centralizerOddPart Q).subgroupOf (Subgroup.centralizer (Q : Set G))).index = 2 ^ k) ∧
    ((centralizerOddPart Q).subgroupOf (Subgroup.normalizer (Q : Set G))).Normal ∧
    (Q ⊓ Subgroup.centralizer (Q : Set G)) ⊔ centralizerOddPart Q =
      Subgroup.centralizer (Q : Set G) ∧
    Disjoint (Q ⊓ Subgroup.centralizer (Q : Set G)) (centralizerOddPart Q) ∧
    (∀ z ∈ Q ⊓ Subgroup.centralizer (Q : Set G), ∀ k ∈ centralizerOddPart Q, z * k = k * z) ∧
    Set.InjOn (centricQuotientMk Q) (P : Set (Subgroup.normalizer (Q : Set G))) ∧
    Set.InjOn (centricQuotientMk Q)
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G)) : Set (Subgroup.normalizer (Q : Set G))) ∧
    (∃ P' : Sylow 2 (centricQuotient Q),
      (P' : Subgroup (centricQuotient Q)) = (P : Subgroup _).map (centricQuotientMk Q)) ∧
    CFSG.pCore 2 (centricQuotient Q) =
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) ∧
    Subgroup.centralizer (((Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map
        (centricQuotientMk Q) : Subgroup (centricQuotient Q)) : Set (centricQuotient Q)) =
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) ⊓
        Subgroup.centralizer (((Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map
          (centricQuotientMk Q) : Subgroup (centricQuotient Q)) : Set (centricQuotient Q)) ∧
    Subgroup.centralizer (((Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map
        (centricQuotientMk Q) : Subgroup (centricQuotient Q)) : Set (centricQuotient Q)) =
      ((Q ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf
        (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp := isComplement'_pPrimeCore_centralizer Q hQ
    (not_two_dvd_relIndex_inf_centralizer Q P hCP)
  have hdecomp := inf_sup_centralizerOddPart_eq Q hcomp
  have hZp : IsPGroup 2 (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) :=
    hQ.to_le inf_le_left
  have hcent := centralizer_map_centricQuotientMk Q hQ hdecomp
  have hchar : ((centralizerOddPart Q).subgroupOf
      (Subgroup.centralizer (Q : Set G))).Characteristic := by
    rw [centralizerOddPart_subgroupOf]
    exact CFSG.pPrimeCore_characteristic
  refine ⟨centralizerOddPart_le_centralizer Q, hchar, Subgroup.normal_of_characteristic _,
    coprime_two_natCard_centralizerOddPart Q, ?_,
    inferInstance, hdecomp, ?_, ?_, injOn_centricQuotientMk Q P.isPGroup',
    (injOn_centricQuotientMk Q P.isPGroup').mono hQP, exists_sylow_eq_map_centricQuotientMk Q P,
    pCore_centricQuotient Q hQ hdecomp hrad, ?_, hcent⟩
  · obtain ⟨a, ha⟩ := hZp.exists_card_eq
    refine ⟨a, ?_⟩
    rw [centralizerOddPart_subgroupOf, hcomp.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, ha]
  · obtain ⟨a, ha⟩ := hZp.exists_card_eq
    apply Subgroup.disjoint_of_coprime_natCard
    rw [ha]
    exact (coprime_two_natCard_centralizerOddPart Q).pow_left a
  · intro z hz k hk
    exact Subgroup.mem_centralizer_iff.mp (centralizerOddPart_le_centralizer Q hk) z hz.1
  · rw [hcent]
    refine (inf_eq_right.mpr ?_).symm
    exact Subgroup.map_mono (Subgroup.comap_mono inf_le_left)

end CFSG.RankTwoShapes
