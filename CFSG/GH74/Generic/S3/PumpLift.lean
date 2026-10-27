module

public import CFSG.GH74.Generic.BarSubnormal
public import CFSG.GH74.Generic.S1.LayerPair
public import CFSG.GH74.Generic.S3.Defs
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.LU.Ident

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 Subgroup
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}

omit [Finite G] in
theorem liftL_isSubnormal (hKsub : K.IsSubnormal) : (S1.liftL x K).IsSubnormal := by
  have hH : (K.comap (proj x)).IsSubnormal := hKsub.comap (proj x)
  have hMH : S1.liftL x K ≤ K.comap (proj x) := S1.liftL_le x K
  have hnorm : ((S1.liftL x K).subgroupOf (K.comap (proj x))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hMH).2
      (le_trans le_normalizer
        (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains _))
  exact Subgroup.IsSubnormal.trans hMH hnorm.isSubnormal hH

theorem map_liftL (hK : ⁅K, K⁆ = K) : (S1.liftL x K).map (proj x) = K := by
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    exact S1.liftL_le x K hl
  · intro k hk
    obtain ⟨l, hl⟩ := S1.piL_surjective hK ⟨k, hk⟩
    exact ⟨l, l.2, congrArg Subtype.val hl⟩

theorem liftL_isQuasisimple
    (hcentral : ∀ n ∈ S1.liftL x K, proj x n = 1 → ∀ l ∈ S1.liftL x K, n * l = l * n)
    (hKs : IsSimpleGroup ↥K) (hKn : ∃ a b : ↥K, a * b ≠ b * a) (hK : ⁅K, K⁆ = K) :
    IsQuasisimple ↥(S1.liftL x K) := by
  have hperf : Group.IsPerfect ↥(S1.liftL x K) :=
    Subgroup.isPerfect_iff.mpr (S1.perfectResidualOf_perfect _)
  have hs := S1.piL_surjective hK (x := x)
  have hcent : (S1.piL x K).ker ≤ center ↥(S1.liftL x K) := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    have hn1 : proj x (n : ↥(centralizer ({x} : Set G))) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hn)
      exact this
    exact Subtype.ext (hcentral _ n.2 hn1 _ g.2).symm
  let e : ↥(S1.liftL x K) ⧸ (S1.piL x K).ker ≃* ↥K :=
    QuotientGroup.quotientKerEquivOfSurjective (S1.piL x K) hs
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient (S1.piL x K).ker hcent
    hperf ((MulEquiv.isSimpleGroup_congr e).mpr hKs) ?_
  obtain ⟨a, b, hab⟩ := hKn
  exact ⟨e.symm a, e.symm b, fun h => hab (by have := congrArg e h; simpa using this)⟩

variable (x K) in
@[expose] noncomputable def liftSub : Subgroup G :=
  (S1.liftL x K).map (centralizer ({x} : Set G)).subtype

omit [Finite G] in
theorem liftSub_le : liftSub x K ≤ centralizer ({x} : Set G) :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem liftSub_subgroupOf :
    (liftSub x K).subgroupOf (centralizer ({x} : Set G)) = S1.liftL x K :=
  Subgroup.comap_map_eq_self_of_injective (centralizer ({x} : Set G)).subtype_injective _

omit [Finite G] in
theorem mem_liftSub {m : G} :
    m ∈ liftSub x K ↔ ∃ n ∈ S1.liftL x K, ((n : ↥(centralizer ({x} : Set G))) : G) = m := by
  unfold liftSub
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩

theorem imgBar_liftSub (hK : ⁅K, K⁆ = K) : imgBar x (liftSub x K) = K := by
  unfold imgBar
  rw [liftSub_subgroupOf]
  exact map_liftL hK

theorem liftSub_isQuasisimple
    (hcentral : ∀ n ∈ S1.liftL x K, proj x n = 1 → ∀ l ∈ S1.liftL x K, n * l = l * n)
    (hKs : IsSimpleGroup ↥K) (hKn : ∃ a b : ↥K, a * b ≠ b * a) (hK : ⁅K, K⁆ = K) :
    IsQuasisimple ↥(liftSub x K) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((S1.liftL x K).equivMapOfInjective (centralizer ({x} : Set G)).subtype
      (centralizer ({x} : Set G)).subtype_injective)
    (liftL_isQuasisimple hcentral hKs hKn hK)

omit [Finite G] in
theorem liftSub_kernel_central
    (hcentral : ∀ n ∈ S1.liftL x K, proj x n = 1 → ∀ l ∈ S1.liftL x K, n * l = l * n)
    {m : G} (hm : m ∈ liftSub x K) (hmC : m ∈ centralizer ({x} : Set G))
    (h1 : proj x ⟨m, hmC⟩ = 1) : ∀ n ∈ liftSub x K, m * n = n * m := by
  intro n hn
  obtain ⟨m₀, hm₀, rfl⟩ := mem_liftSub.1 hm
  obtain ⟨n₀, hn₀, rfl⟩ := mem_liftSub.1 hn
  exact congrArg Subtype.val (hcentral m₀ hm₀ h1 n₀ hn₀)

end Lift

section TwoComp

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_of_subnormal_block {V B : Subgroup G} (hBV : B ≤ V)
    (hsub : (B.subgroupOf V).IsSubnormal) (hq : IsQuasisimple ↥B) :
    CFSG.GH74.GLS.IsPCompIn 2 V B := by
  have hcomp : IsComponent (B.subgroupOf V) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hBV).symm hq, hsub⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCO : Group.IsSolvable (pPrimeCore 2 ↥V) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    have := pPrimeCore_coprime_card (p := 2) (G := ↥V)
    exact (Nat.coprime_two_left.1 this)
  exact ⟨hBV, CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp
    (CFSG.LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hcomp hCO)⟩

end TwoComp

end CFSG.GH74.Generic.S3
