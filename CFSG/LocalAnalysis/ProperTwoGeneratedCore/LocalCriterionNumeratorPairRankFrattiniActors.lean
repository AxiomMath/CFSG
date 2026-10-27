module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniOriginalSetup

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG CFSG.ShultStronglyClosedTI LocalCriterionGeometry LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

theorem involution_zpowers_eq_one_or (t : G) (ht : orderOf t = 2)
    (x : G) (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hmod := zpow_mod_orderOf t n
  norm_num only [ht] at hmod
  have hn : n % (2 : ℤ) = 0 ∨ n % (2 : ℤ) = 1 := by omega
  rcases hn with hn | hn
  · left
    simpa only [hn, zpow_zero] using hmod.symm
  · right
    simpa only [hn, zpow_one] using hmod.symm

theorem four_flip_zpowers_disjoint (W : Subgroup G) (t : G)
    (ht : orderOf t = 2) (htW : t ∉ W) : Disjoint W (Subgroup.zpowers t) := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  change x = 1
  rcases involution_zpowers_eq_one_or t ht x hx.2 with hx1 | hxt
  · exact hx1
  · exact (htW (hxt ▸ hx.1)).elim

theorem four_flip_cross_commutes (W : Subgroup G) (t : G)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    (w : W) (a : Subgroup.zpowers t) : Commute (W.subtype w) ((Subgroup.zpowers t).subtype a) := by
  have hcomm : Commute (w : G) t := centralizer_four_group_commutes W t hWt w
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.property
  change Commute (w : G) (a : G)
  rw [← hn]
  exact hcomm.zpow_right n

@[expose] def fourFlipProduct (W : Subgroup G) (t : G)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G)) :
    W × Subgroup.zpowers t →* G :=
  W.subtype.noncommCoprod (Subgroup.zpowers t).subtype (four_flip_cross_commutes W t hWt)

theorem fourFlipProduct_range (W : Subgroup G) (t : G)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G)) :
    (fourFlipProduct W t hWt).range = W ⊔ Subgroup.zpowers t := by
  exact (MonoidHom.noncommCoprod_range W.subtype (Subgroup.zpowers t).subtype
    (four_flip_cross_commutes W t hWt)).trans (by rw [Subgroup.range_subtype,
      Subgroup.range_subtype])

@[expose] def fourFlipProductEquiv (W : Subgroup G) (t : G)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    (ht : orderOf t = 2) (htW : t ∉ W) :
    W × Subgroup.zpowers t ≃* ↥(W ⊔ Subgroup.zpowers t) := by
  let f := fourFlipProduct W t hWt
  have hf : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    simpa only [Subgroup.range_subtype] using
      (show Function.Injective W.subtype ∧
        Function.Injective (Subgroup.zpowers t).subtype ∧
        Disjoint W (Subgroup.zpowers t) from
          ⟨W.subtype_injective, (Subgroup.zpowers t).subtype_injective,
            four_flip_zpowers_disjoint W t ht htW⟩)
  have hrange := fourFlipProduct_range W t hWt
  let g := f.codRestrict (W ⊔ Subgroup.zpowers t) (fun x => by
    rw [← hrange]
    exact ⟨x, rfl⟩)
  apply MulEquiv.ofBijective g
  constructor
  · intro x y hxy
    exact hf (congrArg Subtype.val hxy)
  · intro x
    have hx : (x : G) ∈ f.range := hrange.symm ▸ x.property
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, Subtype.ext ha⟩

theorem four_flip_isElementary (W : Subgroup G) [IsElementaryAbelian 2 W]
    (t : G) (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    (ht : orderOf t = 2) (htW : t ∉ W) :
    IsElementaryAbelian 2 ↥(W ⊔ Subgroup.zpowers t) := by
  let e := fourFlipProductEquiv W t hWt ht htW
  have hcomm : IsMulCommutative ↥(W ⊔ Subgroup.zpowers t) :=
    e.surjective.isMulCommutative (inferInstance : IsMulCommutative (W × Subgroup.zpowers t))
  refine
    { toIsMulCommutative := hcomm
      exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro x
  obtain ⟨⟨w, a⟩, rfl⟩ := e.surjective x
  have hp : (w, a) ^ 2 = 1 := by
    apply Prod.ext
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) w
    · apply Subtype.ext
      exact orderOf_dvd_iff_pow_eq_one.mp
        (by simpa only [ht] using orderOf_dvd_of_mem_zpowers a.property)
  rw [← map_pow, hp, map_one]

theorem four_flip_card [Finite G] (W : Subgroup G) (hWcard : Nat.card W = 4)
    (t : G) (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    (ht : orderOf t = 2) (htW : t ∉ W) :
    Nat.card ↥(W ⊔ Subgroup.zpowers t) = 8 := by
  calc
    Nat.card ↥(W ⊔ Subgroup.zpowers t) = Nat.card (W × Subgroup.zpowers t) :=
      (Nat.card_congr (fourFlipProductEquiv W t hWt ht htW).toEquiv).symm
    _ = 8 := by rw [Nat.card_prod, hWcard, Nat.card_zpowers, ht]

theorem four_flip_finrank [Finite G] (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWcard : Nat.card W = 4) (t : G)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    (ht : orderOf t = 2) (htW : t ∉ W) :
    let : IsElementaryAbelian 2 ↥(W ⊔ Subgroup.zpowers t) :=
      four_flip_isElementary W t hWt ht htW
    Module.finrank (ZMod 2) (Additive ↥(W ⊔ Subgroup.zpowers t)) = 3 := by
  let : IsElementaryAbelian 2 ↥(W ⊔ Subgroup.zpowers t) :=
    four_flip_isElementary W t hWt ht htW
  apply Nat.pow_right_injective (a := 2) (by decide)
  change 2 ^ Module.finrank (ZMod 2) (Additive ↥(W ⊔ Subgroup.zpowers t)) = 2 ^ 3
  rw [← elementary_card_eq_pow_finrank (p := 2), four_flip_card W hWcard t hWt ht htW]

theorem original_pair_flip_not_mem_four_group
    {H : Subgroup G} {z : G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {t : G}
    (ht : t ∈ rightPairFlipFiber H z beta)
    (W : Subgroup G) (hWB : W ≤ pairPointStabilizer H beta) : t ∉ W :=
  fun htW => pair_flip_not_mem_point hbeta ht
    (pairPointStabilizer_le_point H beta (hWB htW))

theorem original_pair_generated_actor_structure [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (hWB : W ≤ pairPointStabilizer H beta)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G)) :
    IsElementaryAbelian 2 ↥(W ⊔ Subgroup.zpowers t) ∧
      Nat.card ↥(W ⊔ Subgroup.zpowers t) = 8 := by
  have htW := original_pair_flip_not_mem_four_group hbeta ht W hWB
  have htorder := original_pair_flip_order h ht
  exact ⟨four_flip_isElementary W t hWt htorder htW,
    four_flip_card W hWcard t hWt htorder htW⟩

theorem original_generated_actor_frattini_lifting [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (hWB : W ≤ pairPointStabilizer H beta)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hinvariant : W ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G)) :
    let A := W ⊔ Subgroup.zpowers t
    let := normalizerFrattiniBaseAction P
    let : MulDistribMulAction A P := MulDistribMulAction.compHom P (Subgroup.inclusion hinvariant)
    let := frattiniQuotientAction (A := A) (P := P)
    IsElementaryAbelian 2 A ∧ Nat.card A = 8 ∧
      Nat.Coprime (Nat.card A) (Nat.card (frattini P)) ∧
        Nat.Coprime (Nat.card A) (Nat.card (P ⧸ frattini P)) ∧
          ∀ a : A, actorFixedSubgroup (I := P ⧸ frattini P) a =
            (actorFixedSubgroup (I := P) a).map (QuotientGroup.mk' (frattini P)) := by
  let A := W ⊔ Subgroup.zpowers t
  obtain ⟨helem, hcard⟩ := original_pair_generated_actor_structure h hbeta ht W hWcard hWB hWt
  let : IsElementaryAbelian 2 A := helem
  let := normalizerFrattiniBaseAction P
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P (Subgroup.inclusion hinvariant)
  let := frattiniQuotientAction (A := A) (P := P)
  have hkernel := frattini_kernel_structure hP hpodd
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨helem, hcard, ?_, ?_, ?_⟩
  · rw [hcard]
    exact hkernel.2.2.1.coprime_two_left.pow_left 3
  · rw [hcard]
    exact hkernel.2.2.2.2.coprime_two_left.pow_left 3
  · intro a
    exact frattini_fixed_quotient_eq_image hP hpodd a
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
