module

public import CFSG.GH74.Generic.Front.Transfer
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidual_surjects_to_perfect_image
  normalizer_preimage_le_normalizer_perfectResidualOf)

variable {G : Type} [Group G]

@[expose] noncomputable def liftL (x : G) (K : Subgroup (CentralizerBar x)) :
    Subgroup ↥(centralizer ({x} : Set G)) :=
  perfectResidualOf (K.comap (proj x))

theorem liftL_le (x : G) (K : Subgroup (CentralizerBar x)) : liftL x K ≤ K.comap (proj x) := by
  unfold liftL perfectResidualOf
  exact Subgroup.map_subtype_le _

theorem le_perfectResidual_of_perfect {H : Type*} [Group H] (Q : Subgroup H) (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual H := by
  refine le_iInf fun n => ?_
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ]
    calc Q = ⁅Q, Q⁆ := hQ.symm
      _ ≤ ⁅derivedSeries H n, derivedSeries H n⁆ := Subgroup.commutator_mono ih ih

theorem le_perfectResidualOf {A : Type*} [Group A] {H Q : Subgroup A} (hQH : Q ≤ H)
    (hQ : ⁅Q, Q⁆ = Q) : Q ≤ perfectResidualOf H := by
  have hQ' : (Q.subgroupOf H).map H.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQH]
  have hperf : ⁅Q.subgroupOf H, Q.subgroupOf H⁆ = Q.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hQ', hQ]
  have h1 := le_perfectResidual_of_perfect _ hperf
  calc Q = (Q.subgroupOf H).map H.subtype := hQ'.symm
    _ ≤ perfectResidualOf H := Subgroup.map_mono h1

theorem perfectResidualOf_perfect {A : Type*} [Group A] [Finite A] (H : Subgroup A) :
    ⁅perfectResidualOf H, perfectResidualOf H⁆ = perfectResidualOf H :=
  Subgroup.isPerfect_iff.mp (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect H)

theorem perfect_le_liftL {x : G} {K : Subgroup (CentralizerBar x)}
    {Q : Subgroup ↥(centralizer ({x} : Set G))} (hQK : Q ≤ K.comap (proj x)) (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ liftL x K :=
  le_perfectResidualOf hQK hQ

theorem liftL_normal {x : G} {K : Subgroup (CentralizerBar x)} [K.Normal] :
    (liftL x K).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  apply top_le_iff.1
  intro g _
  have h := normalizer_preimage_le_normalizer_perfectResidualOf (proj x) K
    (show g ∈ Subgroup.comap (proj x) (Subgroup.normalizer (K : Set (CentralizerBar x))) by
      rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
      trivial)
  exact h

@[expose] noncomputable def piL (x : G) (K : Subgroup (CentralizerBar x)) : ↥(liftL x K) →* ↥K :=
  ((proj x).comp (liftL x K).subtype).codRestrict K fun l => liftL_le x K l.2

theorem piL_apply (x : G) (K : Subgroup (CentralizerBar x)) (l : ↥(liftL x K)) :
    ((piL x K l : ↥K) : CentralizerBar x) = proj x (l : ↥(centralizer ({x} : Set G))) := rfl

theorem piL_surjective [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} (hK : ⁅K, K⁆ = K) :
    Function.Surjective (piL x K) := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  set P : Subgroup ↥(centralizer ({x} : Set G)) := K.comap (proj x) with hP
  let f : ↥P →* ↥K := ((proj x).comp P.subtype).codRestrict K fun p => p.2
  have hf : Function.Surjective f := by
    intro k
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (k : CentralizerBar x)
    exact ⟨⟨c, show proj x c ∈ K from by rw [proj_apply, hc]; exact k.2⟩, Subtype.ext hc⟩
  have h1 := finite_perfectResidual_surjects_to_perfect_image f hf
  intro k
  have hk : k ∈ (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥P).map f := by rw [h1]; trivial
  obtain ⟨l, hl, hlk⟩ := hk
  refine ⟨⟨(l : ↥(centralizer ({x} : Set G))), ⟨l, hl, rfl⟩⟩, ?_⟩
  exact hlk

@[expose] def LiftExact (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ l ∈ liftL x K, proj x l = 1 → l = 1

theorem piL_injective {x : G} {K : Subgroup (CentralizerBar x)} (h : LiftExact x K) :
    Function.Injective (piL x K) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  apply Subtype.ext
  apply h _ l.2
  have := congrArg Subtype.val hl
  exact this

@[expose] noncomputable def liftEquiv [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} (h : LiftExact x K)
    (hK : ⁅K, K⁆ = K) : ↥(liftL x K) ≃* ↥K :=
  MulEquiv.ofBijective (piL x K) ⟨piL_injective h, piL_surjective hK⟩

@[expose] noncomputable def liftHom [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} (h : LiftExact x K)
    (hK : ⁅K, K⁆ = K) : ↥K →* G :=
  ((centralizer ({x} : Set G)).subtype.comp (liftL x K).subtype).comp (liftEquiv h hK).symm.toMonoidHom

end CFSG.GH74.Generic.S1
