module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open Equiv Equiv.Perm CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem cycleType_two_two {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1) (hc : σ.support.card = 4) :
    σ.cycleType = {2, 2} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := Equiv.Perm.cycleType_of_pow_prime_eq_one h2
  have hs := Equiv.Perm.sum_cycleType σ
  rw [hn, hc, Multiset.sum_replicate] at hs
  have : σ.cycleType.card = 2 := by simp at hs; omega
  rw [hn, this]
  rfl

theorem cycleType_two_four {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1) (hc : σ.support.card = 8) :
    σ.cycleType = {2, 2, 2, 2} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := Equiv.Perm.cycleType_of_pow_prime_eq_one h2
  have hs := Equiv.Perm.sum_cycleType σ
  rw [hn, hc, Multiset.sum_replicate] at hs
  have : σ.cycleType.card = 4 := by simp at hs; omega
  rw [hn, this]
  rfl

theorem mem_alternatingGroup_two_two {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1)
    (hc : σ.support.card = 4) : σ ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup, sign_of_cycleType, cycleType_two_two h2 hc]
  decide

theorem mem_alternatingGroup_two_four {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1)
    (hc : σ.support.card = 8) : σ ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup, sign_of_cycleType, cycleType_two_four h2 hc]
  decide

structure A8Emb (a z : G) where
  φ : alternatingGroup (Fin 8) →* G
  injective : Function.Injective φ
  comm : ∀ t, a * φ t = φ t * a
  b : G
  hb : b ∈ orb2A a a
  comm_b : ∀ t, b * φ t = φ t * b
  shape_2211 : ∀ t : alternatingGroup (Fin 8), (t : Perm (Fin 8)).cycleType = {2, 2} →
    IsConj a (φ t)
  shape_2222 : ∀ t : alternatingGroup (Fin 8), (t : Perm (Fin 8)).cycleType = {2, 2, 2, 2} →
    IsConj z (φ t)
  fig8b : ∀ t : alternatingGroup (Fin 8), (t : Perm (Fin 8)).cycleType = {2, 2, 2, 2} →
    IsConj a (a * φ t)
  fig8b_b : ∀ t : alternatingGroup (Fin 8), (t : Perm (Fin 8)).cycleType = {2, 2, 2, 2} →
    IsConj a (b * φ t)
  fig8b_ab : ∀ t : alternatingGroup (Fin 8), (t : Perm (Fin 8)).cycleType = {2, 2, 2, 2} →
    IsConj a (a * b * φ t)

theorem A8Emb.nonempty (hL : F5Local G a z) : Nonempty (A8Emb a z) := by
  obtain ⟨b, hb⟩ := (hL.tableV.self.partition.orbit 0).nonempty
  have hb' : b ∈ orb2A a a := hb
  obtain ⟨e⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8
    (hL.tableV.self.shape_2A b hb')
  have hK : derivedOf (Gxy a b) ≤ Gx a :=
    (derivedOf_le _).trans (by rw [Gxy_eq_inf]; exact inf_le_left)
  have hKb : derivedOf (Gxy a b) ≤ Gx b :=
    (derivedOf_le _).trans (by rw [Gxy_eq_inf]; exact inf_le_right)
  refine ⟨⟨(derivedOf (Gxy a b)).subtype.comp e.toMonoidHom, ?_, ?_, b, hb', ?_, ?_, ?_, ?_, ?_,
    ?_⟩⟩
  · exact Subtype.coe_injective.comp e.injective
  · intro t
    exact mem_Gx.1 (hK (e t).2)
  · intro t
    exact mem_Gx.1 (hKb (e t).2)
  · intro t ht
    exact hL.a8shapes.self.shape_2211 _ hK e t ht
  · intro t ht
    exact hL.a8shapes.self.shape_2222 _ hK e t ht
  · intro t ht
    exact (hL.a8pictures.self.fig8b b hb' e t ht).2.1
  · intro t ht
    exact (hL.a8pictures.self.fig8b b hb' e t ht).2.2.1
  · intro t ht
    exact (hL.a8pictures.self.fig8b b hb' e t ht).2.2.2

@[expose] def TT (t : alternatingGroup (Fin 8)) : Prop :=
  (t : Perm (Fin 8)) ^ 2 = 1 ∧ (t : Perm (Fin 8)).support.card = 4

@[expose] def FF (t : alternatingGroup (Fin 8)) : Prop :=
  (t : Perm (Fin 8)) ^ 2 = 1 ∧ (t : Perm (Fin 8)).support.card = 8

instance (t : alternatingGroup (Fin 8)) : Decidable (TT t) := by unfold TT; infer_instance

instance (t : alternatingGroup (Fin 8)) : Decidable (FF t) := by unfold FF; infer_instance

theorem TT.cycleType {t : alternatingGroup (Fin 8)} (h : TT t) :
    (t : Perm (Fin 8)).cycleType = {2, 2} :=
  cycleType_two_two h.1 h.2

theorem FF.cycleType {t : alternatingGroup (Fin 8)} (h : FF t) :
    (t : Perm (Fin 8)).cycleType = {2, 2, 2, 2} :=
  cycleType_two_four h.1 h.2

@[expose] def ttElem (σ : Perm (Fin 8)) (h2 : σ ^ 2 = 1) (hc : σ.support.card = 4) :
    alternatingGroup (Fin 8) :=
  ⟨σ, mem_alternatingGroup_two_two h2 hc⟩

@[expose] def ffElem (σ : Perm (Fin 8)) (h2 : σ ^ 2 = 1) (hc : σ.support.card = 8) :
    alternatingGroup (Fin 8) :=
  ⟨σ, mem_alternatingGroup_two_four h2 hc⟩

theorem A8Emb.isConj_a (E : A8Emb a z) {t : alternatingGroup (Fin 8)} (h : TT t) :
    IsConj a (E.φ t) :=
  E.shape_2211 t h.cycleType

theorem A8Emb.isConj_z (E : A8Emb a z) {t : alternatingGroup (Fin 8)} (h : FF t) :
    IsConj z (E.φ t) :=
  E.shape_2222 t h.cycleType

theorem A8Emb.isConj_a_mul (E : A8Emb a z) {t : alternatingGroup (Fin 8)} (h : FF t) :
    IsConj a (a * E.φ t) :=
  E.fig8b t h.cycleType

theorem A8Emb.orderOf_φ (E : A8Emb a z) (t : alternatingGroup (Fin 8)) :
    orderOf (E.φ t) = orderOf t :=
  orderOf_injective E.φ E.injective t

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
