module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalPointHullClass
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalGraphFusion

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G]

@[expose] def conjugateQInvolutions (Q : Subgroup G) : Set G :=
  Group.conjugatesOfSet {z : G | z ∈ Q ∧ orderOf z = 2}

theorem mem_conjugateQInvolutions_iff (Q : Subgroup G) (x : G) :
    x ∈ conjugateQInvolutions Q ↔
      ∃ g : G, x ∈ rightConjugate Q g ∧ orderOf x = 2 := by
  constructor
  · intro hx
    obtain ⟨z, ⟨hzQ, hz⟩, hzx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨a, rfl⟩ := isConj_iff.mp hzx
    refine ⟨a⁻¹, ?_, ((MulAut.conj a).orderOf_eq z).trans hz⟩
    exact Subgroup.mem_map.mpr ⟨z, hzQ, by simp only [MulEquiv.coe_toMonoidHom,
      inv_inv, MulAut.conj_apply]⟩
  · rintro ⟨g, hxQ, hx⟩
    obtain ⟨z, hzQ, hzx⟩ := Subgroup.mem_map.mp hxQ
    have hz : orderOf z = 2 := by
      have heq : (MulAut.conj g⁻¹) z = x := hzx
      rw [← heq] at hx
      exact ((MulAut.conj g⁻¹).orderOf_eq z).symm.trans hx
    exact Group.mem_conjugatesOfSet_iff.mpr
      ⟨z, ⟨hzQ, hz⟩, isConj_iff.mpr ⟨g⁻¹, hzx⟩⟩

theorem conjugateQInvolutions_order_two (Q : Subgroup G) :
    ∀ x ∈ conjugateQInvolutions Q, orderOf x = 2 := by
  intro x hx
  exact ((mem_conjugateQInvolutions_iff Q x).mp hx).choose_spec.2

theorem conjugateQInvolutions_conj_mem (Q : Subgroup G) :
    ∀ x ∈ conjugateQInvolutions Q, ∀ g : G,
      (MulAut.conj g) x ∈ conjugateQInvolutions Q := by
  intro x hx g
  exact Group.conj_mem_conjugatesOfSet hx

theorem involution_mem_conjugateQInvolutions (Q : Subgroup G)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    z ∈ conjugateQInvolutions Q := by
  apply (mem_conjugateQInvolutions_iff Q z).mpr
  exact ⟨1, by simpa only [rightConjugate_one] using hzQ, hz⟩

variable [Finite G]

theorem conjugates_eq_of_common_involution (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (a b x : G)
    (hxa : x ∈ rightConjugate Q a) (hxb : x ∈ rightConjugate Q b)
    (hx : orderOf x = 2) :
    rightConjugate Q a = rightConjugate Q b := by
  let z := (MulAut.conj a) x
  have hzQ : z ∈ Q := (mem_rightConjugate_iff Q a x).mp hxa
  have hz : orderOf z = 2 := ((MulAut.conj a).orderOf_eq x).trans hx
  have hconjQ : (a * b⁻¹)⁻¹ * z * (a * b⁻¹) ∈ Q := by
    have heq : (a * b⁻¹)⁻¹ * z * (a * b⁻¹) = b * x * b⁻¹ := by
      dsimp only [z, MulAut.conj_apply]
      group
    rw [heq]
    exact (mem_rightConjugate_iff Q b x).mp hxb
  have hab : a * b⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (involution_conjugate_mem_Q_iff Q hodd z hzQ hz (a * b⁻¹)).mp hconjQ
  have heq := (rightConjugate_eq_self_iff Q (a * b⁻¹)).mpr hab
  have hmap := congrArg (fun R : Subgroup G => rightConjugate R b) heq
  simpa only [rightConjugate_mul, inv_mul_cancel_right] using hmap

theorem conjugates_eq_of_commuting_involutions (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (a b x y : G)
    (hxa : x ∈ rightConjugate Q a) (hyb : y ∈ rightConjugate Q b)
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hcomm : Commute x y) :
    rightConjugate Q a = rightConjugate Q b := by
  let z := (MulAut.conj a) x
  let t := (MulAut.conj a) y
  have hzQ : z ∈ Q := (mem_rightConjugate_iff Q a x).mp hxa
  have hz : orderOf z = 2 := ((MulAut.conj a).orderOf_eq x).trans hx
  have ht : orderOf t = 2 := ((MulAut.conj a).orderOf_eq y).trans hy
  have htH : t ∈ Subgroup.normalizer (Q : Set G) :=
    involution_centralizer_le_normalizer Q hodd z hzQ hz
      (Subgroup.mem_centralizer_singleton_iff.mpr
        ((hcomm.map (MulAut.conj a).toMonoidHom).symm))
  have htQconj : t ∈ rightConjugate Q (b * a⁻¹) := by
    apply (mem_rightConjugate_iff Q (b * a⁻¹) t).mpr
    have heq : (b * a⁻¹) * t * (b * a⁻¹)⁻¹ = b * y * b⁻¹ := by
      dsimp only [t, MulAut.conj_apply]
      group
    rw [heq]
    exact (mem_rightConjugate_iff Q b y).mp hyb
  have hba : b * a⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
    by_contra houtside
    exact (hodd (b * a⁻¹) houtside).not_two_dvd_nat
      (ht ▸ Subgroup.orderOf_dvd_natCard
        (rightConjugate Q (b * a⁻¹) ⊓ Subgroup.normalizer (Q : Set G))
        ⟨htQconj, htH⟩)
  have heq := (rightConjugate_eq_self_iff Q (b * a⁻¹)).mpr hba
  have hmap := congrArg (fun R : Subgroup G => rightConjugate R a) heq
  have hmap' : rightConjugate Q b = rightConjugate Q a := by
    simpa only [rightConjugate_mul, inv_mul_cancel_right] using hmap
  exact hmap'.symm

theorem conjugateQInvolutions_mul_mem (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) :
    ∀ x ∈ conjugateQInvolutions Q, ∀ y ∈ conjugateQInvolutions Q,
      x ≠ y → Commute x y → x * y ∈ conjugateQInvolutions Q := by
  intro x hxD y hyD hne hcomm
  obtain ⟨a, hxa, hx⟩ := (mem_conjugateQInvolutions_iff Q x).mp hxD
  obtain ⟨b, hyb, hy⟩ := (mem_conjugateQInvolutions_iff Q y).mp hyD
  have heq := conjugates_eq_of_commuting_involutions Q hodd a b x y hxa hyb hx hy hcomm
  have hya : y ∈ rightConjugate Q a := heq.symm ▸ hyb
  have hprodne : x * y ≠ 1 := by
    intro hprod
    exact hne ((mul_eq_one_iff_eq_inv.mp hprod).trans (inv_eq_self_of_orderOf_eq_two hy))
  have hprodorder : orderOf (x * y) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, hprodne⟩
    rw [hcomm.mul_pow]
    rw [show x ^ 2 = 1 from by simpa only [hx] using pow_orderOf_eq_one x,
      show y ^ 2 = 1 from by simpa only [hy] using pow_orderOf_eq_one y, one_mul]
  exact (mem_conjugateQInvolutions_iff Q (x * y)).mpr
    ⟨a, (rightConjugate Q a).mul_mem hxa hya, hprodorder⟩

theorem conjugateQInvolutions_reachable_stays_in_conjugate (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (a : G) (x y : conjugateQInvolutions Q)
    (hxa : (x : G) ∈ rightConjugate Q a)
    (hreach : (NormalGraph.graph (conjugateQInvolutions Q)
      (conjugateQInvolutions_order_two Q)).Reachable x y) :
    (y : G) ∈ rightConjugate Q a := by
  apply hreach.elim
  intro walk
  clear hreach
  induction walk with
  | @nil v => exact hxa
  | @cons x v y hadj tail ih =>
    apply ih
    obtain ⟨b, hvb, hv⟩ := (mem_conjugateQInvolutions_iff Q v).mp v.property
    have heq := conjugates_eq_of_commuting_involutions Q hodd a b x v hxa hvb
      (conjugateQInvolutions_order_two Q x x.property) hv hadj.2
    exact heq.symm ▸ hvb

theorem conjugateQInvolutions_graph_disconnected (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    ¬ (NormalGraph.graph (conjugateQInvolutions Q)
      (conjugateQInvolutions_order_two Q)).Preconnected := by
  intro hconnected
  apply hnormal
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  have hzD := involution_mem_conjugateQInvolutions Q z hzQ hz
  have hzgD := conjugateQInvolutions_conj_mem Q z hzD g⁻¹
  have hzConj : z ∈ rightConjugate Q 1 := by simpa only [rightConjugate_one] using hzQ
  have hzgQ := conjugateQInvolutions_reachable_stays_in_conjugate Q hodd 1
    ⟨z, hzD⟩ ⟨(MulAut.conj g⁻¹) z, hzgD⟩ hzConj (hconnected _ _)
  rw [rightConjugate_one] at hzgQ
  exact (involution_conjugate_mem_Q_iff Q hodd z hzQ hz g).mp
    (by simpa only [MulAut.conj_apply, inv_inv] using hzgQ)

theorem conjugateQInvolutions_eq_pointClass (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    conjugateQInvolutions Q = involutionPointClass z := by
  rw [localPointHullClass_eq_conjugatesOf]
  exact NormalGraph.eq_conjugacy_class (conjugateQInvolutions Q)
    (conjugateQInvolutions_order_two Q) (conjugateQInvolutions_conj_mem Q)
    (conjugateQInvolutions_mul_mem Q hodd)
    (conjugateQInvolutions_graph_disconnected Q hodd hnormal z hzQ hz)
    ⟨z, involution_mem_conjugateQInvolutions Q z hzQ hz⟩

end CFSG.ComponentClassification.AschbacherTightEmbedding
