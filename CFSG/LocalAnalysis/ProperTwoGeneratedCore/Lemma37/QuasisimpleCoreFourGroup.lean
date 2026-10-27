module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreFour

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z : J}

noncomputable def fourGroup (z : J) : Subgroup J :=
  Subgroup.closure {centralElt J, z}

omit [Finite J] in
theorem centralElt_mem_fourGroup (z : J) : centralElt J ∈ fourGroup z :=
  Subgroup.subset_closure (Set.mem_insert _ _)

omit [Finite J] in
theorem mem_fourGroup (z : J) : z ∈ fourGroup z :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

omit [Finite J] in
theorem fourGroup_le {K : Subgroup J} (he : centralElt J ∈ K) (hz : z ∈ K) : fourGroup z ≤ K := by
  rw [fourGroup, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact he
  · exact hz

namespace FourGen

omit [Finite J] in
theorem mul_self (hz : FourGen Q z) : z * z = 1 := by
  rw [← pow_two, ← hz.order, pow_orderOf_eq_one]

theorem ne_centralElt (hz : FourGen Q z) (h : Setting J Q B) : z ≠ centralElt J :=
  (h.not_mem_center_iff hz.order).mp hz.not_mem_center

theorem conj_eq (hz : FourGen Q z) (h : Setting J Q B) {q : J} (hq : q ∈ (Q : Subgroup J)) :
    q * z * q⁻¹ = z ∨ q * z * q⁻¹ = centralElt J * z := by
  have hqz : q * z * q⁻¹ = (q * z * q⁻¹ * z⁻¹) * z := by group
  rcases h.mem_center_iff.mp (hz.comm_mem_center q hq) with h1 | he
  · left
    rw [hqz, h1, one_mul]
  · right
    rw [hqz, he]

theorem fourGroup_eq (hz : FourGen Q z) (h : Setting J Q B) :
    fourGroup z = CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions (centralElt J) z
      h.centralElt_mul_self hz.mul_self (h.commute_centralElt z).symm := by
  refine le_antisymm (fourGroup_le ?_ ?_) fun y hy => ?_
  · change centralElt J ∈ ({centralElt J * z, centralElt J, z, 1} : Set J)
    simp
  · change z ∈ ({centralElt J * z, centralElt J, z, 1} : Set J)
    simp
  · change y ∈ ({centralElt J * z, centralElt J, z, 1} : Set J) at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy <;> rw [hy]
    · exact (fourGroup z).mul_mem (centralElt_mem_fourGroup z) (mem_fourGroup z)
    · exact centralElt_mem_fourGroup z
    · exact mem_fourGroup z
    · exact (fourGroup z).one_mem

theorem mem_fourGroup_iff (hz : FourGen Q z) (h : Setting J Q B) {x : J} :
    x ∈ fourGroup z ↔ x = 1 ∨ x = centralElt J ∨ x = z ∨ x = centralElt J * z := by
  rw [hz.fourGroup_eq h]
  change x ∈ ({centralElt J * z, centralElt J, z, 1} : Set J) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem fourGroup_le_sylow (hz : FourGen Q z) (h : Setting J Q B) :
    fourGroup z ≤ (Q : Subgroup J) :=
  fourGroup_le h.centralElt_mem_sylow hz.mem

theorem fourGroup_le_core (hz : FourGen Q z) (h : Setting J Q B) : fourGroup z ≤ B :=
  (hz.fourGroup_le_sylow h).trans h.sylow_le

theorem conj_mem_fourGroup (hz : FourGen Q z) (h : Setting J Q B) {q : J}
    (hq : q ∈ (Q : Subgroup J)) {x : J} (hx : x ∈ fourGroup z) : q * x * q⁻¹ ∈ fourGroup z := by
  have he := centralElt_mem_fourGroup (J := J) z
  have hzV := mem_fourGroup z
  have hqe : q * centralElt J * q⁻¹ = centralElt J := by
    rw [(h.commute_centralElt q).eq, mul_inv_cancel_right]
  rcases (hz.mem_fourGroup_iff h).mp hx with hx | hx | hx | hx <;> rw [hx]
  · rw [mul_one, mul_inv_cancel]
    exact (fourGroup z).one_mem
  · rw [hqe]
    exact he
  · rcases hz.conj_eq h hq with h1 | h1 <;> rw [h1]
    · exact hzV
    · exact (fourGroup z).mul_mem he hzV
  · have hconj : q * (centralElt J * z) * q⁻¹ = centralElt J * (q * z * q⁻¹) := by
      rw [← mul_assoc q, (h.commute_centralElt q).eq, mul_assoc, mul_assoc, mul_assoc]
    rw [hconj]
    rcases hz.conj_eq h hq with h1 | h1 <;> rw [h1]
    · exact (fourGroup z).mul_mem he hzV
    · rw [← mul_assoc, h.centralElt_mul_self, one_mul]
      exact hzV

theorem le_normalizer_fourGroup (hz : FourGen Q z) (h : Setting J Q B) :
    (Q : Subgroup J) ≤ Subgroup.normalizer (fourGroup z : Set J) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hz.conj_mem_fourGroup h hq, fun hx => ?_⟩
  have := hz.conj_mem_fourGroup h ((Q : Subgroup J).inv_mem hq) hx
  simpa [mul_assoc] using this

theorem two_le_pRank_fourGroup (hz : FourGen Q z) (h : Setting J Q B) :
    2 ≤ CFSG.Open.pRank 2 (fourGroup z) :=
  two_le_pRank_of_commuting_involutions (centralElt_mem_fourGroup z) (mem_fourGroup z)
    h.orderOf_centralElt hz.order (hz.ne_centralElt h).symm (h.commute_centralElt z).symm

theorem normalizer_fourGroup_le (hz : FourGen Q z) (h : Setting J Q B) :
    Subgroup.normalizer (fourGroup z : Set J) ≤ B :=
  h.normalizer_le (hz.fourGroup_le_core h) (hz.two_le_pRank_fourGroup h)

omit [Finite J] in
theorem comm_mem_center' (hz : FourGen Q z) {w : J} (hwQ : w ∈ (Q : Subgroup J)) :
    z * w * z⁻¹ * w⁻¹ ∈ Subgroup.center J := by
  have := (Subgroup.center J).inv_mem (hz.comm_mem_center w hwQ)
  simpa [mul_assoc] using this

end FourGen

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
