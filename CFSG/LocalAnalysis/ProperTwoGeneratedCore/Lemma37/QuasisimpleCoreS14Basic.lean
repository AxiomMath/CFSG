module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z : J}

namespace Setting

theorem mul_self_of_mem_center (h : Setting J Q B) {c : J} (hc : c ∈ Subgroup.center J) :
    c * c = 1 := by
  rcases h.mem_center_iff.mp hc with rfl | rfl
  · exact mul_one 1
  · exact h.centralElt_mul_self

omit [Finite J] in
theorem conj_eq_of_mem_center {c : J} (hc : c ∈ Subgroup.center J) (k : J) : k * c * k⁻¹ = c := by
  rw [Subgroup.mem_center_iff.mp hc k, mul_inv_cancel_right]

theorem mul_central_left (h : Setting J Q B) (a b : J) :
    a * (centralElt J * b) = centralElt J * (a * b) := by
  calc a * (centralElt J * b) = (a * centralElt J) * b := by group
    _ = (centralElt J * a) * b := by rw [(h.commute_centralElt a).eq]
    _ = centralElt J * (a * b) := by group

theorem central_mul_central (h : Setting J Q B) (a b : J) :
    (centralElt J * a) * (centralElt J * b) = a * b := by
  calc (centralElt J * a) * (centralElt J * b) = centralElt J * (a * centralElt J) * b := by
        group
    _ = centralElt J * (centralElt J * a) * b := by rw [(h.commute_centralElt a).eq]
    _ = (centralElt J * centralElt J) * (a * b) := by group
    _ = a * b := by rw [h.centralElt_mul_self, one_mul]

theorem conj_mul_self (h : Setting J Q B) {w : J} (hw : w * w = centralElt J) (k : J) :
    (k⁻¹ * w * k) * (k⁻¹ * w * k) = centralElt J := by
  calc (k⁻¹ * w * k) * (k⁻¹ * w * k) = k⁻¹ * (w * w) * k⁻¹⁻¹ := by group
    _ = centralElt J := by rw [hw, conj_eq_of_mem_center h.centralElt_mem_center]

theorem conj_eq_of_comm_mem_center (h : Setting J Q B) {x a : J}
    (hx : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.center J) :
    x * a * x⁻¹ = a ∨ x * a * x⁻¹ = centralElt J * a := by
  have hxa : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
  rcases h.mem_center_iff.mp hx with h1 | he
  · left
    rw [hxa, h1, one_mul]
  · right
    rw [hxa, he]

omit [Finite J] in
theorem inv_comm_mem_center {x a : J} (hx : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.center J) :
    x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ ∈ Subgroup.center J := by
  rw [← commute_mk_iff] at hx ⊢
  rw [QuotientGroup.mk_inv]
  exact hx.inv_left

theorem conj_eq_of_mem_quasiNormalizer (h : Setting J Q B) {w : J} (hw : w * w = centralElt J)
    {x : J} (hx : x ∈ quasiNormalizer w) :
    x * w * x⁻¹ = w ∨ x * w * x⁻¹ = centralElt J * w :=
  h.conj_eq_of_comm_mem_center ((h.mem_normalizer_zpowers_iff hw).mp hx)

theorem mem_quasiNormalizer_of_mul_eq (h : Setting J Q B) {w : J} (hw : w * w = centralElt J)
    {x : J} (hxw : x * w = w * x) : x ∈ quasiNormalizer w := by
  rw [h.mem_normalizer_zpowers_iff hw, hxw, mul_inv_cancel_right, mul_inv_cancel]
  exact (Subgroup.center J).one_mem

theorem mem_quasiNormalizer_conj_iff (h : Setting J Q B) {w : J} (hw : w * w = centralElt J)
    (k x : J) : x ∈ quasiNormalizer (k⁻¹ * w * k) ↔ k * x * k⁻¹ ∈ quasiNormalizer w := by
  rw [h.mem_normalizer_zpowers_iff (h.conj_mul_self hw k), h.mem_normalizer_zpowers_iff hw]
  have heq : k * x * k⁻¹ * w * (k * x * k⁻¹)⁻¹ * w⁻¹ =
      k * (x * (k⁻¹ * w * k) * x⁻¹ * (k⁻¹ * w * k)⁻¹) * k⁻¹ := by group
  rw [heq]
  constructor
  · intro hc
    rwa [conj_eq_of_mem_center hc]
  · intro hc
    have := conj_eq_of_mem_center hc k⁻¹
    rw [show k⁻¹ * (k * (x * (k⁻¹ * w * k) * x⁻¹ * (k⁻¹ * w * k)⁻¹) * k⁻¹) * k⁻¹⁻¹ =
      x * (k⁻¹ * w * k) * x⁻¹ * (k⁻¹ * w * k)⁻¹ by group] at this
    rw [this]
    exact hc

theorem mul_comm_of_odd (h : Setting J Q B) {n a : J} (hn : Odd (orderOf n))
    (hc : n * a * n⁻¹ * a⁻¹ ∈ Subgroup.center J) : n * a = a * n := by
  set c := n * a * n⁻¹ * a⁻¹ with hcdef
  have hcc : c * c = 1 := h.mul_self_of_mem_center hc
  have hna : n * a * n⁻¹ = c * a := by rw [hcdef]; group
  have hnc : n * c = c * n := Subgroup.mem_center_iff.mp hc n
  have h1 : (n * n) * a * (n * n)⁻¹ = a := by
    calc (n * n) * a * (n * n)⁻¹ = n * (n * a * n⁻¹) * n⁻¹ := by group
      _ = (n * c) * a * n⁻¹ := by rw [hna]; group
      _ = c * (n * a * n⁻¹) := by rw [hnc]; group
      _ = a := by rw [hna, ← mul_assoc, hcc, one_mul]
  have hn2 : Commute (n * n) a := by
    change (n * n) * a = a * (n * n)
    calc (n * n) * a = (n * n) * a * (n * n)⁻¹ * (n * n) := by group
      _ = a * (n * n) := by rw [h1]
  obtain ⟨m, hm⟩ := hn
  have hnpow : (n * n) ^ (m + 1) = n := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf n + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have := (hn2.pow_left (m + 1)).eq
  rwa [hnpow] at this

end Setting

namespace FourGen

theorem conj_mem_fourGroup_of_comm (hz : FourGen Q z) (h : Setting J Q B) {q : J}
    (hq : q * z * q⁻¹ * z⁻¹ ∈ Subgroup.center J) {x : J} (hx : x ∈ fourGroup z) :
    q * x * q⁻¹ ∈ fourGroup z := by
  have he := centralElt_mem_fourGroup (J := J) z
  have hzV := mem_fourGroup z
  have hqe : q * centralElt J * q⁻¹ = centralElt J :=
    Setting.conj_eq_of_mem_center h.centralElt_mem_center q
  rcases (hz.mem_fourGroup_iff h).mp hx with hx | hx | hx | hx <;> rw [hx]
  · rw [mul_one, mul_inv_cancel]
    exact (fourGroup z).one_mem
  · rw [hqe]
    exact he
  · rcases h.conj_eq_of_comm_mem_center hq with h1 | h1 <;> rw [h1]
    · exact hzV
    · exact (fourGroup z).mul_mem he hzV
  · have hconj : q * (centralElt J * z) * q⁻¹ = centralElt J * (q * z * q⁻¹) := by
      rw [← mul_assoc q, (h.commute_centralElt q).eq, mul_assoc, mul_assoc, mul_assoc]
    rw [hconj]
    rcases h.conj_eq_of_comm_mem_center hq with h1 | h1 <;> rw [h1]
    · exact (fourGroup z).mul_mem he hzV
    · rw [← mul_assoc, h.centralElt_mul_self, one_mul]
      exact hzV

theorem mem_normalizer_fourGroup (hz : FourGen Q z) (h : Setting J Q B) {q : J}
    (hq : q * z * q⁻¹ * z⁻¹ ∈ Subgroup.center J) :
    q ∈ Subgroup.normalizer (fourGroup z : Set J) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hz.conj_mem_fourGroup_of_comm h hq, fun hx => ?_⟩
  have := hz.conj_mem_fourGroup_of_comm h (Setting.inv_comm_mem_center hq) hx
  simpa [mul_assoc] using this

theorem conj_eq_of_mem_normalizer (hz : FourGen Q z) (h : Setting J Q B) {n : J}
    (hn : n ∈ Subgroup.normalizer (fourGroup z : Set J)) :
    n * z * n⁻¹ = z ∨ n * z * n⁻¹ = centralElt J * z := by
  have hmem : n * z * n⁻¹ ∈ fourGroup z :=
    (Subgroup.mem_normalizer_iff.mp hn z).mp (mem_fourGroup z)
  rcases (hz.mem_fourGroup_iff h).mp hmem with h1 | he | hz' | hez
  · exfalso
    rw [conj_eq_one_iff] at h1
    have := hz.order
    rw [h1, orderOf_one] at this
    exact absurd this (by decide)
  · exfalso
    apply hz.ne_centralElt h
    calc z = n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ := by group
      _ = centralElt J := by rw [he, Setting.conj_eq_of_mem_center h.centralElt_mem_center]
  · exact Or.inl hz'
  · exact Or.inr hez

theorem mul_comm_of_mem_fourGroup (hz : FourGen Q z) (h : Setting J Q B) {y : J}
    (hy : y ∈ fourGroup z) : y * z = z * y := by
  rcases (hz.mem_fourGroup_iff h).mp hy with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact (h.commute_centralElt z).eq.symm
  · rfl
  · rw [mul_assoc, ← mul_assoc z, (h.commute_centralElt z).eq, mul_assoc]

theorem eq_of_mem_fourGroup_of_ne_one (hz : FourGen Q z) (h : Setting J Q B) {y : J}
    (hy : y ∈ fourGroup z) (hy1 : y ≠ 1) :
    y = centralElt J ∨ y = z ∨ y = centralElt J * z := by
  rcases (hz.mem_fourGroup_iff h).mp hy with h1 | h1 | h1 | h1
  · exact absurd h1 hy1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem three_le_pRank (hz : FourGen Q z) (h : Setting J Q B) {M : Subgroup J}
    (heM : centralElt J ∈ M) (hzM : z ∈ M) {x : J} (hxM : x ∈ M) (hx : x * x = 1)
    (hxz : x * z = z * x) (hxV : x ∉ fourGroup z) : 3 ≤ CFSG.Open.pRank 2 M := by
  have hx1 : x ≠ 1 := fun h1 => hxV (h1 ▸ (fourGroup z).one_mem)
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  refine three_le_pRank_of_commuting_involutions heM hzM hxM h.orderOf_centralElt hz.order hx2
    (h.commute_centralElt z).symm (h.commute_centralElt x).symm
    (show Commute x z from hxz).symm (hz.ne_centralElt h).symm
    (fun h' => hxV (h' ▸ centralElt_mem_fourGroup z)) (fun h' => hxV (h' ▸ mem_fourGroup z))
    (fun h' => hxV (h' ▸ (fourGroup z).mul_mem (centralElt_mem_fourGroup z) (mem_fourGroup z)))

end FourGen

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
