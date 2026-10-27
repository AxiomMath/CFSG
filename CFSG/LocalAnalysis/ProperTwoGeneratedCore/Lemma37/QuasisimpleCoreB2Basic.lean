module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePB1
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Inv

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace PartC

variable {G : Type} [Group G] {T Q P : Subgroup G} {e u : G}

theorem mul_self_of_caseB2 (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) {t : G} (ht : t ∈ T) : t * t = 1 ∨ t * t = e := by
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp (hT ht)
  rw [hc.mul_mul_self_of_mem hq hp]
  rcases quaternion_mul_self hc.quaternion.some hc.mem_left hc.order hq with h1 | h1 <;>
    rcases quaternion_mul_self φ hc.mem_right hc.order hp with h2 | h2 <;> rw [h1, h2]
  · exact Or.inl (mul_one 1)
  · exact Or.inr (one_mul e)
  · exact Or.inr (mul_one e)
  · exact Or.inl hc.centralElt_mul_self

theorem mem_or_mem_of_caseB2 (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) {t : G} (ht : t ∈ T) (htt : t * t = e) : t ∈ Q ∨ t ∈ P := by
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp (hT ht)
  rw [hc.mul_mul_self_of_mem hq hp] at htt
  rcases quaternion_mul_self hc.quaternion.some hc.mem_left hc.order hq with h1 | h1
  · right
    rcases quaternion_eq_of_mul_self hc.quaternion.some hc.mem_left hc.order hq h1 with rfl | rfl
    · rw [one_mul]
      exact hp
    · exact P.mul_mem hc.mem_right hp
  · left
    rw [h1] at htt
    have hpp : p * p = 1 := by
      calc p * p = e⁻¹ * (e * (p * p)) := by group
        _ = 1 := by rw [htt, inv_mul_cancel]
    rcases quaternion_eq_of_mul_self φ hc.mem_right hc.order hp hpp with rfl | rfl
    · rw [mul_one]
      exact hq
    · exact Q.mul_mem hq hc.mem_left

theorem mem_and_mem_of_caseB2 (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) {a b : G} (ha : a ∈ T) (hb : b ∈ T) (haa : a * a = e)
    (hbb : b * b = e) (hab : a * b ≠ b * a) : (a ∈ Q ∧ b ∈ Q) ∨ (a ∈ P ∧ b ∈ P) := by
  rcases hc.mem_or_mem_of_caseB2 hT φ ha haa with haQ | haP <;>
    rcases hc.mem_or_mem_of_caseB2 hT φ hb hbb with hbQ | hbP
  · exact Or.inl ⟨haQ, hbQ⟩
  · exact absurd (hc.commute a haQ b hbP) hab
  · exact absurd (hc.commute b hbQ a haP).symm hab
  · exact Or.inr ⟨haP, hbP⟩

theorem conj_mul_eq_mul_conj (x c d : G) : x * (c * d) * x⁻¹ = x * c * x⁻¹ * (x * d * x⁻¹) := by
  group

theorem conj_cases_of_caseB2 (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) {R : Subgroup G} (ψ : R ≃* QuaternionGroup 2) (heR : e ∈ R)
    (hRT : R ≤ T) {x : G} (hx : ∀ t ∈ T, x * t * x⁻¹ ∈ T) :
    (∀ r ∈ R, x * r * x⁻¹ ∈ Q) ∨ (∀ r ∈ R, x * r * x⁻¹ ∈ P) := by
  obtain ⟨a, ha, b, hb, haa, hbb, hba, hbae⟩ := quaternion_exists_pair ψ heR hc.order
  have hab := quaternion_anticomm ψ heR hc.order ha hb haa hbb hba hbae
  have hxe : x * e * x⁻¹ = e := hc.conj_centralElt x
  have ha' : x * a * x⁻¹ * (x * a * x⁻¹) = e := by rw [← conj_mul_eq_mul_conj, haa, hxe]
  have hb' : x * b * x⁻¹ * (x * b * x⁻¹) = e := by rw [← conj_mul_eq_mul_conj, hbb, hxe]
  have hab' : x * a * x⁻¹ * (x * b * x⁻¹) ≠ x * b * x⁻¹ * (x * a * x⁻¹) := by
    intro h
    rw [← conj_mul_eq_mul_conj, ← conj_mul_eq_mul_conj] at h
    have h' : a * b = b * a := mul_left_cancel (mul_right_cancel h)
    rw [hab] at h'
    exact hc.centralElt_ne_one (mul_left_cancel (h'.trans (mul_one _).symm))
  have hmem : ∀ K : Subgroup G, e ∈ K → x * a * x⁻¹ ∈ K → x * b * x⁻¹ ∈ K →
      ∀ r ∈ R, x * r * x⁻¹ ∈ K := by
    intro K heK haK hbK r hr
    rcases quaternion_enum ψ heR hc.order ha hb hr haa hbb hba hbae with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact K.one_mem
    · rw [hxe]
      exact heK
    · exact haK
    · rw [conj_mul_eq_mul_conj, hxe]
      exact K.mul_mem haK heK
    · exact hbK
    · rw [conj_mul_eq_mul_conj, hxe]
      exact K.mul_mem hbK heK
    · rw [conj_mul_eq_mul_conj]
      exact K.mul_mem haK hbK
    · rw [conj_mul_eq_mul_conj, conj_mul_eq_mul_conj, hxe]
      exact K.mul_mem (K.mul_mem haK hbK) heK
  rcases hc.mem_and_mem_of_caseB2 hT φ (hx a (hRT ha)) (hx b (hRT hb)) ha' hb' hab' with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (hmem Q hc.mem_left h1 h2)
  · exact Or.inr (hmem P hc.mem_right h1 h2)

theorem eq_or_eq_mul_of_commute_of_quaternion {K : Subgroup G} (ψ : K ≃* QuaternionGroup 2)
    (heK : e ∈ K)
    (he2 : orderOf e = 2) {a b : G} (ha : a ∈ K) (hb : b ∈ K) (haa : a * a = e)
    (hbb : b * b = e) (hab : a * b = b * a) : b = a ∨ b = a * e := by
  by_contra hne
  push Not at hne
  have h := quaternion_anticomm ψ heK he2 ha hb haa hbb hne.1 hne.2
  rw [hab] at h
  have he1 : e ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at he2
    exact absurd he2 (by decide)
  exact he1 (mul_left_cancel (h.symm.trans (mul_one _).symm))

theorem mul_self_eq_one_of_mem_left_right (hc : PartC T Q P e u) {p : G} (hpQ : p ∈ Q)
    (hpP : p ∈ P) :
    p * p = 1 := by
  rcases hc.mem_inf p hpQ hpP with rfl | rfl
  · exact mul_one 1
  · exact hc.centralElt_mul_self

theorem not_conj_left_left (hc : PartC T Q P e u) (φ : P ≃* QuaternionGroup 2) {x : G}
    (hQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hP : ∀ p ∈ P, x * p * x⁻¹ ∈ Q) : False := by
  obtain ⟨q, hq, -, -, hqq, -, -, -⟩ := quaternion_exists_pair hc.quaternion.some hc.mem_left
    hc.order
  obtain ⟨p, hp, -, -, hpp, -, -, -⟩ := quaternion_exists_pair φ hc.mem_right hc.order
  have hxe : x * e * x⁻¹ = e := hc.conj_centralElt x
  have h := eq_or_eq_mul_of_commute_of_quaternion hc.quaternion.some hc.mem_left hc.order
    (hQ q hq) (hP p hp)
    (by rw [← conj_mul_eq_mul_conj, hqq, hxe]) (by rw [← conj_mul_eq_mul_conj, hpp, hxe])
    (by rw [← conj_mul_eq_mul_conj, ← conj_mul_eq_mul_conj, hc.commute q hq p hp])
  have hpQ : p ∈ Q := by
    rcases h with h | h
    · rw [mul_left_cancel (mul_right_cancel h)]
      exact hq
    · rw [← hxe, ← conj_mul_eq_mul_conj] at h
      rw [mul_left_cancel (mul_right_cancel h)]
      exact Q.mul_mem hq hc.mem_left
  have h1 := hc.mul_self_eq_one_of_mem_left_right hpQ hp
  rw [hpp] at h1
  exact hc.centralElt_ne_one h1

theorem conj_right_or_swap (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) {x : G} (hx : ∀ t ∈ T, x * t * x⁻¹ ∈ T) :
    (∀ p ∈ P, x * p * x⁻¹ ∈ P) ∨
      ((∀ p ∈ P, x * p * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, x * q * x⁻¹ ∈ P)) := by
  rcases hc.conj_cases_of_caseB2 hT φ φ hc.mem_right hc.right_le hx with hP | hP
  · rcases hc.conj_cases_of_caseB2 hT φ hc.quaternion.some hc.mem_left hc.left_le hx with
      hQ | hQ
    · exact (hc.not_conj_left_left φ hQ hP).elim
    · exact Or.inr ⟨hP, hQ⟩
  · exact Or.inl hP

variable (Z : Subgroup G) [Z.Normal]

theorem mul_self_map_of_caseB2 (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {w : G ⧸ Z}
    (hw : w ∈ T.map (QuotientGroup.mk' Z)) : w * w = 1 := by
  obtain ⟨t, ht, rfl⟩ := hw
  rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ]
  exact hc.mul_self_of_caseB2 hT φ ht

theorem comm_map_of_caseB2 (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {a b : G ⧸ Z}
    (ha : a ∈ T.map (QuotientGroup.mk' Z)) (hb : b ∈ T.map (QuotientGroup.mk' Z)) :
    a * b = b * a := by
  have haa := hc.mul_self_map_of_caseB2 Z hT φ hZ ha
  have hbb := hc.mul_self_map_of_caseB2 Z hT φ hZ hb
  have hab := hc.mul_self_map_of_caseB2 Z hT φ hZ (Subgroup.mul_mem _ ha hb)
  calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb]

theorem card_map_of_caseB2 (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) :
    Nat.card (T.map (QuotientGroup.mk' Z)) = 16 := by
  obtain ⟨ψ⟩ := hc.nonempty_map_mulEquiv_dihedral φ (le_antisymm hT hc.sup_le) Z hZ
  rw [Nat.card_congr ψ.toEquiv, Nat.card_prod, DihedralGroup.nat_card]

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
