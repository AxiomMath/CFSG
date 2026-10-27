module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePOuter
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

theorem mem_zpowers_of_mul_self (hc : PartC T Q P₁ e u) {w x : G} (hw : w * w = e)
    (hx : x ∈ Subgroup.zpowers w) : x = 1 ∨ x = w ∨ x = e ∨ x = w * e := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h4 : orderOf w = 4 := by
    have h4 : orderOf w = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow ?_ ?_
      · rw [pow_one, pow_two, hw]
        exact hc.centralElt_ne_one
      · rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, hw,
          hc.centralElt_mul_self]
    rw [h4]
    norm_num
  rw [← zpow_mod_orderOf, h4]
  have h0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h1 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
  obtain h | h | h | h : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨
      k % ((4 : ℕ) : ℤ) = 2 ∨ k % ((4 : ℕ) : ℤ) = 3 := by omega
  · left
    rw [h, zpow_zero]
  · right; left
    rw [h, zpow_one]
  · right; right; left
    rw [h, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hw]
  · right; right; right
    rw [h, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ, pow_two, hw]
    exact (hc.commute_centralElt w).symm

theorem eq_of_mem_zpowers_of_mul_self (hc : PartC T Q P₁ e u) {w x : G} (hw : w * w = e)
    (hx : x ∈ Subgroup.zpowers w) (hxx : x * x = e) : x = w ∨ x = w * e := by
  rcases hc.mem_zpowers_of_mul_self hw hx with rfl | rfl | rfl | rfl
  · exact absurd (hxx.symm.trans (mul_one 1)) hc.centralElt_ne_one
  · exact Or.inl rfl
  · exact absurd (hxx.symm.trans hc.centralElt_mul_self) hc.centralElt_ne_one
  · exact Or.inr rfl

theorem conj_eq_of_mem_zpowers (hc : PartC T Q P₁ e u) {w g : G} (hw : w * w = e)
    (hg : g * w * g⁻¹ ∈ Subgroup.zpowers w) : g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w * e := by
  refine hc.eq_of_mem_zpowers_of_mul_self hw hg ?_
  rw [show g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ by group, hw, hc.conj_centralElt]

theorem mem_normalizer_zpowers_of_conj_mem [Finite G] {g v : G}
    (h : g * v * g⁻¹ ∈ Subgroup.zpowers v) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
  have hmem : ∀ x ∈ Subgroup.zpowers v, g * x * g⁻¹ ∈ Subgroup.zpowers v := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h k
  let φ : Subgroup.zpowers v → Subgroup.zpowers v := fun x => ⟨g * x * g⁻¹, hmem x x.2⟩
  have hφ : Function.Injective φ := fun x y hxy => by
    have h1 : g * (x : G) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hφs := Finite.surjective_of_injective hφ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hmem x hx, fun hx => ?_⟩
  obtain ⟨x', hx'⟩ := hφs ⟨g * x * g⁻¹, hx⟩
  have hxx : (x' : G) = x := by
    have h1 : g * (x' : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hx'
    exact mul_left_cancel (mul_right_cancel h1)
  exact hxx ▸ x'.2

theorem mul_centralElt_mem_zpowers {w : G} (hw : w * w = e) : w * e ∈ Subgroup.zpowers w := by
  rw [← hw]
  exact Subgroup.mul_mem _ (Subgroup.mem_zpowers w)
    (Subgroup.mul_mem _ (Subgroup.mem_zpowers w) (Subgroup.mem_zpowers w))

theorem comm_or_anticomm (hc : PartC T Q P₁ e u) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    a * b = b * a ∨ a * b = b * a * e := by
  by_cases ha' : a = 1 ∨ a = e
  · left
    rcases ha' with rfl | rfl
    · group
    · exact (hc.commute_centralElt b).symm
  by_cases hb' : b = 1 ∨ b = e
  · left
    rcases hb' with rfl | rfl
    · group
    · exact hc.commute_centralElt a
  push Not at ha' hb'
  have haa := hc.mul_self_of_ne ha ha'.1 ha'.2
  have hbb := hc.mul_self_of_ne hb hb'.1 hb'.2
  by_cases hba : b = a ∨ b = a * e
  · left
    rcases hba with rfl | rfl
    · rfl
    · rw [mul_assoc a e a, ← hc.commute_centralElt a]
  · push Not at hba
    exact Or.inr (hc.anticomm ha hb haa hbb hba.1 hba.2)

theorem mul_conj_mem (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hyy : y * y ∈ P₁) {v : G}
    (hfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e) {q : G} (hq : q ∈ Q) :
    q * (y * q * y⁻¹) = 1 ∨ q * (y * q * y⁻¹) = e ∨ q * (y * q * y⁻¹) = v ∨
      q * (y * q * y⁻¹) = v * e := by
  have hb := hc.normal_left y hyT q hq
  set b := y * q * y⁻¹ with hbdef
  have hyb : y * b * y⁻¹ = q := by
    have h := hc.commute q hq _ hyy
    calc y * b * y⁻¹ = (y * y) * q * (y * y)⁻¹ := by rw [hbdef]; group
      _ = q * (y * y) * (y * y)⁻¹ := by rw [h]
      _ = q := by group
  have hconj : y * (q * b) * y⁻¹ = b * q := by
    calc y * (q * b) * y⁻¹ = (y * q * y⁻¹) * (y * b * y⁻¹) := by group
      _ = b * q := by rw [← hbdef, hyb]
  refine hfix _ (Q.mul_mem hq hb) ?_
  rw [hconj]
  rcases hc.comm_or_anticomm hq hb with h | h
  · exact Or.inl h.symm
  · right
    rw [h, hc.mul_centralElt_mul_centralElt]

theorem le_normalizer_zpowers_of_inv [Finite G] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) {v : G} (hvQ : v ∈ Q) (hvv : v * v = e) (hyv : y * v * y⁻¹ = v⁻¹) :
    T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
  rw [← hc.sup_zpowers_sup_eq hyT hy]
  refine _root_.sup_le (_root_.sup_le (fun p hp => ?_) ?_) fun q hq => ?_
  · refine mem_normalizer_zpowers_of_conj_mem ?_
    rw [← hc.commute v hvQ p hp, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers v
  · rw [Subgroup.zpowers_le]
    refine mem_normalizer_zpowers_of_conj_mem ?_
    rw [hyv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers v)
  · refine mem_normalizer_zpowers_of_conj_mem ?_
    rcases hc.comm_or_anticomm hq hvQ with h | h
    · rw [h, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers v
    · have h' : q * v * q⁻¹ = v * e := by
        rw [h, mul_assoc v q e, hc.commute_centralElt q]
        group
      rw [h']
      exact mul_centralElt_mem_zpowers hvv

theorem exists_mul_eq_of_mem (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) {t : G}
    (ht : t ∈ T) : ∃ q ∈ Q, ∃ w ∈ P₁ ⊔ Subgroup.zpowers y, q * w = t := by
  have hle : P₁ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (Q : Set G) := fun w hw => by
    have hwT := hc.sup_zpowers_le hyT hw
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hc.normal_left w hwT h hh, fun hh => ?_⟩
    have := hc.normal_left w⁻¹ (T.inv_mem hwT) _ hh
    rwa [show w⁻¹ * (w * h * w⁻¹) * w⁻¹⁻¹ = h by group] at this
  have htT : t⁻¹ ∈ ((P₁ ⊔ Subgroup.zpowers y) ⊔ Q : Subgroup G) := by
    rw [hc.sup_zpowers_sup_eq hyT hy]
    exact T.inv_mem ht
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle,
    Set.mem_mul] at htT
  obtain ⟨w, hw, q, hq, hwq⟩ := htT
  exact ⟨q⁻¹, Q.inv_mem hq, w⁻¹, Subgroup.inv_mem _ hw, by rw [← mul_inv_rev, hwq, inv_inv]⟩

theorem mem_right_of_mem_sup (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) {w : G} (hw : w ∈ P₁ ⊔ Subgroup.zpowers y) (hwQ : w ∈ Q ⊔ P₁) :
    w ∈ P₁ := by
  rcases (hc.mem_sup_zpowers_iff hyT hyy).mp hw with h | h
  · exact h
  · exact absurd (mem_sup_of_mul_inv_mem h hwQ) hy

theorem mul_self_mem_right (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hyy : y * y ∈ P₁) {w : G}
    (hw : w ∈ P₁ ⊔ Subgroup.zpowers y) : w * w ∈ P₁ := by
  rcases (hc.mem_sup_zpowers_iff hyT hyy).mp hw with h | h
  · exact P₁.mul_mem h h
  · rw [show w * w = (w * y⁻¹) * (y * (w * y⁻¹) * y⁻¹) * (y * y) by group]
    exact P₁.mul_mem (P₁.mul_mem h (hc.normal_right y hyT _ h)) hyy

theorem conj_eq_conj_of_not_mem (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hyy : y * y ∈ P₁)
    {w : G} (hw : w ∈ P₁ ⊔ Subgroup.zpowers y) (hw₁ : w ∉ P₁) {q : G} (hq : q ∈ Q) :
    w * q * w⁻¹ = y * q * y⁻¹ := by
  have hp := ((hc.mem_sup_zpowers_iff hyT hyy).mp hw).resolve_left hw₁
  have h := hc.commute _ (hc.normal_left y hyT q hq) _ hp
  calc w * q * w⁻¹ = (w * y⁻¹) * (y * q * y⁻¹) * (w * y⁻¹)⁻¹ := by group
    _ = (y * q * y⁻¹) * (w * y⁻¹) * (w * y⁻¹)⁻¹ := by rw [← h]
    _ = y * q * y⁻¹ := by group

theorem mul_mul_self_eq (q w : G) : q * w * (q * w) = q * (w * q * w⁻¹) * (w * w) := by
  group

theorem conj_eq_mul_centralElt (hc : PartC T Q P₁ e u) {t s : G} (htT : t ∈ T)
    (ht : t ∉ Q ⊔ P₁) (htt : t * t = e) (hsT : s ∈ Q ⊔ P₁) (hss : s * s = e)
    (hts : t * s * t⁻¹ ∈ Subgroup.zpowers s) : t * s * t⁻¹ = s * e := by
  rcases hc.conj_eq_of_mem_zpowers hss hts with h | h
  · exfalso
    have hcomm : t * s = s * t := by
      calc t * s = t * s * t⁻¹ * t := by group
        _ = s * t := by rw [h]
    have hinv : (t * s) * (t * s) = 1 := by
      rw [show t * s * (t * s) = t * t * (s * s) by
        rw [show t * s * (t * s) = t * (s * t) * s by group, ← hcomm]; group, htt, hss,
        hc.centralElt_mul_self]
    have hts1 : t * s ≠ 1 := fun h1 => ht (by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (Q ⊔ P₁).inv_mem hsT)
    have hmem := hc.involution_mem (t * s) (T.mul_mem htT (hc.sup_le hsT))
      (orderOf_eq_prime (by rw [pow_two]; exact hinv) hts1)
    exact ht (by simpa using (Q ⊔ P₁).mul_mem hmem ((Q ⊔ P₁).inv_mem hsT))
  · exact h

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
