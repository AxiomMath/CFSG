module

public import CFSG.CGT.PushingUpLit.SubnormalTwoGroup
public import CFSG.RankThree.PartTwo.Sec5.Bender.Core
public import CFSG.CGT.PushingUp.ResidualTwo

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement Pointwise

namespace SixThree

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_sup_of_normal {Y L C : Subgroup G} [C.Normal] (hYL : Y ≤ L)
    (h : (Y.subgroupOf L).IsSubnormal) : ((Y ⊔ C).subgroupOf (L ⊔ C)).IsSubnormal := by
  have key : ∀ H : Subgroup ↥L, H.IsSubnormal →
      ((H.map L.subtype ⊔ C).subgroupOf (L ⊔ C)).IsSubnormal := by
    intro H hH
    induction hH with
    | top =>
      have : (⊤ : Subgroup ↥L).map L.subtype = L := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      rw [this, Subgroup.subgroupOf_self]
      exact Subgroup.IsSubnormal.top
    | step H K hHK hK hN ih =>
      have hM : K.map L.subtype ⊔ C ≤ L ⊔ C :=
        sup_le_sup_right (Subgroup.map_subtype_le K) C
      have hAB : H.map L.subtype ⊔ C ≤ K.map L.subtype ⊔ C :=
        sup_le_sup_right (Subgroup.map_mono hHK) C
      have hN' : K ≤ Subgroup.normalizer (H : Set ↥L) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN
      have hKH : K.map L.subtype ≤
          Subgroup.normalizer ((H.map L.subtype : Subgroup G) : Set G) :=
        (Subgroup.map_mono hN').trans (Subgroup.le_normalizer_map _)
      have hBN : K.map L.subtype ⊔ C ≤
          Subgroup.normalizer ((H.map L.subtype ⊔ C : Subgroup G) : Set G) := by
        refine sup_le ?_ ?_
        · refine le_trans (le_inf hKH ?_) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
          rw [Subgroup.normalizer_eq_top C]
          exact le_top
        · exact le_sup_right.trans Subgroup.le_normalizer
      have hle : (H.map L.subtype ⊔ C).subgroupOf (L ⊔ C) ≤
          (K.map L.subtype ⊔ C).subgroupOf (L ⊔ C) := Subgroup.comap_mono hAB
      refine Subgroup.IsSubnormal.step ((H.map L.subtype ⊔ C).subgroupOf (L ⊔ C))
        ((K.map L.subtype ⊔ C).subgroupOf (L ⊔ C)) hle ih ?_
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle,
        ← Subgroup.subgroupOf_normalizer_eq (hAB.trans hM)]
      exact Subgroup.comap_mono hBN
  have := key _ h
  rwa [Subgroup.map_subgroupOf_eq_of_le hYL] at this

theorem isSubnormal_subgroupOf_of_le_normalizer {Y L : Subgroup G} (hYL : Y ≤ L)
    (hn : L ≤ Subgroup.normalizer (Y : Set G)) : (Y.subgroupOf L).IsSubnormal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hYL).mpr hn).isSubnormal

theorem isSubnormal_of_subgroupOf_top {Y : Subgroup G} (h : (Y.subgroupOf ⊤).IsSubnormal) :
    Y.IsSubnormal :=
  Subgroup.IsSubnormal.trans le_top h Subgroup.IsSubnormal.top

theorem exists_pow_two_pow_odd_orderOf [Finite G] (y : G) : ∃ k : ℕ, Odd (orderOf (y ^ 2 ^ k)) := by
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_⟩
  have hd : 2 ^ k ∣ orderOf y := hk ▸ dvd_mul_right _ _
  rw [orderOf_pow_of_dvd (by positivity) hd]
  have : orderOf y / 2 ^ k = m := by
    rw [hk]
    exact Nat.mul_div_cancel_left m (by positivity)
  rw [this]
  exact hm

theorem eq_of_odd_orderOf_mem [Finite G] {Y K : Subgroup G} (hY : SubTwo.NoTwoQuotient Y)
    (hKY : K ≤ Y) (hn : Y ≤ Subgroup.normalizer (K : Set G))
    (h : ∀ y ∈ Y, Odd (orderOf y) → y ∈ K) : K = Y := by
  refine hY K hKY hn fun y hy => ?_
  obtain ⟨k, hk⟩ := exists_pow_two_pow_odd_orderOf y
  exact ⟨k, h _ (Y.pow_mem hy _) hk⟩

theorem coprime_card_zpowers_of_odd [Finite G] {a : G} {P : Subgroup G} (ha : Odd (orderOf a))
    (hP : IsPGroup 2 P) : Nat.Coprime (Nat.card (Subgroup.zpowers a)) (Nat.card P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [Nat.card_zpowers, hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr ha)

theorem commutator_le_commutator_commutator_of_odd [Finite G] {P : Subgroup G} {a : G}
    (hP : IsPGroup 2 P) (ha : Odd (orderOf a)) (hn : a ∈ Subgroup.normalizer (P : Set G)) :
    ⁅P, Subgroup.zpowers a⁆ ≤ ⁅⁅P, Subgroup.zpowers a⁆, Subgroup.zpowers a⁆ :=
  CFSG.RankThree.PartTwo.Sec5.Bender.commutator_le_commutator_commutator P (Subgroup.zpowers a)
    (Subgroup.zpowers_le.mpr hn) (coprime_card_zpowers_of_odd ha hP)

theorem commutator_commutator_eq [Finite G] {Y P : Subgroup G} (hY : SubTwo.NoTwoQuotient Y)
    (hP : IsPGroup 2 P) (hYP : Y ≤ Subgroup.normalizer (P : Set G)) :
    ⁅⁅P, Y⁆, Y⁆ = ⁅P, Y⁆ := by
  have hYPY : Y ≤ Subgroup.normalizer ((⁅P, Y⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right P Y
  have hYN : Y ≤ Subgroup.normalizer ((⁅⁅P, Y⁆, Y⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ Y
  apply le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hYPY)
  set N : Subgroup G := ⁅⁅P, Y⁆, Y⁆ with hN
  have hconj : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hYN hy) x).mp hx
  have hPconj : ∀ y ∈ Y, ∀ x ∈ P, y * x * y⁻¹ ∈ P := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hYP hy) x).mp hx
  let K : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ ∀ x ∈ P, ⁅x, y⁆ ∈ N}
      one_mem' := ⟨Y.one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨Y.mul_mem hy₁ hy₂, fun x hx => ?_⟩
        rw [commutatorElement_mul_right_eq_mul_conj]
        have := hconj y₁ hy₁ _ (h₂ x hx)
        simpa [mul_assoc] using N.mul_mem (h₁ x hx) this
      inv_mem' := by
        rintro y ⟨hy, h⟩
        refine ⟨Y.inv_mem hy, fun x hx => ?_⟩
        rw [commutatorElement_inv_right, ← commutatorElement_inv]
        have := hconj y⁻¹ (Y.inv_mem hy) _ (N.inv_mem (h x hx))
        simpa [mul_assoc] using this }
  have hKY : K ≤ Y := fun y hy => hy.1
  have key : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    rintro y hy k ⟨hkY, hk⟩
    refine ⟨Y.mul_mem (Y.mul_mem hy hkY) (Y.inv_mem hy), fun x hx => ?_⟩
    have e : ⁅x, y * k * y⁻¹⁆ = y * ⁅y⁻¹ * x * y, k⁆ * y⁻¹ := by
      rw [conjugate_commutatorElement]
      have e1 : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
      rw [e1]
    rw [e]
    have hx' : y⁻¹ * x * y ∈ P := by
      simpa using hPconj y⁻¹ (Y.inv_mem hy) x hx
    exact hconj y hy _ (hk _ hx')
  have hKn : Y ≤ Subgroup.normalizer (K : Set G) := fun y hy =>
    Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => key y hy k hk, fun hk => by
      have := key y⁻¹ (Y.inv_mem hy) _ hk
      simpa [mul_assoc] using this⟩
  have hodd : ∀ a ∈ Y, Odd (orderOf a) → a ∈ K := by
    intro a ha hao
    refine ⟨ha, fun x hx => ?_⟩
    have hAY : Subgroup.zpowers a ≤ Y := Subgroup.zpowers_le.mpr ha
    have h1 : ⁅x, a⁆ ∈ ⁅P, Subgroup.zpowers a⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers a)
    exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hAY) hAY
      (commutator_le_commutator_commutator_of_odd hP hao (hYP ha) h1)
  have hKeq : K = Y := eq_of_odd_orderOf_mem hY hKY hKn hodd
  exact Subgroup.commutator_le.mpr fun x hx y hy => (hKeq.ge hy).2 x hx

end SixThree

end CFSG.CGT.PushingUpLit
