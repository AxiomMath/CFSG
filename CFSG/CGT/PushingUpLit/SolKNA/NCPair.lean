module

public import CFSG.CGT.Timmesfeld75.StrongClosure
public import CFSG.RankThree.GF2n.Basic
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def IsConjOf2 (T T' U : Subgroup Y) : Prop :=
  (∃ y : Y, U = conjSubgroup y T) ∨ ∃ y : Y, U = conjSubgroup y T'

structure NCPair (T T' : Subgroup Y) : Prop where
  elem : IsElemAbelian 2 T
  elem' : IsElemAbelian 2 T'
  ne_bot : T ≠ ⊥
  ne_bot' : T' ≠ ⊥
  ne : T ≠ T'
  gen : T ⊔ T' = ⊤
  nc : ∀ U₁ U₂ : Subgroup Y, IsConjOf2 T T' U₁ → IsConjOf2 T T' U₂ → ∀ u₁ ∈ U₁, ∀ u₂ ∈ U₂,
    u₁ ≠ 1 → u₂ ≠ 1 → u₁ * u₂ = u₂ * u₁ → U₁ = U₂

theorem elem2_mul_self {T : Subgroup Y} (hT : IsElemAbelian 2 T) {x : Y} (hx : x ∈ T) :
    x * x = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hT hx

namespace NCPair

variable {T T' : Subgroup Y} (h : NCPair T T')
include h

theorem isConjOf2_left : IsConjOf2 T T' T :=
  Or.inl ⟨1, (CFSG.RankThree.GF2n.conjSubgroup_one T).symm⟩

theorem isConjOf2_right : IsConjOf2 T T' T' :=
  Or.inr ⟨1, (CFSG.RankThree.GF2n.conjSubgroup_one T').symm⟩

theorem symm : NCPair T' T where
  elem := h.elem'
  elem' := h.elem
  ne_bot := h.ne_bot'
  ne_bot' := h.ne_bot
  ne := h.ne.symm
  gen := by rw [sup_comm]; exact h.gen
  nc U₁ U₂ h₁ h₂ := h.nc U₁ U₂ h₁.symm h₂.symm

theorem strongWC : StrongWC T := by
  refine ⟨h.elem, fun t ht ht1 a ha g hg => ?_⟩
  by_cases ha1 : a = 1
  · rw [ha1]
    simp
  have hmem : g⁻¹ * a * g ∈ conjSubgroup g⁻¹ T := by
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
    exact ha
  have hne : g⁻¹ * a * g ≠ 1 := fun h1 => ha1 (by
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h1]
    group)
  have hcomm : g⁻¹ * a * g * t = t * (g⁻¹ * a * g) :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have heq := h.nc (conjSubgroup g⁻¹ T) T (Or.inl ⟨g⁻¹, rfl⟩) h.isConjOf2_left _ hmem t ht hne ht1
    hcomm
  rw [heq] at hmem
  exact hmem

theorem odd_orderOf_mul {a b : Y} (ha : a ∈ T) (ha1 : a ≠ 1) (hb : b ∈ T') (hb1 : b ≠ 1) :
    Odd (orderOf (a * b)) := by
  rcases Nat.even_or_odd (orderOf (a * b)) with ⟨m, hm⟩ | hodd
  swap
  · exact hodd
  exfalso
  have haa : a * a = 1 := elem2_mul_self h.elem ha
  have hbb : b * b = 1 := elem2_mul_self h.elem' hb
  have hm0 : 0 < m := by
    have := orderOf_pos (a * b)
    omega
  have hord : orderOf (b * a) = 2 * m := by
    have h1 : b * a = (a * b)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb]
    rw [h1, orderOf_inv]
    omega
  obtain ⟨z, hzz, hz1, hbz, haz, hconj⟩ := dihedral_central_of_even_order hbb haa hm0 hord
  have hacomm : a * z * a = a * (a * z) := by
    calc a * z * a = a * (z * a) := mul_assoc _ _ _
      _ = a * (a * z) := by rw [haz]
  have haz1 : ∀ u : Y, u ≠ 1 → ∀ g : Y, a * z = g⁻¹ * u * g → a * z ≠ 1 := by
    intro u hu g hg h1
    apply hu
    have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [this, ← hg, h1]
    group
  have hazT : a * z ∈ T := by
    rcases hconj with ⟨g, hg⟩ | ⟨g, hg⟩
    · have hmem : a * z ∈ conjSubgroup g⁻¹ T' := by
        rw [mem_conjSubgroup, inv_inv, hg, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
        exact hb
      have heq := h.nc (conjSubgroup g⁻¹ T') T (Or.inr ⟨g⁻¹, rfl⟩) h.isConjOf2_left _ hmem a ha
        (haz1 b hb1 g hg) ha1 hacomm
      rw [heq] at hmem
      exact hmem
    · have hmem : a * z ∈ conjSubgroup g⁻¹ T := by
        rw [mem_conjSubgroup, inv_inv, hg, show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
        exact ha
      have heq := h.nc (conjSubgroup g⁻¹ T) T (Or.inl ⟨g⁻¹, rfl⟩) h.isConjOf2_left _ hmem a ha
        (haz1 a ha1 g hg) ha1 hacomm
      rw [heq] at hmem
      exact hmem
  have hzT : z ∈ T := by
    have := T.mul_mem (T.inv_mem ha) hazT
    rwa [inv_mul_cancel_left] at this
  exact h.ne (h.nc T T' h.isConjOf2_left h.isConjOf2_right z hzT b hb hz1 hb1 hbz.symm)

theorem exists_conj : ∃ y : Y, T' = conjSubgroup y T := by
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ T, a ≠ 1 := by
    obtain ⟨⟨a, ha⟩, h1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.ne_bot
    exact ⟨a, ha, fun h' => h1 (Subtype.ext h')⟩
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ T', b ≠ 1 := by
    obtain ⟨⟨b, hb⟩, h1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.ne_bot'
    exact ⟨b, hb, fun h' => h1 (Subtype.ext h')⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_odd_orderOf_mul (elem2_mul_self h.elem ha)
    (elem2_mul_self h.elem' hb) (h.odd_orderOf_mul ha ha1 hb hb1))
  have hmem : b ∈ conjSubgroup c T := by
    rw [mem_conjSubgroup, ← hc]
    simpa [mul_assoc] using ha
  exact ⟨c, (h.nc (conjSubgroup c T) T' (Or.inl ⟨c, rfl⟩) h.isConjOf2_right b hmem b hb
    (by rw [← hc]; intro h1; exact ha1 (by simpa using h1)) hb1 rfl).symm⟩

end NCPair

end CFSG.CGT.PushingUpLit.SolKNA
