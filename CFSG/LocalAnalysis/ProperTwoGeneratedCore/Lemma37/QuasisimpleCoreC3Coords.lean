module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Iso
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Count

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}

@[expose] noncomputable def caseC3Word (Z : Subgroup G) [Z.Normal] (u m y x : G) (v : Fin 64) :
    G ⧸ Z :=
  c3Word (u : G ⧸ Z) (m : G ⧸ Z) ((x : G ⧸ Z) * (u : G ⧸ Z) * (x : G ⧸ Z)⁻¹)
    ((x : G ⧸ Z) * (m : G ⧸ Z) * (x : G ⧸ Z)⁻¹) (y : G ⧸ Z) (x : G ⧸ Z) v

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z)
include hb

omit hb in
theorem caseC3Word_eq (v : Fin 64) :
    caseC3Word Z u m y x v = ((u ^ (v.val / 32 % 2) * m ^ (v.val / 16 % 2) : G) : G ⧸ Z) *
      (((x * u * x⁻¹) ^ (v.val / 8 % 2) * (x * m * x⁻¹) ^ (v.val / 4 % 2) : G) : G ⧸ Z) *
      (y : G ⧸ Z) ^ (v.val / 2 % 2) * (x : G ⧸ Z) ^ (v.val % 2) := by
  simp only [caseC3Word, c3Word, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
    QuotientGroup.mk_inv]
  group

theorem pPart_mem (i j : ℕ) : u ^ i * m ^ j ∈ P₁ :=
  P₁.mul_mem (P₁.pow_mem hb.partC.self_mem _) (P₁.pow_mem hb.m_mem _)

theorem qPart_mem (k l : ℕ) : (x * u * x⁻¹) ^ k * (x * m * x⁻¹) ^ l ∈ Q :=
  Q.mul_mem (Q.pow_mem (hb.swap_right u hb.partC.self_mem) _)
    (Q.pow_mem (hb.swap_right m hb.m_mem) _)

theorem caseC3Word_mem_bot {v : Fin 64} (hv : v.val % 2 = 0) :
    caseC3Word Z u m y x v ∈ T.map (QuotientGroup.mk' Z) := by
  have hc := hb.partC
  rw [caseC3Word_eq, hv, pow_zero, mul_one]
  have hT : ∀ {g : G}, g ∈ T → (g : G ⧸ Z) ∈ T.map (QuotientGroup.mk' Z) :=
    fun hg => Subgroup.mem_map_of_mem _ hg
  exact (T.map _).mul_mem ((T.map _).mul_mem (hT (hc.right_le (hb.pPart_mem _ _)))
    (hT (hc.left_le (hb.qPart_mem _ _)))) ((T.map _).pow_mem (hT hb.mem) _)

theorem caseC3Word_mem_sup {v : Fin 64} (hv : v.val % 4 = 0) :
    caseC3Word Z u m y x v ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) := by
  have h2 : v.val / 2 % 2 = 0 := by omega
  have h1 : v.val % 2 = 0 := by omega
  rw [caseC3Word_eq, h1, h2, pow_zero, pow_zero, mul_one, mul_one]
  exact Subgroup.mem_map_of_mem (QuotientGroup.mk' Z)
    ((Q ⊔ P₁).mul_mem (Subgroup.mem_sup_right (hb.pPart_mem _ _))
      (Subgroup.mem_sup_left (hb.qPart_mem _ _)))

theorem caseC3Word_not_mem_bot {v : Fin 64} (hv : v.val % 2 = 1) :
    caseC3Word Z u m y x v ∉ T.map (QuotientGroup.mk' Z) := by
  intro hmem
  have hv' : (⟨v.val - 1, by omega⟩ : Fin 64).val % 2 = 0 := by simp only; omega
  have h0 := hb.caseC3Word_mem_bot hv'
  rw [caseC3Word_eq] at hmem h0
  simp only at h0
  rw [show (v.val - 1) / 32 % 2 = v.val / 32 % 2 by omega,
    show (v.val - 1) / 16 % 2 = v.val / 16 % 2 by omega,
    show (v.val - 1) / 8 % 2 = v.val / 8 % 2 by omega,
    show (v.val - 1) / 4 % 2 = v.val / 4 % 2 by omega,
    show (v.val - 1) / 2 % 2 = v.val / 2 % 2 by omega,
    show (v.val - 1) % 2 = 0 by omega, pow_zero, mul_one] at h0
  rw [hv, pow_one] at hmem
  exact hb.mk_not_mem_bot ((Subgroup.mul_mem_cancel_left _ h0).mp hmem)

theorem caseC3Word_not_mem_sup {v : Fin 64} (hv : v.val % 2 = 0) (hv4 : v.val % 4 ≠ 0) :
    caseC3Word Z u m y x v ∉ (Q ⊔ P₁).map (QuotientGroup.mk' Z) := by
  intro hmem
  obtain ⟨-, hyW, -⟩ := hb.toCaseC3.mk_facts Z hb.mem_iff
  have hv' : (⟨v.val - 2, by omega⟩ : Fin 64).val % 4 = 0 := by simp only; omega
  have h0 := hb.caseC3Word_mem_sup hv'
  rw [caseC3Word_eq] at hmem h0
  simp only at h0
  rw [show (v.val - 2) / 32 % 2 = v.val / 32 % 2 by omega,
    show (v.val - 2) / 16 % 2 = v.val / 16 % 2 by omega,
    show (v.val - 2) / 8 % 2 = v.val / 8 % 2 by omega,
    show (v.val - 2) / 4 % 2 = v.val / 4 % 2 by omega,
    show (v.val - 2) / 2 % 2 = 0 by omega, show (v.val - 2) % 2 = 0 by omega,
    pow_zero, pow_zero, mul_one, mul_one] at h0
  rw [show v.val / 2 % 2 = 1 by omega, hv, pow_one, pow_zero, mul_one] at hmem
  exact hyW ((Subgroup.mul_mem_cancel_left _ h0).mp hmem)

theorem caseC3Word_mul [Finite G] (v w : Fin 64) :
    caseC3Word Z u m y x v * caseC3Word Z u m y x w = caseC3Word Z u m y x (c3Mul v w) :=
  hb.c3Relations.c3Word_mul v w

omit hb in
theorem caseC3Word_zero : caseC3Word Z u m y x 0 = 1 := by
  simp [caseC3Word, c3Word]

theorem le_left : Z ≤ Q := fun g hg => by
  rcases (hb.mem_iff g).mp hg with rfl | rfl
  exacts [Q.one_mem, hb.partC.mem_left]

theorem le_right : Z ≤ P₁ := fun g hg => by
  rcases (hb.mem_iff g).mp hg with rfl | rfl
  exacts [P₁.one_mem, hb.partC.mem_right]

theorem pPart_mk_eq_one {i j : ℕ} (hi : i < 2) (hj : j < 2)
    (h1 : ((u ^ i * m ^ j : G) : G ⧸ Z) = 1) : i = 0 ∧ j = 0 := by
  have hw := caseC3Word_eq (Z := Z) (u := u) (m := m) (y := y) (x := x)
    (⟨32 * i + 16 * j, by omega⟩ : Fin 64)
  simp only at hw
  rw [show (32 * i + 16 * j) / 32 % 2 = i by omega, show (32 * i + 16 * j) / 16 % 2 = j by omega,
    show (32 * i + 16 * j) / 8 % 2 = 0 by omega, show (32 * i + 16 * j) / 4 % 2 = 0 by omega,
    show (32 * i + 16 * j) / 2 % 2 = 0 by omega, show (32 * i + 16 * j) % 2 = 0 by omega,
    h1] at hw
  simp only [pow_zero, mul_one, QuotientGroup.mk_one] at hw
  have := congrArg Fin.val (hb.c3Word_eq_one _ hw)
  simp only [Fin.val_zero] at this
  omega

theorem qPart_mk_eq_one {k l : ℕ} (hk : k < 2) (hl : l < 2)
    (h1 : (((x * u * x⁻¹) ^ k * (x * m * x⁻¹) ^ l : G) : G ⧸ Z) = 1) : k = 0 ∧ l = 0 := by
  have hw := caseC3Word_eq (Z := Z) (u := u) (m := m) (y := y) (x := x)
    (⟨8 * k + 4 * l, by omega⟩ : Fin 64)
  simp only at hw
  rw [show (8 * k + 4 * l) / 32 % 2 = 0 by omega, show (8 * k + 4 * l) / 16 % 2 = 0 by omega,
    show (8 * k + 4 * l) / 8 % 2 = k by omega, show (8 * k + 4 * l) / 4 % 2 = l by omega,
    show (8 * k + 4 * l) / 2 % 2 = 0 by omega, show (8 * k + 4 * l) % 2 = 0 by omega,
    h1] at hw
  simp only [pow_zero, mul_one, QuotientGroup.mk_one] at hw
  have := congrArg Fin.val (hb.c3Word_eq_one _ hw)
  simp only [Fin.val_zero] at this
  omega

theorem c3GenW_of_genuine {v : Fin 64} (hv : v.val % 4 = 0)
    (hgen : CaseC3.Genuine Z (caseC3Word Z u m y x v)) : v = 0 ∨ c3GenW v := by
  have hc := hb.partC
  obtain ⟨φQ⟩ := hc.quaternion
  by_cases hg : c3GenW v
  · exact Or.inr hg
  left
  have hpart : v.val / 16 % 4 = 0 ∨ v.val / 4 % 4 = 0 := by
    unfold c3GenW at hg
    push Not at hg
    omega
  have hw := caseC3Word_eq (Z := Z) (u := u) (m := m) (y := y) (x := x) v
  rw [show v.val % 2 = 0 by omega, show v.val / 2 % 2 = 0 by omega, pow_zero, pow_zero, mul_one,
    mul_one] at hw
  obtain ⟨g, hg1, hg2⟩ := hgen
  apply hb.c3Word_eq_one v
  change caseC3Word Z u m y x v = 1
  rcases hpart with hP | hQ
  · rw [show v.val / 32 % 2 = 0 by omega, show v.val / 16 % 2 = 0 by omega, pow_zero, pow_zero,
      mul_one, QuotientGroup.mk_one, one_mul] at hw
    have hqQ := hb.qPart_mem (v.val / 8 % 2) (v.val / 4 % 2)
    rw [hw] at hg1 ⊢
    have hgq := QuotientGroup.eq.mp hg1
    have hgQ : g ∈ Q := by
      rw [show g = ((x * u * x⁻¹) ^ (v.val / 8 % 2) * (x * m * x⁻¹) ^ (v.val / 4 % 2)) *
        (g⁻¹ * ((x * u * x⁻¹) ^ (v.val / 8 % 2) * (x * m * x⁻¹) ^ (v.val / 4 % 2)))⁻¹ by group]
      exact Q.mul_mem hqQ (Q.inv_mem (hb.le_left hgq))
    rw [← hg1]
    rcases quaternion_eq_of_mul_self φQ hc.mem_left hc.order hgQ hg2 with h3 | h3
    · rw [h3, QuotientGroup.mk_one]
    · rw [h3, hb.mk_centralElt]
  · rw [show v.val / 8 % 2 = 0 by omega, show v.val / 4 % 2 = 0 by omega, pow_zero, pow_zero,
      mul_one, QuotientGroup.mk_one, mul_one] at hw
    have hpP := hb.pPart_mem (v.val / 32 % 2) (v.val / 16 % 2)
    rw [hw] at hg1 ⊢
    have hgp := QuotientGroup.eq.mp hg1
    have hgP : g ∈ P₁ := by
      rw [show g = (u ^ (v.val / 32 % 2) * m ^ (v.val / 16 % 2)) *
        (g⁻¹ * (u ^ (v.val / 32 % 2) * m ^ (v.val / 16 % 2)))⁻¹ by group]
      exact P₁.mul_mem hpP (P₁.inv_mem (hb.le_right hgp))
    rw [← hg1]
    rcases hc.eq_of_mem_right_of_mul_self hgP hg2 with h3 | h3
    · rw [h3, QuotientGroup.mk_one]
    · rw [h3, hb.mk_centralElt]

omit hb in
theorem caseC3Word_forty : caseC3Word Z u m y x 40 = ((u * (x * u * x⁻¹) : G) : G ⧸ Z) := by
  rw [caseC3Word_eq]
  simp only [show (40 : Fin 64).val = 40 from rfl]
  norm_num [QuotientGroup.mk_mul]

theorem genuine_forty : CaseC3.Genuine Z (caseC3Word Z u m y x 40) := by
  have hc := hb.partC
  refine ⟨u * (x * u * x⁻¹), caseC3Word_forty.symm, ?_⟩
  have hq := hb.swap_right u hc.self_mem
  rw [show u * (x * u * x⁻¹) * (u * (x * u * x⁻¹)) = u * ((x * u * x⁻¹) * u) * (x * u * x⁻¹) by
    group, hc.commute _ hq u hc.self_mem,
    show u * (u * (x * u * x⁻¹)) * (x * u * x⁻¹) = u * u * (x * (u * u) * x⁻¹) by group, hc.sq,
    hc.conj_centralElt, hc.centralElt_mul_self]

theorem caseC3Word_bijective [Finite G] :
    Function.Injective (caseC3Word Z u m y x) ∧
      (∀ v, caseC3Word Z u m y x v ∈ S.map (QuotientGroup.mk' Z)) ∧
      ∀ s ∈ S.map (QuotientGroup.mk' Z), ∃ v, caseC3Word Z u m y x v = s :=
  hb.c3Word_bijective

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
