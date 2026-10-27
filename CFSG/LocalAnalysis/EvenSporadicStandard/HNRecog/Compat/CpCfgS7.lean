module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private lemma orderOf_eq_two_of_cycleType {σ : Sym 7}
    (h : σ.cycleType = {2} ∨ σ.cycleType = {2, 2} ∨ σ.cycleType = {2, 2, 2}) :
    orderOf σ = 2 := by
  rw [← Equiv.Perm.lcm_cycleType]
  rcases h with h | h | h <;> rw [h] <;> decide

private lemma cp_s7_pair_comm {x : G} (φ : ↥(Gxy a x) ≃* Sym 7) (τ₁ τ₂ : Sym 7) :
    x ∈ Gxy ((φ.symm τ₁ : ↥(Gxy a x)) : G) ((φ.symm τ₂ : ↥(Gxy a x)) : G) ∧
      ((φ.symm τ₁ : ↥(Gxy a x)) : G) * ((φ.symm τ₂ : ↥(Gxy a x)) : G) =
        ((φ.symm (τ₁ * τ₂) : ↥(Gxy a x)) : G) := by
  constructor
  · refine mem_Gxy.mpr ⟨?_, ?_⟩
    · exact mem_Gx.mpr ((mem_Gx.mp ((mem_Gxy.mp (φ.symm τ₁).2).2)).symm)
    · exact mem_Gx.mpr ((mem_Gx.mp ((mem_Gxy.mp (φ.symm τ₂).2).2)).symm)
  · exact (congrArg (fun u : ↥(Gxy a x) => (u : G)) (map_mul φ.symm τ₁ τ₂)).symm

theorem cp_s7_class (h : F5Std a z) {x : G} (hx : x ∈ orb3A a a) (φ : ↥(Gxy a x) ≃* Sym 7)
    (τ : Sym 7) (hτ : orderOf τ = 2) :
    (τ.cycleType = {2} → (φ.symm τ : G) ∈ orb2A a a ∩ orb2A a x) ∧
      (τ.cycleType = {2, 2} → (φ.symm τ : G) ∈ orb2B a z a ∩ orb2B a z x) ∧
      (τ.cycleType = {2, 2, 2} → (φ.symm τ : G) ∈ orb2BB a z a ∩ orb2BB a z x) := by
  have hpart := h.loc.s7.self.classes x hx
  have ht2 : orderOf (((φ.symm τ : ↥(Gxy a x)) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ (φ.symm τ),
      MulEquiv.apply_symm_apply, hτ]
  have hmem : ((φ.symm τ : ↥(Gxy a x)) : G) ∈
      {t : G | t ∈ Gxy a x ∧ orderOf t = 2} :=
    ⟨(φ.symm τ).2, ht2⟩
  obtain ⟨i, hi⟩ := hpart.cover _ hmem
  have hcyc := h.loc.s7.self.cycleType x hx φ (φ.symm τ)
  have hφ : φ (φ.symm τ) = τ := MulEquiv.apply_symm_apply φ τ
  fin_cases i
  · have hi0 : ((φ.symm τ : ↥(Gxy a x)) : G) ∈ orb2A a a ∩ orb2A a x := by
      simpa [s7Set] using hi
    refine ⟨fun _ => hi0, ?_, ?_⟩
    · intro hc
      exfalso
      have h2 : (φ (φ.symm τ)).cycleType = {2} := hcyc.1 hi0
      rw [hφ] at h2
      exact (by decide : ({2} : Multiset ℕ) ≠ {2, 2}) (h2.symm.trans hc)
    · intro hc
      exfalso
      have h2 : (φ (φ.symm τ)).cycleType = {2} := hcyc.1 hi0
      rw [hφ] at h2
      exact (by decide : ({2} : Multiset ℕ) ≠ {2, 2, 2}) (h2.symm.trans hc)
  · have hi1 : ((φ.symm τ : ↥(Gxy a x)) : G) ∈ orb2B a z a ∩ orb2B a z x := by
      simpa [s7Set] using hi
    refine ⟨?_, fun _ => hi1, ?_⟩
    · intro hc
      exfalso
      have h2 : (φ (φ.symm τ)).cycleType = {2, 2} := hcyc.2.1 hi1
      rw [hφ] at h2
      exact (by decide : ({2, 2} : Multiset ℕ) ≠ {2}) (h2.symm.trans hc)
    · intro hc
      exfalso
      have h2 : (φ (φ.symm τ)).cycleType = {2, 2} := hcyc.2.1 hi1
      rw [hφ] at h2
      exact (by decide : ({2, 2} : Multiset ℕ) ≠ {2, 2, 2}) (h2.symm.trans hc)
  · have hi2 : ((φ.symm τ : ↥(Gxy a x)) : G) ∈ orb2BB a z a ∩ orb2BB a z x := by
      simpa [s7Set] using hi
    refine ⟨?_, ?_, fun _ => hi2⟩
    · intro hc
      exfalso
      have h2 : (φ (φ.symm τ)).cycleType = {2, 2, 2} := hcyc.2.2 hi2
      rw [hφ] at h2
      exact (by decide : ({2, 2, 2} : Multiset ℕ) ≠ {2}) (h2.symm.trans hc)
    · intro hc
      exfalso
      have h2 : (φ (φ.symm τ)).cycleType = {2, 2, 2} := hcyc.2.2 hi2
      rw [hφ] at h2
      exact (by decide : ({2, 2, 2} : Multiset ℕ) ≠ {2, 2}) (h2.symm.trans hc)

theorem cp_s7_pair_ABBB (h : F5Std a z) :
    ∃ t t' x : G, t ∈ orb2A a a ∧ t' ∈ orb2B a z a ∧ t * t' ∈ orb2BB a z a ∧ x ∈ orb3A a a ∧
      x ∈ Gxy t t' := by
  obtain ⟨x, hx⟩ := h.loc.s7.self.orbit.nonempty
  obtain ⟨φ⟩ := h.loc.s7.self.shape x hx
  have hcyc₁ : (Equiv.swap (0 : Fin 7) 1).cycleType = ({2} : Multiset ℕ) :=
    Equiv.Perm.isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
  have hcyc₂ : (Equiv.swap (2 : Fin 7) 3 * Equiv.swap 4 5).cycleType =
      ({2, 2} : Multiset ℕ) :=
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (by decide : ([2, 3, 4, 5] : List (Fin 7)).Nodup)
  have hcyc₁₂ : (Equiv.swap (0 : Fin 7) 1 * (Equiv.swap 2 3 * Equiv.swap 4 5)).cycleType =
      ({2, 2, 2} : Multiset ℕ) := by
    rw [Equiv.Perm.Disjoint.cycleType_mul (show Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 7) 1)
      (Equiv.swap 2 3 * Equiv.swap 4 5) by
        intro y
        fin_cases y <;> decide)]
    rw [hcyc₁, hcyc₂]
    decide
  have hτ₁ : orderOf (Equiv.swap (0 : Fin 7) 1) = 2 :=
    orderOf_eq_two_of_cycleType (Or.inl hcyc₁)
  have hτ₂ : orderOf (Equiv.swap (2 : Fin 7) 3 * Equiv.swap 4 5) = 2 :=
    orderOf_eq_two_of_cycleType (Or.inr (Or.inl hcyc₂))
  have hτ₁₂ : orderOf (Equiv.swap (0 : Fin 7) 1 * (Equiv.swap 2 3 * Equiv.swap 4 5)) = 2 :=
    orderOf_eq_two_of_cycleType (Or.inr (Or.inr hcyc₁₂))
  have hcls₁ := cp_s7_class h hx φ (Equiv.swap (0 : Fin 7) 1) hτ₁
  have hcls₂ := cp_s7_class h hx φ (Equiv.swap (2 : Fin 7) 3 * Equiv.swap 4 5) hτ₂
  have hcls₁₂ := cp_s7_class h hx φ
    (Equiv.swap (0 : Fin 7) 1 * (Equiv.swap 2 3 * Equiv.swap 4 5)) hτ₁₂
  have hcomm := cp_s7_pair_comm (x := x) φ (Equiv.swap (0 : Fin 7) 1)
    (Equiv.swap (2 : Fin 7) 3 * Equiv.swap 4 5)
  refine ⟨(φ.symm (Equiv.swap (0 : Fin 7) 1) : G),
    (φ.symm (Equiv.swap (2 : Fin 7) 3 * Equiv.swap 4 5) : G), x,
    (hcls₁.1 hcyc₁).1, (hcls₂.2.1 hcyc₂).1, ?_, hx, hcomm.1⟩
  rw [hcomm.2]
  exact (hcls₁₂.2.2 hcyc₁₂).1

theorem cp_s7_pair_BBB (h : F5Std a z) :
    ∃ t t' x : G, t ∈ orb2B a z a ∧ t' ∈ orb2B a z a ∧ t * t' ∈ orb2B a z a ∧ x ∈ orb3A a a ∧
      x ∈ Gxy t t' := by
  obtain ⟨x, hx⟩ := h.loc.s7.self.orbit.nonempty
  obtain ⟨φ⟩ := h.loc.s7.self.shape x hx
  have hcyc₁ : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3).cycleType =
      ({2, 2} : Multiset ℕ) :=
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (by decide : ([0, 1, 2, 3] : List (Fin 7)).Nodup)
  have hcyc₂ : (Equiv.swap (0 : Fin 7) 2 * Equiv.swap 1 3).cycleType =
      ({2, 2} : Multiset ℕ) :=
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (by decide : ([0, 2, 1, 3] : List (Fin 7)).Nodup)
  have hprod : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) *
      (Equiv.swap 0 2 * Equiv.swap 1 3) = Equiv.swap 0 3 * Equiv.swap 1 2 := by decide
  have hcyc₁₂ : ((Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) *
      (Equiv.swap 0 2 * Equiv.swap 1 3)).cycleType = ({2, 2} : Multiset ℕ) := by
    rw [hprod]
    exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (by decide : ([0, 3, 1, 2] : List (Fin 7)).Nodup)
  have hτ₁ : orderOf (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) = 2 :=
    orderOf_eq_two_of_cycleType (Or.inr (Or.inl hcyc₁))
  have hτ₂ : orderOf (Equiv.swap (0 : Fin 7) 2 * Equiv.swap 1 3) = 2 :=
    orderOf_eq_two_of_cycleType (Or.inr (Or.inl hcyc₂))
  have hτ₁₂ : orderOf ((Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) *
      (Equiv.swap 0 2 * Equiv.swap 1 3)) = 2 :=
    orderOf_eq_two_of_cycleType (Or.inr (Or.inl hcyc₁₂))
  have hcls₁ := cp_s7_class h hx φ (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) hτ₁
  have hcls₂ := cp_s7_class h hx φ (Equiv.swap (0 : Fin 7) 2 * Equiv.swap 1 3) hτ₂
  have hcls₁₂ := cp_s7_class h hx φ
    ((Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) * (Equiv.swap 0 2 * Equiv.swap 1 3)) hτ₁₂
  have hcomm := cp_s7_pair_comm (x := x) φ (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3)
    (Equiv.swap (0 : Fin 7) 2 * Equiv.swap 1 3)
  refine ⟨(φ.symm (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) : G),
    (φ.symm (Equiv.swap (0 : Fin 7) 2 * Equiv.swap 1 3) : G), x,
    (hcls₁.2.1 hcyc₁).1, (hcls₂.2.1 hcyc₂).1, ?_, hx, hcomm.1⟩
  rw [hcomm.2]
  exact (hcls₁₂.2.1 hcyc₁₂).1

end CFSG.EvenSporadicStandard.HNRecog.Section4
