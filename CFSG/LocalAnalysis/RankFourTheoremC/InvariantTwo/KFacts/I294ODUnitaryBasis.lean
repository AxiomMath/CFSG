module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryHerm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace I294OD

open Polynomial Matrix CFSG.ClassicalGroups.Unitary TorusU
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid)

section Family

variable {K : Type} [Field K] [Finite K] {r e0 p n : ℕ} [Fact r.Prime] [CharP K r]
  [hpf : Fact p.Prime] {c : K} [hirr : Fact (Irreducible (X ^ p - C c : K[X]))]
  {σ : K ≃+* K} {B : GL (Fin n) K}

theorem od_perp_stable (S : OdSetup r e0 p c σ B) {k : ℕ} (w : Fin k → Fin n → K)
    {x : Fin n → K}
    (hx : x ∈ perp σ (fun t : Fin k × Fin p => odBv B ((t.2 : ℕ) : ℤ) (w t.1))) :
    ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈
      perp σ (fun t : Fin k × Fin p => odBv B ((t.2 : ℕ) : ℤ) (w t.1)) := by
  have hx' : ∀ (i : Fin k) (j : Fin p), herm σ (odBv B ((j : ℕ) : ℤ) (w i)) x = 0 :=
    fun i j => (mem_perp.1 hx) (i, j)
  rw [mem_perp]
  rintro ⟨i, j⟩
  show herm σ (odBv B ((j : ℕ) : ℤ) (w i)) _ = 0
  rw [← odBv_one x]
  have h1 : odBv B ((j : ℕ) : ℤ) (w i) = odBv B 1 (odBv B (((j : ℕ) : ℤ) - 1) (w i)) := by
    rw [← odBv_add]; congr 1; ring
  rw [h1, odBv_herm S.hB]
  by_cases hj : (j : ℕ) = 0
  · have h2 : odBv B (((p - 1 : ℕ)) : ℤ) (w i) = c • odBv B (-1) (w i) := by
      have hp1 : ((p - 1 : ℕ) : ℤ) = -1 + p := by have := hpf.out.pos; omega
      rw [hp1, odBv_add, odBv_p S.hBp, odBv_smul]
    have h3 : odBv B (-1) (w i) = c⁻¹ • odBv B (((p - 1 : ℕ)) : ℤ) (w i) := by
      rw [h2, smul_smul, inv_mul_cancel₀ S.hc0, one_smul]
    rw [hj, show (((0 : ℕ) : ℤ) - 1) = -1 by norm_num, h3, herm_smul_left,
      hx' i ⟨p - 1, by have := hpf.out.pos; omega⟩, mul_zero]
  · have h4 := hx' i ⟨(j : ℕ) - 1, by have := j.2; omega⟩
    have h5 : (((j : ℕ) : ℤ) - 1) = (((j : ℕ) - 1 : ℕ) : ℤ) := by omega
    rw [h5]
    exact h4

theorem od_exists_orbit_family (S : OdSetup r e0 p c σ B) (hσ : IsUnitaryInvolution σ) (m : ℕ)
    (hm : p * m = n) :
    ∃ w : Fin m → Fin n → K, ∀ (i i' : Fin m) (j j' : Fin p),
      herm σ (odBv B ((j : ℕ) : ℤ) (w i)) (odBv B ((j' : ℕ) : ℤ) (w i')) =
        if (i, j) = (i', j') then 1 else 0 := by
  have key : ∀ k : ℕ, k ≤ m → ∃ w : Fin k → Fin n → K, ∀ (i i' : Fin k) (j j' : Fin p),
      herm σ (odBv B ((j : ℕ) : ℤ) (w i)) (odBv B ((j' : ℕ) : ℤ) (w i')) =
        if (i, j) = (i', j') then 1 else 0 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hw⟩ := ih (by omega)
      set b' : Fin k × Fin p → Fin n → K := fun t => odBv B ((t.2 : ℕ) : ℤ) (w t.1) with hb'
      have hb : ∀ s t, herm σ (b' s) (b' t) = if s = t then 1 else 0 :=
        fun s t => hw s.1 t.1 s.2 t.2
      let Q : (Fin n → K) →ₗ[K] (Fin n → K) :=
        LinearMap.id - ∑ t : Fin k × Fin p, (hermL σ (b' t)).smulRight (b' t)
      have hQy : ∀ y, Q y = y - ∑ t, herm σ (b' t) y • b' t := fun y => by simp [Q]
      have hQ1 : ∀ y t, herm σ (b' t) (Q y) = 0 := by
        intro y t
        rw [hQy, herm_sub_right, herm_sum_right]
        simp [herm_smul_right, hb]
      have hkn : k * p < n := by
        have h1 : k * p < m * p := Nat.mul_lt_mul_of_pos_right (by omega) hpf.out.pos
        rw [mul_comm m p, hm] at h1
        exact h1
      obtain ⟨y, hy⟩ := exists_aniso_of_lt hσ hkn (fun t => b' (finProdFinEquiv.symm t)) Q
        (fun y => by
          rw [hQy, sub_sub_cancel]
          exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
            (Submodule.subset_span ⟨finProdFinEquiv t, by simp⟩))
        (fun y t => hQ1 y _)
      have hzperp : Q y ∈ perp σ b' := mem_perp.2 (hQ1 y)
      obtain ⟨e, he⟩ := od_exists_orbit S hy
      have hW : ∀ x ∈ perp σ b', ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈
          perp σ b' := fun x hx => od_perp_stable S w hx
      have hwmem : odAct p c _ S.hBp e *ᵥ Q y ∈ perp σ b' := odAct_mem S hW e hzperp
      have horbit : ∀ j : ℕ, odBv B (j : ℤ) (odAct p c _ S.hBp e *ᵥ Q y) ∈ perp σ b' := by
        intro j
        rw [odBv_natCast]
        induction j with
        | zero => simpa using hwmem
        | succ j ih =>
          rw [pow_succ', ← Matrix.mulVec_mulVec]
          exact hW _ ih
      refine ⟨Fin.snoc (α := fun _ => Fin n → K) w (odAct p c _ S.hBp e *ᵥ Q y), ?_⟩
      intro i i' j j'
      induction i using Fin.lastCases with
      | last =>
        induction i' using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last]
          rw [he j j' j.2 j'.2]
          simp [Fin.ext_iff]
        | cast a =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          have h0 : herm σ (odBv B ((j : ℕ) : ℤ) (odAct p c _ S.hBp e *ᵥ Q y))
              (odBv B ((j' : ℕ) : ℤ) (w a)) = 0 :=
            herm_eq_zero_comm σ S.hσσ (mem_perp.1 (horbit (j : ℕ)) (a, j'))
          rw [h0, if_neg]
          intro h
          exact (Fin.castSucc_lt_last a).ne' (Prod.mk.inj h).1
      | cast a =>
        induction i' using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          have h0 : herm σ (odBv B ((j : ℕ) : ℤ) (w a))
              (odBv B ((j' : ℕ) : ℤ) (odAct p c _ S.hBp e *ᵥ Q y)) = 0 :=
            mem_perp.1 (horbit (j' : ℕ)) (a, j)
          rw [h0, if_neg]
          intro h
          exact (Fin.castSucc_lt_last a).ne (Prod.mk.inj h).1
        | cast a' =>
          simp only [Fin.snoc_castSucc]
          rw [hw a a' j j']
          simp [Prod.mk.injEq, Fin.castSucc_inj]
  exact key m le_rfl

end Family

end I294OD

end CFSG.LocalAnalysis.RankFourTheoremC
