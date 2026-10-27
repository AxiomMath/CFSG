module

public import CFSG.CGT.L5R.L2SubDL

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.CGT.M24R

section FA

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem conjVia_sound {fm : Array ℕ} {P X : Table} {p x : N8} (hP : IsTab P p) (hX : IsTab X x)
    (h : conjVia (mkCtx ()) fm P X = true) : ∃ n : N8, n * p * n⁻¹ = x := by
  simp only [conjVia, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, heq⟩ := h
  have hN := isTab_tab hn
  have e := ((hN.mul hP).beq_iff hcard (hX.mul hN) (compT_size _ _) (compT_size _ _)).1 heq
  exact ⟨_, by rw [e, mul_inv_cancel_right]⟩


theorem gL_notMem_T8 : gL ∉ T8 := by
  intro h
  have h1 := bCheckL_spec.2.2.2.2
  rw [(isTt_iff hcard isTab_gamT (wTab_size _)).2 h] at h1
  exact absurd h1 (by decide)

theorem gL_ne_one : gL ≠ 1 := fun h => gL_notMem_T8 hcard (h ▸ T8.one_mem)

omit hcard in
theorem bL_ne_one : bL 0 ≠ 1 := by
  intro h
  have hnd := eightE_b8_nodup
  rw [h] at hnd
  simp [eightE] at hnd

omit hcard in
theorem bL_mem_B8L : bL 0 ∈ B8L := Subgroup.subset_closure (by simp)

theorem inv_classL (x : N8) (hx : x * x = 1) (hxT : x ∉ T8)
    (hc8 : Nat.card ↥(T8 ⊓ Subgroup.centralizer ({x} : Set N8)) = 8) :
    (∃ n : N8, n * bL 0 * n⁻¹ = x) ∨ ∃ n : N8, n * gL * n⁻¹ = x := by
  obtain ⟨c, hc, rfl⟩ := el_surj hcard x
  have hX := isTab_tab (mem_codes.1 hc).1
  have hXs := tab_size c
  have h := Certificates.certificate21196.2.1
  simp only [faCheckL, List.all_eq_true] at h
  have hc' := h c hc
  have hsq : (compT 16 ((mkCtx ()).tab c) ((mkCtx ()).tab c) == idT 16) = true :=
    ((hX.mul hX).beq_iff hcard IsTab.one (compT_size _ _) idT_size).2 hx
  have hT : (mkCtx ()).isTt ((mkCtx ()).tab c) = false := by
    rw [Bool.eq_false_iff]
    intro h'
    exact hxT ((isTt_iff hcard hX hXs).1 h')
  have hcnt : ((mkCtx ()).commCount ((mkCtx ()).tab c) == 8) = true := by
    rw [commCount_eq hcard hX, hc8]
    rfl
  rw [hsq, hT, hcnt] at hc'
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hc'
  rcases hc' with h1 | h1
  · exact Or.inl (conjVia_sound hcard (isTab_betaT 0) hX h1)
  · exact Or.inr (conjVia_sound hcard isTab_gamT hX h1)

end FA

end CFSG.CGT.L5R
