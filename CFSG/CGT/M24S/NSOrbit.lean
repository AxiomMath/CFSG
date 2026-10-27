module

public import CFSG.CGT.M24S.NSForm

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

theorem lv_zero (v : Fin 3 → ZMod 2) : lv 0 v = 1 := by
  simp [lv]

theorem exists_mul_of_over {v : Fin 3 → ZMod 2} {y y' : G} (hy : Over c v y)
    (hy' : Over c v y') : ∃ s ∈ T, y' = y * s ∧ v ⬝ᵥ tail (c.vec s) = 0 := by
  have hs : y⁻¹ * y' ∈ T := by
    apply mem_T_of_top_eq_zero c (c.E.mul_mem (c.E.inv_mem hy.1) hy'.1)
    rw [top_mul_of_mem_E c (c.E.inv_mem hy.1) hy'.1, top_inv_of_mem_E c hy.1, hy.2.1, hy'.2.1,
      vec_add_self]
  refine ⟨y⁻¹ * y', hs, by group, ?_⟩
  rcases zmod_two_eq_zero_or_one (v ⬝ᵥ tail (c.vec (y⁻¹ * y'))) with h | h
  · exact h
  · exfalso
    have h1 := sq_mul_of_dot_one c hy.1 hs (by rw [hy.2.1]; exact h)
    rw [mul_inv_cancel_left, hy'.2.2, hy.2.2, one_mul] at h1
    exact c.z_ne_one h1.symm

theorem fix_of_over {g : G} {v cc : Fin 3 → ZMod 2} {y : G} (hcc : v ⬝ᵥ cc = 0)
    (hB : blk (c.mat g) = lv cc v) (hy : Over c v y) :
    vecMul (top (c.mat y)) (blk (c.mat g)) = top (c.mat y) := by
  rw [hB, hy.2.1]
  exact vecMul_lv_self hcc

theorem disp_over_eq {g : G} {v cc : Fin 3 → ZMod 2} {y y' : G}
    (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (hcc : v ⬝ᵥ cc = 0)
    (hB : blk (c.mat g) = lv cc v) (hy : Over c v y) (hy' : Over c v y') :
    disp c g y' = disp c g y := by
  obtain ⟨s, hs, rfl, hvs⟩ := exists_mul_of_over c hy hy'
  have hT := mem_T_of_fix c hg hy.1 (fix_of_over c hcc hB hy)
  rw [disp_mul_right c hg hs (by rw [hy.2.1]; exact hB) hT, hy.2.1, hvs, zero_smul, add_zero]

theorem disp_eq_zero_or {g : G} {v cc : Fin 3 → ZMod 2} {y : G}
    (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (hcc : v ⬝ᵥ cc = 0)
    (hB : blk (c.mat g) = lv cc v) (hy : Over c v y) :
    disp c g y = 0 ∨ disp c g y = cc := by
  have hT := mem_T_of_fix c hg hy.1 (fix_of_over c hcc hB hy)
  by_cases hc0 : cc = 0
  · subst hc0
    rw [lv_zero] at hB
    exact Or.inl (disp_of_mem_E c (mem_E_of_blk_eq_one c hg hB) hy.1)
  refine eq_zero_or_eq_of_forall_dotProduct cc _ hc0 fun f hf => ?_
  obtain ⟨h, hh, hhB⟩ := c.exists_mem_cent (lv cc f) (det_lv hf)
  have hvB : vecMul v (lv cc f) = v := by rw [vecMul_lv, hcc, zero_smul, add_zero]
  have hy' : Over c v (h * y * h⁻¹) :=
    ⟨c.conj_mem_E hh hy.1, top_conj_eq c hh hy.1 hy.2.1 (by rw [hhB]; exact hvB),
      by rw [conj_pow, hy.2.2, mul_one, mul_inv_cancel]⟩
  have hg' : h * g * h⁻¹ ∈ H ⊓ Subgroup.centralizer ({t} : Set G) :=
    mul_mem (mul_mem hh hg) (inv_mem hh)
  have hB' : blk (c.mat (h * g * h⁻¹)) = blk (c.mat g) := by
    rw [blk_mul_of_mem c (mul_mem hh hg) (H.inv_mem hh.1), blk_mul_of_mem c hh hg.1, hB, hhB,
      lv_comm hf hcc, mul_assoc, ← hhB, blk_mul_inv c hh, mul_one]
  have h1 := disp_conj c hh hT
  have hT' := mem_T_of_fix c hg hy'.1 (fix_of_over c hcc hB hy')
  rw [disp_of_blk_eq c hg hg' hy'.1 hB' hT', disp_over_eq c hg hcc hB hy hy', hhB,
    lv_mulVec] at h1
  have h2 : (f ⬝ᵥ disp c g y) • cc = 0 := add_eq_left.1 h1.symm
  rcases zmod_two_eq_zero_or_one (f ⬝ᵥ disp c g y) with h3 | h3
  · exact h3
  · rw [h3, one_smul] at h2
    exact absurd h2 hc0

theorem moves_or_fixes (v : Fin 3 → ZMod 2) : Moves c v ∨ Fixes c v := by
  by_cases hF : Fixes c v
  · exact Or.inr hF
  left
  simp only [Fixes, not_forall] at hF
  obtain ⟨g₁, hg₁, c₁, hc₁, hB₁, y₁, hy₁, hd₁⟩ := hF
  have hd₁' : disp c g₁ y₁ = c₁ := (disp_eq_zero_or c hg₁ hc₁ hB₁ hy₁).resolve_left hd₁
  have hc₁0 : c₁ ≠ 0 := fun h => hd₁ (hd₁'.trans h)
  have hT₁ := mem_T_of_fix c hg₁ hy₁.1 (fix_of_over c hc₁ hB₁ hy₁)
  intro g hg cc hcc hB y hy
  rcases disp_eq_zero_or c hg hcc hB hy with h | h
  · by_contra hne
    have hcc0 : cc ≠ 0 := fun h0 => hne (h.trans h0.symm)
    have hgy₁ : disp c g y₁ = 0 := (disp_over_eq c hg hcc hB hy hy₁).trans h
    have hT := mem_T_of_fix c hg hy₁.1 (fix_of_over c hcc hB hy₁)
    by_cases heq : cc = c₁
    · subst heq
      rw [disp_of_blk_eq c hg₁ hg hy₁.1 (hB.trans hB₁.symm) hT₁, hd₁'] at hgy₁
      exact hc₁0 hgy₁
    · have hB₁₂ : blk (c.mat (g₁ * g)) = lv (c₁ + cc) v := by
        rw [blk_mul_of_mem c hg₁ hg.1, hB₁, hB, lv_mul_lv hcc]
      have hcs : v ⬝ᵥ (c₁ + cc) = 0 := by rw [dotProduct_add, hc₁, hcc, add_zero]
      have h12 := disp_mul c hg₁ hT₁ hT
      rw [hd₁', hgy₁, mulVec_zero, add_zero] at h12
      rcases disp_eq_zero_or c (mul_mem hg₁ hg) hcs hB₁₂ hy₁ with h' | h'
      · exact hc₁0 (h12.symm.trans h')
      · exact hcc0 (add_eq_left.1 (h'.symm.trans h12))
  · exact h

theorem fixes_of_conj {v v' : Fin 3 → ZMod 2} {k : G}
    (hk : k ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (hvv : vecMul v' (blk (c.mat k)) = v)
    (hF : Fixes c v) : Fixes c v' := by
  intro g' hg' cc' hcc' hB' y' hy'
  have hk' : k⁻¹ ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := inv_mem hk
  have hBg : blk (c.mat (k⁻¹ * g' * k⁻¹⁻¹)) = lv (blk (c.mat k⁻¹) *ᵥ cc') v := by
    rw [blk_mul_of_mem c (mul_mem hk' hg') (H.inv_mem hk'.1), blk_mul_of_mem c hk' hg'.1, hB',
      inv_inv, lv_conj (blk_inv_mul c hk) cc' v', hvv]
  have hcc : v ⬝ᵥ (blk (c.mat k⁻¹) *ᵥ cc') = 0 := by
    rw [dotProduct_mulVec, ← hvv, vecMul_vecMul, blk_mul_inv c hk, vecMul_one, hcc']
  have hy : Over c v (k⁻¹ * y' * k⁻¹⁻¹) :=
    ⟨c.conj_mem_E hk' hy'.1, by rw [top_conj c hk' hy'.1, inv_inv, hy'.2.1, hvv],
      by rw [conj_pow, hy'.2.2, mul_one, mul_inv_cancel]⟩
  have h0 := hF _ (mul_mem (mul_mem hk' hg') (inv_mem hk')) _ hcc hBg _ hy
  have hT' := mem_T_of_fix c hg' hy'.1 (fix_of_over c hcc' hB' hy')
  rw [disp_conj c hk' hT'] at h0
  have h1 := congrArg (blk (c.mat k) *ᵥ ·) h0
  rwa [mulVec_mulVec, blk_mul_inv c hk, one_mulVec, mulVec_zero] at h1

end CFSG.CGT.M24S.NSB
