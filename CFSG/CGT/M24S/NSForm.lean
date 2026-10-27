module

public import CFSG.CGT.M24S.NSGL3
public import CFSG.CGT.M24S.NSSecondBasic

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

theorem blk_mul_of_mem {g g' : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (hg' : g' ∈ H) : blk (c.mat (g * g')) = blk (c.mat g) * blk (c.mat g') := by
  rw [c.mat_mul hg.1 hg', blk_mul _ _ (c.mat_mulVec_e0 hg)]

theorem blk_inv_mul {g : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) :
    blk (c.mat g⁻¹) * blk (c.mat g) = 1 := by
  rw [← blk_mul_of_mem c (inv_mem hg) hg.1, inv_mul_cancel, c.mat_one, blk_one]

theorem blk_mul_inv {g : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) :
    blk (c.mat g) * blk (c.mat g⁻¹) = 1 := by
  rw [← blk_mul_of_mem c hg (H.inv_mem hg.1), mul_inv_cancel, c.mat_one, blk_one]

theorem mem_E_of_blk_eq_one {g : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (h : blk (c.mat g) = 1) : g ∈ c.E :=
  (c.mem_E_iff).2 ⟨hg.1, c.mat_mulVec_e0 hg, h⟩

theorem commute_t {g : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) :
    g * t = t * g :=
  Subgroup.mem_centralizer_singleton_iff.1 hg.2

theorem tail_vec_conj {g s : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (hs : s ∈ T) : tail (c.vec (g * s * g⁻¹)) = blk (c.mat g) *ᵥ tail (c.vec s) := by
  rw [c.vec_conj hg.1 hs, tail_mulVec _ (c.mat_mulVec_e0 hg)]

theorem top_conj_eq {g y : G} {v : Fin 3 → ZMod 2}
    (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (hy : y ∈ c.E)
    (hyv : top (c.mat y) = v) (hv : vecMul v (blk (c.mat g)) = v) :
    top (c.mat (g * y * g⁻¹)) = v := by
  have h1 := c.vecMul_top_conj hg hy
  calc top (c.mat (g * y * g⁻¹))
      = vecMul (vecMul (top (c.mat (g * y * g⁻¹))) (blk (c.mat g))) (blk (c.mat g⁻¹)) := by
        rw [vecMul_vecMul, blk_mul_inv c hg, vecMul_one]
    _ = vecMul (vecMul v (blk (c.mat g))) (blk (c.mat g⁻¹)) := by rw [h1, hyv, hv]
    _ = v := by rw [vecMul_vecMul, blk_mul_inv c hg, vecMul_one]

theorem conj_mem_E_eq {e y : G} (he : e ∈ c.E) (hy : y ∈ c.E) :
    e * y * e⁻¹ = y ∨ e * y * e⁻¹ = y * t := by
  have h := c.isExtraspecialAt_E.2.2.2.2.2 y hy e⁻¹ (c.E.inv_mem he)
  rw [inv_inv] at h
  have key : e * y * e⁻¹ = y * (y⁻¹ * e * y * e⁻¹) := by group
  rcases h with h | h
  · left
    rw [key, h, mul_one]
  · right
    rw [key, h]

theorem eq_one_or_eq_t_of_tail_eq_zero {s : G} (hs : s ∈ T) (h : tail (c.vec s) = 0) :
    s = 1 ∨ s = t := by
  rcases eq_zero_or_eq_e0_of_tail_eq_zero h with h | h
  · exact Or.inl (c.eq_of_vec_eq hs T.one_mem (h.trans c.vec_one.symm))
  · exact Or.inr (c.eq_of_vec_eq hs c.mem (h.trans c.vec_z.symm))

theorem tail_vec_one : tail (c.vec 1) = 0 := by
  rw [c.vec_one, tail_zero]

theorem tail_vec_t : tail (c.vec t) = 0 := by
  rw [c.vec_z, tail_e0]

include c in
theorem mul_self_of_mem_T {s : G} (hs : s ∈ T) : s * s = 1 :=
  c.eq_of_vec_eq (T.mul_mem hs hs) T.one_mem (by rw [c.vec_mul hs hs, vec_add_self, c.vec_one])

include c in
theorem commute_of_mem_T {s s' : G} (hs : s ∈ T) (hs' : s' ∈ T) : s * s' = s' * s :=
  c.eq_of_vec_eq (T.mul_mem hs hs') (T.mul_mem hs' hs)
    (by rw [c.vec_mul hs hs', c.vec_mul hs' hs, add_comm])

theorem sq_mul_of_dot_zero {y s : G} (hy : y ∈ c.E) (hs : s ∈ T)
    (h : top (c.mat y) ⬝ᵥ tail (c.vec s) = 0) : (y * s) ^ 2 = y ^ 2 := by
  have h1 := conj_eq_of_dotProduct_eq_zero c hy hs h
  have h2 : s * y = y * s := by
    calc s * y = s * y * s⁻¹ * s := by group
      _ = y * s := by rw [h1]
  calc (y * s) ^ 2 = y * (s * y) * s := by simp only [pow_two, mul_assoc]
    _ = y ^ 2 * (s * s) := by rw [h2, pow_two]; simp only [mul_assoc]
    _ = y ^ 2 := by rw [mul_self_of_mem_T c hs, mul_one]

theorem sq_mul_of_dot_one {y s : G} (hy : y ∈ c.E) (hs : s ∈ T)
    (h : top (c.mat y) ⬝ᵥ tail (c.vec s) = 1) : (y * s) ^ 2 = y ^ 2 * t := by
  have h1 := conj_eq_of_dotProduct_eq_one c hy hs h
  have h2 : s * y = y * t * s := by
    calc s * y = s * y * s⁻¹ * s := by group
      _ = y * t * s := by rw [h1]
  calc (y * s) ^ 2 = y * (s * y) * s := by simp only [pow_two, mul_assoc]
    _ = y ^ 2 * t * (s * s) := by rw [h2, pow_two]; simp only [mul_assoc]
    _ = y ^ 2 * t := by rw [mul_self_of_mem_T c hs, mul_one]

theorem centreTransvecting_of_mem_E {e : G} (he : e ∈ c.E) : CentreTransvecting T t e := by
  intro s hs
  obtain ⟨hm, hv⟩ := vec_commutator c (c.E.inv_mem he) hs
  rw [inv_inv] at hm hv
  rcases zmod_two_eq_zero_or_one (top (c.mat e⁻¹) ⬝ᵥ tail (c.vec s)) with h | h
  · rw [h, zero_smul] at hv
    exact Or.inl (c.eq_of_vec_eq hm T.one_mem (hv.trans c.vec_one.symm))
  · rw [h, one_smul] at hv
    exact Or.inr (c.eq_of_vec_eq hm c.mem (hv.trans c.vec_z.symm))

theorem vecMul_lv (u cc v : Fin 3 → ZMod 2) : vecMul u (lv cc v) = u + (u ⬝ᵥ cc) • v :=
  vecMul_one_add_vecMulVec cc v u

theorem lv_mulVec (cc v w : Fin 3 → ZMod 2) : lv cc v *ᵥ w = w + (v ⬝ᵥ w) • cc :=
  one_add_vecMulVec_mulVec cc v w

theorem vecMul_lv_self {cc v : Fin 3 → ZMod 2} (h : v ⬝ᵥ cc = 0) : vecMul v (lv cc v) = v := by
  rw [vecMul_lv, h, zero_smul, add_zero]

theorem lv_mul_self {cc v : Fin 3 → ZMod 2} (h : v ⬝ᵥ cc = 0) : lv cc v * lv cc v = 1 :=
  one_add_vecMulVec_mul_self h

theorem det_lv {cc v : Fin 3 → ZMod 2} (h : v ⬝ᵥ cc = 0) : (lv cc v).det = 1 :=
  det_eq_one_of_mul_self (lv_mul_self h)

theorem lv_mul_lv {c₁ c₂ v : Fin 3 → ZMod 2} (h : v ⬝ᵥ c₂ = 0) :
    lv c₁ v * lv c₂ v = lv (c₁ + c₂) v := by
  simp only [lv, add_mul, mul_add, one_mul, mul_one, vecMulVec_mul_vecMulVec, h, zero_smul,
    vecMulVec_zero, add_zero, add_vecMulVec, add_assoc]

@[expose] noncomputable def disp (g y : G) : Fin 3 → ZMod 2 := tail (c.vec (y⁻¹ * g * y * g⁻¹))

theorem mem_T_of_fix {g y : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (hy : y ∈ c.E) (hv : vecMul (top (c.mat y)) (blk (c.mat g)) = top (c.mat y)) :
    y⁻¹ * g * y * g⁻¹ ∈ T := by
  have hy' := c.conj_mem_E hg hy
  have htop := top_conj_eq c hg hy rfl hv
  have e : y⁻¹ * g * y * g⁻¹ = y⁻¹ * (g * y * g⁻¹) := by group
  rw [e]
  apply mem_T_of_top_eq_zero c (c.E.mul_mem (c.E.inv_mem hy) hy')
  rw [top_mul_of_mem_E c (c.E.inv_mem hy) hy', top_inv_of_mem_E c hy, htop, vec_add_self]

theorem disp_eq_zero_iff {g y : G} (hT : y⁻¹ * g * y * g⁻¹ ∈ T) :
    disp c g y = 0 ↔ g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y * t := by
  have e : g * y * g⁻¹ = y * (y⁻¹ * g * y * g⁻¹) := by group
  constructor
  · intro h
    rcases eq_one_or_eq_t_of_tail_eq_zero c hT h with h1 | h1
    · left
      rw [e, h1, mul_one]
    · right
      rw [e, h1]
  · rintro (h | h)
    · have h1 : y⁻¹ * g * y * g⁻¹ = 1 := by
        rw [show y⁻¹ * g * y * g⁻¹ = y⁻¹ * (g * y * g⁻¹) by group, h, inv_mul_cancel]
      rw [disp, h1, tail_vec_one]
    · have h1 : y⁻¹ * g * y * g⁻¹ = t := by
        rw [show y⁻¹ * g * y * g⁻¹ = y⁻¹ * (g * y * g⁻¹) by group, h, inv_mul_cancel_left]
      rw [disp, h1, tail_vec_t]

theorem disp_of_mem_E {e y : G} (he : e ∈ c.E) (hy : y ∈ c.E) : disp c e y = 0 := by
  have hT : y⁻¹ * e * y * e⁻¹ ∈ T := by
    rw [show y⁻¹ * e * y * e⁻¹ = y⁻¹ * (e * y * e⁻¹) by group]
    rcases conj_mem_E_eq c he hy with h | h <;> rw [h]
    · rw [inv_mul_cancel]
      exact T.one_mem
    · rw [inv_mul_cancel_left]
      exact c.mem
  exact (disp_eq_zero_iff c hT).2 (conj_mem_E_eq c he hy)

theorem disp_mul_right {g y s : G} {cc : Fin 3 → ZMod 2}
    (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (hs : s ∈ T)
    (hB : blk (c.mat g) = lv cc (top (c.mat y))) (hT : y⁻¹ * g * y * g⁻¹ ∈ T) :
    disp c g (y * s) = disp c g y + (top (c.mat y) ⬝ᵥ tail (c.vec s)) • cc := by
  have hc : g * s * g⁻¹ ∈ T := c.conj_mem hg.1 hs
  have e : (y * s)⁻¹ * g * (y * s) * g⁻¹ = s⁻¹ * (y⁻¹ * g * y * g⁻¹) * (g * s * g⁻¹) := by
    group
  rw [disp, e, c.vec_mul (T.mul_mem (T.inv_mem hs) hT) hc, c.vec_mul (T.inv_mem hs) hT,
    vec_inv c hs, GL4.tail_add, GL4.tail_add, tail_vec_conj c hg hs, hB, lv_mulVec, disp]
  rw [add_comm (tail (c.vec s)) (tail (c.vec (y⁻¹ * g * y * g⁻¹))), add_assoc, ← add_assoc
    (tail (c.vec s)), vec_add_self, zero_add]

theorem disp_of_blk_eq {g g' y : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (hg' : g' ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (hy : y ∈ c.E)
    (hb : blk (c.mat g') = blk (c.mat g)) (hT : y⁻¹ * g * y * g⁻¹ ∈ T) :
    disp c g' y = disp c g y := by
  have he : g⁻¹ * g' ∈ c.E := by
    refine mem_E_of_blk_eq_one c (mul_mem (inv_mem hg) hg') ?_
    rw [blk_mul_of_mem c (inv_mem hg) hg'.1, hb, blk_inv_mul c hg]
  have e : y⁻¹ * g' * y * g'⁻¹ =
      y⁻¹ * g * ((g⁻¹ * g') * y * (g⁻¹ * g')⁻¹) * g⁻¹ := by group
  rw [disp, e]
  rcases conj_mem_E_eq c he hy with h | h
  · rw [h, disp]
  · have e2 : y⁻¹ * g * (y * t) * g⁻¹ = (y⁻¹ * g * y * g⁻¹) * (g * t * g⁻¹) := by group
    rw [h, e2, show g * t * g⁻¹ = t by rw [commute_t hg, mul_inv_cancel_right],
      c.vec_mul hT c.mem, GL4.tail_add, tail_vec_t, add_zero, disp]

theorem disp_conj {h g y : G} (hh : h ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (hT : y⁻¹ * g * y * g⁻¹ ∈ T) :
    disp c (h * g * h⁻¹) (h * y * h⁻¹) = blk (c.mat h) *ᵥ disp c g y := by
  have e : (h * y * h⁻¹)⁻¹ * (h * g * h⁻¹) * (h * y * h⁻¹) * (h * g * h⁻¹)⁻¹ =
      h * (y⁻¹ * g * y * g⁻¹) * h⁻¹ := by group
  rw [disp, e, tail_vec_conj c hh hT, disp]

theorem disp_mul {g₁ g₂ y : G} (hg₁ : g₁ ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (hT₁ : y⁻¹ * g₁ * y * g₁⁻¹ ∈ T) (hT₂ : y⁻¹ * g₂ * y * g₂⁻¹ ∈ T) :
    disp c (g₁ * g₂) y = disp c g₁ y + blk (c.mat g₁) *ᵥ disp c g₂ y := by
  have e : y⁻¹ * (g₁ * g₂) * y * (g₁ * g₂)⁻¹ =
      (y⁻¹ * g₁ * y * g₁⁻¹) * (g₁ * (y⁻¹ * g₂ * y * g₂⁻¹) * g₁⁻¹) := by group
  rw [disp, e, c.vec_mul hT₁ (c.conj_mem hg₁.1 hT₂), GL4.tail_add, tail_vec_conj c hg₁ hT₂, disp,
    disp]

theorem top_conj {g y : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (hy : y ∈ c.E) :
    top (c.mat (g * y * g⁻¹)) = vecMul (top (c.mat y)) (blk (c.mat g⁻¹)) := by
  rw [← c.vecMul_top_conj hg hy, vecMul_vecMul, blk_mul_inv c hg, vecMul_one]

theorem lv_conj {P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : P * Q = 1) (cc w : Fin 3 → ZMod 2) :
    P * lv cc w * Q = lv (P *ᵥ cc) (vecMul w Q) := by
  rw [lv, lv, mul_add, add_mul, mul_one, h, mul_vecMulVec, vecMulVec_mul]

theorem lv_comm {cc f v : Fin 3 → ZMod 2} (hf : f ⬝ᵥ cc = 0) (hv : v ⬝ᵥ cc = 0) :
    lv cc f * lv cc v = lv cc v * lv cc f := by
  simp only [lv, add_mul, mul_add, one_mul, mul_one, vecMulVec_mul_vecMulVec, hf, hv, zero_smul,
    vecMulVec_zero, add_zero]
  abel

@[expose] def Over (v : Fin 3 → ZMod 2) (y : G) : Prop :=
  y ∈ c.E ∧ top (c.mat y) = v ∧ y ^ 2 = 1

@[expose] def Moves (v : Fin 3 → ZMod 2) : Prop :=
  ∀ g ∈ H ⊓ Subgroup.centralizer ({t} : Set G), ∀ cc : Fin 3 → ZMod 2, v ⬝ᵥ cc = 0 →
    blk (c.mat g) = lv cc v → ∀ y : G, Over c v y → disp c g y = cc

@[expose] def Fixes (v : Fin 3 → ZMod 2) : Prop :=
  ∀ g ∈ H ⊓ Subgroup.centralizer ({t} : Set G), ∀ cc : Fin 3 → ZMod 2, v ⬝ᵥ cc = 0 →
    blk (c.mat g) = lv cc v → ∀ y : G, Over c v y → disp c g y = 0

end CFSG.CGT.M24S.NSB
