module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAMC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Generic Wr Equiv

variable {n : ℕ}

theorem eq_of_permBar_eq_one {M B : Subgroup (AEQ n)} {w : AEQ n}
    (h6 : ∀ T : Subgroup (AEQ n), T ≤ M → (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      IsPGroup 2 ↥T → ∀ x ∈ B, x ∈ T → x = 1 ∨ x = w)
    (hBM : B ≤ M) {x : AEQ n} (hx : x ∈ B) (h1 : permBar n x = 1) : x = 1 ∨ x = w := by
  refine h6 ((permBar n).ker ⊓ M) inf_le_right
    (fun g hg t ht => Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr ?_, ?_⟩) ?_ x hx
    (Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr h1, hBM hx⟩)
  · rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp ht.1, mul_one, mul_inv_cancel]
  · exact M.mul_mem (M.mul_mem hg ht.2) (M.inv_mem hg)
  · refine fun g => ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (mul_self_of_permBar_eq_one (MonoidHom.mem_ker.mp g.2.1))

theorem modPi_add_swap {b u q : Fin n → ZMod 2} (h : ModPi (b + u) q) : ModPi (q + b) u := by
  rcases h with h | h
  · left
    funext i
    have h' := congrFun h i
    revert h'
    show b i + u i = q i → q i + b i = u i
    generalize b i = c
    generalize u i = d
    generalize q i = e
    revert c d e
    decide
  · right
    funext i
    have h' := congrFun h i
    revert h'
    show b i + u i = q i + 1 → q i + b i = u i + 1
    generalize b i = c
    generalize u i = d
    generalize q i = e
    revert c d e
    decide

theorem pairCond_of_conj {P : Subgroup (Perm (Fin n))} {B : Subgroup (AEQ n)} {w : AEQ n}
    {u : Fin n → ZMod 2}
    (hwu : w = vbar n u) (hBv : ∀ x ∈ B, permBar n x = 1 → x = 1 ∨ x = w)
    {x y : AEQ n} (hx : x ∈ B) (hy : y ∈ B) (hxy : x * y = w * (y * x))
    (h9 : ∀ g ∈ aeBarOver P, g * w = w * g → conjSub g B = B ∨ Commutes B (conjSub g B))
    (a c : Fin n) : PairCond (permBar n x) (permBar n y) u (pairVec a c) := by
  have hgM : vbar n (pairVec a c) ∈ aeBarOver P := vbar_mem_aeBarOver (sum_pairVec a c)
  have hgw : vbar n (pairVec a c) * w = w * vbar n (pairVec a c) := by
    rw [hwu, ← vbar_add, ← vbar_add, add_comm]
  have hginv : (vbar n (pairVec a c))⁻¹ = vbar n (pairVec a c) :=
    inv_eq_of_mul_eq_one_right (by rw [← vbar_add, add_self_vec, vbar_zero])
  have hconj : ∀ z : AEQ n, vbar n (pairVec a c) * z * (vbar n (pairVec a c))⁻¹ =
      vbar n (pairVec a c + actV (permBar n z) (pairVec a c)) * z := fun z => by
    rw [vbar_add, ← conj_vbar (g := z) rfl, hginv]
    group
  rcases h9 _ hgM hgw with h | h
  · left
    have key : ∀ z ∈ B, ModPi (pairVec a c + actV (permBar n z) (pairVec a c)) 0 ∨
        ModPi (pairVec a c + actV (permBar n z) (pairVec a c)) u := by
      intro z hz
      have hm : vbar n (pairVec a c) * z * (vbar n (pairVec a c))⁻¹ ∈ B := by
        rw [← h]
        exact conj_mem_conjSub hz
      rw [hconj] at hm
      have hm2 := B.mul_mem hm (B.inv_mem hz)
      rw [mul_inv_cancel_right] at hm2
      rcases hBv _ hm2 (permBar_vbar _) with h1 | h1
      · left
        rwa [← vbar_zero, vbar_eq_iff] at h1
      · right
        rwa [hwu, vbar_eq_iff] at h1
    exact ⟨key x hx, key y hy⟩
  · right
    have hc := h x hx _ (conj_mem_conjSub (n := vbar n (pairVec a c)) hy)
    rw [hconj] at hc
    have e2 : ∀ q : Fin n → ZMod 2, x * vbar n q = vbar n (actV (permBar n x) q) * x :=
      fun q => by rw [← conj_vbar (g := x) rfl]; group
    have e3 : vbar n (actV (permBar n x) (pairVec a c + actV (permBar n y) (pairVec a c))) * w =
        vbar n (pairVec a c + actV (permBar n y) (pairVec a c)) := by
      refine mul_right_cancel (b := y * x) ?_
      rw [mul_assoc, ← hxy, ← mul_assoc, ← e2, mul_assoc, hc, mul_assoc]
    rw [hwu, ← vbar_add, vbar_eq_iff] at e3
    exact modPi_add_swap e3

end CFSG.ClassicalInvolution.Q3.TL4
