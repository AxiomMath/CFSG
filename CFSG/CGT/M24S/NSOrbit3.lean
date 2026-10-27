module

public import CFSG.CGT.M24S.NSOrbit2

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

@[expose] def Wset (e : G) : Prop :=
  e ∈ c.E ∧ e ^ 2 = 1 ∧ ∀ g ∈ H ⊓ Subgroup.centralizer ({t} : Set G),
    vecMul (top (c.mat e)) (blk (c.mat g)) = top (c.mat e) → disp c g e = 0

theorem over_of_wset {e : G} (he : Wset c e) : Over c (top (c.mat e)) e :=
  ⟨he.1, rfl, he.2.1⟩

theorem wset_one : Wset c 1 := by
  refine ⟨c.E.one_mem, one_pow 2, fun g hg _ => ?_⟩
  rw [disp, inv_one, one_mul, mul_one, mul_inv_cancel, tail_vec_one]

theorem wset_mul_t {e : G} (he : Wset c e) : Wset c (e * t) := by
  have htE : t ∈ c.E := c.T_le_E c.mem
  have hte : e * t = t * e := (commute_t (c.E_le he.1)).symm.symm
  have htop : top (c.mat (e * t)) = top (c.mat e) := by
    rw [top_mul_of_mem_E c he.1 htE, top_eq_zero_of_mem_T c c.mem, add_zero]
  refine ⟨c.E.mul_mem he.1 htE, ?_, fun g hg hv => ?_⟩
  · rw [pow_two, show e * t * (e * t) = e * e * (t * t) by
      rw [mul_assoc, ← mul_assoc t e t, ← hte]; group, ← pow_two, ← pow_two, he.2.1, c.z_sq,
      one_mul]
  · rw [htop] at hv
    have hT := mem_T_of_fix c hg he.1 hv
    rw [disp_mul_right' c hg c.mem hT, tail_vec_t, zero_add, mulVec_zero, add_zero,
      he.2.2 g hg hv]

theorem wset_t : Wset c t := by
  simpa using wset_mul_t c (wset_one c)

theorem wset_conj {k e : G} (hk : k ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (he : Wset c e) :
    Wset c (k * e * k⁻¹) := by
  refine ⟨c.conj_mem_E hk he.1, by rw [conj_pow, he.2.1, mul_one, mul_inv_cancel],
    fun g hg hv => ?_⟩
  have hk' : k⁻¹ ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := inv_mem hk
  have hg' : k⁻¹ * g * k⁻¹⁻¹ ∈ H ⊓ Subgroup.centralizer ({t} : Set G) :=
    mul_mem (mul_mem hk' hg) (inv_mem hk')
  rw [top_conj c hk he.1] at hv
  have hv' : vecMul (top (c.mat e)) (blk (c.mat (k⁻¹ * g * k⁻¹⁻¹))) = top (c.mat e) := by
    rw [blk_mul_of_mem c (mul_mem hk' hg) (H.inv_mem hk'.1), blk_mul_of_mem c hk' hg.1, inv_inv,
      ← vecMul_vecMul, ← vecMul_vecMul, hv, vecMul_vecMul, blk_inv_mul c hk, vecMul_one]
  have h0 := he.2.2 _ hg' hv'
  have hT := mem_T_of_fix c hg' he.1 hv'
  have h1 := disp_conj c hk hT
  rw [h0, mulVec_zero, show k * (k⁻¹ * g * k⁻¹⁻¹) * k⁻¹ = g by group] at h1
  exact h1

theorem wset_T {s : G} (hs : s ∈ T) (hW : Wset c s) : s = 1 ∨ s = t := by
  refine eq_one_or_eq_t_of_tail_eq_zero c hs ?_
  by_contra hne
  obtain ⟨B, hBB, -, hBw⟩ := exists_transvection (a := v₀) (by decide) hne
  obtain ⟨g, hg, hgB⟩ := c.exists_mem_cent B (det_eq_one_of_mul_self hBB)
  have hv : vecMul (top (c.mat s)) (blk (c.mat g)) = top (c.mat s) := by
    rw [top_eq_zero_of_mem_T c hs, zero_vecMul]
  have h0 := hW.2.2 g hg hv
  have e : s⁻¹ * g * s * g⁻¹ = s⁻¹ * (g * s * g⁻¹) := by group
  rw [disp, e, c.vec_mul (T.inv_mem hs) (c.conj_mem hg.1 hs), vec_inv c hs, GL4.tail_add,
    tail_vec_conj c hg hs, hgB] at h0
  apply hBw
  have h1 := congrArg (· + tail (c.vec s)) h0
  rwa [add_comm (tail (c.vec s)) (B *ᵥ _), add_assoc, vec_add_self, add_zero, zero_add] at h1

theorem wset_unique {e e' : G} (he : Wset c e) (he' : Wset c e')
    (hv : top (c.mat e') = top (c.mat e)) (hv0 : top (c.mat e) ≠ 0) : e' = e ∨ e' = e * t := by
  have ho' : Over c (top (c.mat e)) e' := ⟨he'.1, hv, he'.2.1⟩
  obtain ⟨s, hs, rfl, -⟩ := exists_mul_of_over c (over_of_wset c he) ho'
  suffices h : tail (c.vec s) = 0 by
    rcases eq_one_or_eq_t_of_tail_eq_zero c hs h with h1 | h1 <;> rw [h1]
    · exact Or.inl (mul_one e)
    · exact Or.inr rfl
  by_contra hne
  obtain ⟨B, hBB, hvB, hBw⟩ := exists_transvection hv0 hne
  obtain ⟨g, hg, hgB⟩ := c.exists_mem_cent B (det_eq_one_of_mul_self hBB)
  have hfix : vecMul (top (c.mat e)) (blk (c.mat g)) = top (c.mat e) := by rw [hgB]; exact hvB
  have hT := mem_T_of_fix c hg he.1 hfix
  have h0 := he'.2.2 g hg (by rw [hv]; exact hfix)
  rw [disp_mul_right' c hg hs hT, he.2.2 g hg hfix, add_zero, hgB] at h0
  apply hBw
  have h1 := congrArg (· + tail (c.vec s)) h0
  rwa [add_comm (tail (c.vec s)) (B *ᵥ _), add_assoc, vec_add_self, add_zero, zero_add] at h1

theorem exists_wset (hF : Fixes c v₀) (v : Fin 3 → ZMod 2) : ∃ e : G, Wset c e ∧
    top (c.mat e) = v := by
  by_cases hv : v = 0
  · exact ⟨1, wset_one c, by rw [c.mat_one, top_one, hv]⟩
  obtain ⟨e₀, he₀, hfix⟩ := exists_fixed_over_v₀ c hF
  have hW₀ : Wset c e₀ := ⟨he₀.1, he₀.2.2, fun g hg hv' => hfix g ⟨hg, by rwa [he₀.2.1] at hv'⟩⟩
  obtain ⟨B, hB1, hBv⟩ := exists_vecMul_v₀_eq v hv
  obtain ⟨k, hk, hkB⟩ := c.exists_mem_cent B hB1
  have hk' : k⁻¹ ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := inv_mem hk
  refine ⟨k⁻¹ * e₀ * k⁻¹⁻¹, wset_conj c hk' hW₀, ?_⟩
  rw [top_conj c hk' he₀.1, inv_inv, he₀.2.1, hkB, hBv]

end CFSG.CGT.M24S.NSB
