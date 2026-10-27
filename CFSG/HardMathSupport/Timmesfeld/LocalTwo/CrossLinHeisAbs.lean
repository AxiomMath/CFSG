module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisMix
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisTop

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module CFSG.RankThree.PartOne.KCLinPlane

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {p : ℕ} [NeZero p] {f : ZMod p → Module.End K V} {t ti : Module.End K V} {c₀ : K}

theorem two_ne_zero_zmod [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h1)

theorem eq_top_of_heisData [Fact p.Prime] [FiniteDimensional K V] [Nontrivial V] (hp2 : p ≠ 2)
    (H : HeisData p f t ti c₀) (hdim : ∀ j, 2 ≤ finrank K (LinearMap.range (f j)))
    (G : Subgroup (V ≃ₗ[K] V)) (hG : ∀ g ∈ G, LinearEquiv.det g = 1)
    (hsupp : ∀ j, suppGroup (f j) ≤ G)
    (hGt : ∀ β : Module.End K V, β * t = t * β → (∀ v, β (β v) = 0) →
      ∃ x ∈ G, ∀ v, x v = v + β v) :
    ∀ g : V ≃ₗ[K] V, LinearEquiv.det g = 1 → g ∈ G := by
  classical
  have hidem' : ∀ j v, f j (f j v) = f j v := H.f_idem_apply
  have hblk : ∀ (y : V), f 0 y = y → ∀ m : ZMod p, f m ((t ^ m.val) y) = (t ^ m.val) y := by
    intro y hy m
    have := H.tpow_apply_block m.val hy
    rwa [zero_add, ZMod.natCast_zmod_val] at this
  refine eq_top_of_peel f H.idem H.orth H.sum hdim G hG hsupp ?_
  intro r s hrs
  have h2 := two_ne_zero_zmod (p := p) hp2
  set j : ZMod p := (r + s) / 2 with hjdef
  have hj2 : 2 * j = r + s := by rw [hjdef]; field_simp
  have hjr : j ≠ r := by
    intro h
    apply hrs
    rw [h] at hj2
    linear_combination hj2
  have hjs : j ≠ s := by
    intro h
    apply hrs
    rw [h] at hj2
    linear_combination -hj2
  refine ⟨j, hjr, hjs, ?_⟩
  set c : ZMod p := j - r with hc
  obtain ⟨y, hy, hy0⟩ : ∃ y, f 0 y = y ∧ y ≠ 0 := by
    obtain ⟨x, hx, hxs⟩ := exists_block_indep (hidem' 0) (hdim 0) 0
    exact ⟨x, hx, fun h => hxs (by rw [h]; exact Submodule.zero_mem _)⟩
  set z : V := (t ^ c.val) y with hzdef
  have hz : f c z = z := hblk y hy c
  have hz0 : z ≠ 0 := H.tpow_ne_zero _ hy0
  obtain ⟨x0, hx0f, hx0⟩ := exists_block_indep (hidem' c) (hdim c) z
  obtain ⟨ξ, hξ, hξz, hξx0⟩ := exists_block_dual (hidem' c) hz hx0f hx0
  have hξz' : ξ ((t ^ c.val) y) = 0 := hξz
  have hsq := H.betaOp_sq hy hξ hξz'
  obtain ⟨x, hxG, hxv⟩ := hGt (betaOp p t ti y ξ) (H.betaOp_comm y ξ) hsq
  refine ⟨x, hxG, betaOp p t ti y ξ, hxv, hsq, ?_, ?_, ?_⟩
  · intro v
    have hjc : j - c = r := by rw [hc]; ring
    rw [H.betaOp_f hξ j v, hjc, map_smul, hblk y hy r]
  · intro v
    have hsc : s - c = j := by rw [hc]; linear_combination -hj2
    rw [H.f_betaOp hy ξ j v, H.betaOp_f hξ s v, hsc, map_smul, hblk y hy j]
  · have hjc : j - c = r := by rw [hc]; ring
    set a : V := (t ^ r.val) x0 with hadef
    have ha : f j a = a := by
      have := H.tpow_apply_block r.val hx0f
      rw [ZMod.natCast_zmod_val] at this
      have e : j = c + r := by rw [hc]; ring
      rw [e]
      exact this
    have hξa : ξ ((ti ^ r.val) a) = ξ x0 := by rw [hadef, H.ti_pow_t_pow_apply]
    have hβa : betaOp p t ti y ξ a = ξ x0 • (t ^ r.val) y := by
      conv_lhs => rw [← ha]
      rw [H.betaOp_f hξ j a, hjc, hξa]
    have hβa0 : betaOp p t ti y ξ a ≠ 0 := by
      rw [hβa]
      exact smul_ne_zero hξx0 (H.tpow_ne_zero _ hy0)
    set b : V := (t ^ j.val) y with hbdef
    have hb : f j b = b := hblk y hy j
    have hb0 : b ≠ 0 := H.tpow_ne_zero _ hy0
    have hbspan : b ∉ Submodule.span K {a} := by
      intro hmem
      obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hmem
      have h1 : ξ ((ti ^ r.val) b) = 0 :=
        H.dual_ti_t_eq_zero hy hξ hξz' (ZMod.val_lt r) (ZMod.val_lt j)
      rw [← hl, map_smul, map_smul, hξa, smul_eq_mul] at h1
      have hl0 : l = 0 := (mul_eq_zero.1 h1).resolve_right hξx0
      apply hb0
      rw [← hl, hl0, zero_smul]
    obtain ⟨α, hα, hαa, hαb⟩ := exists_block_dual (hidem' j) ha hb hbspan
    refine ⟨a, ha, α, hα, hαa, hβa0, (t ^ j.val) x0, ?_⟩
    rw [← hα (betaOp p t ti y ξ ((t ^ j.val) x0)), H.f_betaOp hy ξ j, map_smul,
      H.ti_pow_t_pow_apply, smul_eq_mul]
    exact mul_ne_zero hξx0 hαb

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
