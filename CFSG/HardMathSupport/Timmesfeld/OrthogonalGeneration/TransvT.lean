module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvGeom

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

omit [Module.Finite (ZMod 2) V] in
theorem transv_invariant {t g : V ≃ₗ[ZMod 2] V} {v : V} {f : V →ₗ[ZMod 2] ZMod 2} (hv : v ≠ 0)
    (htv : ∀ x, t x = x + f x • v) (hc : g * t = t * g) (x : V) : f (g x) = f x := by
  have h1 : f x • g v = f (g x) • v := by
    have := congrArg (fun m : V ≃ₗ[ZMod 2] V => m x) hc
    simp only [LinearEquiv.mul_apply, htv, map_add, map_smul] at this
    exact add_left_cancel this
  rcases IsF2.eq_zero_or_one (f x) with h | h
  · rw [h, zero_smul] at h1
    rcases smul_eq_zero.mp h1.symm with h2 | h2
    · rw [h2, h]
    · exact absurd h2 hv
  · rw [h, one_smul] at h1
    rcases IsF2.eq_zero_or_one (f (g x)) with h2 | h2
    · rw [h2, zero_smul, LinearEquiv.map_eq_zero_iff] at h1
      exact absurd h1 hv
    · rw [h, h2]

theorem exists_mem_fixSub_apply_ne_zero {g : V ≃ₗ[ZMod 2] V} {N : ℕ} (hN : Odd N) (hgN : g ^ N = 1)
    {f : V →ₗ[ZMod 2] ZMod 2} (hf : ∀ x, f (g x) = f x) (hf0 : f ≠ 0) :
    ∃ x ∈ fixSub (Subgroup.zpowers g), f x ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have := finite_linearEquiv (K := ZMod 2) (V := V)
  set E := Subgroup.zpowers g with hE
  have hodd : Odd (Nat.card E) := by
    refine odd_natCard_subgroup_of_pow_eq_one hN fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgN, one_zpow]
  let H : Subgroup (V ≃ₗ[ZMod 2] V) :=
    { carrier := {h | ∀ x, f (h x) = f x}
      one_mem' := fun _ => rfl
      mul_mem' := fun {a b} ha hb x => by rw [LinearEquiv.mul_apply, ha, hb]
      inv_mem' := fun {a} ha x => by
        have := ha (a⁻¹ x)
        rw [LinearEquiv.apply_inv_apply'] at this
        exact this.symm }
  have hEH : E ≤ H := by
    rw [hE, Subgroup.zpowers_le]
    exact hf
  refine ⟨avgOp E y, avgOp_mem_fixSub E y, ?_⟩
  have : Fintype E := Fintype.ofFinite E
  rw [avgOp_eq_sum, map_sum]
  have h2 : ∀ h : E, f ((h : V ≃ₗ[ZMod 2] V) y) = f y := fun h => hEH h.2 y
  simp only [h2, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul (ZMod 2), natCast_eq_one_of_odd hodd,
    one_smul]
  exact hy

theorem not_commute_orthJ_transv {p : ℕ} (hQ : (polarBilin Q).Nondegenerate) (hodd : Odd p)
    {r t : V ≃ₗ[ZMod 2] V} (hr : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hrp : r ^ p = 1)
    {v : V} {f : V →ₗ[ZMod 2] ZMod 2} (hv : v ≠ 0) (hf0 : f ≠ 0)
    (htv : ∀ x, t x = x + f x • v) (hcr : r * t = t * r)
    (hdim : 4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers r))) :
    ¬ ∀ z ∈ orthJ Q (fixSub (Subgroup.zpowers r)), t * z = z * t := by
  intro hall
  have hWnd := polarNondegOn_fixSub_zpowers hQ hodd hr hrp
  have htW : ∀ w, w ∈ fixSub (Subgroup.zpowers r) ↔ t w ∈ fixSub (Subgroup.zpowers r) := by
    intro w
    rw [mem_fixSub_zpowers, mem_fixSub_zpowers]
    have h1 : r (t w) = t (r w) := by
      have := congrArg (fun m : V ≃ₗ[ZMod 2] V => m w) hcr
      exact this.symm ▸ rfl
    rw [h1]
    constructor
    · intro h
      rw [h]
    · intro h
      exact t.injective h
  have hfix := eq_apply_of_commute_orthJ_of_three_le hWnd (by omega) htW hall
  have hinv : ∀ x, f (r x) = f x := transv_invariant hv htv hcr
  obtain ⟨x, hxW, hfx⟩ := exists_mem_fixSub_apply_ne_zero hodd hrp hinv hf0
  have h1 := hfix x hxW
  rw [htv x] at h1
  have h2 : f x • v = 0 := by
    have := congrArg (fun z => z - x) h1
    simpa using this
  rcases smul_eq_zero.mp h2 with h | h
  · exact hfx h
  · exact hv h

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
