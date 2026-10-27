module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace CFSG.FeitThompson

open Module Submodule LinearMap Pointwise

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {N : End k V}

theorem apply_apply_eq_zero_of_sq_eq_zero (hN : N ^ 2 = 0) (x : V) : N (N x) = 0 := by
  have : (N * N) x = 0 := by rw [show N * N = N ^ 2 from (pow_two N).symm, hN]; rfl
  simpa using this

theorem smul_mul_smul_eq_zero_of_sq_eq_zero (hN : N ^ 2 = 0) (c d : k) :
    (c • N) * (d • N) = 0 := by
  rw [smul_mul_smul_comm, show N * N = N ^ 2 from (pow_two N).symm, hN, smul_zero]

def oneAddSMulUnit (hN : N ^ 2 = 0) (c : k) : (End k V)ˣ where
  val := 1 + c • N
  inv := 1 - c • N
  val_inv := by
    rw [mul_sub, mul_one, add_mul, one_mul, smul_mul_smul_eq_zero_of_sq_eq_zero hN, add_zero,
      add_sub_cancel_right]
  inv_val := by
    rw [mul_add, mul_one, sub_mul, one_mul, smul_mul_smul_eq_zero_of_sq_eq_zero hN, sub_zero,
      sub_add_cancel]

@[simp]
theorem oneAddSMulUnit_coe (hN : N ^ 2 = 0) (c : k) :
    (oneAddSMulUnit hN c : End k V) = 1 + c • N := (rfl)

theorem oneAddSMulUnit_apply (hN : N ^ 2 = 0) (c : k) (x : V) :
    (oneAddSMulUnit hN c : End k V) x = x + c • N x := by
  rw [oneAddSMulUnit_coe]; simp

@[simp]
theorem oneAddSMulUnit_zero (hN : N ^ 2 = 0) : oneAddSMulUnit hN (0 : k) = 1 :=
  Units.ext <| by rw [oneAddSMulUnit_coe, Units.val_one, zero_smul, add_zero]

theorem oneAddSMulUnit_add (hN : N ^ 2 = 0) (c d : k) :
    oneAddSMulUnit hN (c + d) = oneAddSMulUnit hN c * oneAddSMulUnit hN d :=
  Units.ext <| by
    rw [Units.val_mul, oneAddSMulUnit_coe, oneAddSMulUnit_coe, oneAddSMulUnit_coe, add_mul,
      one_mul, mul_add, mul_one, smul_mul_smul_eq_zero_of_sq_eq_zero hN, add_zero, add_smul]
    abel

def oneAddSMulHom (hN : N ^ 2 = 0) : Multiplicative k →* (End k V)ˣ where
  toFun c := oneAddSMulUnit hN c.toAdd
  map_one' := oneAddSMulUnit_zero hN
  map_mul' c d := oneAddSMulUnit_add hN c.toAdd d.toAdd

theorem oneAddSMulHom_apply (hN : N ^ 2 = 0) (c : Multiplicative k) :
    oneAddSMulHom hN c = oneAddSMulUnit hN c.toAdd := (rfl)

def oneAddSMulGroup (hN : N ^ 2 = 0) : Subgroup (End k V)ˣ := (oneAddSMulHom hN).range

theorem oneAddSMulUnit_mem_oneAddSMulGroup (hN : N ^ 2 = 0) (c : k) :
    oneAddSMulUnit hN c ∈ oneAddSMulGroup hN :=
  ⟨Multiplicative.ofAdd c, by rw [oneAddSMulHom_apply]; rfl⟩

theorem mem_oneAddSMulGroup_iff {hN : N ^ 2 = 0} {u : (End k V)ˣ} :
    u ∈ oneAddSMulGroup hN ↔ ∃ c : k, (u : End k V) = 1 + c • N := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.toAdd, by rw [oneAddSMulHom_apply, oneAddSMulUnit_coe]⟩
  · rintro ⟨c, hc⟩
    refine ⟨Multiplicative.ofAdd c, Units.ext ?_⟩
    rw [oneAddSMulHom_apply, oneAddSMulUnit_coe, hc]
    rfl

theorem smul_submodule_eq_map (u : (End k V)ˣ) (L : Submodule k V) :
    u • L = L.map (u : End k V) := by
  rw [Units.smul_def, Submodule.pointwise_smul_def]; rfl

theorem oneAddSMulUnit_smul_span_singleton (hN : N ^ 2 = 0) (c : k) (w : V) :
    oneAddSMulUnit hN c • (k ∙ w) = k ∙ (w + c • N w) := by
  rw [smul_submodule_eq_map, Submodule.map_span, Set.image_singleton, oneAddSMulUnit_apply]

theorem oneAddSMulUnit_smul_ker (hN : N ^ 2 = 0) (c : k) :
    oneAddSMulUnit hN c • ker N = ker N := by
  rw [smul_submodule_eq_map]
  refine le_antisymm ?_ fun y hy => ⟨y, hy, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [oneAddSMulUnit_apply, LinearMap.mem_ker.1 hx, smul_zero, add_zero]
    exact hx
  · rw [oneAddSMulUnit_apply, LinearMap.mem_ker.1 hy, smul_zero, add_zero]

theorem oneAddSMulUnit_smul_span_add_smul (hN : N ^ 2 = 0) (w : V) (t c : k) :
    oneAddSMulUnit hN c • (k ∙ (w + t • N w)) = k ∙ (w + (t + c) • N w) := by
  rw [oneAddSMulUnit_smul_span_singleton, show
    (w + t • N w) + c • N (w + t • N w) = w + (t + c) • N w by
      rw [map_add, map_smul, apply_apply_eq_zero_of_sq_eq_zero hN, smul_zero, add_zero, add_smul]
      abel]

theorem finrank_ker_eq_one_of_sq_eq_zero (hV : finrank k V = 2) (hN0 : N ≠ 0) (hN : N ^ 2 = 0) :
    finrank k (ker N) = 1 := by
  have : FiniteDimensional k V := .of_finrank_eq_succ hV
  have hle : range N ≤ ker N := by
    rw [LinearMap.range_le_ker_iff, ← Module.End.mul_eq_comp, ← pow_two, hN]
  have h1 : finrank k (range N) + finrank k (ker N) = 2 := by
    rw [LinearMap.finrank_range_add_finrank_ker, hV]
  have hr : range N ≠ ⊥ := by simpa [LinearMap.range_eq_bot] using hN0
  have hr1 : 1 ≤ finrank k (range N) := Submodule.one_le_finrank_iff.2 hr
  have hk1 : 1 ≤ finrank k (ker N) :=
    Submodule.one_le_finrank_iff.2 fun h => hr (le_bot_iff.1 (h ▸ hle))
  omega

theorem exists_notMem_ker (hN0 : N ≠ 0) : ∃ w : V, w ∉ ker N := by
  by_contra h
  exact hN0 (LinearMap.ker_eq_top.1 (Submodule.eq_top_iff'.2 (by simpa using h)))

theorem linearIndependent_pair_of_notMem_ker (hN : N ^ 2 = 0) {w : V} (hw : w ∉ ker N) :
    LinearIndependent k ![w, N w] := by
  have hNw : N w ≠ 0 := by simpa [LinearMap.mem_ker] using hw
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : N (s • w + t • N w) = 0 := by rw [hst, map_zero]
  rw [map_add, map_smul, map_smul, apply_apply_eq_zero_of_sq_eq_zero hN, smul_zero,
    add_zero] at h1
  have hs : s = 0 := by
    rcases smul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h hNw
  refine ⟨hs, ?_⟩
  rw [hs, zero_smul, zero_add] at hst
  rcases smul_eq_zero.1 hst with h | h
  · exact h
  · exact absurd h hNw

theorem span_pair_eq_top_of_notMem_ker (hV : finrank k V = 2) (hN : N ^ 2 = 0) {w : V}
    (hw : w ∉ ker N) : span k ({w, N w} : Set V) = ⊤ := by
  have h := (linearIndependent_pair_of_notMem_ker hN hw).span_eq_top_of_card_eq_finrank
    (by simp [hV])
  rw [show Set.range ![w, N w] = {w, N w} by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]] at h
  exact h

theorem notMem_ker_add_smul (hN : N ^ 2 = 0) {w : V} (hw : w ∉ ker N) (t : k) :
    w + t • N w ∉ ker N := by
  simp only [LinearMap.mem_ker, map_add, map_smul, apply_apply_eq_zero_of_sq_eq_zero hN,
    smul_zero, add_zero] at hw ⊢
  exact hw

theorem finrank_span_add_smul (hN : N ^ 2 = 0) {w : V} (hw : w ∉ ker N) (t : k) :
    finrank k (k ∙ (w + t • N w)) = 1 :=
  finrank_span_singleton fun h => notMem_ker_add_smul hN hw t (h ▸ Submodule.zero_mem _)

theorem span_add_smul_ne_ker (hN : N ^ 2 = 0) {w : V} (hw : w ∉ ker N) (t : k) :
    (k ∙ (w + t • N w)) ≠ ker N := fun h =>
  notMem_ker_add_smul hN hw t (h ▸ Submodule.mem_span_singleton_self _)

theorem exists_eq_span_add_smul (hV : finrank k V = 2) (hN0 : N ≠ 0) (hN : N ^ 2 = 0) {w : V}
    (hw : w ∉ ker N) {L : Submodule k V} (hL : finrank k L = 1) (hne : L ≠ ker N) :
    ∃ t : k, L = k ∙ (w + t • N w) := by
  have hfd : FiniteDimensional k V := .of_finrank_eq_succ hV
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.1 hL.ge)
  have hLv : L = k ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hL hv hv0
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1
    (by rw [span_pair_eq_top_of_notMem_ker hV hN hw]; trivial : v ∈ span k ({w, N w} : Set V))
  have ha : a ≠ 0 := by
    intro h
    rw [h, zero_smul, zero_add] at hab
    have hle : L ≤ ker N := by
      rw [hLv, Submodule.span_singleton_le_iff_mem, ← hab]
      simp [LinearMap.mem_ker, apply_apply_eq_zero_of_sq_eq_zero hN]
    exact hne (Submodule.eq_of_le_of_finrank_eq hle
      (by rw [hL, finrank_ker_eq_one_of_sq_eq_zero hV hN0 hN]))
  refine ⟨a⁻¹ * b, ?_⟩
  rw [hLv, ← Submodule.span_singleton_smul_eq (IsUnit.inv (isUnit_iff_ne_zero.2 ha)) v, ← hab,
    smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem span_add_smul_injective (hN : N ^ 2 = 0) {w : V} (hw : w ∉ ker N) :
    Function.Injective fun t : k => k ∙ (w + t • N w) := by
  intro s t h
  simp only at h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    (show w + s • N w ∈ k ∙ (w + t • N w) by
      rw [← h]; exact Submodule.mem_span_singleton_self _)
  have ha' : a • w + (a * t) • N w = (1 : k) • w + s • N w := by
    rw [← smul_smul, ← smul_add, ha, one_smul]
  obtain ⟨rfl, h2⟩ := (linearIndependent_pair_of_notMem_ker hN hw).eq_of_pair ha'
  rw [one_mul] at h2
  exact h2.symm

theorem exists_mem_oneAddSMulGroup_smul_eq (hV : finrank k V = 2) (hN0 : N ≠ 0) (hN : N ^ 2 = 0)
    {L₁ L₂ : Submodule k V} (hL₁ : finrank k L₁ = 1) (hL₂ : finrank k L₂ = 1)
    (hne₁ : L₁ ≠ ker N) (hne₂ : L₂ ≠ ker N) :
    ∃ u ∈ oneAddSMulGroup hN, u • L₁ = L₂ := by
  obtain ⟨w, hw⟩ := exists_notMem_ker hN0
  obtain ⟨t₁, rfl⟩ := exists_eq_span_add_smul hV hN0 hN hw hL₁ hne₁
  obtain ⟨t₂, rfl⟩ := exists_eq_span_add_smul hV hN0 hN hw hL₂ hne₂
  refine ⟨oneAddSMulUnit hN (t₂ - t₁), oneAddSMulUnit_mem_oneAddSMulGroup hN _, ?_⟩
  rw [oneAddSMulUnit_smul_span_add_smul, add_sub_cancel]

theorem card_lines_ne_ker (hV : finrank k V = 2) (hN0 : N ≠ 0) (hN : N ^ 2 = 0) :
    Nat.card {L : Submodule k V // finrank k L = 1 ∧ L ≠ ker N} = Nat.card k := by
  obtain ⟨w, hw⟩ := exists_notMem_ker hN0
  refine (Nat.card_eq_of_bijective
    (fun t : k => (⟨k ∙ (w + t • N w),
      finrank_span_add_smul hN hw t, span_add_smul_ne_ker hN hw t⟩ :
      {L : Submodule k V // finrank k L = 1 ∧ L ≠ ker N})) ⟨?_, ?_⟩).symm
  · intro s t h
    exact span_add_smul_injective hN hw (congrArg Subtype.val h)
  · rintro ⟨L, hL, hne⟩
    obtain ⟨t, rfl⟩ := exists_eq_span_add_smul hV hN0 hN hw hL hne
    exact ⟨t, rfl⟩

theorem card_lines_ne_ker_zmod {p : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    [Fact p.Prime] {M : End (ZMod p) W} (hW : finrank (ZMod p) W = 2) (hM0 : M ≠ 0)
    (hM : M ^ 2 = 0) :
    Nat.card {L : Submodule (ZMod p) W // finrank (ZMod p) L = 1 ∧ L ≠ ker M} = p := by
  rw [card_lines_ne_ker hW hM0 hM, Nat.card_zmod]

end
end CFSG.FeitThompson
