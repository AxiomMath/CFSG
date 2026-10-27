module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankE81

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LBID4

open QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def NDeg (Q : QuadraticForm K V) (M : Submodule K V) : Prop :=
  ∀ v ∈ M, (∀ w ∈ M, polar Q v w = 0) → v = 0

theorem NDeg.exists_ne_zero {M : Submodule K V} (hM : NDeg Q M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, Q v ≠ 0 := by
  obtain ⟨x, hxM, hx0⟩ := (Submodule.ne_bot_iff M).mp hne
  by_contra h
  push Not at h
  apply hx0
  refine hM x hxM fun w hw => ?_
  rw [polar, h _ (M.add_mem hxM hw), h x hxM, h w hw]
  ring

theorem polar_map_of_mem {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (x y : V) : polar Q (g x) (g y) = polar Q x y := by
  have hQ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  simp only [polar, ← map_add, hQ]

namespace EFrame

variable (F : EFrame Q)

@[expose] noncomputable def orthSub : Submodule K V := LinearMap.ker (pol Q F.b) ⊓ LinearMap.ker (pol Q F.b')

theorem mem_orthSub {v : V} : v ∈ F.orthSub ↔ F.Orth v := by
  simp [orthSub, Orth]

@[expose] def plane : Submodule K V := Submodule.span K (Set.range ![F.b, F.b'])

theorem b_mem_plane : F.b ∈ F.plane := Submodule.subset_span ⟨0, rfl⟩

theorem b'_mem_plane : F.b' ∈ F.plane := Submodule.subset_span ⟨1, rfl⟩

theorem plane_le {M : Submodule K V} (hb : F.b ∈ M) (hb' : F.b' ∈ M) : F.plane ≤ M := by
  rw [plane, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hb
  · exact hb'

variable (h3 : (3 : K) ≠ 0)
include h3

theorem linearIndependent_pair : LinearIndependent K ![F.b, F.b'] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hc := F.c_ne
  have e1 := congrArg (pol Q F.b) hst
  have e2 := congrArg (pol Q F.b') hst
  simp only [map_add, map_smul, pol_apply, map_zero, smul_eq_mul, F.polar_bb, F.polar_b'b,
    F.polar_bb', F.polar_b'b'] at e1 e2
  have hs3 : 3 * F.c * s = 0 := by linear_combination 2 * e1 + e2
  have hs : s = 0 := by
    rcases mul_eq_zero.mp hs3 with h | h
    · exact absurd h (mul_ne_zero h3 hc)
    · exact h
  refine ⟨hs, ?_⟩
  rw [hs] at e1
  have : F.c * t = 0 := by linear_combination -e1
  exact (mul_eq_zero.mp this).resolve_left hc

theorem finrank_plane : finrank K F.plane = 2 := by
  rw [plane, finrank_span_eq_card (F.linearIndependent_pair h3)]
  rfl

omit h3 in
theorem proj_mem_plane (v : V) : F.proj v ∈ F.plane := by
  rw [proj_apply]
  exact F.plane.add_mem (F.plane.smul_mem _ F.b_mem_plane) (F.plane.smul_mem _ F.b'_mem_plane)

theorem proj_eq_self_of_mem_plane {v : V} (hv : v ∈ F.plane) : F.proj v = v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · exact F.proj_b h3
    · exact F.proj_b' h3
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

theorem plane_inf_orthSub : F.plane ⊓ F.orthSub = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hv, hvo⟩
  rw [← F.proj_eq_self_of_mem_plane h3 hv, F.proj_of_orth ((F.mem_orthSub).mp hvo)]

theorem split [FiniteDimensional K V] {M : Submodule K V} (hb : F.b ∈ M) (hb' : F.b' ∈ M)
    (hM : NDeg Q M) : NDeg Q (M ⊓ F.orthSub) ∧ finrank K ↥(M ⊓ F.orthSub) + 2 = finrank K M := by
  constructor
  · intro v hv hvw
    refine hM v hv.1 fun w hw => ?_
    have e : w = F.proj w + (w - F.proj w) := by abel
    have hvo : F.Orth v := (F.mem_orthSub).mp hv.2
    have hpw : polar Q v (F.proj w) = 0 := by
      rw [proj_apply, polar_add_right, polar_smul_right, polar_smul_right, hvo.1, hvo.2]
      simp
    have hwM : w - F.proj w ∈ M ⊓ F.orthSub :=
      ⟨M.sub_mem hw (F.plane_le hb hb' (F.proj_mem_plane w)),
        (F.mem_orthSub).mpr (F.orth_sub_proj h3 w)⟩
    rw [e, polar_add_right, hpw, hvw _ hwM, add_zero]
  · have hsup : F.plane ⊔ (M ⊓ F.orthSub) = M := by
      refine le_antisymm (sup_le (F.plane_le hb hb') inf_le_left) fun w hw => ?_
      have e : w = F.proj w + (w - F.proj w) := by abel
      rw [e]
      exact Submodule.add_mem_sup (F.proj_mem_plane w)
        ⟨M.sub_mem hw (F.plane_le hb hb' (F.proj_mem_plane w)),
          (F.mem_orthSub).mpr (F.orth_sub_proj h3 w)⟩
    have hinf : F.plane ⊓ (M ⊓ F.orthSub) = ⊥ := by
      rw [eq_bot_iff, ← F.plane_inf_orthSub h3]
      exact inf_le_inf_left _ inf_le_right
    have h := Submodule.finrank_sup_add_finrank_inf_eq F.plane (M ⊓ F.orthSub)
    rw [hsup, hinf, finrank_bot, add_zero, F.finrank_plane h3] at h
    omega

omit h3 in
theorem inf_orthSub_invariant {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hF : Adapted g F) {M : Submodule K V}
    (hM : ∀ v ∈ M, g v ∈ M) : ∀ v ∈ M ⊓ F.orthSub, g v ∈ M ⊓ F.orthSub := by
  intro v hv
  have hvo : F.Orth v := (F.mem_orthSub).mp hv.2
  refine ⟨hM v hv.1, (F.mem_orthSub).mpr ?_⟩
  obtain ⟨w, w', hw, hw', hwo, hw'o⟩ : ∃ w w' : V, g w = F.b ∧ g w' = F.b' ∧
      polar Q v w = 0 ∧ polar Q v w' = 0 := by
    rcases hF with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨F.b, F.b', h1, h2, hvo.1, hvo.2⟩
    · refine ⟨-F.b - F.b', F.b, ?_, h1, ?_, hvo.1⟩
      · rw [map_sub, map_neg, h1, h2]; abel
      · rw [polar_sub_right, polar_neg_right, hvo.1, hvo.2]; ring
  constructor
  · rw [← hw, polar_map_of_mem hg, hwo]
  · rw [← hw', polar_map_of_mem hg, hw'o]

end EFrame

section OrderThree

variable (g : V ≃ₗ[K] V)

@[expose] def fixSp : Submodule K V := LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id)

@[expose] def movSp : Submodule K V :=
  LinearMap.ker (LinearMap.id + (g : V →ₗ[K] V) + (g : V →ₗ[K] V) ∘ₗ (g : V →ₗ[K] V))

variable {g}

theorem mem_fixSp {v : V} : v ∈ fixSp g ↔ g v = v := by
  simp [fixSp, sub_eq_zero]

theorem mem_movSp {v : V} : v ∈ movSp g ↔ v + g v + g (g v) = 0 := by
  simp [movSp]

variable (h3 : (3 : K) ≠ 0) (hg3 : ∀ v, g (g (g v)) = v)
include h3 hg3

omit h3 in
theorem fix3_mem (v : V) : (3 : K)⁻¹ • (v + g v + g (g v)) ∈ fixSp g := by
  rw [mem_fixSp, map_smul, map_add, map_add, hg3]
  congr 1
  abel

theorem sub_fix3_mem (v : V) : v - (3 : K)⁻¹ • (v + g v + g (g v)) ∈ movSp g := by
  rw [mem_movSp, map_sub, map_sub, map_smul, map_smul, map_add, map_add, map_add, map_add, hg3]
  have e : ∀ x : V, x = (3 : K)⁻¹ • ((3 : K) • x) := fun x => by
    rw [smul_smul, inv_mul_cancel₀ h3, one_smul]
  set s := v + g v + g (g v)
  have hs : v - (3 : K)⁻¹ • s + (g v - (3 : K)⁻¹ • (g v + g (g v) + v)) +
      (g (g v) - (3 : K)⁻¹ • (g (g v) + v + g v)) = s - (3 : K)⁻¹ • ((3 : K) • s) := by
    simp only [s]
    module
  rw [hs, ← e, sub_self]

omit h3 in
theorem movSp_apply_mem {v : V} (hv : v ∈ movSp g) : g v ∈ movSp g := by
  rw [mem_movSp] at hv ⊢
  rw [hg3]
  have := congrArg g hv
  rw [map_add, map_add, map_zero, hg3] at this
  exact this

omit hg3 in
theorem polar_fixSp_movSp (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {b w : V}
    (hb : b ∈ fixSp g) (hw : w ∈ movSp g) : polar Q b w = 0 := by
  rw [mem_fixSp] at hb
  rw [mem_movSp] at hw
  have h1 : polar Q b (g w) = polar Q b w := by
    rw [← polar_map_of_mem hg b w, hb]
  have h2 : polar Q b (g (g w)) = polar Q b w :=
    calc polar Q b (g (g w)) = polar Q (g b) (g (g w)) := by rw [hb]
      _ = polar Q b (g w) := polar_map_of_mem hg b (g w)
      _ = polar Q b w := h1
  have h : (3 : K) * polar Q b w = 0 := by
    have e : polar Q b (w + g w + g (g w)) = 0 := by rw [hw, polar_zero_right]
    rw [polar_add_right, polar_add_right, h1, h2] at e
    linear_combination e
  exact (mul_eq_zero.mp h).resolve_left h3

theorem nDeg_inf_movSp (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {M : Submodule K V}
    (hM : NDeg Q M) (hMg : ∀ v ∈ M, g v ∈ M) : NDeg Q (M ⊓ movSp g) := by
  intro v hv hvw
  refine hM v hv.1 fun m hm => ?_
  set p := (3 : K)⁻¹ • (m + g m + g (g m))
  have hpM : p ∈ M := M.smul_mem _ (M.add_mem (M.add_mem hm (hMg m hm)) (hMg _ (hMg m hm)))
  have e : m = p + (m - p) := by abel
  rw [e, polar_add_right, polar_comm, polar_fixSp_movSp h3 hg (fix3_mem hg3 m) hv.2,
    zero_add]
  exact hvw _ ⟨M.sub_mem hm hpM, sub_fix3_mem h3 hg3 m⟩

theorem le_fixSp_of_inf_movSp {M : Submodule K V} (hMg : ∀ v ∈ M, g v ∈ M)
    (h : M ⊓ movSp g = ⊥) : M ≤ fixSp g := by
  intro m hm
  set p := (3 : K)⁻¹ • (m + g m + g (g m))
  have hpM : p ∈ M := M.smul_mem _ (M.add_mem (M.add_mem hm (hMg m hm)) (hMg _ (hMg m hm)))
  have h0 : m - p ∈ M ⊓ movSp g := ⟨M.sub_mem hm hpM, sub_fix3_mem h3 hg3 m⟩
  rw [h, Submodule.mem_bot, sub_eq_zero] at h0
  rw [h0]
  exact fix3_mem hg3 m

omit h3 hg3 in
theorem exists_rotFrame (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {v : V}
    (hv : v ∈ movSp g) (hQv : Q v ≠ 0) :
    ∃ F : EFrame Q, F.b = v ∧ F.b' = g v ∧ Adapted g F := by
  have hQ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  rw [mem_movSp] at hv
  have hgg : g (g v) = -v - g v := by
    rw [← sub_eq_zero, ← hv]
    abel
  have hpol : polar Q v (g v) = -Q v := by
    have e := hQ (g v)
    rw [hgg, show -v - g v = -(v + g v) by abel, QuadraticMap.map_neg, q_add, hQ v] at e
    linear_combination e
  refine ⟨⟨v, g v, Q v, hQv, rfl, hQ v, hpol⟩, rfl, rfl, Or.inr ⟨rfl, ?_⟩⟩
  exact hgg

end OrderThree

theorem adapted_of_mem_fixSp {g : V ≃ₗ[K] V} {F : EFrame Q} (hb : F.b ∈ fixSp g)
    (hb' : F.b' ∈ fixSp g) : Adapted g F :=
  Or.inl ⟨mem_fixSp.mp hb, mem_fixSp.mp hb'⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LBID4
