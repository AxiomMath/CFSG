module

public import CFSG.GH74.BNPair.Parabolic

public section

namespace CFSG.GH74.BNPair

open scoped Pointwise

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
  {S : Finset (WeylGroup B N)}

@[expose] def WPos (B N : Subgroup X) [(cartan B N).Normal] (w : WeylGroup B N) (x y : X) : Prop :=
  y * x⁻¹ ∈ dc B N w

theorem WPos.inv {w : WeylGroup B N} {x y : X} (h : WPos B N w x y) : WPos B N w⁻¹ y x := by
  have := inv_mem_dc h
  simpa [WPos] using this

theorem WPos.congr_left {w : WeylGroup B N} {x x' y : X} (h : WPos B N w x y)
    (hx : x' * x⁻¹ ∈ B) : WPos B N w x' y := by
  have h1 : x * x'⁻¹ ∈ B := by simpa using B.inv_mem hx
  have := mul_mem_dc h B.one_mem h1
  simpa [WPos, mul_assoc] using this

theorem WPos.congr_right {w : WeylGroup B N} {x y y' : X} (h : WPos B N w x y)
    (hy : y' * y⁻¹ ∈ B) : WPos B N w x y' := by
  have := mul_mem_dc h hy B.one_mem
  simpa [WPos, mul_assoc] using this

theorem WPos.refl (x : X) : WPos B N 1 x x := by
  simp [WPos, mem_dc_one, B.one_mem]

theorem wpos_one_iff {x y : X} : WPos B N 1 x y ↔ y * x⁻¹ ∈ B := mem_dc_one

theorem WPos.unique (T : IsTitsSystem B N S) {w w' : WeylGroup B N} {x y : X}
    (h : WPos B N w x y) (h' : WPos B N w' x y) : w = w' :=
  T.dc_injective (dc_eq_of_mem h h')

theorem exists_wpos (T : IsTitsSystem B N S) (x y : X) : ∃ w, WPos B N w x y := by
  have : y * x⁻¹ ∈ ⋃ w, dc B N w := T.iUnion_dc ▸ Set.mem_univ _
  simpa [WPos] using this

theorem mem_parabolic_single_iff (T : IsTitsSystem B N S) {s : WeylGroup B N} (hs : s ∈ S)
    {x : X} : x ∈ parabolic B N {s} ↔ x ∈ B ∨ x ∈ dc B N s := by
  have hcore : BNCore B N ({s} : Set (WeylGroup B N)) :=
    T.bnCore.mono (by simpa using Finset.mem_coe.2 hs)
  rw [hcore.mem_parabolic_iff]
  constructor
  · rintro ⟨w, hw, hx⟩
    rcases eq_one_or_eq_of_mem_closure_singleton (hcore.mul_self_eq_one s rfl) hw with rfl | rfl
    · left; exact mem_dc_one.1 hx
    · right; exact hx
  · rintro (hx | hx)
    · exact ⟨1, Subgroup.one_mem _, mem_dc_one.2 hx⟩
    · exact ⟨s, Subgroup.subset_closure rfl, hx⟩

theorem IsTitsSystem.mul_self_gen (T : IsTitsSystem B N S) {s : WeylGroup B N} (hs : s ∈ S) :
    s * s = 1 :=
  T.bnCore.mul_self_eq_one s (Finset.mem_coe.2 hs)

theorem IsTitsSystem.gen_ne_one (T : IsTitsSystem B N S) {s : WeylGroup B N} (hs : s ∈ S) :
    s ≠ 1 :=
  T.bnCore.ne_one s (Finset.mem_coe.2 hs)

theorem WPos.step_up (T : IsTitsSystem B N S) {s w : WeylGroup B N} (hs : s ∈ S)
    (hlen : wordLength (S : Set (WeylGroup B N)) w <
      wordLength (S : Set (WeylGroup B N)) (s * w))
    {x y z : X} (hxy : WPos B N w x y) (hz : z * y⁻¹ ∈ parabolic B N {s})
    (hzB : z * y⁻¹ ∉ B) : WPos B N (s * w) x z := by
  have hs' : z * y⁻¹ ∈ dc B N s := ((mem_parabolic_single_iff T hs).1 hz).resolve_left hzB
  have key := T.bnCore.mul_subset_of_lt (Finset.mem_coe.2 hs) (T.mem_closure w) hlen
  have e : z * x⁻¹ = (z * y⁻¹) * (y * x⁻¹) := by group
  unfold WPos
  rw [e]
  exact key (Set.mem_mul.2 ⟨_, hs', _, hxy, rfl⟩)

theorem WPos.step_down (T : IsTitsSystem B N S) {s w : WeylGroup B N} (hs : s ∈ S)
    {x y : X} (hxy : WPos B N w x y) :
    ∃ z, z * y⁻¹ ∈ parabolic B N {s} ∧ WPos B N (s * w) x z := by
  have hss : s * s = 1 := T.mul_self_gen hs
  have hw : w = s * (s * w) := by rw [← mul_assoc, hss, one_mul]
  have h1 : y * x⁻¹ ∈ dc B N s * dc B N (s * w) := by
    have := dc_mul_subset_of s (s * w)
    rw [← hw] at this
    exact this hxy
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.1 h1
  refine ⟨q * x, ?_, ?_⟩
  · have e : q * x * y⁻¹ = p⁻¹ := by
      have h2 : y * x⁻¹ = p * q := hpq.symm
      calc q * x * y⁻¹ = q * (y * x⁻¹)⁻¹ := by group
        _ = p⁻¹ := by rw [h2]; group
    rw [e]
    have hp' : p⁻¹ ∈ dc B N s := by
      have := inv_mem_dc hp
      rwa [T.bnCore.inv_eq (Finset.mem_coe.2 hs)] at this
    exact (mem_parabolic_single_iff T hs).2 (Or.inr hp')
  · show q * x * x⁻¹ ∈ dc B N (s * w)
    simpa using hq

theorem WPos.panel_unique (T : IsTitsSystem B N S) {s w : WeylGroup B N} (hs : s ∈ S)
    (hlen : wordLength (S : Set (WeylGroup B N)) (s * w) <
      wordLength (S : Set (WeylGroup B N)) w)
    {x y z z' : X} (hz : z * y⁻¹ ∈ parabolic B N {s}) (hz' : z' * y⁻¹ ∈ parabolic B N {s})
    (hxz : WPos B N (s * w) x z) (hxz' : WPos B N (s * w) x z') : z' * z⁻¹ ∈ B := by
  have hss : s * s = 1 := T.mul_self_gen hs
  have hmem : z' * z⁻¹ ∈ parabolic B N {s} := by
    have := (parabolic B N {s}).mul_mem hz' ((parabolic B N {s}).inv_mem hz)
    simpa [mul_assoc] using this
  by_contra hnB
  have hds : z' * z⁻¹ ∈ dc B N s := ((mem_parabolic_single_iff T hs).1 hmem).resolve_left hnB
  have hlen' : wordLength (S : Set (WeylGroup B N)) (s * w) <
      wordLength (S : Set (WeylGroup B N)) (s * (s * w)) := by
    rwa [← mul_assoc, hss, one_mul]
  have key := T.bnCore.mul_subset_of_lt (Finset.mem_coe.2 hs) (T.mem_closure (s * w)) hlen'
  have hmem2 : WPos B N (s * (s * w)) x z' := by
    have e : z' * x⁻¹ = (z' * z⁻¹) * (z * x⁻¹) := by group
    unfold WPos
    rw [e]
    exact key (Set.mem_mul.2 ⟨_, hds, _, hxz, rfl⟩)
  have heq := WPos.unique T hmem2 hxz'
  rw [← mul_assoc, hss, one_mul] at heq
  rw [← heq] at hlen
  exact lt_irrefl _ hlen

theorem exists_translate {w : WeylGroup B N} {x y x' y' : X} (h : WPos B N w x y)
    (h' : WPos B N w x' y') :
    ∃ g : X, x * g⁻¹ * x'⁻¹ ∈ B ∧ y * g⁻¹ * y'⁻¹ ∈ B := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨b₁, hb₁, b₂, hb₂, e⟩ := (mem_dc_of_lift (n := m) rfl).1 h
  obtain ⟨b₃, hb₃, b₄, hb₄, e'⟩ := (mem_dc_of_lift (n := m) rfl).1 h'
  refine ⟨(x⁻¹ * (b₂⁻¹ * b₄) * x')⁻¹, ?_, ?_⟩
  · rw [inv_inv]
    have : x * (x⁻¹ * (b₂⁻¹ * b₄) * x') * x'⁻¹ = b₂⁻¹ * b₄ := by group
    rw [this]
    exact B.mul_mem (B.inv_mem hb₂) hb₄
  · have e1 : y = b₁ * m * b₂ * x := by
      have : y = (y * x⁻¹) * x := by group
      rw [this, e]
    have e2 : y' = b₃ * m * b₄ * x' := by
      have : y' = (y' * x'⁻¹) * x' := by group
      rw [this, e']
    have : y * (x⁻¹ * (b₂⁻¹ * b₄) * x') * y'⁻¹ = b₁ * b₃⁻¹ := by
      rw [e1, e2]; group
    rw [inv_inv, this]
    exact B.mul_mem hb₁ (B.inv_mem hb₃)

end CFSG.GH74.BNPair
