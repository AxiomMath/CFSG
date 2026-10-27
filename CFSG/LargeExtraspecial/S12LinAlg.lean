module

public import CFSG.LargeExtraspecial.S12Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem s12_pow_six_apply {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2)
    {x : V ≃ₗ[ZMod 2] V} (hx : ∀ w ∈ W, x w ∈ W) (hx' : ∀ w ∈ W, x.symm w ∈ W) :
    ∀ w ∈ W, (x ^ 6) w = w := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype V := Fintype.ofFinite V
  set S := {w : V // w ∈ W ∧ w ≠ 0}
  have hcardW : Nat.card W = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hW, Nat.card_zmod]
    norm_num
  have hcardS : Fintype.card S = 3 := by
    have h1 : Fintype.card {w : V // w ∈ W} = 4 := by
      rw [← hcardW, ← Nat.card_eq_fintype_card]
    have h2 : Fintype.card S = Fintype.card {w : V // w ∈ W} - 1 := by
      rw [show Fintype.card S = Fintype.card {w : {w : V // w ∈ W} // w ≠ 0} from
        Fintype.card_congr ⟨fun w => ⟨⟨w.1, w.2.1⟩, fun h => w.2.2 (congrArg Subtype.val h)⟩,
          fun w => ⟨w.1.1, w.1.2, fun h => w.2 (Subtype.ext h)⟩, fun _ => rfl, fun _ => rfl⟩]
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    rw [h2, h1]
  let σ : Equiv.Perm S :=
    { toFun := fun w => ⟨x w.1, hx _ w.2.1, fun h => w.2.2 (x.injective (by rw [h, map_zero]))⟩
      invFun := fun w => ⟨x.symm w.1, hx' _ w.2.1,
        fun h => w.2.2 (x.symm.injective (by rw [h, map_zero]))⟩
      left_inv := fun w => Subtype.ext (x.symm_apply_apply w.1)
      right_inv := fun w => Subtype.ext (x.apply_symm_apply w.1) }
  have hσpow : ∀ k : ℕ, ∀ w : S, ((σ ^ k) w).1 = (x ^ k) w.1 := by
    intro k
    induction k with
    | zero => intro w; rfl
    | succ k ih =>
      intro w
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', LinearEquiv.mul_apply]
      change x ((σ ^ k) w).1 = _
      rw [ih]
  have hσ6 : σ ^ 6 = 1 := by
    have h := orderOf_dvd_card (G := Equiv.Perm S) (x := σ)
    rw [Fintype.card_perm, hcardS] at h
    exact orderOf_dvd_iff_pow_eq_one.mp (by simpa [Nat.factorial] using h)
  intro w hw
  by_cases hw0 : w = 0
  · rw [hw0, map_zero]
  · have := hσpow 6 ⟨w, hw, hw0⟩
    rw [hσ6] at this
    exact this.symm

theorem s12_no_fix_of_pow_three {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2)
    {c : V ≃ₗ[ZMod 2] V} (hc3 : c ^ 3 = 1) (hcW : ∀ w ∈ W, c w ∈ W)
    (hc1 : ∃ w ∈ W, c w ≠ w) {p : V} (hp : p ∈ W) (hp0 : p ≠ 0) : c p ≠ p := by
  intro hcp
  obtain ⟨w, hw, hcw⟩ := hc1
  have hwp : w ≠ p := fun e => hcw (by rw [e, hcp])
  have hw0 : w ≠ 0 := fun e => hcw (by rw [e, map_zero])
  have hcw' : c w = w + p := by
    rcases s12_mem_of_span_pair hW hp hw hp0 hw0 (Ne.symm hwp) (hcW w hw) with h | h | h | h
    · exact absurd (c.injective (by rw [h, map_zero])) hw0
    · exact absurd (c.injective (by rw [h, hcp])) hwp
    · exact absurd h hcw
    · rw [h, add_comm]
  have hc2w : (c ^ 2) w = w := by
    rw [pow_two, LinearEquiv.mul_apply, hcw', map_add, hcw', hcp, add_assoc,
      OrthoF2.vec_add_self, add_zero]
  apply hcw
  have : (c ^ 3) w = w := by rw [hc3]; rfl
  rw [pow_succ', LinearEquiv.mul_apply, hc2w] at this
  exact this

theorem s12_orbit_of_pow_three {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2)
    {c : V ≃ₗ[ZMod 2] V} (hc3 : c ^ 3 = 1) (hcW : ∀ w ∈ W, c w ∈ W)
    (hc1 : ∃ w ∈ W, c w ≠ w) {p : V} (hp : p ∈ W) (hp0 : p ≠ 0) :
    c p ≠ p ∧ (c ^ 2) p = p + c p ∧
      ∀ w ∈ W, w = 0 ∨ w = p ∨ w = c p ∨ w = p + c p := by
  have hcp := s12_no_fix_of_pow_three hW hc3 hcW hc1 hp hp0
  have hcpW := hcW p hp
  have hcp0 : c p ≠ 0 := fun e => hp0 (c.injective (by rw [e, map_zero]))
  refine ⟨hcp, ?_, fun w hw => s12_mem_of_span_pair hW hp hcpW hp0 hcp0 (Ne.symm hcp) hw⟩
  have hc2W : (c ^ 2) p ∈ W := by rw [pow_two, LinearEquiv.mul_apply]; exact hcW _ hcpW
  rcases s12_mem_of_span_pair hW hp hcpW hp0 hcp0 (Ne.symm hcp) hc2W with h | h | h | h
  · exfalso
    apply hp0
    have : (c ^ 2) p = c (c p) := by rw [pow_two, LinearEquiv.mul_apply]
    rw [this] at h
    exact c.injective (c.injective (by rw [h, map_zero, map_zero]))
  · exfalso
    have e3 : (c ^ 3) p = p := by rw [hc3]; rfl
    rw [pow_succ', LinearEquiv.mul_apply, h] at e3
    exact hcp e3
  · exfalso
    have : (c ^ 2) p = c (c p) := by rw [pow_two, LinearEquiv.mul_apply]
    rw [this] at h
    exact hcp (c.injective h)
  · exact h

theorem s12_eq_or_eq_sq_of_pow_three {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2)
    {c c' : V ≃ₗ[ZMod 2] V} (hc3 : c ^ 3 = 1) (hc'3 : c' ^ 3 = 1) (hcW : ∀ w ∈ W, c w ∈ W)
    (hc'W : ∀ w ∈ W, c' w ∈ W) (hc1 : ∃ w ∈ W, c w ≠ w) (hc'1 : ∃ w ∈ W, c' w ≠ w) :
    (∀ w ∈ W, c' w = c w) ∨ ∀ w ∈ W, c' w = (c ^ 2) w := by
  obtain ⟨p, hp, hp0⟩ : ∃ p ∈ W, p ≠ 0 := by
    obtain ⟨w, hw, hcw⟩ := hc1
    exact ⟨w, hw, fun e => hcw (by rw [e, map_zero])⟩
  obtain ⟨hcp, hc2p, hall⟩ := s12_orbit_of_pow_three hW hc3 hcW hc1 hp hp0
  obtain ⟨hc'p, hc'2p, -⟩ := s12_orbit_of_pow_three hW hc'3 hc'W hc'1 hp hp0
  have hcpW := hcW p hp
  have hcp0 : c p ≠ 0 := fun e => hp0 (c.injective (by rw [e, map_zero]))
  have hext : ∀ {f f' : V ≃ₗ[ZMod 2] V}, f p = f' p → f (c p) = f' (c p) →
      ∀ w ∈ W, f w = f' w := by
    intro f f' h1 h2 w hw
    rcases hall w hw with rfl | rfl | rfl | rfl
    · simp
    · exact h1
    · exact h2
    · rw [map_add, map_add, h1, h2]
  have hc'pW := hc'W p hp
  rcases hall _ hc'pW with h | h | h | h
  · exact absurd (c'.injective (by rw [h, map_zero])) hp0
  · exact absurd h hc'p
  · left
    refine hext h ?_
    rw [← h, ← LinearEquiv.mul_apply, ← pow_two, hc'2p, h, ← hc2p, pow_two,
      LinearEquiv.mul_apply]
  · right
    have hc4 : (c ^ 2) (c p) = p := by
      have e3 : (c ^ 3) p = p := by rw [hc3]; rfl
      rw [pow_succ, LinearEquiv.mul_apply] at e3
      exact e3
    refine hext (by rw [h, hc2p]) ?_
    rw [hc4]
    have e1 : c p = p + c' p := by rw [h, ← add_assoc, OrthoF2.vec_add_self, zero_add]
    calc c' (c p) = c' (p + c' p) := by rw [e1]
      _ = c' p + (c' ^ 2) p := by rw [map_add, pow_two, LinearEquiv.mul_apply]
      _ = c' p + (p + c' p) := by rw [hc'2p]
      _ = p := by rw [add_comm p, ← add_assoc, OrthoF2.vec_add_self, zero_add]

omit [FiniteDimensional (ZMod 2) V] in
theorem s12_fix_of_apply_sub_mem_span {q : QuadraticForm (ZMod 2) V} {ℓ : V ≃ₗ[ZMod 2] V}
    (hℓ : ℓ ∈ TauCeti.QuadraticMap.orthogonalGroup q) {Y : Submodule (ZMod 2) V} {w v₀ : V}
    (hqw : q w = 0) (hv₀ : v₀ ∈ Y) (hpol : polar q v₀ w ≠ 0)
    (h : ∀ v ∈ Y, ℓ v - v ∈ (ZMod 2) ∙ w) : ∀ v ∈ Y, ℓ v = v := by
  have hpol1 : polar q v₀ w = 1 := OrthoF2.zmod2_eq_one_of_ne_zero hpol
  have hcases : ∀ v ∈ Y, ℓ v = v ∨ ℓ v = v + w := by
    intro v hv
    rcases OrthoF2.mem_span_singleton_iff.mp (h v hv) with h1 | h1
    · left; exact sub_eq_zero.mp h1
    · right; rw [← h1]; abel
  have hv₀fix : ℓ v₀ = v₀ := by
    rcases hcases v₀ hv₀ with h1 | h1
    · exact h1
    · exfalso
      have e := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hℓ v₀
      rw [h1, map_add_eq, hqw, hpol1] at e
      simp at e
  intro v hv
  rcases hcases v hv with h1 | h1
  · exact h1
  · exfalso
    have e := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hℓ v v₀
    rw [h1, hv₀fix, polar_add_left, QuadraticMap.polar_comm q w v₀, hpol1] at e
    simp at e

theorem s12_two_mul_finrank_fixSpace_le {x z : V ≃ₗ[ZMod 2] V} (hz : fixSpace z = ⊥)
    (hxz : x * z = z * z * x) :
    2 * finrank (ZMod 2) (fixSpace x) ≤ finrank (ZMod 2) V := by
  set A := fixSpace x
  set B := A.map (z : V →ₗ[ZMod 2] V)
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvA, u, huA, rfl⟩
    have hxu : x u = u := mem_fixSpace.mp huA
    have hxv : x (z u) = z u := mem_fixSpace.mp hvA
    have e : x (z u) = z (z (x u)) := by
      rw [← LinearEquiv.mul_apply, hxz, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [e, hxu] at hxv
    have hzu : z u = u := z.injective hxv
    have hu0 : u ∈ (⊥ : Submodule (ZMod 2) V) := hz ▸ mem_fixSpace.mpr hzu
    rw [(Submodule.mem_bot _).mp hu0]
    simp
  have hB : finrank (ZMod 2) B = finrank (ZMod 2) A :=
    LinearEquiv.finrank_map_eq z A
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hAB, finrank_bot, add_zero, hB] at h
  have := Submodule.finrank_le (A ⊔ B)
  omega

end CFSG.LargeExtraspecial
