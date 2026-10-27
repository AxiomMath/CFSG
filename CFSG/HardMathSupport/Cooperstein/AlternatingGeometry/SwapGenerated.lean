module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockFixClosure
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IndexTwoBlockUniqueness
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OmegaEquiv
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightNormalizer

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

theorem swap_unique_of_isPGroup {Ω : Type*} [DecidableEq Ω] {W : Subgroup (Perm Ω)}
    (hW : IsPGroup 2 W) {x y z : Ω} (hy : y ≠ x) (hz : z ≠ x)
    (hxy : swap x y ∈ W) (hxz : swap x z ∈ W) : y = z := by
  by_contra hyz
  have hg : swap x y * swap x z ∈ W := W.mul_mem hxy hxz
  have hzy : z ≠ y := fun h => hyz h.symm
  refine not_isPGroup_of_threeCycle hW hg (a := x) (b := z) (c := y) hz.symm hzy hy ?_ ?_ ?_
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hz hzy]
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy hyz, swap_apply_right]

theorem permCongr_swap_eq {Ω Ω' : Type*} [DecidableEq Ω] [DecidableEq Ω'] (e : Ω ≃ Ω') (x y : Ω) :
    e.permCongrHom (swap x y) = swap (e x) (e y) := by
  refine Equiv.ext fun z => ?_
  obtain ⟨w, rfl⟩ := e.surjective z
  show e (swap x y (e.symm (e w))) = swap (e x) (e y) (e w)
  rw [e.symm_apply_apply]
  by_cases h1 : w = x
  · subst h1; simp
  · by_cases h2 : w = y
    · subst h2; simp
    · rw [swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne (fun h => h1 (e.injective h))
        (fun h => h2 (e.injective h))]

theorem embL_blockTransp (r s : ℕ) (i : Fin r) (b : Bool) :
    swap (Sum.inl (i, b) : OmegaE r s) (Sum.inl (i, !b)) = embL r s (blockTransp i) := by
  refine Equiv.ext fun z => ?_
  rcases z with ⟨k, c⟩ | j
  · rw [embL_apply_inl, blockTransp]
    by_cases hz : (k, c) = (i, b)
    · rw [hz, swap_apply_left]
      cases b <;> simp
    · by_cases hz' : (k, c) = (i, !b)
      · rw [hz', swap_apply_right]
        cases b <;> simp
      · rw [swap_apply_of_ne_of_ne (by simpa using hz) (by simpa using hz')]
        have h1 : (k, c) ≠ (i, false) ∨ b ≠ false := by
          by_contra h; push Not at h; exact hz (by rw [h.1, h.2])
        cases b
        · rw [swap_apply_of_ne_of_ne (by simpa using hz) (by simpa using hz')]
        · rw [swap_apply_of_ne_of_ne (by simpa using hz') (by simpa using hz)]
  · rw [embL_apply_inr]
    exact swap_apply_of_ne_of_ne (by simp) (by simp)

theorem exists_omegaEquiv_Wr_of_swaps {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {W : Subgroup (Perm Ω)} (hW : IsPGroup 2 W)
    (hgen : W ≤ Subgroup.closure {g | g ∈ W ∧ ∃ a b, a ≠ b ∧ g = swap a b}) :
    ∃ (r s : ℕ) (e : Ω ≃ OmegaE r s), W.map e.permCongrHom.toMonoidHom = Wr r s := by
  classical
  let P : Ω → Prop := fun x => ∃ y, y ≠ x ∧ swap x y ∈ W
  let σ : Ω → Ω := fun x => if h : P x then Classical.choose h else x
  have hσ : ∀ x, P x → σ x ≠ x ∧ swap x (σ x) ∈ W := fun x hx => by
    simp only [σ, dif_pos hx]; exact Classical.choose_spec hx
  have hσu : ∀ x y, y ≠ x → swap x y ∈ W → σ x = y := fun x y hy hxy => by
    have hP : P x := ⟨y, hy, hxy⟩
    exact swap_unique_of_isPGroup hW (hσ x hP).1 hy (hσ x hP).2 hxy
  have hσ1 : ∀ x, P x → σ x ≠ x := fun x hx => (hσ x hx).1
  have hσP : ∀ x, P x → P (σ x) := fun x hx =>
    ⟨x, (hσ1 x hx).symm, by rw [swap_comm]; exact (hσ x hx).2⟩
  have hσ2 : ∀ x, P x → σ (σ x) = x := fun x hx =>
    hσu (σ x) x (hσ1 x hx).symm (by rw [swap_comm]; exact (hσ x hx).2)
  obtain ⟨r, s, e, hPe, he⟩ := exists_omegaEquiv P σ hσP hσ1 hσ2
  refine ⟨r, s, e, ?_⟩
  let G : Set (Perm Ω) := {g | ∃ x, P x ∧ g = swap x (σ x)}
  have hWG : W = Subgroup.closure G := by
    apply le_antisymm
    · refine hgen.trans (Subgroup.closure_mono ?_)
      rintro g ⟨hgW, a, b, hab, rfl⟩
      exact ⟨a, ⟨b, hab.symm, hgW⟩, by rw [hσu a b hab.symm hgW]⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact (hσ x hx).2
  have hset : (e.permCongrHom.toMonoidHom) '' G = embL r s '' Set.range (blockTransp (ι := Fin r)) := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨i, b, hex, heσ⟩ := he x hx
      refine ⟨blockTransp i, ⟨i, rfl⟩, ?_⟩
      show embL r s (blockTransp i) = e.permCongrHom (swap x (σ x))
      rw [permCongr_swap_eq, hex, heσ, embL_blockTransp]
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      set x : Ω := e.symm (Sum.inl (i, false)) with hx
      have hex : e x = Sum.inl (i, false) := by simp [hx]
      have hPx : P x := (hPe x).2 ⟨_, hex⟩
      obtain ⟨i', b', hex', heσ'⟩ := he x hPx
      rw [hex] at hex'
      have hi : (i, false) = (i', b') := Sum.inl_injective hex'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hi
      refine ⟨swap x (σ x), ⟨x, hPx, rfl⟩, ?_⟩
      show e.permCongrHom (swap x (σ x)) = embL r s (blockTransp i)
      rw [permCongr_swap_eq, hex, heσ', ← embL_blockTransp]
  rw [hWG, MonoidHom.map_closure, hset]
  unfold Wr
  rw [blockFix_eq_closure, MonoidHom.map_closure]

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
