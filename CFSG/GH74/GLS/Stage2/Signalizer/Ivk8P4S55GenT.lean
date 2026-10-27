module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG

section Transport

variable {p : ℕ} [Fact p.Prime] {Y Y' : Type} [Group Y] [Group Y']

theorem EvenParabolics.of_mulEquiv [Finite Y] (e : Y ≃* Y') (h : EvenParabolics p Y') :
    EvenParabolics p Y := by
  intro S M hSM hM
  have hesurj : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, by simp⟩
  have h1 : normalizer (((S.mapSurjective (f := e.toMonoidHom) hesurj : Sylow p Y') :
      Subgroup Y') : Set Y') ≤ M.map e.toMonoidHom := by
    rw [Sylow.coe_mapSurjective, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hSM
  have h2 : M.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hM
    rw [eq_top_iff]
    intro x _
    have : e x ∈ M.map e.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨z, hz, hze⟩ := this
    have : z = x := e.injective hze
    rwa [← this]
  have h3 := h _ _ h1 h2
  have h4 : (M.map e.toMonoidHom).index = M.index := Subgroup.index_map_equiv M e
  rwa [h4] at h3

omit [Fact p.Prime] in
theorem OuterFalse.of_mulEquiv [Finite Y] (e : Y ≃* Y') (h : OuterFalse p Y') :
    OuterFalse p Y := by
  intro α hα hαp hS hHH
  have : Finite Y' := Finite.of_equiv Y e.toEquiv
  have hesurj : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, by simp⟩
  let α' : MulAut Y' := MulAut.congr e α
  have hα'y : ∀ y : Y, α' (e y) = e (α y) := by
    intro y
    simp [α', MulAut.congr_apply]
  refine h α' ?_ ?_ ?_ ?_
  · rintro ⟨y', hy'⟩
    apply hα
    refine ⟨e.symm y', ?_⟩
    ext y
    have := congrArg (fun φ : MulAut Y' => φ (e y)) hy'
    simp only [MulAut.conj_apply, hα'y] at this
    apply e.injective
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact this
  · have : α' ^ p = MulAut.congr e (α ^ p) := (map_pow (MulAut.congr e) α p).symm
    rw [this, hαp, map_one]
  · obtain ⟨S, hS⟩ := hS
    refine ⟨S.mapSurjective (f := e.toMonoidHom) hesurj, ?_⟩
    intro s hs
    have hs' : s ∈ (S : Subgroup Y).map e.toMonoidHom := by
      rw [← Sylow.coe_mapSurjective hesurj S]
      exact hs
    obtain ⟨x, hx, rfl⟩ := hs'
    have := hα'y x
    simp only [MulEquiv.coe_toMonoidHom] at this ⊢
    rw [this, hS x hx]
  · intro r hr hr2 hrp Q' hQ' hinv x' hx'
    let Q : Subgroup Y := Q'.comap e.toMonoidHom
    have hQ : IsPGroup r ↥Q := hQ'.comap_of_injective e.toMonoidHom e.injective
    have hinvQ : ∀ x ∈ Q, α x ∈ Q := by
      intro x hx
      show e (α x) ∈ Q'
      rw [← hα'y]
      exact hinv _ hx
    have hfix := hHH r hr hr2 hrp Q hQ hinvQ
    have hmem : e.symm x' ∈ Q := by
      show e (e.symm x') ∈ Q'
      simpa using hx'
    have h1 := hfix _ hmem
    have h2 := hα'y (e.symm x')
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h2, h1, MulEquiv.apply_symm_apply]

end Transport

section Torus

variable {p : ℕ} {Y : Type} [Group Y]

theorem false_of_torus_moved {α h f : MulAut Y} (hα : α = h * f * h⁻¹) {T : Subgroup Y} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p) (hT : IsPGroup r ↥T) (hfT : ∀ x ∈ T, f x ∈ T)
    {t : Y} (ht : t ∈ T) (hne : f t ≠ t)
    (hHH : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Y, IsPGroup r ↥Q →
      (∀ x ∈ Q, α x ∈ Q) → ∀ x ∈ Q, α x = x) : False := by
  have hαy : ∀ y : Y, α (h y) = h (f y) := by
    intro y
    rw [hα]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hQp : IsPGroup r ↥(T.map h.toMonoidHom) := hT.map h.toMonoidHom
  have hinv : ∀ x ∈ T.map h.toMonoidHom, α x ∈ T.map h.toMonoidHom := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨f y, hfT y hy, (hαy y).symm⟩
  have hfix := hHH r hr hr2 hrp _ hQp hinv (h t) ⟨t, ht, rfl⟩
  rw [hαy] at hfix
  exact hne (h.injective hfix)

end Torus

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
