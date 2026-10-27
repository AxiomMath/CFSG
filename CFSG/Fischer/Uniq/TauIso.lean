module

public import CFSG.Fischer.Pairs

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

@[expose] def tauE (hE : Pair X E) (e f : E) : E := ⟨e * f * e, Pair.mul_mul_mem hE e.2 f.2⟩

theorem conjPerm_eq_tau (hE : Pair X E) (e f : E) : Pair.conjPerm hE e f = tauE hE e f := by
  apply Subtype.ext
  rw [Pair.conjPerm_apply, Pair.inv_eq hE e.2]
  rfl

theorem range_conjPerm (hE : Pair X E) :
    (Pair.conjPerm hE).range = Subgroup.closure (Set.range fun e : E => Pair.conjPerm hE e) := by
  rw [MonoidHom.range_eq_map, ← Pair.closure_eq hE, MonoidHom.map_closure]
  congr 1
  ext σ
  simp

theorem exists_mulEquiv_of_tau (hE : Pair X E) (hF : Pair Y F) (hZE : Subgroup.center X = ⊥)
    (hZF : Subgroup.center Y = ⊥) (β : E ≃ F)
    (hβ : ∀ e f : E, β (tauE hE e f) = tauE hF (β e) (β f)) :
    ∃ φ : X ≃* Y, φ '' E = F := by
  set ρ := Pair.conjPerm hE
  set σ := Pair.conjPerm hF
  let c : Equiv.Perm E ≃* Equiv.Perm F := Equiv.permCongrHom β
  have hc : ∀ e : E, c (ρ e) = σ (β e) := by
    intro e
    ext f
    obtain ⟨f0, rfl⟩ := β.surjective f
    show (β (ρ e (β.symm (β f0))) : Y) = _
    rw [Equiv.symm_apply_apply, conjPerm_eq_tau, conjPerm_eq_tau, hβ]
  have hrange : ρ.range.map c.toMonoidHom = σ.range := by
    rw [range_conjPerm, range_conjPerm, MonoidHom.map_closure]
    congr 1
    ext τ
    constructor
    · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
      exact ⟨β e, (hc e).symm⟩
    · rintro ⟨f, rfl⟩
      obtain ⟨e, rfl⟩ := β.surjective f
      exact ⟨ρ e, ⟨e, rfl⟩, hc e⟩
  let eX : X ≃* ρ.range := MonoidHom.ofInjective (Pair.conjPerm_injective hE hZE)
  let eY : Y ≃* σ.range := MonoidHom.ofInjective (Pair.conjPerm_injective hF hZF)
  let eR : ρ.range ≃* σ.range :=
    (ρ.range.equivMapOfInjective c.toMonoidHom c.injective).trans (MulEquiv.subgroupCongr hrange)
  let φ : X ≃* Y := (eX.trans eR).trans eY.symm
  have hφ : ∀ e : E, φ e = β e := by
    intro e
    apply Pair.conjPerm_injective hF hZF
    have h1 : (eY (φ e) : Equiv.Perm F) = σ (φ e) := rfl
    have h2 : eY (φ e) = eR (eX e) := by simp [φ]
    rw [← h1, h2]
    exact hc e
  refine ⟨φ, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hφ ⟨x, hx⟩]
    exact (β ⟨x, hx⟩).2
  · intro hy
    obtain ⟨e, he⟩ := β.surjective ⟨y, hy⟩
    refine ⟨e, e.2, ?_⟩
    rw [hφ e, he]

end CFSG.Fischer
