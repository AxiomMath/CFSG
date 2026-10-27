module

public import CFSG.Fischer.Uniq.TauIso

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer CFSG.Fischer Subgroup

theorem exists_hom_of_conjugation_bijection {X Y : Type} [Group X] [Group Y]
    (S : Set X) (hS2 : ∀ x ∈ S, x * x = 1)
    (hSS : ∀ x ∈ S, ∀ y ∈ S, x * y * x ∈ S)
    {D : Set Y} (hP : Pair Y D) (hZ : center Y = ⊥) (β : S ≃ D)
    (hβ : ∀ x y : S, (β ⟨x * y * x, hSS x x.2 y y.2⟩ : Y) = β x * β y * β x) :
    ∃ φ : closure S →* Y, Function.Surjective φ ∧
      ∀ x : S, φ ⟨x, subset_closure x.2⟩ = β x := by
  classical
  have hconj : ∀ g ∈ closure S, ∀ x ∈ S, g * x * g⁻¹ ∈ S ∧ g⁻¹ * x * g ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hS2 g hg)
      intro x hx
      rw [hgi]
      exact ⟨hSS g hg x hx, hSS g hg x hx⟩
    | one => intro x hx; simpa using And.intro hx hx
    | mul g h _ _ hg hh =>
      intro x hx
      constructor
      · have hs := (hg _ (hh x hx).1).1
        convert hs using 1; group
      · have hs := (hh _ (hg x hx).2).2
        convert hs using 1; group
    | inv g _ hg => intro x hx; simpa using And.intro (hg x hx).2 (hg x hx).1
  let K := closure S
  let ρ : K →* Equiv.Perm S :=
    { toFun := fun g =>
        { toFun := fun x => ⟨(g : X) * x * (g : X)⁻¹, (hconj g g.2 x x.2).1⟩
          invFun := fun x => ⟨(g : X)⁻¹ * x * (g : X), (hconj g g.2 x x.2).2⟩
          left_inv := fun x => Subtype.ext (by simp [mul_assoc])
          right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
      map_one' := Equiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun g h => Equiv.ext fun x => Subtype.ext (by simp [mul_assoc]) }
  let τ := (Equiv.permCongrHom β).toMonoidHom.comp ρ
  let σ := Pair.conjPerm hP
  have hτ : ∀ x : S, τ ⟨x, subset_closure x.2⟩ = σ (β x) := by
    intro x
    ext d
    obtain ⟨y, rfl⟩ := β.surjective d
    change (β (ρ ⟨x, subset_closure x.2⟩ (β.symm (β y))) : Y) =
      (β x : Y) * β y * (β x : Y)⁻¹
    rw [β.symm_apply_apply, Pair.inv_eq hP (β x).2]
    have hx : (x : X)⁻¹ = x := inv_eq_of_mul_eq_one_right (hS2 x x.2)
    change (β ⟨(x : X) * y * (x : X)⁻¹, _⟩ : Y) = _
    simpa only [hx] using hβ x y
  have hrange : τ.range = σ.range := by
    rw [MonoidHom.range_eq_map, ← closure_closure_coe_preimage (k := S), MonoidHom.map_closure,
      range_conjPerm hP]
    congr 1
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨β ⟨x, hx⟩, (hτ ⟨x, hx⟩).symm⟩
    · rintro ⟨d, rfl⟩
      obtain ⟨x, rfl⟩ := β.surjective d
      exact ⟨⟨x, subset_closure x.2⟩, x.2, hτ x⟩
  let τ' : K →* σ.range := τ.codRestrict σ.range (fun x => hrange ▸ ⟨x, rfl⟩)
  have hτ' : Function.Surjective τ' := by
    intro p
    have hp : (p : Equiv.Perm D) ∈ τ.range := hrange.symm ▸ p.2
    obtain ⟨x, hx⟩ := hp
    exact ⟨x, Subtype.ext hx⟩
  let e := MonoidHom.ofInjective (Pair.conjPerm_injective hP hZ)
  let φ := e.symm.toMonoidHom.comp τ'
  refine ⟨φ, e.symm.surjective.comp hτ', fun x => ?_⟩
  apply e.injective
  change e (e.symm (τ' ⟨x, subset_closure x.2⟩)) = e (β x)
  rw [e.apply_symm_apply]
  exact Subtype.ext (hτ x)

theorem exists_embedding_of_conjugation_bijection {X Y : Type} [Group X] [Group Y]
    (S : Set X) [Finite (closure S)] (hS2 : ∀ x ∈ S, x * x = 1)
    (hSS : ∀ x ∈ S, ∀ y ∈ S, x * y * x ∈ S)
    {D : Set Y} (hP : Pair Y D) (hZ : center Y = ⊥) (β : S ≃ D)
    (hβ : ∀ x y : S, (β ⟨x * y * x, hSS x x.2 y y.2⟩ : Y) = β x * β y * β x)
    (hcard : Nat.card (closure S) ≤ Nat.card Y) :
    ∃ ι : Y →* X, Function.Injective ι ∧ ∀ x : S, ι (β x) = x := by
  obtain ⟨φ, hφ, hφS⟩ := exists_hom_of_conjugation_bijection S hS2 hSS hP hZ β hβ
  let e := MulEquiv.ofBijective φ (hφ.bijective_of_nat_card_le hcard)
  refine ⟨(closure S).subtype.comp e.symm.toMonoidHom,
    (closure S).subtype_injective.comp e.symm.injective, fun x => ?_⟩
  have h := e.symm_apply_apply ⟨x, subset_closure x.2⟩
  change e.symm (φ ⟨x, subset_closure x.2⟩) = _ at h
  rw [hφS] at h
  exact congrArg Subtype.val h

end CFSG.Fischer
