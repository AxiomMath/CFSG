module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsJ
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsTau
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsRow

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type*} [Field F] [Finite F]

theorem exists_mul_self_ne_self_of_card_four (hF : Nat.card F = 4) : ∃ t : F, t * t ≠ t := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set F) ⊆ {0, 1} := fun t _ => by
    have h1 : t * (t - 1) = 0 := by rw [mul_sub, mul_one, h t, sub_self]
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (sub_eq_zero.1 h2)
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, hF] at h3
  have h4 := Set.ncard_insert_le (0 : F) {1}
  rw [Set.ncard_singleton] at h4
  omega

structure IsUFiveAbelianRadical (X : Subgroup (unitriangular 5 F)) : Prop where
  comm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x
  normal : X.Normal
  cent : ∀ g : unitriangular 5 F, (∀ x ∈ X, g * x = x * g) → g ∈ X
  sq : ∀ x ∈ X, x * x = 1
  card : Nat.card X = 2 ^ 8
  fieldStr : ∃ τ : X ≃* X, (∀ (g : unitriangular 5 F) (x y : X),
      (y : unitriangular 5 F) = g * x * g⁻¹ → (τ y : unitriangular 5 F) = g * τ x * g⁻¹) ∧
    ∀ x, τ x = x → x = 1

theorem isUFiveAbelianRadical_uFiveRow [CharP F 2] (hF : Nat.card F = 4) :
    IsUFiveAbelianRadical (uFiveRow (F := F)) where
  comm := fun _ hx _ hy => uFiveRow_comm hx hy
  normal := ⟨fun _ hx g => conj_mem_uFiveRow hx g⟩
  cent := fun _ h => mem_uFiveRow_of_comm h
  sq := fun _ hx => uFiveRow_mul_self hx
  card := by rw [card_uFiveRow, hF]; norm_num
  fieldStr := by
    obtain ⟨t, ht⟩ := exists_mul_self_ne_self_of_card_four hF
    have ht0 : t ≠ 0 := by rintro rfl; exact ht (mul_zero 0)
    have ht1 : t ≠ 1 := by rintro rfl; exact ht (mul_one 1)
    exact ⟨uFiveRowScalar t ht0, fun g x y hxy => uFiveRowScalar_conj t ht0 g x y hxy,
      fun x hx => uFiveRowScalar_eq_self t ht0 ht1 x hx⟩

omit [Finite F] in
theorem IsUFiveAbelianRadical.map {X : Subgroup (unitriangular 5 F)} (hX : IsUFiveAbelianRadical X)
    (φ : MulAut (unitriangular 5 F)) : IsUFiveAbelianRadical (X.map φ.toMonoidHom) where
  comm := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hX.comm x hx y hy]
  normal := hX.normal.map φ.toMonoidHom φ.surjective
  cent := by
    intro g hg
    refine ⟨φ.symm g, hX.cent _ fun x hx => φ.injective ?_, φ.apply_symm_apply g⟩
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact hg _ ⟨x, hx, rfl⟩
  sq := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hX.sq x hx, map_one]
  card := by rw [Subgroup.card_map_of_injective φ.injective, hX.card]
  fieldStr := by
    obtain ⟨τ, hτ, hfix⟩ := hX.fieldStr
    let ψ := X.equivMapOfInjective φ.toMonoidHom φ.injective
    have hψ : ∀ x : X, ((ψ x : X.map φ.toMonoidHom) : unitriangular 5 F) = φ x := fun _ => rfl
    refine ⟨ψ.symm.trans (τ.trans ψ), fun g x y hxy => ?_, fun x hx => ?_⟩
    · have hxy' : ((ψ.symm y : X) : unitriangular 5 F) =
          φ.symm g * (ψ.symm x : X) * (φ.symm g)⁻¹ := by
        apply φ.injective
        rw [map_mul, map_mul, map_inv, φ.apply_symm_apply, ← hψ, ← hψ, ψ.apply_symm_apply,
          ψ.apply_symm_apply, hxy]
      have h := hτ _ _ _ hxy'
      change ((ψ (τ (ψ.symm y)) : X.map φ.toMonoidHom) : unitriangular 5 F) =
        g * ((ψ (τ (ψ.symm x)) : X.map φ.toMonoidHom) : unitriangular 5 F) * g⁻¹
      rw [hψ, hψ, h, map_mul, map_mul, map_inv, φ.apply_symm_apply]
    · have h : τ (ψ.symm x) = ψ.symm x := by
        apply ψ.injective
        rw [ψ.apply_symm_apply]
        exact hx
      have h1 := hfix _ h
      rw [← ψ.apply_symm_apply x, h1, map_one]

theorem IsUFiveAbelianRadical.eq_uFiveRow_of_apply34 [CharP F 2] (hF : Nat.card F = 4)
    {X : Subgroup (unitriangular 5 F)} (hX : IsUFiveAbelianRadical X)
    (h34 : ∀ x ∈ X, ypsMat x 3 4 = 0) : X = uFiveRow := by
  obtain ⟨e, rfl⟩ := exists_eq_uFiveTwisted hF hX.comm hX.cent hX.normal hX.sq hX.card h34
  by_cases he : e = 0
  · rw [he]
    exact uFiveTwisted_zero
  · obtain ⟨τ, hτ, hfix⟩ := hX.fieldStr
    obtain ⟨t, ht⟩ := exists_mul_self_ne_self_of_card_four hF
    exact (not_exists_fixedPointFree_equivariant_uFiveTwisted he ht τ hτ hfix).elim

theorem IsUFiveAbelianRadical.eq_uFiveRow_or_uFiveCol [CharP F 2] (hF : Nat.card F = 4)
    {X : Subgroup (unitriangular 5 F)} (hX : IsUFiveAbelianRadical X) :
    X = uFiveRow ∨ X = uFiveCol := by
  rcases apply34_or_apply01_of_radical hF hX.comm hX.cent hX.normal hX.sq hX.card with h | h
  · exact Or.inl (hX.eq_uFiveRow_of_apply34 hF h)
  · right
    have h' : X.map uFiveGraph.toMonoidHom = uFiveRow :=
      (hX.map uFiveGraph).eq_uFiveRow_of_apply34 hF (by
        rintro _ ⟨x, hx, rfl⟩
        change ypsMat (uFiveGraph x) 3 4 = 0
        rw [ypsMat_uFiveGraph_apply34, h x hx, neg_zero])
    have hγγ : (X.map uFiveGraph.toMonoidHom).map uFiveGraph.toMonoidHom = X := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id X
      exact MonoidHom.ext fun x => uFiveGraph_uFiveGraph x
    rw [← hγγ, h', map_uFiveGraph_uFiveRow]

theorem map_uFiveRow_eq_or [CharP F 2] (hF : Nat.card F = 4) (φ : MulAut (unitriangular 5 F)) :
    (uFiveRow (F := F)).map φ.toMonoidHom = uFiveRow ∨
      (uFiveRow (F := F)).map φ.toMonoidHom = uFiveCol :=
  ((isUFiveAbelianRadical_uFiveRow hF).map φ).eq_uFiveRow_or_uFiveCol hF

theorem map_uFiveRow_orbit [CharP F 2] (hF : Nat.card F = 4) (φ ψ : MulAut (unitriangular 5 F)) :
    (uFiveRow (F := F)).map φ.toMonoidHom = uFiveRow ∨
      (uFiveRow (F := F)).map ψ.toMonoidHom = uFiveRow ∨
      (uFiveRow (F := F)).map φ.toMonoidHom = (uFiveRow (F := F)).map ψ.toMonoidHom := by
  rcases map_uFiveRow_eq_or hF φ with h | h
  · exact Or.inl h
  · rcases map_uFiveRow_eq_or hF ψ with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (h.trans h'.symm))

end CFSG.SeitzReduction.LinearPilot
