module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def FooteType {X : Type} [Group X] (L : Subgroup X) : Prop :=
  Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f

@[expose] def footeFamily {X : Type} [Group X] (L : Subgroup X) : Set (Subgroup X) :=
  {A | GSMaximalComponent A ∧ Nonempty (A ⧸ Open.fusionZStar A ≃* L ⧸ Open.fusionZStar L)}

@[expose] def FooteSetting (X : Type) [Group X] (x : X) (L : Subgroup X) : Prop :=
  IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ Assembly.KProper Blueprint.Catalog X ∧
    orderOf x = 2 ∧ L ≤ centralizer ({x} : Set X) ∧
    IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))) ∧ GSMaximalComponent L ∧
    FooteType L

@[expose] def FooteExceptional (X : Type) [Group X] (L : Subgroup X) : Prop :=
  (Nonempty (X ≃* alternatingGroup (Fin 9)) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5))) ∨
    (Nonempty (X ≃* alternatingGroup (Fin 10)) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 6))) ∨
    (Nonempty (X ≃* alternatingGroup (Fin 11)) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))) ∨
    (Nonempty (X ≃* Blueprint.NativeSporadic.J2) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5)))

@[expose] def FooteCaseOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X) (L : Subgroup X), FooteSetting X x L →
    (∃ A ∈ footeFamily L, CFSG.pRank 2 ↥A = 1) → Blueprint.OddLieType X

@[expose] def FooteCaseRankBound : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X) (L : Subgroup X), FooteSetting X x L →
    (∀ A ∈ footeFamily L, CFSG.pRank 2 ↥A ≠ 1) →
    ∀ A ∈ footeFamily L, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2

@[expose] def FooteCaseRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X) (L : Subgroup X), FooteSetting X x L →
    (∀ A ∈ footeFamily L, CFSG.pRank 2 ↥A ≠ 1) →
    (∀ A ∈ footeFamily L, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2) →
    CFSG.pRank 2 ↥(coreActionKernel L) = 2 →
    Blueprint.OddLieType X ∨ FooteExceptional X L

theorem mem_footeFamily_self {X : Type} [Group X] {L : Subgroup X} (h : GSMaximalComponent L) :
    L ∈ footeFamily L :=
  ⟨h, ⟨MulEquiv.refl _⟩⟩

theorem one_le_pRank_of_orderOf_eq_two {H : Type*} [Group H] [Finite H] {g : H}
    (hg : orderOf g = 2) : 1 ≤ CFSG.pRank 2 H := by
  have hgg : ∀ y ∈ zpowers g, y ^ 2 = 1 := by
    rintro y ⟨k, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg, pow_orderOf_eq_one,
      one_zpow]
  have hE : IsElementaryAbelian 2 (zpowers g) :=
    { is_comm := ⟨fun a b => Subtype.ext (by
          obtain ⟨i, hi⟩ := a.2
          obtain ⟨j, hj⟩ := b.2
          rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm])⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
        Subtype.ext (by rw [SubmonoidClass.coe_pow, hgg y y.2, OneMemClass.coe_one]) }
  apply le_csSup
  · refine ⟨Nat.card H, ?_⟩
    rintro r ⟨B, -, hB⟩
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : Nat.card B ≤ Nat.card H := Subgroup.card_le_card_group B
    omega
  · exact ⟨zpowers g, hE, by rw [Nat.card_zpowers, hg, pow_one]⟩

theorem mem_coreActionKernel_of_le_centralizer {X : Type*} [Group X] {s : X} {L : Subgroup X}
    (hLs : L ≤ centralizer ({s} : Set X)) : s ∈ coreActionKernel L := by
  have hsC : s ∈ centralizer (L : Set X) :=
    mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hLs hh)
  refine ⟨centralizer_le_normalizer _ hsC, fun j hj => ?_⟩
  have hjs : j * s = s * j := mem_centralizer_singleton_iff.mp (hLs hj)
  have h1 : j⁻¹ * s⁻¹ * j * s = 1 := by
    calc j⁻¹ * s⁻¹ * j * s = j⁻¹ * s⁻¹ * (j * s) := by group
      _ = j⁻¹ * s⁻¹ * (s * j) := by rw [hjs]
      _ = 1 := by group
  rw [h1]
  exact one_mem _

theorem one_le_pRank_coreActionKernel {X : Type} [Group X] [Finite X] {x : X}
    (hx : orderOf x = 2) {L : Subgroup X} (hLx : L ≤ centralizer ({x} : Set X)) :
    1 ≤ CFSG.pRank 2 ↥(coreActionKernel L) := by
  have hxC : x ∈ coreActionKernel L := mem_coreActionKernel_of_le_centralizer hLx
  exact one_le_pRank_of_orderOf_eq_two (g := (⟨x, hxC⟩ : coreActionKernel L))
    (by rw [Subgroup.orderOf_mk]; exact hx)

theorem footeInput_of_cases (h1 : FooteCaseOne) (h3 : FooteCaseRankBound)
    (h4 : FooteCaseRankTwo) : GSLit.FooteInput := by
  intro X _ _ _ hnonab hK x hx L hLx hL hmax htype
  have hS : FooteSetting X x L := ⟨inferInstance, hnonab, hK, hx, hLx, hL, hmax, htype⟩
  by_cases hone : ∃ A ∈ footeFamily L, CFSG.pRank 2 ↥A = 1
  · exact Or.inl (h1 X x L hS hone)
  have hone' : ∀ A ∈ footeFamily L, CFSG.pRank 2 ↥A ≠ 1 := fun A hA h => hone ⟨A, hA, h⟩
  have hbound := h3 X x L hS hone'
  have hle := hbound L (mem_footeFamily_self hmax)
  have hge := one_le_pRank_coreActionKernel hx hLx
  rcases (show CFSG.pRank 2 ↥(coreActionKernel L) = 1 ∨
      CFSG.pRank 2 ↥(coreActionKernel L) = 2 by omega) with h | h
  · exact Or.inr (Or.inl h)
  · rcases h4 X x L hS hone' hbound h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')

end CFSG.ComponentClassification.FooteLit
