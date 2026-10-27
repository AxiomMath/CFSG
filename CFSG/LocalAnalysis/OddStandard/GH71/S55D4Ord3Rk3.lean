module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Rk1
public import CFSG.RankThree.PartOne.KGD.D4QA3
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.KGD.D4QFrame

public noncomputable section

namespace CFSG.OddStandard.GH71.S55

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups


variable {L : Type} [Field L] {r₁ r₂ r₃ : Fin TwistTag.D4.tag.rank → ℤ}

local notation "ρ" => rootSL2 TwistTag.D4.tag L
local notation "𝒩" => trialityOpposition L * diagramMap TwistTag.D4 L

theorem d4_rk3_rels (h₁ : IsRoot TwistTag.D4.tag r₁) (h₂ : IsRoot TwistTag.D4.tag r₂)
    (h₃ : IsRoot TwistTag.D4.tag r₃) (e₁ : permLattice TwistTag.D4.perm r₁ = -r₂)
    (e₂ : permLattice TwistTag.D4.perm r₂ = -r₃) (e₃ : permLattice TwistTag.D4.perm r₃ = r₁) :
    ∃ s₁ s₂ y : Lˣ, (∀ A : SL2 L, 𝒩 * ρ r₁ A * (𝒩)⁻¹ = ρ r₂ (conjSL (diagUnitOne s₁) A)) ∧
      (∀ A : SL2 L, 𝒩 * ρ r₂ A * (𝒩)⁻¹ = ρ r₃ (conjSL (diagUnitOne s₂) A)) ∧
      (∀ A : SL2 L, 𝒩 * ρ r₃ A * (𝒩)⁻¹ = ρ r₁ (conjSL (swapGL * diagUnitOne y) A)) := by
  have hzM := trialityOpposition_mem_monomialSubgroup (K := L)
  have hzW : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      weylQuotientHom TwistTag.D4.tag L ⟨_, hzM⟩ • x = -x := fun x =>
    weylQuotientHom_trialityOpposition_smul x
  obtain ⟨s₁, h₁'⟩ := exists_conj_rootSL2_eq_twist hzM h₁
  obtain ⟨s₂, h₂'⟩ := exists_conj_rootSL2_eq_twist hzM h₂
  obtain ⟨s₃, h₃'⟩ := exists_conj_rootSL2_eq_twist hzM h₃
  rw [e₁, hzW, neg_neg] at h₁'
  rw [e₂, hzW, neg_neg] at h₂'
  rw [e₃, hzW] at h₃'
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) h₁
  refine ⟨s₁, s₂, a * s₃, h₁', h₂', fun A => ?_⟩
  rw [h₃' A, ha, ← conjSL_mul, mul_assoc, diagUnitOne_mul]

theorem d4_rk3_twist (Fr : L →+* L) (hc12 : ∀ A B : SL2 L, Commute (ρ r₁ A) (ρ r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (ρ r₁ A) (ρ r₃ C)) {M₁ M₂ M₃ : GL (Fin 2) L}
    (h₁ : ∀ A : SL2 L, 𝒩 * ρ r₁ A * (𝒩)⁻¹ = ρ r₂ (conjSL M₁ A))
    (h₂ : ∀ A : SL2 L, 𝒩 * ρ r₂ A * (𝒩)⁻¹ = ρ r₃ (conjSL M₂ A))
    (h₃ : ∀ A : SL2 L, 𝒩 * ρ r₃ A * (𝒩)⁻¹ = ρ r₁ (conjSL M₃ A)) (A B C : SL2 L) :
    𝒩 * Units.map (entrywiseHom Fr) (ρ r₁ A * ρ r₂ B * ρ r₃ C) * (𝒩)⁻¹ =
      ρ r₁ (twHom Fr M₃ C) * ρ r₂ (twHom Fr M₁ A) * ρ r₃ (twHom Fr M₂ B) := by
  rw [map_mul, map_mul, entrywise_rootSL2_of_field, entrywise_rootSL2_of_field,
    entrywise_rootSL2_of_field]
  calc 𝒩 * (ρ r₁ (SpecialLinearGroup.map Fr A) * ρ r₂ (SpecialLinearGroup.map Fr B) *
        ρ r₃ (SpecialLinearGroup.map Fr C)) * (𝒩)⁻¹ =
      (𝒩 * ρ r₁ (SpecialLinearGroup.map Fr A) * (𝒩)⁻¹) *
        (𝒩 * ρ r₂ (SpecialLinearGroup.map Fr B) * (𝒩)⁻¹) *
        (𝒩 * ρ r₃ (SpecialLinearGroup.map Fr C) * (𝒩)⁻¹) := by group
    _ = ρ r₂ (twHom Fr M₁ A) * ρ r₃ (twHom Fr M₂ B) * ρ r₁ (twHom Fr M₃ C) := by
      rw [h₁, h₂, h₃]
      rfl
    _ = _ := by
      rw [mul_assoc (ρ r₁ _)]
      exact ((hc12 _ _).mul_right (hc13 _ _)).eq.symm

variable {p f : ℕ} [Fact p.Prime] [CharP L p] [IsAlgClosed L]

theorem d4_rk3_pElt (hf : 1 ≤ f) (h₁ : IsRoot TwistTag.D4.tag r₁)
    (h₂ : IsRoot TwistTag.D4.tag r₂) (h₃ : IsRoot TwistTag.D4.tag r₃)
    (e₁ : permLattice TwistTag.D4.perm r₁ = -r₂) (e₂ : permLattice TwistTag.D4.perm r₂ = -r₃)
    (e₃ : permLattice TwistTag.D4.perm r₃ = r₁) (hc12 : ∀ A B : SL2 L, Commute (ρ r₁ A) (ρ r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (ρ r₁ A) (ρ r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (ρ r₂ B) (ρ r₃ C)) :
    ∃ u : ModGL TwistTag.D4.tag L, u ∈ adjointGroup TwistTag.D4.tag L ∧ u ≠ 1 ∧ u ^ p = 1 ∧
      trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) u *
        (trialityOpposition L)⁻¹ = u ∧
      ∀ a : Fin TwistTag.D4.tag.rank → Lˣ, rootChar a r₁ = 1 → rootChar a r₂ = 1 →
        rootChar a r₃ = 1 →
          rootDiagUnit TwistTag.D4.tag a * u = u * rootDiagUnit TwistTag.D4.tag a := by
  classical
  have hp : p.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  obtain ⟨s₁, s₂, y, hr₁, hr₂, hr₃⟩ := d4_rk3_rels h₁ h₂ h₃ e₁ e₂ e₃ (L := L)
  set M₁ : GL (Fin 2) L := diagUnitOne s₁ with hM₁
  set M₂ : GL (Fin 2) L := diagUnitOne s₂ with hM₂
  set M₃ : GL (Fin 2) L := swapGL * diagUnitOne y with hM₃
  obtain ⟨k₃, _, _, _, hk₃⟩ := exists_finite_field_into p (3 * f) (by omega) L
  set Fr₃ : L →+* L := iterateFrobenius L p (3 * f) with hFr₃def
  have hFr₃ : ∀ c, Fr₃ c = c ^ Nat.card k₃ := fun c => by
    rw [hk₃]
    exact iterateFrobenius_def p (3 * f) c
  have hFr3eq : Fr.comp (Fr.comp Fr) = Fr₃ := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, hFrdef, hFr₃def, iterateFrobenius_def]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  set g : GL (Fin 2) L := M₃ * GeneralLinearGroup.map Fr (M₂ * GeneralLinearGroup.map Fr M₁)
    with hgdef
  have hg : g = swapGL * diagUnitOne (y * Units.map Fr.toMonoidHom
      (s₂ * Units.map Fr.toMonoidHom s₁)) := by
    rw [hgdef, hM₃, hM₂, hM₁, glMap_diagUnitOne, diagUnitOne_mul, glMap_diagUnitOne, mul_assoc,
      diagUnitOne_mul]
  obtain ⟨Pm, hPm⟩ := exists_twist_antidiag (K := k₃) Fr₃ hFr₃ 1
    (y * Units.map Fr.toMonoidHom (s₂ * Units.map Fr.toMonoidHom s₁)) g (by
      rw [hg, coe_swapGL_mul_diagUnitOne]
      simp)
  obtain ⟨hXmem, hXc, hXp⟩ := conj_sl2Upper_data (p := p) (k := k₃) Pm
  set X := conjSL Pm (sl2Upper L 1) with hXdef
  have hX : twHom Fr M₃ (twHom Fr M₂ (twHom Fr M₁ X)) = X := by
    rw [twHom_comp_three, hFr3eq, ← hgdef, ← hPm]
    exact (sl2_twistedFixed_iff Fr₃ (frobenius_fixed_iff Fr₃ hFr₃) Pm X).2 hXmem
  have hY : twHom Fr M₁ X ^ p = 1 := by rw [← map_pow, hXp, map_one]
  have hZ : twHom Fr M₂ (twHom Fr M₁ X) ^ p = 1 := by rw [← map_pow, hY, map_one]
  have hadj : ∀ r (A : SL2 L), ρ r A ∈ adjointGroup TwistTag.D4.tag L := fun r A =>
    (exceptional_Lang_root_rank_one_data TwistTag.D4.tag L r).2.2.2.2.1 A
  refine ⟨ρ r₁ X * ρ r₂ (twHom Fr M₁ X) * ρ r₃ (twHom Fr M₂ (twHom Fr M₁ X)),
    mul_mem (mul_mem (hadj _ _) (hadj _ _)) (hadj _ _), fun h => ?_, ?_, ?_, ?_⟩
  · exact hXc (threeA1Tw_mem_center_of_mul_eq_one hc12 hc13 hc23 h).1
  · have hc : Commute (ρ r₁ X * ρ r₂ (twHom Fr M₁ X)) (ρ r₃ (twHom Fr M₂ (twHom Fr M₁ X))) :=
      (hc13 _ _).mul_left (hc23 _ _)
    rw [hc.mul_pow, (hc12 _ _).mul_pow, ← map_pow (ρ r₁), ← map_pow (ρ r₂), ← map_pow (ρ r₃),
      hXp, hY, hZ, map_one, map_one, map_one, mul_one, mul_one]
  · have h := d4_rk3_twist Fr hc12 hc13 hr₁ hr₂ hr₃ X (twHom Fr M₁ X)
      (twHom Fr M₂ (twHom Fr M₁ X))
    rw [hX] at h
    rw [twistHom_apply]
    conv_rhs => rw [← h]
    group
  · intro a ha₁ ha₂ ha₃
    have f : ∀ {r : Fin TwistTag.D4.tag.rank → ℤ}, IsRoot TwistTag.D4.tag r → rootChar a r = 1 →
        ∀ A : SL2 L, Commute (rootDiagUnit TwistTag.D4.tag a) (ρ r A) := fun hr har A =>
      (Subgroup.mem_centralizer_iff.1 ((rootDiagUnit_mem_centralizer_iff hr a).2 har) _
        ⟨A, rfl⟩).symm
    exact (((f h₁ ha₁ _).mul_right (f h₂ ha₂ _)).mul_right (f h₃ ha₃ _)).eq

end CFSG.OddStandard.GH71.S55
