module

public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.KGD.D4Twist

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped Matrix MatrixGroups


variable {τ : Tag} {L : Type} [Field L]

theorem conj_rootSL2_of_conj_pinnedX_neg {m : ModGL τ L}
    (hX : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ μ : Lˣ, ∀ c : L,
      m * pinnedX τ L α c * m⁻¹ = pinnedX τ L (-α) (μ * c))
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ s : Lˣ, ∀ A : SL2 L, m * rootSL2 τ L β A * m⁻¹ =
      rootSL2 τ L (-β) (conjSL (diagUnitOne s) A) := by
  classical
  set γ := -β with hγ
  have hγroot : IsRoot τ γ := IsRoot.neg hβ
  have hinj := rootSL2_injective_of_field (τ := τ) (K := L) γ
  let Ψ : SL2 L →* ModGL τ L := (MulAut.conj m).toMonoidHom.comp (rootSL2 τ L β)
  obtain ⟨uβ, huβ, hεβ⟩ := exists_unit_zsmul_eq_mul (K := L) (pinnedSign_eq τ β)
  obtain ⟨uγ, huγ, hεγ⟩ := exists_unit_zsmul_eq_mul (K := L) (pinnedSign_eq τ γ)
  obtain ⟨εβ, hεβ', hvβ⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  obtain ⟨εγ, hεγ', hvγ⟩ := exists_rootSL2_vSL_eq (K := L) hγroot
  obtain ⟨μ₁, hμ₁⟩ := hX β hβ
  obtain ⟨μ₂, hμ₂⟩ := hX (-β) (IsRoot.neg hβ)
  have hneg : -(-β) = -γ := by rw [hγ]
  rw [hneg] at hμ₂
  have hεγ'' : (εγ : L) * εγ = 1 := hεγ'
  let a : Lˣ := uγ⁻¹ * μ₁ * uβ
  let b : Lˣ := Units.mkOfMulEqOne εγ εγ hεγ' * μ₂ * Units.mkOfMulEqOne εβ εβ hεβ'
  have hΨu : ∀ c, Ψ (uSL c) = rootSL2 τ L γ (uSL ((a : L) * c)) := by
    intro c
    change m * rootSL2 τ L β (uSL c) * m⁻¹ = _
    rw [rootSL2_uSL_eq, hεβ, hμ₁, rootSL2_uSL_eq, hεγ]
    congr 1
    simp only [a, Units.val_mul, Units.val_inv_eq_inv_val]
    have : (uγ : L) ≠ 0 := uγ.ne_zero
    field_simp
  have hΨv : ∀ c, Ψ (vSL c) = rootSL2 τ L γ (vSL ((b : L) * c)) := by
    intro c
    change m * rootSL2 τ L β (vSL c) * m⁻¹ = _
    rw [hvβ, hμ₂, hvγ]
    congr 1
    simp only [b, Units.val_mul, Units.val_mkOfMulEqOne]
    linear_combination (-(μ₂ * (εβ * c))) * hεγ''
  have hrange : ∀ A : SL2 L, Ψ A ∈ (rootSL2 τ L γ).range := by
    intro A
    have hle : (⊤ : Subgroup (SL2 L)) ≤ (rootSL2 τ L γ).range.comap Ψ := by
      rw [← sl2_closure_upper_lower (K := L)]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨uSL ((a : L) * c), (hΨu c).symm⟩
      · exact ⟨vSL ((b : L) * c), (hΨv c).symm⟩
    exact hle (Subgroup.mem_top A)
  let T : SL2 L →* SL2 L := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    (Ψ.codRestrict _ hrange)
  have hT : ∀ A, rootSL2 τ L γ (T A) = Ψ A := fun A => by
    have := (MonoidHom.ofInjective hinj).apply_symm_apply ⟨Ψ A, hrange A⟩
    exact congrArg Subtype.val this
  have hu : ∀ c, T (sl2Upper L c) = sl2Upper L ((a : L) * (RingEquiv.refl L) c) := fun c =>
    hinj (by rw [hT]; exact hΨu c)
  have hl : ∀ c, T (sl2Lower L c) = sl2Lower L ((b : L) * (RingEquiv.refl L) c) := fun c =>
    hinj (by rw [hT]; exact hΨv c)
  obtain ⟨-, M, hM, hTM⟩ := sl2_semilinear_root_compatibility (RingEquiv.refl L) a b T hu hl
  refine ⟨a, fun A => ?_⟩
  have hMe : M = diagUnitOne a := Units.ext (by rw [hM, coe_diagUnitOne])
  have : T A = conjSL (diagUnitOne a) A := by
    apply Subtype.ext
    rw [hTM A, coe_conjSL, hMe]
    simp
  show Ψ A = _
  rw [← hT, this]

theorem exists_rootSL2_fixed_of_neg {K : Type} [Field K] [Finite K] [Algebra K L] [IsAlgClosed L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) {m : ModGL τ L}
    (hX : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ μ : Lˣ, ∀ c : L,
      m * pinnedX τ L α c * m⁻¹ = pinnedX τ L (-α) (μ * c))
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ P : GL (Fin 2) L, ∀ B : SL2 L,
      m * Units.map (entrywiseHom Fr) (rootSL2 τ L β B) * m⁻¹ = rootSL2 τ L β B ↔
        B ∈ (SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) := by
  obtain ⟨s, hs⟩ := conj_rootSL2_of_conj_pinnedX_neg hX hβ
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) hβ
  have hM : swapGL * diagUnitOne a * diagUnitOne s =
      (swapGL * diagUnitOne (a * s) : GL (Fin 2) L) := by
    rw [mul_assoc, diagUnitOne_mul]
  obtain ⟨P, hP⟩ := exists_twist_antidiag (K := K) Fr hFr 1 (a * s)
    (swapGL * diagUnitOne a * diagUnitOne s) (by
      rw [hM, coe_swapGL_mul_diagUnitOne]
      simp)
  refine ⟨P, fun B => a1_hS1_of_action Fr hFr P (fun B' => ?_) B⟩
  rw [hP, entrywise_rootSL2_of_field Fr β B', hs, ha, ← conjSL_mul]

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
