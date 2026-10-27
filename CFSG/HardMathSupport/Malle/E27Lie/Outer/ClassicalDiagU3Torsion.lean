module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagThreeTorsion
public import CFSG.RankThree.PartOne.FOC.ComponentFact
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Curtis.Coordinator

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {ℓ f : ℕ} {F : Type} [Field F] {h : UnitaryFieldData ℓ f F}

theorem normOneScalars_le_center (n : ℕ) :
    normOneScalars h (gramSU h (idGram F n)) n ≤ Subgroup.center ↥(gramSU h (idGram F n)) := by
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro g'
  obtain ⟨c, -, -, hc⟩ := hg
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (GeneralLinearGroup.scalar_commute c _).symm

theorem card_normOneScalars_le_three [Finite F] {H : Subgroup (GL (Fin 3) F)} :
    Nat.card (normOneScalars h H 3) ≤ 3 := by
  classical
  let ι : normOneScalars h H 3 → rootsOfUnity 3 F := fun g =>
    ⟨Classical.choose g.2,
      (mem_rootsOfUnity 3 _).2 (Classical.choose_spec g.2).2.1⟩
  have hι : Function.Injective ι := by
    intro g g' hgg
    have e : Classical.choose g.2 = Classical.choose g'.2 :=
      congrArg (fun z : rootsOfUnity 3 F => (z : Fˣ)) hgg
    apply Subtype.ext
    apply Subtype.ext
    rw [(Classical.choose_spec g.2).2.2, (Classical.choose_spec g'.2).2.2, e]
  exact (Nat.card_le_card_of_injective ι hι).trans (_root_.card_rootsOfUnity F 3)

theorem card_le_three_of_fixed_exponent_three_U [Finite F] (hg : 3 ∣ ℓ ^ f + 1)
    (y : primeFormUnitary h (idGram F 3)) (c : Fˣ)
    (hc : (y : GL (Fin 3) F) ^ 3 = GeneralLinearGroup.scalar (Fin 3) c)
    (hnp : ∀ b : F, b ^ 3 ≠ c) (T : Subgroup (primeFormP h (idGram F 3)))
    (hfix : ∀ x ∈ T, primeFormConjHom h (idGram F 3) y x = x) (hT3 : ∀ x ∈ T, x ^ 3 = 1) :
    Nat.card T ≤ 3 := by
  classical
  have hirr : Irreducible (X ^ 3 - C (c : F) : F[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_three hnp
  let G := gramSU h (idGram F 3)
  let Z : Subgroup G := normOneScalars h G 3
  let π : G →* primeFormP h (idGram F 3) := QuotientGroup.mk' Z
  have hπker : π.ker = Z := QuotientGroup.ker_mk' _
  let slc : G → G := fun g => ⟨(y : GL (Fin 3) F) * g * (y : GL (Fin 3) F)⁻¹,
    conj_mem_gramSU h _ y.2 g.2⟩
  have hπslc : ∀ g : G, primeFormConjHom h (idGram F 3) y (π g) = π (slc g) := fun g =>
    primeFormConjHom_mk h (idGram F 3) y g
  have hmem : ∀ g : G, π g ∈ T → slc g * g⁻¹ ∈ Z := by
    intro g hg'
    rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, ← hπslc, hfix _ hg', mul_inv_cancel]
  have hslc_mul : ∀ g g' : G, slc (g * g') = slc g * slc g' := fun g g' =>
    Subtype.ext (by
      change (y : GL (Fin 3) F) * ((g : GL (Fin 3) F) * g') * (y : GL (Fin 3) F)⁻¹ =
        ((y : GL (Fin 3) F) * g * (y : GL (Fin 3) F)⁻¹) *
          ((y : GL (Fin 3) F) * g' * (y : GL (Fin 3) F)⁻¹)
      group)
  have hslc_inv : ∀ g : G, slc g⁻¹ = (slc g)⁻¹ := fun g =>
    Subtype.ext (by
      change (y : GL (Fin 3) F) * (g : GL (Fin 3) F)⁻¹ * (y : GL (Fin 3) F)⁻¹ =
        ((y : GL (Fin 3) F) * g * (y : GL (Fin 3) F)⁻¹)⁻¹
      group)
  let Tt : Subgroup G := T.comap π
  let Λ : Tt →* Z :=
    { toFun := fun g => ⟨slc g * (g : G)⁻¹, hmem g g.2⟩
      map_one' := by
        apply Subtype.ext
        change slc 1 * (1 : G)⁻¹ = 1
        have : slc 1 = 1 := Subtype.ext (by
          change (y : GL (Fin 3) F) * 1 * (y : GL (Fin 3) F)⁻¹ = 1
          group)
        rw [this]; group
      map_mul' := by
        intro g g'
        apply Subtype.ext
        have hz := Subgroup.mem_center_iff.1 (normOneScalars_le_center 3 (hmem g' g'.2))
        have e : slc g * (slc g' * (g' : G)⁻¹ * (g : G)⁻¹) =
            slc g * (g : G)⁻¹ * (slc g' * (g' : G)⁻¹) := by
          rw [← hz, mul_assoc]
        change slc (g * g') * ((g : G) * g')⁻¹ = (slc g * (g : G)⁻¹) * (slc g' * (g' : G)⁻¹)
        rw [hslc_mul, ← e]
        group }
  let π' : Tt →* T := π.subgroupComap T
  have hπ' : Function.Surjective π' :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective Z)
  have hker1 : π'.ker ≤ Λ.ker := by
    intro g hg'
    rw [MonoidHom.mem_ker] at hg' ⊢
    have h1 : π g = 1 := congrArg Subtype.val hg'
    have : (g : G) ∈ Z := by rw [← hπker]; exact h1
    obtain ⟨d, -, -, hgd⟩ := this
    apply Subtype.ext
    show slc g * (g : G)⁻¹ = 1
    rw [mul_inv_eq_one]
    apply Subtype.ext
    change (y : GL (Fin 3) F) * (g : GL (Fin 3) F) * (y : GL (Fin 3) F)⁻¹ = (g : GL (Fin 3) F)
    rw [hgd, (commute_scalar d (y : GL (Fin 3) F)).eq, mul_inv_cancel_right]
  have hker2 : Λ.ker ≤ π'.ker := by
    intro g hg'
    rw [MonoidHom.mem_ker] at hg' ⊢
    have h1 : slc g * (g : G)⁻¹ = 1 := congrArg Subtype.val hg'
    have hcomm_G : slc g = g := mul_inv_eq_one.1 h1
    have hcomm_GL : (y : GL (Fin 3) F) * (g : GL (Fin 3) F) * (y : GL (Fin 3) F)⁻¹ =
        (g : GL (Fin 3) F) := congrArg Subtype.val hcomm_G
    have hcomm : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((g : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have : (y : GL (Fin 3) F) * (g : GL (Fin 3) F) = (g : GL (Fin 3) F) * (y : GL (Fin 3) F) := by
        rw [mul_inv_eq_iff_eq_mul] at hcomm_GL
        exact hcomm_GL
      exact congrArg (fun z : GL (Fin 3) F => (z : Matrix (Fin 3) (Fin 3) F)) this
    have hg3 : (g : G) ^ 3 ∈ Z := by
      rw [← hπker, MonoidHom.mem_ker, map_pow]
      exact hT3 _ g.2
    obtain ⟨d, -, -, hgd⟩ := hg3
    have hpow : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
        Matrix.scalar (Fin 3) (d : F) := by
      have e1 : ((g : GL (Fin 3) F)) ^ 3 = GeneralLinearGroup.scalar (Fin 3) d := by
        rw [← hgd]; rfl
      have := congrArg (fun z : GL (Fin 3) F => (z : Matrix (Fin 3) (Fin 3) F)) e1
      simpa [Units.val_pow_eq_pow_val] using this
    obtain ⟨s, hs⟩ := scalar_of_commute_matrix (y : GL (Fin 3) F) c hc hirr
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) hcomm g.1.2.2 (d : F) hpow
    have hs3 : s ^ 3 = 1 := by
      have := (g : G).2.2
      rw [hs] at this
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using this
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs3
    have hsn : h.norm s = 1 := by
      obtain ⟨k, hk⟩ := hg
      rw [h.norm_eq_pow, hk, pow_mul, hs3, one_pow]
    apply Subtype.ext
    change π (g : G) = 1
    rw [← MonoidHom.mem_ker, hπker]
    refine ⟨Units.mk0 s hs0, ?_, Units.ext (by simpa using hs3), ?_⟩
    · simpa using hsn
    · apply Units.ext
      rw [hs]
      simp [Matrix.scalar_apply]
  let Φ : T →* Z := MonoidHom.liftOfSurjective π' hπ' ⟨Λ, hker1⟩
  have hΦ : ∀ g : Tt, Φ (π' g) = Λ g := fun g =>
    π'.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hπ') ⟨Λ, hker1⟩ g
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    obtain ⟨g, rfl⟩ := hπ' t
    rw [hΦ] at ht
    exact hker2 ht
  exact (Nat.card_le_card_of_injective Φ hΦinj).trans card_normOneScalars_le_three

end CFSG.HardMathSupport.Malle.E27Lie
