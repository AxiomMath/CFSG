module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddOpen
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRankOne

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD
open scoped MatrixGroups

section Model

variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem exists_asub_chart_field {ℓ f : ℕ} (hX : Nat.card X = (ℓ ^ f) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) :
    ∃ ι : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ,
      (∀ x : C0 σ, x ∈ Asub σ ↔ ∃ M, ι M = x) ∧
      ∀ (δ : X ≃+* X) M, fieldActor (t := TwistTag.D4) σ δ (ι M) =
        ι (Matrix.SpecialLinearGroup.map δ.toRingHom M) := by
  classical
  have hσ3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hX hσ
  have h3 : ∀ c : X, σ (σ (σ c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card (σ := σ.toRingHom) hX hσ
  set a₁ : Fin TwistTag.D4.foldedTag.rank := KS11Lie4Proof.d4Outer with ha₁
  have hL₁ : ∀ c : X, c ∈ orbitField TwistTag.D4 X σ.toRingHom a₁ := fun c => by
    rw [orbitField_D4_zero_eq_top σ h3]
    exact Subfield.mem_top c
  let f₁ : X →+* orbitField TwistTag.D4 X σ.toRingHom a₁ := (RingHom.id X).codRestrict _ hL₁
  let R := orbitRankOneHom TwistTag.D4 X σ.toRingHom a₁
  have hRC : ∀ N, R N ∈ graphFixedRootGroup TwistTag.D4 X σ.toRingHom := fun N =>
    CFSG.RankThree.Chevalley.orbitRankOneHom_mem_graphFixedRootGroup a₁ N
  let ι : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ :=
    (R.comp (Matrix.SpecialLinearGroup.map f₁)).codRestrict _ fun M => hRC _
  have hcoe : ∀ M, ((ι M : C0 σ) : ModGL TwistTag.D4.tag X) =
      R (Matrix.SpecialLinearGroup.map f₁ M) := fun M => rfl
  refine ⟨ι, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨N, hN⟩ := hx
      refine ⟨Matrix.SpecialLinearGroup.map (orbitField TwistTag.D4 X σ.toRingHom a₁).subtype N,
        Subtype.ext ?_⟩
      rw [hcoe]
      have : Matrix.SpecialLinearGroup.map f₁
          (Matrix.SpecialLinearGroup.map (orbitField TwistTag.D4 X σ.toRingHom a₁).subtype N) =
            N := by
        refine Subtype.ext ?_
        ext i j
        simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
          Matrix.map_apply]
        rfl
      rw [this]
      exact hN
    · rintro ⟨M, rfl⟩
      exact ⟨Matrix.SpecialLinearGroup.map f₁ M, hcoe M⟩
  · intro δ M
    have hι_up : ∀ c : X, ι (uSL c) = fixedOrbitX TwistTag.D4 X σ.toRingHom a₁ (f₁ c) := by
      intro c
      apply Subtype.ext
      rw [hcoe, map_uSL, orbitRankOneHom_uSL]
      rfl
    have hι_lo : ∀ c : X, ι (vSL c) = fixedOrbitY TwistTag.D4 X σ.toRingHom a₁ (f₁ c) := by
      intro c
      apply Subtype.ext
      rw [hcoe, map_vSL, orbitRankOneHom_vSL]
      rfl
    have key : (fieldActor (t := TwistTag.D4) σ δ).toMonoidHom.comp ι =
        ι.comp (Matrix.SpecialLinearGroup.map δ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := X)) ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show fieldActor (t := TwistTag.D4) σ δ (ι (uSL c)) =
          ι (Matrix.SpecialLinearGroup.map δ.toRingHom (uSL c))
        rw [map_uSL, hι_up, hι_up, fieldActor_fixedOrbitX]
        rfl
      · show fieldActor (t := TwistTag.D4) σ δ (ι (vSL c)) =
          ι (Matrix.SpecialLinearGroup.map δ.toRingHom (vSL c))
        rw [map_vSL, hι_lo, hι_lo, fieldActor_fixedOrbitY]
        rfl
    exact DFunLike.congr_fun key M

theorem fieldActor_mem_Asub {ℓ f : ℕ} (hX : Nat.card X = (ℓ ^ f) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) (δ : X ≃+* X) {a : C0 σ} (ha : a ∈ Asub σ) :
    fieldActor (t := TwistTag.D4) σ δ a ∈ Asub σ := by
  obtain ⟨ι, hιA, hιδ⟩ := exists_asub_chart_field σ hX hσ
  obtain ⟨M, rfl⟩ := (hιA a).1 ha
  rw [hιδ]
  exact (hιA _).2 ⟨_, rfl⟩

theorem isClassX_map {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) (α : MulAut (C0 σ))
    {x : C0 σ} (hx : TriOddIsClassX σ x) : TriOddIsClassX σ (α x) := by
  obtain ⟨-, hdec, -⟩ := odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf X hX σ hσ
  obtain ⟨⟨g, δ⟩, hgδ⟩ := (hdec α).exists
  obtain ⟨h, hh⟩ := hx
  set φ := fieldActor (t := TwistTag.D4) σ δ with hφ
  refine ⟨φ h * g⁻¹, ?_⟩
  have hαx : α x = g * φ x * g⁻¹ := by
    rw [hgδ]
    rfl
  have e : φ h * g⁻¹ * α x * (φ h * g⁻¹)⁻¹ = φ (h * x * h⁻¹) := by
    rw [hαx, map_mul, map_mul, map_inv]
    group
  rw [e]
  exact fieldActor_mem_Asub σ hX hσ δ hh

theorem exists_conj_gA2_of_classX {ℓ f : ℕ} (hX : Nat.card X = (ℓ ^ f) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) {L : Type} [Field L] [IsAlgClosed L] [Algebra X L]
    {ζ : Lˣ} (hζ : orderOf ζ = 3) {x : C0 σ} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxX : TriOddIsClassX σ x) :
    ∃ k ∈ adjointGroup TwistTag.D4.tag L,
      triEmb X σ L x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA2) * k⁻¹ := by
  have hσ3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hX hσ
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  obtain ⟨h, hh⟩ := hxX
  have hz3 : (h * x * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
  have hz1 : h * x * h⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨k, hk, hkz⟩ := exists_conj_dA_of_mem_short hσ3 hζ hh hz3 hz1
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [1, 2, 3, 2, 1]) with hn
  have hnA : n ∈ adjointGroup TwistTag.D4.tag L := canonicalRep_mem_adjointGroup _ L _
  have hdA : rootDiagUnit TwistTag.D4.tag (tup ζ gA) =
      n * rootDiagUnit TwistTag.D4.tag (tup ζ gA2) * n⁻¹ := by
    have := rootDiagUnit_tup_eq_conj (L := L) hζ3 [1, 2, 3, 2, 1] gA2
    rw [show wordExp [1, 2, 3, 2, 1] gA2 = gA by decide] at this
    rw [this, hn]
    group
  have hιh := triEmb_injective (K := X) (σ := σ) (L := L)
  refine ⟨(triEmb X σ L h)⁻¹ * k * n, ?_, ?_⟩
  · exact mul_mem (mul_mem (inv_mem (triEmb_mem_adjointGroup _)) hk) hnA
  · have e : triEmb X σ L x = (triEmb X σ L h)⁻¹ * triEmb X σ L (h * x * h⁻¹) *
        triEmb X σ L h := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [e, hkz, hdA]
    group

end Model

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape
