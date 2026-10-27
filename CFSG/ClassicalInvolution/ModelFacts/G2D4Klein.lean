module

public import CFSG.LieType.Chevalley.CLSOddDiagramFourGroup
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairG2
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Count

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem exists_kleinFour_g2 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) :
    ∃ V : Subgroup ↥(adjointGroup Tag.G2 (GaloisField p e)),
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 4 := by
  set F := GaloisField p e with hF
  have hodd : Odd (Nat.card F) := by
    rw [GaloisField.card p e (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  have hneg : (-1 : Fˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h)
  let i₀ : Fin Tag.G2.rank := ⟨0, by decide⟩
  let i₁ : Fin Tag.G2.rank := ⟨1, by decide⟩
  let b : Fin Tag.G2.rank → Fin Tag.G2.rank → Fˣ := fun i j => (-1 : Fˣ) ^ Tag.G2.cartan i j
  have hx : ∀ i : Fin Tag.G2.rank, simpleRootSL2 Tag.G2 F i (-1) = rootDiagUnit Tag.G2 (b i) := by
    intro i
    rw [neg_one_eq_HSL, simpleRootSL2_HSL]
    exact torusElt_eq_rootDiagUnit i (-1)
  set x₀ : ↥(adjointGroup Tag.G2 F) :=
    ⟨simpleRootSL2 Tag.G2 F i₀ (-1), simpleRootSL2_mem_adjointGroup i₀ (-1)⟩ with hx₀
  set x₁ : ↥(adjointGroup Tag.G2 F) :=
    ⟨simpleRootSL2 Tag.G2 F i₁ (-1), simpleRootSL2_mem_adjointGroup i₁ (-1)⟩ with hx₁
  have hsq : ∀ i : Fin Tag.G2.rank, simpleRootSL2 Tag.G2 F i (-1) * simpleRootSL2 Tag.G2 F i (-1) =
      1 := by
    intro i
    rw [← map_mul]
    have h : (-1 : SL(2, F)) * -1 = 1 := by simp
    rw [h, map_one]
  have hx₀sq : x₀ * x₀ = 1 := Subtype.ext (hsq i₀)
  have hx₁sq : x₁ * x₁ = 1 := Subtype.ext (hsq i₁)
  have hcomm : x₀ * x₁ = x₁ * x₀ := by
    apply Subtype.ext
    show simpleRootSL2 Tag.G2 F i₀ (-1) * simpleRootSL2 Tag.G2 F i₁ (-1) =
      simpleRootSL2 Tag.G2 F i₁ (-1) * simpleRootSL2 Tag.G2 F i₀ (-1)
    rw [hx, hx, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hx₀1 : x₀ ≠ 1 := by
    intro h
    have h1 : simpleRootSL2 Tag.G2 F i₀ (-1) = simpleRootSL2 Tag.G2 F i₀ 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := simpleRootSL2_injective hK2 i₀ h1
    have h3 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h2
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using h3)
  have hx₁1 : x₁ ≠ 1 := by
    intro h
    have h1 : simpleRootSL2 Tag.G2 F i₁ (-1) = simpleRootSL2 Tag.G2 F i₁ 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := simpleRootSL2_injective hK2 i₁ h1
    have h3 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h2
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using h3)
  have hne : x₀ ≠ x₁ := by
    intro h
    have h1 : rootDiagUnit Tag.G2 (b i₀) = rootDiagUnit Tag.G2 (b i₁) := by
      rw [← hx, ← hx]
      exact congrArg Subtype.val h
    have h2 := congrFun (rootDiagUnit_injective h1) i₀
    have h3 : Tag.G2.cartan i₀ i₀ = 2 := by decide
    have h4 : Tag.G2.cartan i₁ i₀ = -3 := by decide
    simp only [b, h3, h4] at h2
    have h5 : (-1 : Fˣ) ^ (-3 : ℤ) = -1 := by
      rw [zpow_neg, zpow_ofNat]
      simp [pow_succ]
    rw [h5] at h2
    have h6 : (-1 : Fˣ) ^ (2 : ℤ) = 1 := by simp
    rw [h6] at h2
    exact hneg h2.symm
  obtain ⟨V, -, -, hVel, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.FourGroup.exists_kleinFour hx₀sq hx₁sq hcomm hx₀1 hx₁1 hne
  refine ⟨V, fun u hu v hv => ?_, fun u hu => ?_, hVcard⟩
  · exact congrArg Subtype.val (hVel.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  · have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) u hu
    rwa [sq] at this

open CFSG.LieType.Steinberg.TwistedD4 in
theorem exists_kleinFour_td4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) :
    ∃ V : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)),
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 4 := by
  set K0 := GaloisField p (3 * e) with hK0
  have hodd : Odd (Nat.card K0) := by
    rw [GaloisField.card p (3 * e) (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hchar : ringChar K0 ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  set σ := iterateFrobenius K0 p e with hσ
  obtain ⟨A, hAC, hAel, hAcard, -⟩ :=
    odd_diagram_coordinate_fields_fixed_four_group TwistTag.D4 K0 hchar σ
  have h3 :=
    CFSG.ClassicalInvolution.RouteD.G2D4.map_twistedGroup_eq_graphFixedRootGroup p e hp2 he
  let ι : ↥(twistedGroup σ) →* ModGL TwistTag.D4.tag K0 :=
    (adjointGroup d4 K0).subtype.comp (twistedGroup σ).subtype
  have hι : Function.Injective ι := fun x y h =>
    Subtype.ext (Subtype.ext h)
  have hrange : ι.range = graphFixedRootGroup TwistTag.D4 K0 σ := by
    rw [← h3, MonoidHom.range_comp, Subgroup.range_subtype]
  have hAle : A ≤ ι.range := hrange ▸ hAC
  have hmap : (A.comap ι).map ι = A := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hAle]
  have := hAel
  refine ⟨A.comap ι, fun x hx y hy => ?_, fun x hx => ?_, ?_⟩
  · apply hι
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨ι x, hx⟩ : A) ⟨ι y, hy⟩)
  · apply hι
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) (ι x) hx
    rwa [sq, ← map_mul, ← map_one ι] at h2
  · rw [← Subgroup.card_map_of_injective hι, hmap]
    exact hAcard

theorem exists_kleinFour_model (hp2 : p ≠ 2) {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n e : ℕ} (ht : t = .G2 ∨ t = .trialityD4)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e) :
    ∃ V : Subgroup (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).K,
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 4 := by
  rcases ht with rfl | rfl
  · exact exists_kleinFour_g2 hp2 hadm.2.1
  · exact exists_kleinFour_td4 hp2 hadm.2.1

end CFSG.ClassicalInvolution.G2D4Models
