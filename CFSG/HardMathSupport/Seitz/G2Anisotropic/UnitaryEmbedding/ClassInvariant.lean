module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.CubeTorsionRoots
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLM2
public import CFSG.RankThree.PartOne.RF4.Basic

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U

section Abstract

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem finrank_range_diag_sub_one (c : ι → K) (D : (ι →₀ K) →ₗ[K] (ι →₀ K))
    (hD : ∀ v b, D v b = c b * v b) :
    Module.finrank K (LinearMap.range (D - 1)) = Nat.card {b // c b ≠ 1} := by
  classical
  have hrange : LinearMap.range (D - 1) = Finsupp.supported K K {b | c b ≠ 1} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [Finsupp.mem_supported']
      intro b hb
      have hcb : c b = 1 := by simpa using hb
      simp [hD, hcb]
    · rw [Finsupp.supported_eq_span_single]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have hb' : c b ≠ 1 := hb
      refine ⟨(c b - 1)⁻¹ • Finsupp.single b 1, ?_⟩
      ext b'
      simp only [LinearMap.sub_apply, Module.End.one_apply, Finsupp.coe_sub, Pi.sub_apply, hD,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases h : b = b'
      · subst h
        simp only [ite_true, mul_one]
        have : c b - 1 ≠ 0 := sub_ne_zero.2 hb'
        field_simp
      · simp [h]
  rw [hrange, (Finsupp.supportedEquivFinsupp (M := K) (R := K) {b | c b ≠ 1}).finrank_eq,
    Module.finrank_finsupp_self, Nat.card_eq_fintype_card]
  rfl

end Abstract

section Conj

variable {V K : Type} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_range_conj_sub_one (x : Module.End K V) (y : (Module.End K V)ˣ) :
    Module.finrank K (LinearMap.range ((y : Module.End K V) * x * ((y⁻¹ : (Module.End K V)ˣ) :
      Module.End K V) - 1)) = Module.finrank K (LinearMap.range (x - 1)) := by
  have hy : Function.Bijective (y : Module.End K V) :=
    (Module.End.isUnit_iff _).1 y.isUnit
  have hy' : Function.Bijective ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) :=
    (Module.End.isUnit_iff _).1 (y⁻¹).isUnit
  have e : (y : Module.End K V) * x * ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) - 1 =
      (y : Module.End K V) * (x - 1) * ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [e, Module.End.mul_eq_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 hy'.2), Module.End.mul_eq_comp, LinearMap.range_comp]
  exact (LinearEquiv.ofBijective (y : Module.End K V) hy).finrank_map_eq _

end Conj

section G2

variable {L : Type} [Field L]

theorem finrank_range_rootDiagUnit_sub_one (a : Fin Tag.G2.rank → Lˣ) :
    Module.finrank L (LinearMap.range
      ((rootDiagUnit .G2 a : Module.End L (RootModule .G2 L)) - 1)) =
      Nat.card {γ : {v : Fin Tag.G2.rank → ℤ // IsRoot .G2 v} // rootChar a γ.1 ≠ 1} := by
  classical
  have h := finrank_range_diag_sub_one (K := L) (ι := Label .G2)
    (fun ℓ => ((rootChar a (labelWt .G2 ℓ) : Lˣ) : L)) (rootDiag a)
    (fun v b => CFSG.SeitzReduction.F4Pilot.rootDiag_apply a v b)
  have e : ((rootDiagUnit .G2 a : Module.End L (RootModule .G2 L))) = rootDiag a := rfl
  rw [e, h]
  have hP : ∀ ℓ : Label .G2, ((rootChar a (labelWt .G2 ℓ) : Lˣ) : L) ≠ 1 ↔
      rootChar a (labelWt .G2 ℓ) ≠ 1 := fun ℓ => by simp
  rw [Nat.card_congr (Equiv.subtypeEquivRight hP)]
  refine Nat.card_congr
    { toFun := fun x => match x with
        | ⟨Sum.inl i, hx⟩ => (hx (rootChar_zero a)).elim
        | ⟨Sum.inr γ, hx⟩ => ⟨γ, hx⟩
      invFun := fun γ => ⟨Sum.inr γ.1, γ.2⟩
      left_inv := ?_
      right_inv := fun _ => rfl }
  rintro ⟨_ | γ, hx⟩
  · exact (hx (rootChar_zero a)).elim
  · rfl

theorem card_rootChar_ne_one_cubeTuple3 {ζ : Lˣ} (hζ : orderOf ζ = 3) (i j : Fin 3) :
    Nat.card {γ : {v : Fin Tag.G2.rank → ℤ // IsRoot .G2 v} //
      rootChar (cubeTuple3 ζ i j) γ.1 ≠ 1} =
      (rootList.toFinset.filter fun v => ¬ (3 : ℤ) ∣ cubeExp i.val j.val v).card := by
  have hiff : ∀ γ : {v : Fin Tag.G2.rank → ℤ // IsRoot .G2 v},
      rootChar (cubeTuple3 ζ i j) γ.1 ≠ 1 ↔ ¬ (3 : ℤ) ∣ cubeExp i.val j.val γ.1 := fun γ => by
    rw [ne_eq, cubeTuple3, rootChar_cubeTuple_eq_one_iff hζ]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun v : Fin Tag.G2.rank → ℤ => IsRoot .G2 v)
      (fun v => ¬ (3 : ℤ) ∣ cubeExp i.val j.val v)),
    Nat.card_congr (Equiv.subtypeEquivRight (q := fun v => v ∈ rootList.toFinset.filter
      fun v => ¬ (3 : ℤ) ∣ cubeExp i.val j.val v) (fun v => by
        simp only [Finset.mem_filter, List.mem_toFinset, isRoot_iff_mem_rootList])),
    Nat.card_eq_fintype_card, Fintype.card_coe]

theorem card_A2_eq : (rootList.toFinset.filter fun v =>
    ¬ (3 : ℤ) ∣ cubeExp ((0 : Fin 3) : ℕ) ((1 : Fin 3) : ℕ) v).card = 6 := by decide

theorem card_A1_eq : ∀ i j : Fin 3, i ≠ 0 → (rootList.toFinset.filter fun v =>
    ¬ (3 : ℤ) ∣ cubeExp i.val j.val v).card = 10 := by decide

theorem not_conj_rootDiag_A2_A1 {ζ : Lˣ} (hζ : orderOf ζ = 3) {i : Fin 3} (j : Fin 3)
    (hi : i ≠ 0) (y : ModGL .G2 L) :
    y * rootDiagUnit .G2 (cubeTuple3 ζ 0 1) * y⁻¹ ≠ rootDiagUnit .G2 (cubeTuple3 ζ i j) := by
  intro h
  have h1 := finrank_range_conj_sub_one (rootDiagUnit .G2 (cubeTuple3 ζ 0 1) :
    Module.End L (RootModule .G2 L)) y
  have h2 := congrArg (fun u : ModGL .G2 L => Module.finrank L (LinearMap.range
    ((u : Module.End L (RootModule .G2 L)) - 1))) h
  simp only [Units.val_mul] at h2
  rw [h1, finrank_range_rootDiagUnit_sub_one, finrank_range_rootDiagUnit_sub_one,
    card_rootChar_ne_one_cubeTuple3 hζ, card_rootChar_ne_one_cubeTuple3 hζ] at h2
  have h6 := card_A2_eq
  have h10 := card_A1_eq i j hi
  rw [Fin.val_zero, Fin.val_one] at h6 h2
  omega

end G2

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
