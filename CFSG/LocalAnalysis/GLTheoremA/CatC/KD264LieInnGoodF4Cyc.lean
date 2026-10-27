module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Even
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4SixEven
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4ThreeEven
public import CFSG.LieType.SeitzGeneration.ExtSeitzG2Odd
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.F4Weyl CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2 CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge

section TorusCoordinates


theorem perfectCentralizerPlanes_F4_of_actor_of_coord {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (w : WeylGroup Tag.F4)
    (hcoord : ∀ F : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, F c = c ^ Nat.card K) →
      ∀ P : Subgroup (adjointGroup Tag.F4 K), IsPGroup p P →
      ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K),
        g⁻¹ * Units.map (entrywiseHom F) g =
          canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w ∧
        ∀ y ∈ P, ∃ x ∈ torusGroup Tag.F4 (AlgebraicClosure K) ⊓ conjEntrywiseImage K g⁻¹,
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) = g * x * g⁻¹)
    (hact : ∀ F : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, F c = c ^ Nat.card K) →
      ∀ g : ModGL Tag.F4 (AlgebraicClosure K), g ∈ adjointGroup Tag.F4 (AlgebraicClosure K) →
      g⁻¹ * Units.map (entrywiseHom F) g =
        canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w →
      ∀ x ∈ torusGroup Tag.F4 (AlgebraicClosure K) ⊓ conjEntrywiseImage K g⁻¹, orderOf x = p →
        {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty →
      ∀ x₁ : adjointGroup Tag.F4 K,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹ →
          F4FourActorAt K (AlgebraicClosure K) p g x x₁) :
    PerfectCentralizerPlanes p (adjointGroup Tag.F4 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro E hE hEcard
  have hEpow : ∀ y ∈ E, y ^ p = 1 := fun y hy => hE.2 y hy
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨g, hg, hgn, hc⟩ := hcoord F hF E (IsPGroup.of_card hEcard)
  have hPT : ∀ y ∈ E, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (y : ModGL Tag.F4 K) * g ∈
        torusGroup Tag.F4 (AlgebraicClosure K) ⊓ conjEntrywiseImage K g⁻¹ := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := hc y hy
    rw [hxy, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  let i₀ : Fin Tag.F4.rank := ⟨0, by decide⟩
  let χ : E →* (AlgebraicClosure K)ˣ :=
    { toFun := fun y => Units.mk0 (torusRootChar (g⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((y : adjointGroup Tag.F4 K)) : ModGL Tag.F4 K) * g) (Pi.single i₀ 1))
        (torusRootChar_ne_zero (torusGroup_le_diagonalGroup (hPT y y.2).1) _)
      map_one' := by
        apply Units.ext
        simp only [Subgroup.coe_one, map_one, mul_one, inv_mul_cancel, Units.val_mk0,
          Units.val_one]
        exact torusRootChar_one _
      map_mul' := fun a b => by
        apply Units.ext
        simp only [Subgroup.coe_mul, map_mul, Units.val_mk0, Units.val_mul]
        rw [show g⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((a : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K))
                ((b : adjointGroup Tag.F4 K) : ModGL Tag.F4 K)) * g =
            (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((a : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g) *
            (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((b : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g) by group]
        exact torusRootChar_mul (torusGroup_le_diagonalGroup (hPT a a.2).1)
          (torusGroup_le_diagonalGroup (hPT b b.2).1) _ }
  obtain ⟨a, ha1, hχa⟩ := exists_ne_one_map_eq_one_of_card_sq hp
    (fun a => Subtype.ext (by simpa using hEpow a a.2)) hEcard χ
  obtain ⟨x, hxT, hxb⟩ := hc a a.2
  have hroot : torusRootChar (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((a : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g) (Pi.single i₀ 1) = 1 := by
    have h1 := congrArg Units.val hχa
    simpa [χ] using h1
  set ι' : adjointGroup Tag.F4 K →* ModGL Tag.F4 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup Tag.F4 K).subtype
  have hι'inj : Function.Injective ι' :=
    (baseChangeGL_injective (τ := Tag.F4) (algebraMap K (AlgebraicClosure K))).comp
      Subtype.val_injective
  have hxe : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((a : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g = x := by
    rw [hxb]; group
  have hap : orderOf (a : adjointGroup Tag.F4 K) = p :=
    orderOf_eq_prime (hEpow a a.2) (fun h => ha1 (Subtype.ext h))
  have hxp : orderOf x = p := by
    rw [show x = (MulAut.conj g⁻¹).toMonoidHom (ι' (a : adjointGroup Tag.F4 K)) by
        rw [← hxe]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rfl,
      orderOf_injective _ (MulAut.conj g⁻¹).injective, orderOf_injective ι' hι'inj, hap]
  have hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty :=
    ⟨Pi.single i₀ 1, isRoot_single Tag.F4 i₀, by rw [← hxe]; exact hroot⟩
  have hA := hact F hF g hg hgn x hxT hxp hne a hxb
  set R : Subgroup (adjointGroup Tag.F4 K) :=
    ⁅Subgroup.centralizer ({((a : adjointGroup Tag.F4 K))} : Set (adjointGroup Tag.F4 K)),
      Subgroup.centralizer ({((a : adjointGroup Tag.F4 K))} : Set (adjointGroup Tag.F4 K))⁆
  refine ⟨a, a.2, fun h => ha1 (Subtype.ext h), R, ?_, ?_, ?_⟩
  · exact Subgroup.commutator_le_self _
  · exact Subgroup.isPerfect_iff.mp hA.1.1
  · by_contra h
    exact hA.2.1 (hp.coprime_iff_not_dvd.mpr h)

end TorusCoordinates

section Three


theorem perfectCentralizerPlanes_adjointGroup_F4_three (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.F4 K) := by
  obtain ⟨ℓ, f, hℓ, -, hf, hK⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  refine perfectCentralizerPlanes_F4_of_actor_of_coord hp hp3 (f4Coxeter ^ 4) ?_ ?_
  · intro F hF P hP
    exact exists_lang_torus_coordinates_three_six K (AlgebraicClosure K) F hF
      (Or.inl ⟨rfl, rfl, hpd⟩) hp hp3 P hP
  · intro F hF g hg hgn x hx hxp hne x₁ hx₁
    by_cases h2 : ℓ = 2
    · subst h2
      exact f4ThreeActor_even K (AlgebraicClosure K) F hf hK hF hp hp3 hpd hg hgn hx hxp hne hx₁
    · exact f4ThreeActor_odd K (AlgebraicClosure K) F hℓ h2 hf hK hF hp hp3 hpd hg hgn hx hxp hne
        hx₁

end Three

section Six


theorem perfectCentralizerPlanes_adjointGroup_F4_six (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.F4 K) := by
  obtain ⟨ℓ, f, hℓ, -, hf, hK⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  refine perfectCentralizerPlanes_F4_of_actor_of_coord hp hp3 f4PhiSix ?_ ?_
  · intro F hF P hP
    exact exists_lang_torus_coordinates_three_six K (AlgebraicClosure K) F hF
      (Or.inr ⟨rfl, rfl, hpd⟩) hp hp3 P hP
  · intro F hF g hg hgn x hx hxp hne x₁ hx₁
    by_cases h2 : ℓ = 2
    · subst h2
      exact f4SixActor_even K (AlgebraicClosure K) F hf hK hF hp hp3 hpd hg hgn hx hxp hne hx₁
    · exact f4SixActor_odd K (AlgebraicClosure K) F hℓ h2 hf hK hF hp hp3 hpd hg hgn hx hxp hne
        hx₁

end Six

section Four


theorem perfectCentralizerPlanes_adjointGroup_F4_four (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ Nat.card K ^ 2 + 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.F4 K) := by
  obtain ⟨ℓ, f, hℓ, -, hf, hK⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  refine perfectCentralizerPlanes_F4_of_actor_of_coord hp (by omega) (f4Coxeter ^ 3) ?_ ?_
  · intro F hF P hP
    exact exists_lang_torus_coordinates K (AlgebraicClosure K) F hF hp (by omega) hpd P hP
  · intro F hF g hg hgn x hx hxp hne x₁ hx₁
    by_cases h2 : ℓ = 2
    · subst h2
      exact f4FourActor_even K (AlgebraicClosure K) F hf hK hF hp (by omega) hpd hg hgn hx hxp
        hne hx₁
    · exact f4FourActor_odd K (AlgebraicClosure K) F hℓ h2 hf hK hF hp (by omega) hpd hg hgn hx
        hxp hne hx₁

end Four

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
