module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Jordan.HeisRepACore
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Jordan.HeisRepAComb

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


namespace HeisA

theorem commute_conj {G : Type*} [Group G] (g : G) {x z : G} (h : Commute x z) :
    Commute (g * x * g⁻¹) (g * z * g⁻¹) := by
  show g * x * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * x * g⁻¹)
  calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
    _ = g * (z * x) * g⁻¹ := by rw [h.eq]
    _ = g * z * g⁻¹ * (g * x * g⁻¹) := by group

theorem fixed_elt_of_norm {G : Type*} [Group G] {ℓ : ℕ} {Fr : G →* G}
    {g0 n x y d B₁ B₂ : G} (hg0 : Fr g0 = g0 * n) (hxn : n * Fr x * n⁻¹ = x)
    (hx1 : x ≠ 1) (hxℓ : x ^ ℓ = 1) (hxy : y * x * y⁻¹ = x) (hxd : d * x * d⁻¹ = x)
    (hB₁ : g0⁻¹ * B₁ * g0 = d) (hB₂ : g0⁻¹ * B₂ * g0 = y) :
    g0 * x * g0⁻¹ ≠ 1 ∧ (g0 * x * g0⁻¹) ^ ℓ = 1 ∧ Fr (g0 * x * g0⁻¹) = g0 * x * g0⁻¹ ∧
      Commute (g0 * x * g0⁻¹) B₁ ∧ Commute (g0 * x * g0⁻¹) B₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hx1
    calc x = g0⁻¹ * (g0 * x * g0⁻¹) * g0 := by group
      _ = 1 := by rw [h]; group
  · have := conj_pow (a := g0) (b := x) (i := ℓ)
    rw [this, hxℓ]
    group
  · rw [map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Fr x * (g0 * n)⁻¹ = g0 * (n * Fr x * n⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxn]
  · have hB : B₁ = g0 * d * g0⁻¹ := by
      rw [← hB₁]
      group
    rw [hB]
    refine commute_conj g0 ?_
    show x * d = d * x
    exact (mul_inv_eq_iff_eq_mul.1 hxd).symm
  · have hB : B₂ = g0 * y * g0⁻¹ := by
      rw [← hB₂]
      group
    rw [hB]
    refine commute_conj g0 ?_
    show x * y = y * x
    exact (mul_inv_eq_iff_eq_mul.1 hxy).symm

end HeisA

theorem e6HeisFrameFixedEltA_holds : E6HeisFrameFixedEltA := by
  intro K _ _ hK3 hK4 E hE hcard hd F hA
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h3 : ¬ 3 ∣ Nat.card K := not_three_dvd_card_of_ringChar K hK3
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  set ℓ := ringChar K with hℓdef
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  have hFrEq : F.Fr = iterateFrobenius L ℓ (f : ℕ) := RingHom.ext fun c => by
    rw [F.hFr, iterateFrobenius_def, Nat.card_eq_fintype_card, hf]
  have hFrG : ∀ g : ModGL Tag.E6 L, entrywiseFrobGL Tag.E6 L ℓ (f : ℕ) g =
      Units.map (entrywiseHom F.Fr) g := fun g => by
    rw [hFrEq]
  have hcomp : F.Fr.comp ι = ι := RingHom.ext fun c => by
    change F.Fr (ι c) = ι c
    rw [F.hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hFix : ∀ g : ModGL Tag.E6 K,
      Units.map (entrywiseHom F.Fr) (baseChangeGL ι g) = baseChangeGL ι g := fun g => by
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hpq : Nat.Coprime 3 (ℓ ^ (f : ℕ)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (by rw [← hf, ← Nat.card_eq_fintype_card]; exact h3)
  have hinj := e6InndiagConj_injective K hK4
  have hg₂3 : F.g₂ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ F.hE₂)
  have hd₂3 : (F.g₂ : ModGL Tag.E6 K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₂3
  have hB₂3 : (baseChangeGL ι (F.g₂ : ModGL Tag.E6 K)) ^ 3 = 1 := by
    rw [← map_pow, hd₂3, map_one]
  have hy3 : (F.g0⁻¹ * baseChangeGL ι (F.g₂ : ModGL Tag.E6 K) * F.g0) ^ 3 = 1 := by
    have := conj_pow (a := F.g0⁻¹) (b := baseChangeGL ι (F.g₂ : ModGL Tag.E6 K)) (i := 3)
    simp only [inv_inv] at this
    rw [this, hB₂3]
    group
  obtain ⟨C, π, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9⟩ := classA_components hA
  let D : HeisA.CompData F.a F.w := ⟨C, π, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9⟩
  have hT1 : canonicalRep (coxeterSystem Tag.E6) L F.w' *
      entrywiseFrobGL Tag.E6 L ℓ (f : ℕ) (rootDiagUnit Tag.E6 F.a) *
      (canonicalRep (coxeterSystem Tag.E6) L F.w')⁻¹ = rootDiagUnit Tag.E6 F.a := by
    rw [hFrG]
    exact F.hT.2
  have hT2 : rootDiagUnit Tag.E6 F.a = canonicalRep (coxeterSystem Tag.E6) L F.w' *
      rootDiagUnit Tag.E6 (F.a ^ ℓ ^ (f : ℕ)) * (canonicalRep (coxeterSystem Tag.E6) L F.w')⁻¹ := by
    rw [← entrywiseFrobGL_rootDiagUnit_eq_pow ℓ (f : ℕ) F.a]
    exact hT1.symm
  have hw' : ∀ (_ : Unit) (v : Fin Tag.E6.rank → ℤ),
      rootChar F.a (F.w' • v) = rootChar F.a v ^ ℓ ^ (f : ℕ) := by
    intro _ v
    have := (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) F.a (F.a ^ ℓ ^ (f : ℕ)) F.w').1 hT2 v
    rw [this, rootChar_pow']
  have himg := image_familyKernel_of_pow ℓ hpq (fun _ : Unit => F.a) (fun _ i => F.ha3 i)
    (w := F.w') hw'
  have hnN : canonicalRep (coxeterSystem Tag.E6) L F.w' ∈
      Subgroup.normalizer (familyGroup (K := L) (fun _ : Unit => F.a) : Set (ModGL Tag.E6 L)) :=
    canonicalRep_mem_normalizer_of_image himg
  have himg' : (fun α => F.w' • α) '' rootCharKernel F.a = rootCharKernel F.a := by
    rw [← HeisA.familyKernel_unit]
    exact himg
  have hgSig : ∀ β ∈ rootCharKernel F.a, F.w' • β ∈ rootCharKernel F.a := fun β hβ => by
    have h' : F.w' • β ∈ (fun α => F.w' • α) '' rootCharKernel F.a := ⟨β, hβ, rfl⟩
    rwa [himg'] at h'
  have hg0 : Units.map (entrywiseHom F.Fr) F.g0 =
      F.g0 * canonicalRep (coxeterSystem Tag.E6) L F.w' := F.hg0
  have hΦy : canonicalRep (coxeterSystem Tag.E6) L F.w' * entrywiseFrobGL Tag.E6 L ℓ (f : ℕ)
      (F.g0⁻¹ * baseChangeGL ι (F.g₂ : ModGL Tag.E6 K) * F.g0) *
      (canonicalRep (coxeterSystem Tag.E6) L F.w')⁻¹ =
      F.g0⁻¹ * baseChangeGL ι (F.g₂ : ModGL Tag.E6 K) * F.g0 := by
    rw [hFrG, map_mul, map_mul, map_inv, hg0, hFix]
    group
  obtain ⟨x, hxM, hx1, hxℓ, hxy, hxn⟩ := HeisA.exists_fixed_norm (L := L) (ℓ := ℓ)
    (f := (f : ℕ)) f.pos D F.hw F.hu F.hg₂ hy3 (HeisA.actsAs_canonicalRep F.w') hgSig hnN hΦy
  have hxcent := mem_familyCentralizer.1
    (familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => F.a) hxM)
  have hxn' : canonicalRep (coxeterSystem Tag.E6) L F.w' * Units.map (entrywiseHom F.Fr) x *
      (canonicalRep (coxeterSystem Tag.E6) L F.w')⁻¹ = x := by
    rw [← hFrG]
    exact hxn
  obtain ⟨hv1, hvℓ, hvF, hvc1, hvc2⟩ := HeisA.fixed_elt_of_norm
    (Fr := Units.map (entrywiseHom F.Fr)) hg0 hxn' hx1 hxℓ hxy (hxcent.2 ()) F.hg₁ rfl
  exact ⟨F.g0 * x * F.g0⁻¹, mul_mem (mul_mem F.hg0C hxcent.1) (inv_mem F.hg0C), hv1, hvℓ, hvF,
    hvc1, hvc2⟩

end CFSG.LieType.SeitzGeneration.ExcWideThree
