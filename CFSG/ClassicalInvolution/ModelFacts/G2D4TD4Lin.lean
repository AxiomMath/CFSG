module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Model
public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Prelim

variable {K : Type} [Field K]

theorem uSL_eq_sl2Upper {F : Type} [Field F] (c : F) : (uSL c : SL(2, F)) = sl2Upper c := rfl

theorem vSL_eq_sl2Lower {F : Type} [Field F] (c : F) : (vSL c : SL(2, F)) = sl2Lower c := rfl

theorem twistedIncl_mem_twistedFixedGroup {σ : K →+* K} (x : twistedGroup σ) :
    twistedIncl σ x ∈ twistedFixedGroup TwistTag.D4 K σ := by
  have h := twistedGroup_le_twistFixed σ x.2
  exact (coe_mem_twistedFixedGroup_iff TwistTag.D4 K σ (x : adjointGroup d4 K)).2
    ((mem_twistFixed TwistTag.D4 K σ).1 h)

theorem rootDiagUnit_conj_xPar_td4 (b : Fin d4.rank → Kˣ) {γ : Fin d4.rank → ℤ}
    (hγ : IsRoot d4 γ) (c : K) :
    rootDiagUnit d4 b * ((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 b)⁻¹ =
      ((xPar (rootOperatorFamily d4) γ ((rootChar b γ : K) * c) : adjointGroup d4 K) :
        ModGL d4 K) := by
  rw [ModelFacts.coe_xPar_d4 hγ, ModelFacts.coe_xPar_d4 hγ, rootDiagUnit_conj_pinnedX b hγ]
  congr 1
  ring

theorem canonicalRep_conj_xPar_td4 (w : WeylGroup d4) {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) :
    ∃ η : K, η * η = 1 ∧ ∀ c : K,
      canonicalRep (coxeterSystem d4) K w *
          ((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K) : ModGL d4 K) *
            (canonicalRep (coxeterSystem d4) K w)⁻¹ =
        ((xPar (rootOperatorFamily d4) (w • γ) (η * c) : adjointGroup d4 K) : ModGL d4 K) := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hγ
  have hwγ : IsRoot d4 (w • γ) := IsRoot.smul hγ w
  have s1 := ModelFacts.d4Sign_mul_self (K := K) γ
  have s2 := ModelFacts.d4Sign_mul_self (K := K) (w • γ)
  refine ⟨(ModelFacts.d4Sign (w • γ) : K) * ε * (ModelFacts.d4Sign γ : K), ?_, fun c => ?_⟩
  · calc (ModelFacts.d4Sign (w • γ) : K) * ε * (ModelFacts.d4Sign γ : K) *
        ((ModelFacts.d4Sign (w • γ) : K) * ε * (ModelFacts.d4Sign γ : K)) =
        ((ModelFacts.d4Sign (w • γ) : K) * (ModelFacts.d4Sign (w • γ) : K)) * (ε * ε) *
          ((ModelFacts.d4Sign γ : K) * (ModelFacts.d4Sign γ : K)) := by ring
      _ = 1 := by rw [s1, s2, hε]; ring
  · rw [ModelFacts.coe_xPar_d4 hγ, h, ModelFacts.coe_xPar_d4 hwγ]
    congr 1
    calc ε * ((ModelFacts.d4Sign γ : K) * c) =
        ((ModelFacts.d4Sign (w • γ) : K) * (ModelFacts.d4Sign (w • γ) : K)) *
          (ε * ((ModelFacts.d4Sign γ : K) * c)) := by rw [s2, one_mul]
      _ = (ModelFacts.d4Sign (w • γ) : K) *
          ((ModelFacts.d4Sign (w • γ) : K) * ε * (ModelFacts.d4Sign γ : K) * c) := by ring

end Prelim

section Long

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem twistedIncl_slLong_upper (c : fixedField σ) :
    twistedIncl σ (slLong σ hσ (uSL c)) =
      ((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (c : K) : adjointGroup d4 K) :
        ModGL d4 K) := by
  rw [twistedIncl_apply, slLong_val, uSL_eq_sl2Upper, slLongE_upper]

include hσ in
theorem twistedIncl_slLong_lower (c : fixedField σ) :
    twistedIncl σ (slLong σ hσ (vSL c)) =
      ((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) (c : K) : adjointGroup d4 K) :
        ModGL d4 K) := by
  rw [twistedIncl_apply, slLong_val, vSL_eq_sl2Lower, slLongE_lower]

theorem slLongE_neg_one : slLongE σ (-1) = torusElement d4 K (nd 2) (-1) := by
  have hmem : torusElement d4 K (nd 2) (-1) ∈
      rankOne (rootGroup (rootOperatorFamily d4) K) (nd 2) := torusElement_mem_rankOne (nd 2) (-1)
  set z : SL(2, K) := Matrix.SpecialLinearGroup.map (fixedField σ).subtype (-1) with hz
  have hy : restrictEquiv (rootOperatorFamily d4) cartan_two_zero
      ⟨torusElement d4 K (nd 2) (-1), hmem⟩ = z := by
    apply Subtype.ext
    show ((restrictHom (rootOperatorFamily d4) cartan_two_zero ⟨_, hmem⟩ :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
    rw [restrictHom_torusElement cartan_two_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz, Matrix.SpecialLinearGroup.coe_neg]
  have : (restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm z =
      ⟨torusElement d4 K (nd 2) (-1), hmem⟩ := by
    rw [MulEquiv.symm_apply_eq, hy]
  show (((restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm z :
    rankOne (rootGroup (rootOperatorFamily d4) K) (nd 2)) : adjointGroup d4 K) = _
  rw [this]

include hσ in
theorem twistedIncl_slLong_neg_one :
    twistedIncl σ (slLong σ hσ (-1)) = rootDiagUnit d4 (aLongTD4 K) := by
  rw [← torusElt_long_neg_one, twistedIncl_apply, slLong_val, slLongE_neg_one]
  rfl

include hσ in
theorem linAct_slLong_of_scalar (h2 : (2 : fixedField σ) ≠ 0)
    {x : twistedGroup σ} (hneg : x * slLong σ hσ (-1) * x⁻¹ = slLong σ hσ (-1))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {l₁ l₂ : K}
    (h₁ : ∀ c : K, twistedIncl σ x *
      ((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c : adjointGroup d4 K) : ModGL d4 K) *
        (twistedIncl σ x)⁻¹ =
      ((xPar (rootOperatorFamily d4) (ε • Pi.single (nd 2) 1) (l₁ * c) : adjointGroup d4 K) :
        ModGL d4 K))
    (h₂ : ∀ c : K, twistedIncl σ x *
      ((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) c : adjointGroup d4 K) : ModGL d4 K) *
        (twistedIncl σ x)⁻¹ =
      ((xPar (rootOperatorFamily d4) (-(ε • Pi.single (nd 2) 1)) (l₂ * c) : adjointGroup d4 K) :
        ModGL d4 K)) :
    LinAct (slLong σ hσ) x := by
  have hΦinj := slLong_injective hσ
  have hl : ∀ {s : ℤ} (hs : s = 1 ∨ s = -1) {l : K}
      (hmem : ((xPar (rootOperatorFamily d4) (s • Pi.single (nd 2) 1) l : adjointGroup d4 K) :
        ModGL d4 K) ∈ twistedFixedGroup TwistTag.D4 K σ), σ l = l := by
    intro s hs l hmem
    have hF := (coe_mem_twistedFixedGroup_iff TwistTag.D4 K σ _).1 hmem
    rw [twistC_xPar_smul_single σ hs, rhoPerm_two] at hF
    exact xPar_injective (isRoot_smul_single hs (nd 2)) hF
  have hl₁ : σ l₁ = l₁ := by
    have hy := twistedIncl_slLong_upper hσ (1 : fixedField σ)
    have hmem := twistedIncl_mem_twistedFixedGroup (x * slLong σ hσ (uSL (1 : fixedField σ)) * x⁻¹)
    rw [map_mul, map_mul, map_inv, hy] at hmem
    have h1 := h₁ ((1 : fixedField σ) : K)
    rw [h1] at hmem
    have := hl hε hmem
    simpa using this
  have hl₂ : σ l₂ = l₂ := by
    have hy := twistedIncl_slLong_lower hσ (1 : fixedField σ)
    have hmem := twistedIncl_mem_twistedFixedGroup (x * slLong σ hσ (vSL (1 : fixedField σ)) * x⁻¹)
    rw [map_mul, map_mul, map_inv, hy] at hmem
    have h1 := h₂ ((1 : fixedField σ) : K)
    rw [h1, ← neg_smul] at hmem
    have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with h | h <;> simp [h]
    have := hl hε' hmem
    simpa using this
  have hxF : ∀ c : fixedField σ,
      twistedIncl σ (x * slLong σ hσ (uSL c) * x⁻¹) =
        twistedIncl σ x * ((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (c : K) :
          adjointGroup d4 K) : ModGL d4 K) * (twistedIncl σ x)⁻¹ := fun c => by
    rw [map_mul, map_mul, map_inv, twistedIncl_slLong_upper hσ]
  have hxF' : ∀ c : fixedField σ,
      twistedIncl σ (x * slLong σ hσ (vSL c) * x⁻¹) =
        twistedIncl σ x * ((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) (c : K) :
          adjointGroup d4 K) : ModGL d4 K) * (twistedIncl σ x)⁻¹ := fun c => by
    rw [map_mul, map_mul, map_inv, twistedIncl_slLong_lower hσ]
  have hl₁' : l₁ ∈ fixedField σ := hl₁
  have hl₂' : l₂ ∈ fixedField σ := hl₂
  rcases hε with rfl | rfl
  · simp only [one_smul] at h₁ h₂
    refine linAct_of_signs_diag hΦinj h2 hneg (s := ⟨l₁, hl₁'⟩) (s' := ⟨l₂, hl₂'⟩) (fun c => ?_)
      (fun c => ?_)
    · apply twistedIncl_injective σ
      rw [hxF, h₁, twistedIncl_slLong_upper hσ]
      rfl
    · apply twistedIncl_injective σ
      rw [hxF', h₂, twistedIncl_slLong_lower hσ]
      rfl
  · simp only [neg_one_smul, neg_neg] at h₁ h₂
    refine linAct_of_signs_anti hΦinj h2 hneg (κ := ⟨l₁, hl₁'⟩) (κ' := ⟨l₂, hl₂'⟩) (fun c => ?_)
      (fun c => ?_)
    · apply twistedIncl_injective σ
      rw [hxF, h₁, twistedIncl_slLong_lower hσ]
      rfl
    · apply twistedIncl_injective σ
      rw [hxF', h₂, twistedIncl_slLong_upper hσ]
      rfl

include hσ in
theorem linAct_torus_long (h2 : (2 : fixedField σ) ≠ 0) {x : twistedGroup σ}
    {b : Fin d4.rank → Kˣ} (hx : twistedIncl σ x = rootDiagUnit d4 b) :
    LinAct (slLong σ hσ) x := by
  have hroot := isRoot_single d4 (nd 2)
  refine linAct_slLong_of_scalar hσ h2 ?_ (ε := 1) (Or.inl rfl)
    (l₁ := (rootChar b (Pi.single (nd 2) 1) : K)) (l₂ := (rootChar b (-Pi.single (nd 2) 1) : K))
    (fun c => ?_) (fun c => ?_)
  · apply twistedIncl_injective σ
    rw [map_mul, map_mul, map_inv, hx, twistedIncl_slLong_neg_one hσ, mul_inv_eq_iff_eq_mul,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  · rw [hx, rootDiagUnit_conj_xPar_td4 b hroot c, one_smul]
  · rw [hx, rootDiagUnit_conj_xPar_td4 b (IsRoot.neg hroot) c, one_smul]

include hσ in
theorem linAct_weyl_long (h2 : (2 : fixedField σ) ≠ 0) {x : twistedGroup σ} {w : WeylGroup d4}
    (hx : twistedIncl σ x = canonicalRep (coxeterSystem d4) K w)
    (hwa : w ∈ rootCharStabilizer (aLongTD4 K))
    (hε : w • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = Pi.single (nd 2) 1 ∨
      w • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = -Pi.single (nd 2) 1) :
    LinAct (slLong σ hσ) x := by
  have hroot := isRoot_single d4 (nd 2)
  obtain ⟨η₁, -, hη₁⟩ := canonicalRep_conj_xPar_td4 (K := K) w hroot
  obtain ⟨η₂, -, hη₂⟩ := canonicalRep_conj_xPar_td4 (K := K) w (IsRoot.neg hroot)
  have hneg : x * slLong σ hσ (-1) * x⁻¹ = slLong σ hσ (-1) := by
    apply twistedIncl_injective σ
    rw [map_mul, map_mul, map_inv, hx, twistedIncl_slLong_neg_one hσ]
    have hc := (mem_toralCentralizer.mp (canonicalRep_mem_toralCentralizer hwa)).2
    rw [mul_inv_eq_iff_eq_mul] at hc ⊢
    exact hc.symm
  rcases hε with h | h
  · refine linAct_slLong_of_scalar hσ h2 hneg (ε := 1) (Or.inl rfl) (l₁ := η₁) (l₂ := η₂)
      (fun c => ?_) (fun c => ?_)
    · rw [hx, hη₁ c, h, one_smul]
    · rw [hx, hη₂ c, smul_neg, h, one_smul]
  · refine linAct_slLong_of_scalar hσ h2 hneg (ε := -1) (Or.inr rfl) (l₁ := η₁) (l₂ := η₂)
      (fun c => ?_) (fun c => ?_)
    · rw [hx, hη₁ c, h, neg_one_smul]
    · rw [hx, hη₂ c, smul_neg, h, neg_one_smul]

end Long

section Short

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem sum_four_d4 (f : Fin d4.rank → ℤ) :
    ∑ j, f j = f (nd 0) + f (nd 1) + f (nd 2) + f (nd 3) :=
  Fin.sum_univ_four (fun j : Fin 4 => f j)

theorem weyl_smul_radical (w : WeylGroup d4) (x : Fin d4.rank → ℤ)
    (hx : x (nd 2) % 2 = 0 ∧ (x (nd 0) + x (nd 1) + x (nd 3)) % 2 = 0) :
    ((w • x) (nd 2) % 2 = 0 ∧ ((w • x) (nd 0) + (w • x) (nd 1) + (w • x) (nd 3)) % 2 = 0) ∧
      ∀ i, (w • x) i % 2 = x i % 2 := by
  induction w using (coxeterSystem d4).simple_induction_left with
  | one => exact ⟨by simpa using hx, fun i => by simp⟩
  | mul_simple_left w i ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := ih
    rw [mul_smul, simple_smul]
    set y := w • x with hy
    have hm : (∑ j, d4.cartan i j * y j) % 2 = 0 := by
      rw [sum_four_d4]
      fin_cases i
      · rw [show d4.cartan (nd 0) (nd 0) = 2 by decide, show d4.cartan (nd 0) (nd 1) = 0 by decide,
          show d4.cartan (nd 0) (nd 2) = -1 by decide, show d4.cartan (nd 0) (nd 3) = 0 by decide]
        omega
      · rw [show d4.cartan (nd 1) (nd 0) = 0 by decide, show d4.cartan (nd 1) (nd 1) = 2 by decide,
          show d4.cartan (nd 1) (nd 2) = -1 by decide, show d4.cartan (nd 1) (nd 3) = 0 by decide]
        omega
      · rw [show d4.cartan (nd 2) (nd 0) = -1 by decide,
          show d4.cartan (nd 2) (nd 1) = -1 by decide,
          show d4.cartan (nd 2) (nd 2) = 2 by decide, show d4.cartan (nd 2) (nd 3) = -1 by decide]
        omega
      · rw [show d4.cartan (nd 3) (nd 0) = 0 by decide, show d4.cartan (nd 3) (nd 1) = 0 by decide,
          show d4.cartan (nd 3) (nd 2) = -1 by decide, show d4.cartan (nd 3) (nd 3) = 2 by decide]
        omega
    have hkey : ∀ j, (reflect d4 i y) j % 2 = y j % 2 := by
      intro j
      have hr : (reflect d4 i y) j = y j - (∑ j', d4.cartan i j' * y j') *
          (Pi.single i 1 : Fin d4.rank → ℤ) j := by
        simp [reflect]
      rw [hr]
      by_cases hji : j = i
      · subst hji
        rw [Pi.single_eq_same]
        omega
      · rw [Pi.single_eq_of_ne hji]
        omega
    refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
    · have := hkey (nd 2)
      omega
    · have a0 := hkey (nd 0)
      have a1 := hkey (nd 1)
      have a3 := hkey (nd 3)
      omega
    · have := hkey j
      have := h3 j
      omega

theorem weyl_short_roots (hK : (-1 : Kˣ) ≠ 1) {w : WeylGroup d4}
    (hwρ : weylTwist TwistTag.D4 w = w) (hwa : w ∈ rootCharStabilizer (aShortTD4 K)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      w • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) = ε • Pi.single (nd 0) 1 ∧
      w • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) = ε • Pi.single (nd 1) 1 ∧
      w • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) = ε • Pi.single (nd 3) 1 := by
  have hroot : IsRoot d4 (w • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ)) :=
    IsRoot.smul (isRoot_single d4 (nd 0)) w
  have hchar : rootChar (aShortTD4 K) (w • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ)) = 1 := by
    rw [hwa, rootChar_single_td4]
    rfl
  have hpar := (rootChar_aShort_eq_one_iff hK _).1 hchar
  have hw1 : w • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) =
      rho (w • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ)) := by
    rw [← smul_rho_td4 hwρ, rho_single, rhoPerm_zero]
  have hw3 : w • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) =
      rho (w • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ)) := by
    rw [← smul_rho_td4 hwρ, rho_single, rhoPerm_one]
  have hne : rho (w • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ)) ≠
      w • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) := by
    intro h
    rw [← hw1] at h
    have h2 := congrFun (MulAction.injective w h) (nd 1)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (show nd 1 ≠ nd 0 by decide)] at h2
    exact one_ne_zero h2
  have hrad := weyl_smul_radical w (Pi.single (nd 0) 1 + Pi.single (nd 1) 1) (by
    constructor
    · simp +decide
    · simp +decide)
  rw [smul_add, hw1] at hrad
  have hrad0 := hrad.2 (nd 0)
  have hrad1 := hrad.2 (nd 1)
  have hρ0 : rho (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) = Pi.single (nd 1) 1 := by
    rw [rho_single, rhoPerm_zero]
  have hρ1 : rho (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) = Pi.single (nd 3) 1 := by
    rw [rho_single, rhoPerm_one]
  have hρ3 : rho (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) = Pi.single (nd 0) 1 := by
    rw [rho_single, rhoPerm_three]
  rcases short_rho_ne _ (mem_rootFinset.2 hroot) hpar hne with h | h | h | h | h | h
  ·
    refine ⟨1, Or.inl rfl, by rw [h, one_smul], ?_, ?_⟩
    · rw [hw1, h, hρ0, one_smul]
    · rw [hw3, hw1, h, hρ0, hρ1, one_smul]
  ·
    exfalso
    rw [h, hρ1] at hrad0
    simp +decide at hrad0
  ·
    exfalso
    rw [h, hρ3] at hrad1
    simp +decide at hrad1
  · refine ⟨-1, Or.inr rfl, by rw [h, neg_one_smul], ?_, ?_⟩
    · rw [hw1, h, rho_neg, hρ0, neg_one_smul]
    · rw [hw3, hw1, h, rho_neg, rho_neg, hρ0, hρ1, neg_one_smul]
  · exfalso
    rw [h, rho_neg, hρ1] at hrad0
    simp +decide at hrad0
  · exfalso
    rw [h, rho_neg, hρ3] at hrad1
    simp +decide at hrad1

include hσ in
theorem twistedIncl_slShort_upper (c : K) :
    twistedIncl σ (slShort σ hσ (uSL c)) =
      ((xOuter 1 c (σ c) (σ (σ c)) : adjointGroup d4 K) : ModGL d4 K) := by
  rw [twistedIncl_apply, uSL_eq_sl2Upper, slShort_upper]

include hσ in
theorem twistedIncl_slShort_lower (c : K) :
    twistedIncl σ (slShort σ hσ (vSL c)) =
      ((xOuter (-1) c (σ c) (σ (σ c)) : adjointGroup d4 K) : ModGL d4 K) := by
  rw [twistedIncl_apply, vSL_eq_sl2Lower, slShort_lower]

include hσ in
theorem slShort_neg_one : ((slShort σ hσ (-1) : twistedGroup σ) : adjointGroup d4 K) =
    hShortHom σ (-1) := by
  have hmem : torusElement d4 K (nd 0) (-1) ∈
      rankOne (rootGroup (rootOperatorFamily d4) K) (nd 0) := torusElement_mem_rankOne (nd 0) (-1)
  have hy : restrictEquiv (rootOperatorFamily d4) cartan_zero_two
      ⟨torusElement d4 K (nd 0) (-1), hmem⟩ = -1 := by
    apply Subtype.ext
    show ((restrictHom (rootOperatorFamily d4) cartan_zero_two ⟨_, hmem⟩ :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
    rw [restrictHom_torusElement cartan_zero_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg]
  have : (restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm (-1) =
      ⟨torusElement d4 K (nd 0) (-1), hmem⟩ := by
    rw [MulEquiv.symm_apply_eq, hy]
  simp only [slShort, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, phiShortTw_val]
  exact phiShort_torusElement σ (-1)

include hσ in
theorem twistedIncl_slShort_neg_one :
    twistedIncl σ (slShort σ hσ (-1)) = rootDiagUnit d4 (aShortTD4 K) := by
  rw [twistedIncl_apply, slShort_neg_one hσ]
  have hmap : Units.map σ.toMonoidHom (-1 : Kˣ) = -1 := Units.ext (by simp)
  show ((hShortHom σ (-1) : adjointGroup d4 K) : ModGL d4 K) = _
  rw [hShortHom_apply, hmap, hmap]
  exact torusElt_short_neg_one

theorem conj_xOuter {x : ModGL d4 K} (s s' : ℤ) {l₀ l₁ l₃ : K}
    (h0 : ∀ c : K, x * ((xPar (rootOperatorFamily d4) (s • Pi.single (nd 0) 1) c :
      adjointGroup d4 K) : ModGL d4 K) * x⁻¹ =
      ((xPar (rootOperatorFamily d4) (s' • Pi.single (nd 0) 1) (l₀ * c) : adjointGroup d4 K) :
        ModGL d4 K))
    (h1 : ∀ c : K, x * ((xPar (rootOperatorFamily d4) (s • Pi.single (nd 1) 1) c :
      adjointGroup d4 K) : ModGL d4 K) * x⁻¹ =
      ((xPar (rootOperatorFamily d4) (s' • Pi.single (nd 1) 1) (l₁ * c) : adjointGroup d4 K) :
        ModGL d4 K))
    (h3 : ∀ c : K, x * ((xPar (rootOperatorFamily d4) (s • Pi.single (nd 3) 1) c :
      adjointGroup d4 K) : ModGL d4 K) * x⁻¹ =
      ((xPar (rootOperatorFamily d4) (s' • Pi.single (nd 3) 1) (l₃ * c) : adjointGroup d4 K) :
        ModGL d4 K))
    (c d e : K) :
    x * ((xOuter s c d e : adjointGroup d4 K) : ModGL d4 K) * x⁻¹ =
      ((xOuter s' (l₀ * c) (l₁ * d) (l₃ * e) : adjointGroup d4 K) : ModGL d4 K) := by
  simp only [xOuter, Subgroup.coe_mul]
  calc x * (↑(xPar (rootOperatorFamily d4) (s • Pi.single (nd 0) 1) c) *
        ↑(xPar (rootOperatorFamily d4) (s • Pi.single (nd 1) 1) d) *
          ↑(xPar (rootOperatorFamily d4) (s • Pi.single (nd 3) 1) e)) * x⁻¹ =
      (x * ↑(xPar (rootOperatorFamily d4) (s • Pi.single (nd 0) 1) c) * x⁻¹) *
        (x * ↑(xPar (rootOperatorFamily d4) (s • Pi.single (nd 1) 1) d) * x⁻¹) *
          (x * ↑(xPar (rootOperatorFamily d4) (s • Pi.single (nd 3) 1) e) * x⁻¹) := by group
    _ = _ := by rw [h0, h1, h3]

include hσ in
theorem linAct_slShort_of_scalar (h2 : (2 : K) ≠ 0) {x : twistedGroup σ}
    (hneg : x * slShort σ hσ (-1) * x⁻¹ = slShort σ hσ (-1)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {l₀ l₁ l₃ m₀ m₁ m₃ : K}
    (h₁ : ∀ c d e : K, twistedIncl σ x * ((xOuter 1 c d e : adjointGroup d4 K) : ModGL d4 K) *
      (twistedIncl σ x)⁻¹ =
      ((xOuter ε (l₀ * c) (l₁ * d) (l₃ * e) : adjointGroup d4 K) : ModGL d4 K))
    (h₂ : ∀ c d e : K, twistedIncl σ x * ((xOuter (-1) c d e : adjointGroup d4 K) : ModGL d4 K) *
      (twistedIncl σ x)⁻¹ =
      ((xOuter (-ε) (m₀ * c) (m₁ * d) (m₃ * e) : adjointGroup d4 K) : ModGL d4 K)) :
    LinAct (slShort σ hσ) x := by
  have hΦinj := slShort_injective hσ
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with h | h <;> simp [h]
  have hcompat : ∀ {s : ℤ} (hs : s = 1 ∨ s = -1) {a b c : K},
      ((xOuter s a b c : adjointGroup d4 K) : ModGL d4 K) ∈
        twistedFixedGroup TwistTag.D4 K σ → σ c = a ∧ σ a = b ∧ σ b = c := by
    intro s hs a b c hmem
    have hF := (coe_mem_twistedFixedGroup_iff TwistTag.D4 K σ _).1 hmem
    rw [twistC_xOuter σ hs] at hF
    exact xOuter_inj hs hF
  obtain ⟨hl3, hl0, hl1⟩ : σ l₃ = l₀ ∧ σ l₀ = l₁ ∧ σ l₁ = l₃ := by
    have hy := twistedIncl_slShort_upper hσ (1 : K)
    simp only [map_one] at hy
    have hmem := twistedIncl_mem_twistedFixedGroup (x * slShort σ hσ (uSL (1 : K)) * x⁻¹)
    rw [map_mul, map_mul, map_inv, hy, h₁ 1 1 1] at hmem
    simpa using hcompat hε hmem
  obtain ⟨hm3, hm0, hm1⟩ : σ m₃ = m₀ ∧ σ m₀ = m₁ ∧ σ m₁ = m₃ := by
    have hy := twistedIncl_slShort_lower hσ (1 : K)
    simp only [map_one] at hy
    have hmem := twistedIncl_mem_twistedFixedGroup (x * slShort σ hσ (vSL (1 : K)) * x⁻¹)
    rw [map_mul, map_mul, map_inv, hy, h₂ 1 1 1] at hmem
    simpa using hcompat hε' hmem
  have e1 : ∀ c : K, σ (l₀ * c) = l₁ * σ c := fun c => by rw [map_mul, hl0]
  have e2 : ∀ c : K, σ (σ (l₀ * c)) = l₃ * σ (σ c) := fun c => by rw [e1, map_mul, hl1]
  have f1 : ∀ c : K, σ (m₀ * c) = m₁ * σ c := fun c => by rw [map_mul, hm0]
  have f2 : ∀ c : K, σ (σ (m₀ * c)) = m₃ * σ (σ c) := fun c => by rw [f1, map_mul, hm1]
  have hu_gen : ∀ c : K, twistedIncl σ (x * slShort σ hσ (uSL c) * x⁻¹) =
      ((xOuter ε (l₀ * c) (σ (l₀ * c)) (σ (σ (l₀ * c))) : adjointGroup d4 K) : ModGL d4 K) := by
    intro c
    rw [map_mul, map_mul, map_inv, twistedIncl_slShort_upper hσ, h₁, e2, e1]
  have hv_gen : ∀ c : K, twistedIncl σ (x * slShort σ hσ (vSL c) * x⁻¹) =
      ((xOuter (-ε) (m₀ * c) (σ (m₀ * c)) (σ (σ (m₀ * c))) : adjointGroup d4 K) :
        ModGL d4 K) := by
    intro c
    rw [map_mul, map_mul, map_inv, twistedIncl_slShort_lower hσ, h₂, f2, f1]
  rcases hε with rfl | rfl
  · refine linAct_of_signs_diag hΦinj h2 hneg (s := l₀) (s' := m₀) (fun c => ?_) (fun c => ?_)
    · apply twistedIncl_injective σ
      rw [hu_gen, twistedIncl_slShort_upper hσ]
    · apply twistedIncl_injective σ
      rw [hv_gen, twistedIncl_slShort_lower hσ]
  · refine linAct_of_signs_anti hΦinj h2 hneg (κ := l₀) (κ' := m₀) (fun c => ?_) (fun c => ?_)
    · apply twistedIncl_injective σ
      rw [hu_gen, twistedIncl_slShort_lower hσ]
    · apply twistedIncl_injective σ
      rw [hv_gen, neg_neg, twistedIncl_slShort_upper hσ]

include hσ in
theorem linAct_torus_short (h2 : (2 : K) ≠ 0) {x : twistedGroup σ} {b : Fin d4.rank → Kˣ}
    (hx : twistedIncl σ x = rootDiagUnit d4 b) : LinAct (slShort σ hσ) x := by
  have hs1 : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hsm : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  refine linAct_slShort_of_scalar hσ h2 ?_ (ε := 1) hs1
    (l₀ := (rootChar b ((1 : ℤ) • Pi.single (nd 0) 1) : K))
    (l₁ := (rootChar b ((1 : ℤ) • Pi.single (nd 1) 1) : K))
    (l₃ := (rootChar b ((1 : ℤ) • Pi.single (nd 3) 1) : K))
    (m₀ := (rootChar b ((-1 : ℤ) • Pi.single (nd 0) 1) : K))
    (m₁ := (rootChar b ((-1 : ℤ) • Pi.single (nd 1) 1) : K))
    (m₃ := (rootChar b ((-1 : ℤ) • Pi.single (nd 3) 1) : K)) (fun c d e => ?_) (fun c d e => ?_)
  · apply twistedIncl_injective σ
    rw [map_mul, map_mul, map_inv, hx, twistedIncl_slShort_neg_one hσ, mul_inv_eq_iff_eq_mul,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  · rw [hx]
    exact conj_xOuter 1 1 (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hs1 _) c)
      (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hs1 _) c)
      (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hs1 _) c) c d e
  · rw [hx]
    exact conj_xOuter (-1) (-1) (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hsm _) c)
      (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hsm _) c)
      (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hsm _) c) c d e

include hσ in
theorem linAct_weyl_short (h2 : (2 : K) ≠ 0) (hK : (-1 : Kˣ) ≠ 1) {x : twistedGroup σ}
    {w : WeylGroup d4} (hx : twistedIncl σ x = canonicalRep (coxeterSystem d4) K w)
    (hwρ : weylTwist TwistTag.D4 w = w) (hwa : w ∈ rootCharStabilizer (aShortTD4 K)) :
    LinAct (slShort σ hσ) x := by
  obtain ⟨ε, hε, h0, h1, h3⟩ := weyl_short_roots hK hwρ hwa
  have hs1 : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hsm : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hneg : x * slShort σ hσ (-1) * x⁻¹ = slShort σ hσ (-1) := by
    apply twistedIncl_injective σ
    rw [map_mul, map_mul, map_inv, hx, twistedIncl_slShort_neg_one hσ]
    have hc := (mem_toralCentralizer.mp (canonicalRep_mem_toralCentralizer hwa)).2
    rw [mul_inv_eq_iff_eq_mul] at hc ⊢
    exact hc.symm
  have hp : ∀ {j : Fin d4.rank} (_ : w • (Pi.single j 1 : Fin d4.rank → ℤ) = ε • Pi.single j 1),
      ∃ η η' : K, (∀ c : K, canonicalRep (coxeterSystem d4) K w *
        ((xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single j 1) c : adjointGroup d4 K) :
          ModGL d4 K) * (canonicalRep (coxeterSystem d4) K w)⁻¹ =
        ((xPar (rootOperatorFamily d4) (ε • Pi.single j 1) (η * c) : adjointGroup d4 K) :
          ModGL d4 K)) ∧
      (∀ c : K, canonicalRep (coxeterSystem d4) K w *
        ((xPar (rootOperatorFamily d4) ((-1 : ℤ) • Pi.single j 1) c : adjointGroup d4 K) :
          ModGL d4 K) * (canonicalRep (coxeterSystem d4) K w)⁻¹ =
        ((xPar (rootOperatorFamily d4) ((-ε) • Pi.single j 1) (η' * c) : adjointGroup d4 K) :
          ModGL d4 K)) := by
    intro j hj
    obtain ⟨η, -, hη⟩ := canonicalRep_conj_xPar_td4 (K := K) w (isRoot_smul_single hs1 j)
    obtain ⟨η', -, hη'⟩ := canonicalRep_conj_xPar_td4 (K := K) w (isRoot_smul_single hsm j)
    refine ⟨η, η', fun c => ?_, fun c => ?_⟩
    · rw [hη c, one_smul, hj]
    · rw [hη' c, smul_comm, hj, smul_smul, neg_one_mul]
  obtain ⟨l₀, m₀, hl0, hm0⟩ := hp h0
  obtain ⟨l₁, m₁, hl1, hm1⟩ := hp h1
  obtain ⟨l₃, m₃, hl3, hm3⟩ := hp h3
  refine linAct_slShort_of_scalar hσ h2 hneg hε (l₀ := l₀) (l₁ := l₁) (l₃ := l₃) (m₀ := m₀)
    (m₁ := m₁) (m₃ := m₃) (fun c d e => ?_) (fun c d e => ?_)
  · rw [hx]
    exact conj_xOuter 1 ε hl0 hl1 hl3 c d e
  · rw [hx]
    exact conj_xOuter (-1) (-ε) hm0 hm1 hm3 c d e

end Short

section Factor

variable {K : Type} [Field K]

theorem map_twistedRootSubgroupD4_le_range (σ : K →+* K) {β : Fin (Tag.rank .G2) → ℤ}
    (hβ : IsRoot .G2 β) :
    (twistedRootSubgroupD4 σ β).map (adjointGroup d4 K).subtype ≤ (twistedIncl σ).range := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨x, twistedRootSubgroupD4_le_twistedGroup σ hβ hx⟩, rfl⟩

theorem mem_of_centralizes_aux (σ : K ≃+* K) (a : Fin d4.rank → Kˣ) {α₀ : Fin d4.rank → ℤ}
    (hα₀ : IsRoot d4 α₀) (S : Subgroup (ModGL d4 K))
    (hS1 : nodeGroupTD4 σ.toRingHom α₀ ≤ S)
    (hS2 : ∀ y ∈ (twistedIncl σ.toRingHom).range,
      (∀ z ∈ nodeGroupTD4 σ.toRingHom α₀, y * z = z * y) → y ∈ S)
    (hclosed : ∀ α ∈ psiTD4 a, ∀ β ∈ psiTD4 a, IsRoot d4 (α + β) → α + β ∈ psiTD4 a)
    (hρ : ∀ α ∈ psiTD4 a, rho α ∈ psiTD4 a)
    (hnode : ∀ γ ∈ psiTD4 a, γ ∉ td4Orb α₀ → ∀ δ ∈ td4Orb α₀ ∪ td4Orb (-α₀),
      γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ))
    (hT : ∀ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, h ∈ S)
    (hW : ∀ w : WeylGroup d4, weylTwist TwistTag.D4 w = w → w ∈ rootCharStabilizer a →
      canonicalRep (coxeterSystem d4) K w ∈ (twistedIncl σ.toRingHom).range →
        canonicalRep (coxeterSystem d4) K w ∈ S)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤ (twistedIncl σ.toRingHom).range)
    {g : ModGL d4 K} (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hga : g ∈ Subgroup.centralizer ({rootDiagUnit d4 a} : Set (ModGL d4 K))) : g ∈ S := by
  set Γ := twistedFixedGroup TwistTag.D4 K σ.toRingHom with hΓ
  have hα₀' : IsRoot d4 (-α₀) := IsRoot.neg hα₀
  obtain ⟨w, hw1, hwa, h, hh, u, hu, v, hv, hgeq⟩ :=
    graphFixed_toral_centralizer_Bruhat_factors TwistTag.D4 K σ a hg hga
  have hwρ : weylTwist TwistTag.D4 w = w := hw1
  have hhC₀ : h ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := (Subgroup.mem_inf.1 hh).2
  have hXmS : ∀ β ∈ proj '' psiTD4 a,
      (twistedRootSubgroupD4 σ.toRingHom β).map (adjointGroup d4 K).subtype ≤ S := by
    rintro β ⟨α, hαΨ, rfl⟩
    by_cases hαo : α ∈ td4Orb α₀
    · rw [proj_eq_of_mem_td4Orb hαo, map_twistedRootSubgroupD4_eq σ.toRingHom hα₀]
      exact (le_sup_left : _ ≤ nodeGroupTD4 σ.toRingHom α₀).trans hS1
    · intro y hy
      have hyR : y ∈ (twistedIncl σ.toRingHom).range :=
        map_twistedRootSubgroupD4_le_range σ.toRingHom (isRoot_proj hαΨ.2.1) hy
      refine hS2 y hyR fun z hz => ?_
      rw [map_twistedRootSubgroupD4_eq σ.toRingHom hαΨ.2.1] at hy
      have hzL := nodeGroupTD4_le_rootSpan σ.toRingHom α₀ hz
      have hmemΨ : ∀ γ ∈ td4Orb α, γ ∈ psiTD4 a := by
        intro γ hγ
        simp only [td4Orb, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
        rcases hγ with rfl | rfl | rfl
        · exact hαΨ
        · exact hρ _ hαΨ
        · exact hρ _ (hρ _ hαΨ)
      have hcond : ∀ γ ∈ td4Orb α, ∀ δ ∈ td4Orb α₀ ∪ td4Orb (-α₀),
          γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ) := by
        intro γ hγ δ hδ
        refine hnode γ (hmemΨ γ hγ) (fun hγo => hαo ?_) δ hδ
        have e1 := td4Orb_eq_of_mem hγ
        have e2 := td4Orb_eq_of_mem hγo
        have hself := self_mem_td4Orb α
        rw [← e1, e2] at hself
        exact hself
      exact commute_rootSpan_td4 (fun γ hγ => isRoot_of_mem_td4Orb hαΨ.2.1 hγ)
        (fun δ hδ => hδ.elim (fun h => isRoot_of_mem_td4Orb hα₀ h)
          (fun h => isRoot_of_mem_td4Orb hα₀' h)) hcond hy.1 hzL
  have hXmR : ∀ β ∈ proj '' psiTD4 a,
      (twistedRootSubgroupD4 σ.toRingHom β).map (adjointGroup d4 K).subtype ≤
        (twistedIncl σ.toRingHom).range := by
    rintro β ⟨α, hαΨ, rfl⟩
    exact map_twistedRootSubgroupD4_le_range σ.toRingHom (isRoot_proj hαΨ.2.1)
  have hΨ : rootSpan d4 K (psiTD4 a) ⊓ Γ ≤ S ⊓ (twistedIncl σ.toRingHom).range := by
    refine (rootSpan_inf_twistedFixed_le σ.toRingHom (fun α hα => hα.2) hclosed hρ).trans ?_
    exact le_inf (iSup₂_le fun β hβ => hXmS β hβ) (iSup₂_le fun β hβ => hXmR β hβ)
  have hsub : rootCharKernel a ∩ inversionSet w ⊆ psiTD4 a :=
    fun α hα => ⟨hα.1, hα.2.1, hα.2.2.1⟩
  have huSR := hΨ hu
  have hvSR := hΨ (Subgroup.mem_inf.2 ⟨rootSpan_mono hsub (Subgroup.mem_inf.1 hv).1,
    (Subgroup.mem_inf.1 hv).2⟩)
  have hnR : canonicalRep (coxeterSystem d4) K w ∈ (twistedIncl σ.toRingHom).range := by
    have e : canonicalRep (coxeterSystem d4) K w = (h * u)⁻¹ * g * v⁻¹ := by rw [hgeq]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (mul_mem (hC₀ hhC₀) huSR.2)) (hC₀ hg)) (inv_mem hvSR.2)
  rw [hgeq]
  exact mul_mem (mul_mem (mul_mem (hT h hh) huSR.1) (hW w hwρ hwa hnR)) hvSR.1

end Factor

section Frames

variable {K : Type} [Field K]

theorem psi_long_closed (hK : (-1 : Kˣ) ≠ 1) :
    ∀ α ∈ psiTD4 (aLongTD4 K), ∀ β ∈ psiTD4 (aLongTD4 K), IsRoot d4 (α + β) →
      α + β ∈ psiTD4 (aLongTD4 K) := by
  intro α hα β hβ hr
  exact absurd (mem_rootFinset.2 hr) (long_closed α (mem_rootFinset.2 hα.2.1) β
    (mem_rootFinset.2 hβ.2.1) ((rootChar_aLong_eq_one_iff hK α).1 hα.1.2)
    ((rootChar_aLong_eq_one_iff hK β).1 hβ.1.2) hα.2.2 hβ.2.2)

theorem psi_long_rho (hK : (-1 : Kˣ) ≠ 1) :
    ∀ α ∈ psiTD4 (aLongTD4 K), rho α ∈ psiTD4 (aLongTD4 K) := by
  intro α hα
  obtain ⟨h1, h2, h3⟩ := long_rho_stable α (mem_rootFinset.2 hα.2.1)
    ((rootChar_aLong_eq_one_iff hK α).1 hα.1.2) hα.2.2
  exact ⟨⟨mem_rootFinset.1 h1, (rootChar_aLong_eq_one_iff hK _).2 h2⟩,
    ⟨mem_rootFinset.1 h1, h3⟩⟩

theorem psi_long_node (hK : (-1 : Kˣ) ≠ 1) :
    ∀ γ ∈ psiTD4 (aLongTD4 K), γ ∉ td4Orb (Pi.single (nd 2) 1) →
      ∀ δ ∈ td4Orb (Pi.single (nd 2) 1) ∪ td4Orb (-Pi.single (nd 2) 1),
        γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ) := by
  intro γ hγ hγo δ hδ
  have hne : γ ≠ Pi.single (nd 2) 1 := fun h => hγo (h ▸ self_mem_td4Orb _)
  obtain ⟨h1, h2, h3⟩ := long_commute γ (mem_rootFinset.2 hγ.2.1)
    ((rootChar_aLong_eq_one_iff hK γ).1 hγ.1.2) hγ.2.2 hne
  rw [td4Orb_single_two, td4Orb_neg_single_two] at hδ
  rcases hδ with h | h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact ⟨hne, h1, fun hr => h2 (mem_rootFinset.2 hr)⟩
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact ⟨h1, by rw [neg_neg]; exact hne, fun hr => h3 (mem_rootFinset.2 hr)⟩

theorem weyl_long_root (hK : (-1 : Kˣ) ≠ 1) {w : WeylGroup d4}
    (hwρ : weylTwist TwistTag.D4 w = w) (hwa : w ∈ rootCharStabilizer (aLongTD4 K)) :
    w • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = Pi.single (nd 2) 1 ∨
      w • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = -Pi.single (nd 2) 1 := by
  have hroot : IsRoot d4 (w • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ)) :=
    IsRoot.smul (isRoot_single d4 (nd 2)) w
  have hchar : rootChar (aLongTD4 K) (w • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ)) = 1 := by
    rw [hwa, rootChar_single_td4]
    rfl
  have hpar := (rootChar_aLong_eq_one_iff hK _).1 hchar
  have hfix : rho (w • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ)) =
      w • Pi.single (nd 2) 1 := by
    rw [← smul_rho_td4 hwρ, rho_single, rhoPerm_two]
  exact long_rho_fixed _ (mem_rootFinset.2 hroot) hpar hfix

theorem psi_short_closed (hK : (-1 : Kˣ) ≠ 1) :
    ∀ α ∈ psiTD4 (aShortTD4 K), ∀ β ∈ psiTD4 (aShortTD4 K), IsRoot d4 (α + β) →
      α + β ∈ psiTD4 (aShortTD4 K) := by
  intro α hα β hβ hr
  exact absurd (mem_rootFinset.2 hr) (short_closed α (mem_rootFinset.2 hα.2.1) β
    (mem_rootFinset.2 hβ.2.1) ((rootChar_aShort_eq_one_iff hK α).1 hα.1.2)
    ((rootChar_aShort_eq_one_iff hK β).1 hβ.1.2) hα.2.2 hβ.2.2)

theorem psi_short_rho (hK : (-1 : Kˣ) ≠ 1) :
    ∀ α ∈ psiTD4 (aShortTD4 K), rho α ∈ psiTD4 (aShortTD4 K) := by
  intro α hα
  obtain ⟨h1, h2, h3⟩ := short_rho_stable α (mem_rootFinset.2 hα.2.1)
    ((rootChar_aShort_eq_one_iff hK α).1 hα.1.2) hα.2.2
  exact ⟨⟨mem_rootFinset.1 h1, (rootChar_aShort_eq_one_iff hK _).2 h2⟩,
    ⟨mem_rootFinset.1 h1, h3⟩⟩

theorem psi_short_node (hK : (-1 : Kˣ) ≠ 1) :
    ∀ γ ∈ psiTD4 (aShortTD4 K), γ ∉ td4Orb (Pi.single (nd 0) 1) →
      ∀ δ ∈ td4Orb (Pi.single (nd 0) 1) ∪ td4Orb (-Pi.single (nd 0) 1),
        γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ) := by
  intro γ hγ hγo δ hδ
  rw [td4Orb_single_zero] at hγo
  have h0 : γ ≠ Pi.single (nd 0) 1 := fun h => hγo (by simp [h])
  have h1 : γ ≠ Pi.single (nd 1) 1 := fun h => hγo (by simp [h])
  have h3 : γ ≠ Pi.single (nd 3) 1 := fun h => hγo (by simp [h])
  obtain ⟨⟨a0, b0, c0⟩, ⟨a1, b1, c1⟩, ⟨a3, b3, c3⟩⟩ := short_commute γ
    (mem_rootFinset.2 hγ.2.1) ((rootChar_aShort_eq_one_iff hK γ).1 hγ.1.2) hγ.2.2 h0 h1 h3
  rw [td4Orb_single_zero, td4Orb_neg_single_zero] at hδ
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with (h | h | h) | (h | h | h) <;> subst h
  · exact ⟨h0, a0, fun hr => b0 (mem_rootFinset.2 hr)⟩
  · exact ⟨h1, a1, fun hr => b1 (mem_rootFinset.2 hr)⟩
  · exact ⟨h3, a3, fun hr => b3 (mem_rootFinset.2 hr)⟩
  · exact ⟨a0, by rw [neg_neg]; exact h0, fun hr => c0 (mem_rootFinset.2 hr)⟩
  · exact ⟨a1, by rw [neg_neg]; exact h1, fun hr => c1 (mem_rootFinset.2 hr)⟩
  · exact ⟨a3, by rw [neg_neg]; exact h3, fun hr => c3 (mem_rootFinset.2 hr)⟩

end Frames

section Assembly

variable {K : Type} [Field K]

theorem mem_of_centralizes_aux' {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
    (a : Fin d4.rank → Kˣ) {α₀ : Fin d4.rank → ℤ} (hα₀ : IsRoot d4 α₀)
    (S : Subgroup (ModGL d4 K)) (hS1 : nodeGroupTD4 σ α₀ ≤ S)
    (hS2 : ∀ y ∈ (twistedIncl σ).range, (∀ z ∈ nodeGroupTD4 σ α₀, y * z = z * y) → y ∈ S)
    (hclosed : ∀ α ∈ psiTD4 a, ∀ β ∈ psiTD4 a, IsRoot d4 (α + β) → α + β ∈ psiTD4 a)
    (hρ : ∀ α ∈ psiTD4 a, rho α ∈ psiTD4 a)
    (hnode : ∀ γ ∈ psiTD4 a, γ ∉ td4Orb α₀ → ∀ δ ∈ td4Orb α₀ ∪ td4Orb (-α₀),
      γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ))
    (hT : ∀ h ∈ graphFixedRootTorus TwistTag.D4 K σ, h ∈ S)
    (hW : ∀ w : WeylGroup d4, weylTwist TwistTag.D4 w = w → w ∈ rootCharStabilizer a →
      canonicalRep (coxeterSystem d4) K w ∈ (twistedIncl σ).range →
        canonicalRep (coxeterSystem d4) K w ∈ S)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    {g : ModGL d4 K} (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    (hga : g ∈ Subgroup.centralizer ({rootDiagUnit d4 a} : Set (ModGL d4 K))) : g ∈ S := by
  obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, fun y => ⟨σ (σ y), hσ y⟩⟩, RingHom.ext fun _ => rfl⟩
  exact mem_of_centralizes_aux σ' a hα₀ S hS1 hS2 hclosed hρ hnode hT hW hC₀ hg hga

variable {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem linAct_of_centralizes_long (hK : (-1 : Kˣ) ≠ 1) (h2 : (2 : fixedField σ) ≠ 0)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {x : twistedGroup σ} (hx : x * slLong σ hσ (-1) = slLong σ hσ (-1) * x) :
    LinAct (slLong σ hσ) x := by
  set Φ := slLong σ hσ with hΦ
  set S : Subgroup (ModGL d4 K) := (linActSubgroup Φ).map (twistedIncl σ) with hS
  have hnode : nodeGroupTD4 σ (Pi.single (nd 2) 1) = (Φ.range).map (twistedIncl σ) := by
    rw [← map_rankOne_long, ModelFacts.rankOne_long_eq_range hσ]
  have hga : twistedIncl σ x ∈
      Subgroup.centralizer ({rootDiagUnit d4 (aLongTD4 K)} : Set (ModGL d4 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← twistedIncl_slLong_neg_one hσ, ← map_mul,
      ← map_mul, hx]
  have key : twistedIncl σ x ∈ S := by
    refine mem_of_centralizes_aux' hσ (aLongTD4 K) (isRoot_single d4 (nd 2)) S ?_ ?_
      (psi_long_closed hK) (psi_long_rho hK) (psi_long_node hK) ?_ ?_ hC₀ (hgF x) hga
    · rw [hnode]
      exact Subgroup.map_mono fun y hy => linAct_of_mem_range hy
    · rintro _ ⟨y, rfl⟩ hy
      refine ⟨y, linAct_of_commutes fun A => ?_, rfl⟩
      apply twistedIncl_injective σ
      rw [map_mul, map_mul]
      exact hy _ (by rw [hnode]; exact ⟨Φ A, ⟨A, rfl⟩, rfl⟩)
    · intro h hh
      obtain ⟨y, rfl⟩ := hC₀ (Subgroup.mem_inf.1 hh).2
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
      exact ⟨y, linAct_torus_long hσ h2 hb, rfl⟩
    · intro w hwρ hwa hn
      obtain ⟨y, hy⟩ := hn
      exact ⟨y, linAct_weyl_long hσ h2 hy hwa (weyl_long_root hK hwρ hwa), hy⟩
  obtain ⟨y, hy, hyx⟩ := key
  rw [← twistedIncl_injective σ hyx]
  exact hy

include hσ in
theorem linAct_of_centralizes_short (hK : (-1 : Kˣ) ≠ 1) (h2 : (2 : K) ≠ 0)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {x : twistedGroup σ} (hx : x * slShort σ hσ (-1) = slShort σ hσ (-1) * x) :
    LinAct (slShort σ hσ) x := by
  set Φ := slShort σ hσ with hΦ
  set S : Subgroup (ModGL d4 K) := (linActSubgroup Φ).map (twistedIncl σ) with hS
  have hnode : nodeGroupTD4 σ (Pi.single (nd 0) 1) = (Φ.range).map (twistedIncl σ) := by
    rw [← map_rankOne_short, ModelFacts.rankOne_short_eq_range hσ]
  have hga : twistedIncl σ x ∈
      Subgroup.centralizer ({rootDiagUnit d4 (aShortTD4 K)} : Set (ModGL d4 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← twistedIncl_slShort_neg_one hσ, ← map_mul,
      ← map_mul, hx]
  have key : twistedIncl σ x ∈ S := by
    refine mem_of_centralizes_aux' hσ (aShortTD4 K) (isRoot_single d4 (nd 0)) S ?_ ?_
      (psi_short_closed hK) (psi_short_rho hK) (psi_short_node hK) ?_ ?_ hC₀ (hgF x) hga
    · rw [hnode]
      exact Subgroup.map_mono fun y hy => linAct_of_mem_range hy
    · rintro _ ⟨y, rfl⟩ hy
      refine ⟨y, linAct_of_commutes fun A => ?_, rfl⟩
      apply twistedIncl_injective σ
      rw [map_mul, map_mul]
      exact hy _ (by rw [hnode]; exact ⟨Φ A, ⟨A, rfl⟩, rfl⟩)
    · intro h hh
      obtain ⟨y, rfl⟩ := hC₀ (Subgroup.mem_inf.1 hh).2
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
      exact ⟨y, linAct_torus_short hσ h2 hb, rfl⟩
    · intro w hwρ hwa hn
      obtain ⟨y, hy⟩ := hn
      exact ⟨y, linAct_weyl_short hσ h2 hK hy hwρ hwa, hy⟩
  obtain ⟨y, hy, hyx⟩ := key
  rw [← twistedIncl_injective σ hyx]
  exact hy

end Assembly

end CFSG.ClassicalInvolution.G2D4Models
