module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Fix
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentAssemble
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOFrame
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PSemi
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Grp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RO

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.GroupTheory.SteinbergBK
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

section Scaled

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {k : Subfield K} {W : Submodule k V} {d : K} {Q₀ : QuadraticForm k W}

theorem coe_polar_eq_mul (hQ₀ : ∀ w, ((Q₀ w : k) : K) = d * Q w) (x y : W) :
    ((polar Q₀ x y : k) : K) = d * polar Q x y := by
  simp only [QuadraticMap.polar, Subfield.coe_sub, hQ₀, Submodule.coe_add]
  ring

theorem polar_eq_zero_of_scaled (hd : d ≠ 0) (hQ₀ : ∀ w, ((Q₀ w : k) : K) = d * Q w) {x y : W}
    (h : polar Q₀ x y = 0) : polar Q x y = 0 := by
  have := coe_polar_eq_mul hQ₀ x y
  rw [h, ZeroMemClass.coe_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hd

@[expose] def scaledPair (hd : d ≠ 0) (hQ₀ : ∀ w, ((Q₀ w : k) : K) = d * Q w) (P : HypPair Q₀) :
    HypPair Q where
  e := P.e
  f := d • (P.f : V)
  Q_e := by
    have h := hQ₀ P.e
    rw [P.Q_e, ZeroMemClass.coe_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hd
  Q_f := by
    have h := hQ₀ P.f
    rw [P.Q_f, ZeroMemClass.coe_zero] at h
    rw [QuadraticMap.map_smul, smul_eq_mul, mul_assoc, ← h, mul_zero]
  polar_ef := by
    rw [polar_smul_right, smul_eq_mul, ← coe_polar_eq_mul hQ₀, P.polar_ef, OneMemClass.coe_one]

theorem scaledPair_orth (hd : d ≠ 0) (hQ₀ : ∀ w, ((Q₀ w : k) : K) = d * Q w)
    {P P' : HypPair Q₀} (h : P.Orth P') : (scaledPair hd hQ₀ P).Orth (scaledPair hd hQ₀ P') := by
  refine ⟨polar_eq_zero_of_scaled hd hQ₀ h.ee, ?_, ?_, ?_⟩
  · change polar Q P.e (d • (P'.f : V)) = 0
    rw [polar_smul_right, polar_eq_zero_of_scaled hd hQ₀ h.ef, smul_zero]
  · change polar Q (d • (P.f : V)) P'.e = 0
    rw [polar_smul_left, polar_eq_zero_of_scaled hd hQ₀ h.fe, smul_zero]
  · change polar Q (d • (P.f : V)) (d • (P'.f : V)) = 0
    rw [polar_smul_left, polar_smul_right, polar_eq_zero_of_scaled hd hQ₀ h.ff, smul_zero,
      smul_zero]

end Scaled

section Simple

variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  {Q₀ : QuadraticForm k W}

theorem isSimpleGroup_elementaryGroup_of_hypPairs (h2 : (2 : k) ≠ 0)
    (hnd : (polarBilin Q₀).Nondegenerate) (hodd : Odd (Module.finrank k W))
    {P₁ P₂ P₃ : HypPair Q₀} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    IsSimpleGroup (elementaryGroup Q₀) ∧ ∃ a b : elementaryGroup Q₀, a * b ≠ b * a := by
  have hperf : commutator (elementaryGroup Q₀) = ⊤ :=
    commutator_elementaryGroup_eq_top h₁₂ h₁₃ h₂₃ hnd
  have hsimp : IsSimpleGroup (ProjElementary Q₀) :=
    isSimpleGroup_projElementary_of_hypPairs hnd h₁₂ h₁₃ h₂₃
  have hOE := commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2 hnd h₁₂ h₁₃ h₂₃
  have hv₀ : Q₀ (P₁.e + P₁.f) ≠ 0 := by
    rw [QuadraticMap.map_add Q₀, P₁.Q_e, P₁.Q_f, P₁.polar_ef, zero_add, zero_add]
    exact one_ne_zero
  have hscal : (scalars k W).subgroupOf (elementaryGroup Q₀) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => Subtype.ext ?_
    rw [Subgroup.mem_subgroupOf] at hg
    have hgΩ : (g : W ≃ₗ[k] W) ∈ orthDerived Q₀ := by
      show (g : W ≃ₗ[k] W) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
        TauCeti.QuadraticMap.orthogonalGroup Q₀⁆
      rw [hOE]
      exact g.2
    exact eq_one_of_mem_scalars_of_mem_orthDerived hodd hv₀ hgΩ hg
  have hsE : IsSimpleGroup (elementaryGroup Q₀) := by
    have e : ProjElementary Q₀ ≃* elementaryGroup Q₀ :=
      (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
    exact e.symm.isSimpleGroup
  refine ⟨hsE, ?_⟩
  by_contra hall
  push Not at hall
  have hc : commutator ↥(elementaryGroup Q₀) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hall y x
  rw [hperf] at hc
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(elementaryGroup Q₀)
  have ha : a ∈ (⊥ : Subgroup ↥(elementaryGroup Q₀)) := hc ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup ↥(elementaryGroup Q₀)) := hc ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  exact hab (ha.trans hb.symm)

end Simple

section Package

variable {K : Type} [Field K]

theorem u1_of_comap [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) {α : MulAut (spinGroup (quadOdd 3 K))}
    {G : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hπ : ∀ s v, spinAction (quadOdd 3 K) (α s) v = G (spinAction (quadOdd 3 K) s (G.symm v)))
    {E : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K))}
    (hEq : IsQuasisimple ↥E) (hEZ : center ↥E = ⊥) (hEr : E ≤ (spinAction (quadOdd 3 K)).range)
    (hEG : ∀ g ∈ E, ∀ v, G (g v) = g (G v))
    (hEn : ∀ g ∈ (spinAction (quadOdd 3 K)).range, (∀ v, G (g v) = g (G v)) →
      ∀ h ∈ E, g * h * g⁻¹ ∈ E)
    (hz : spinZ K ∈ ⁅E.comap (spinAction (quadOdd 3 K)), E.comap (spinAction (quadOdd 3 K))⁆)
    (hdvd : (p ^ f) ^ 2 ∣ Nat.card ↥E) :
    ∃ J : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (fixedSubgroup α) ∧
      spinZ K ∈ J ∧ ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have := finite_spinSeven h2
  have hQnd : (quadOdd 3 K).Nondegenerate := nondegenerate_quadOdd 3 K
  set π := spinAction (quadOdd 3 K) with hπdef
  set J := E.comap π with hJ
  have hcen : π.ker ≤ center (spinGroup (quadOdd 3 K)) := ker_spinAction_le_center _
  have hker : ∀ s, s ∈ π.ker ↔ s = 1 ∨ s = spinZ K := mem_ker_spinAction_iff _ hQnd
  have hkerJ : π.ker ≤ ⁅J, J⁆ := fun s hs => by
    rcases (hker s).mp hs with rfl | rfl
    · exact one_mem _
    · exact hz
  have hJq : IsQuasisimple ↥J := isQuasisimple_comap_of_le π hEq hEr hcen hkerJ
  have hJp : ⁅J, J⁆ = J :=
    commutator_comap_eq_of_le π (Subgroup.isPerfect_iff.mp hEq.1) hEr hkerJ
  have hzJ : spinZ K ∈ J := by
    have : spinZ K ∈ π.ker := (hker _).mpr (Or.inr rfl)
    show π (spinZ K) ∈ E
    rw [MonoidHom.mem_ker.mp this]
    exact one_mem _
  obtain ⟨hzz, hz1, -⟩ := spinZ_facts hp hp2 hK
  have hZE : ∀ g ∈ E, (∀ h ∈ E, g * h = h * g) → g * g = 1 := by
    intro g hg hcomm
    have hgZ : (⟨g, hg⟩ : ↥E) ∈ center ↥E := Subgroup.mem_center_iff.mpr fun h =>
      Subtype.ext (hcomm h.1 h.2).symm
    rw [hEZ, Subgroup.mem_bot] at hgZ
    have hg1 : g = 1 := congrArg Subtype.val hgZ
    rw [hg1, one_mul]
  have hker2 : ∀ s ∈ π.ker, s * s = 1 := fun s hs => by
    rcases (hker s).mp hs with rfl | rfl
    · exact one_mul 1
    · exact hzz
  have hO : pPrimeCore 2 ↥J = ⊥ := pPrimeCore_comap_eq_bot π hJq hEr hZE hker2 hzJ hz1 hzz
  have hfix : ∀ s ∈ J, α s = s := by
    refine apply_eq_of_map_apply_eq π hcen hJp α fun s hs => LinearEquiv.ext fun v => ?_
    rw [hπ, hEG (π s) hs, AddEquiv.apply_symm_apply]
  have hJC : J ≤ fixedSubgroup α := fun s hs => mem_fixedSubgroup.mpr (hfix s hs)
  have hnorm : (J.subgroupOf (fixedSubgroup α)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgc : ∀ v, G (π ↑g v) = π ↑g (G v) := fun v => by
      have h1 := hπ (g : spinGroup (quadOdd 3 K)) (G v)
      rw [mem_fixedSubgroup.mp g.2, AddEquiv.symm_apply_apply] at h1
      exact h1.symm
    have h4 := hEn (π ↑g) ⟨_, rfl⟩ hgc (π ↑n) hn
    show π (↑(g * n * g⁻¹)) ∈ E
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
    exact h4
  have h3 : Nat.card ↥E ∣ Nat.card ↥J :=
    Subgroup.card_dvd_of_surjective (comapRestrict_surjective π hEr)
  exact ⟨J, isTwoComponentIn_of_normal_of_pPrimeCore hJC hnorm hJq hO, hzJ,
    not_isSLTwoOver_of_sq_dvd hO (by omega) (hdvd.trans h3)⟩

end Package

section KForm

variable {K : Type} [Field K] {σ : K ≃+* K}
  {G : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
  (hG : ∀ (a : K) v, G (a • v) = σ a • G v) {d : K} (hd : d ≠ 0)
  {Q₀ : QuadraticForm (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ G hG)}
  (hQ₀ : ∀ w, ((Q₀ w : semilinearFixedSubfield σ) : K) = d * quadOdd 3 K w)

include hd in
theorem eichler_smul_mem_fixElem (u w : semilinearFixedSubmodule σ G hG) :
    eichler (quadOdd 3 K) (u : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (d • (w : Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ∈
      fixElem hG (d • quadOdd 3 K) := by
  rw [← eichler_smul_form hd]
  exact eichler_mem_fixElem hG u w

include hQ₀ in
theorem quadOdd_add_ne_zero (P : HypPair Q₀) :
    quadOdd 3 K ((P.e + P.f : semilinearFixedSubmodule σ G hG) : Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≠
      0 := by
  intro h0
  have h1 := hQ₀ (P.e + P.f)
  rw [QuadraticMap.map_add Q₀, P.Q_e, P.Q_f, P.polar_ef, zero_add, zero_add,
    OneMemClass.coe_one, h0, mul_zero] at h1
  exact one_ne_zero h1

include hd hQ₀ in
theorem scaledFrame_perp {P0 P1 P2 : HypPair Q₀} (h02 : P0.Orth P2) (h12 : P1.Orth P2) :
    polar (quadOdd 3 K) (P0.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K)
        ((P2.e + P2.f : semilinearFixedSubmodule σ G hG) : Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 0 ∧
      polar (quadOdd 3 K) (d • (P0.f : Fin 3 ⊕ Fin 3 ⊕ Unit → K))
        ((P2.e + P2.f : semilinearFixedSubmodule σ G hG) : Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 0 ∧
      polar (quadOdd 3 K) (P1.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K)
        ((P2.e + P2.f : semilinearFixedSubmodule σ G hG) : Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 0 ∧
      polar (quadOdd 3 K) (d • (P1.f : Fin 3 ⊕ Fin 3 ⊕ Unit → K))
        ((P2.e + P2.f : semilinearFixedSubmodule σ G hG) : Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 0 := by
  have e1 : polar Q₀ P0.e (P2.e + P2.f) = 0 := by rw [polar_add_right, h02.ee, h02.ef, add_zero]
  have e2 : polar Q₀ P0.f (P2.e + P2.f) = 0 := by rw [polar_add_right, h02.fe, h02.ff, add_zero]
  have e3 : polar Q₀ P1.e (P2.e + P2.f) = 0 := by rw [polar_add_right, h12.ee, h12.ef, add_zero]
  have e4 : polar Q₀ P1.f (P2.e + P2.f) = 0 := by rw [polar_add_right, h12.fe, h12.ff, add_zero]
  refine ⟨polar_eq_zero_of_scaled hd hQ₀ e1, ?_, polar_eq_zero_of_scaled hd hQ₀ e3, ?_⟩
  · rw [polar_smul_left, polar_eq_zero_of_scaled hd hQ₀ e2, smul_zero]
  · rw [polar_smul_left, polar_eq_zero_of_scaled hd hQ₀ e4, smul_zero]

@[expose] def scaledFrame {P0 P1 P2 : HypPair Q₀} (h01 : P0.Orth P1) (h02 : P0.Orth P2)
    (h12 : P1.Orth P2) : HypFrame (quadOdd 3 K) 2 :=
  CFSG.ComponentClassification.Burgoyne.B.frameHyp
    ⟨scaledPair hd hQ₀ P0, scaledPair hd hQ₀ P1, scaledPair_orth hd hQ₀ h01⟩
    ((P2.e + P2.f : semilinearFixedSubmodule σ G hG) : Fin 3 ⊕ Fin 3 ⊕ Unit → K)
    (isUnit_iff_ne_zero.mpr (quadOdd_add_ne_zero hG hQ₀ P2))
    (scaledFrame_perp hG hd hQ₀ h02 h12)

variable {P0 P1 P2 : HypPair Q₀} (h01 : P0.Orth P1) (h02 : P0.Orth P2) (h12 : P1.Orth P2)

theorem scaledFrame_upper_true (a : semilinearFixedSubfield σ) :
    spinAction (quadOdd 3 K) ((scaledFrame hG hd hQ₀ h01 h02 h12).longSL2
      (show (0 : Fin 2) ≠ 1 by decide) true true (upperSL2 (d * a))) ∈
        fixElem hG (d • quadOdd 3 K) := by
  rw [HypFrame.longSL2_upperSL2, HypFrame.spinAction_longRoot_eq_eichler]
  change eichler (quadOdd 3 K) (P1.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K)
    ((d * a) • (P0.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ∈ fixElem hG (d • quadOdd 3 K)
  rw [mul_smul]
  exact eichler_smul_mem_fixElem hG hd P1.e (a • P0.e)

theorem scaledFrame_lower_true (a : semilinearFixedSubfield σ) :
    spinAction (quadOdd 3 K) ((scaledFrame hG hd hQ₀ h01 h02 h12).longSL2
      (show (0 : Fin 2) ≠ 1 by decide) true true (lowerSL2 (d⁻¹ * a))) ∈
        fixElem hG (d • quadOdd 3 K) := by
  rw [HypFrame.longSL2_lowerSL2, HypFrame.spinAction_longRoot_eq_eichler]
  change eichler (quadOdd 3 K) (d • (P0.f : Fin 3 ⊕ Fin 3 ⊕ Unit → K))
    ((d⁻¹ * a) • d • (P1.f : Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ∈ fixElem hG (d • quadOdd 3 K)
  rw [eichler_smul_left, smul_smul (d⁻¹ * (a : K)) d, show d⁻¹ * (a : K) * d = a by field_simp]
  exact eichler_smul_mem_fixElem hG hd P0.f (a • P1.f)

theorem scaledFrame_upper_false (a : semilinearFixedSubfield σ) :
    spinAction (quadOdd 3 K) ((scaledFrame hG hd hQ₀ h01 h02 h12).longSL2
      (show (0 : Fin 2) ≠ 1 by decide) true false (upperSL2 a)) ∈
        fixElem hG (d • quadOdd 3 K) := by
  rw [HypFrame.longSL2_upperSL2, HypFrame.spinAction_longRoot_eq_eichler]
  change eichler (quadOdd 3 K) (d • (P1.f : Fin 3 ⊕ Fin 3 ⊕ Unit → K))
    ((a : K) • (P0.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ∈ fixElem hG (d • quadOdd 3 K)
  rw [eichler_smul_left]
  exact eichler_smul_mem_fixElem hG hd P1.f (a • P0.e)

theorem scaledFrame_lower_false (a : semilinearFixedSubfield σ) :
    spinAction (quadOdd 3 K) ((scaledFrame hG hd hQ₀ h01 h02 h12).longSL2
      (show (0 : Fin 2) ≠ 1 by decide) true false (lowerSL2 a)) ∈
        fixElem hG (d • quadOdd 3 K) := by
  rw [HypFrame.longSL2_lowerSL2, HypFrame.spinAction_longRoot_eq_eichler]
  change eichler (quadOdd 3 K) (d • (P0.f : Fin 3 ⊕ Fin 3 ⊕ Unit → K))
    ((a : K) • (P1.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ∈ fixElem hG (d • quadOdd 3 K)
  rw [eichler_smul_left]
  exact eichler_smul_mem_fixElem hG hd P0.f (a • P1.e)

theorem scaledFrame_neg_one_true_mem [Finite K]
    (hkodd : Odd (Nat.card (semilinearFixedSubfield σ))) :
    (scaledFrame hG hd hQ₀ h01 h02 h12).longSL2 (show (0 : Fin 2) ≠ 1 by decide) true true (-1) ∈
      ⁅(fixElem hG (d • quadOdd 3 K)).comap (spinAction (quadOdd 3 K)),
        (fixElem hG (d • quadOdd 3 K)).comap (spinAction (quadOdd 3 K))⁆ := by
  obtain ⟨x, y, hy, hxy⟩ := exists_sq_add_sq_eq_neg_one hkodd
  have hyK : (y : K) ≠ 0 := fun h => hy (Subtype.ext h)
  have hxyK : (x : K) ^ 2 + (y : K) ^ 2 = -1 := by
    have := congrArg (fun t : semilinearFixedSubfield σ => (t : K)) hxy
    simpa using this
  have hc' := commutatorElement_upperSL2_lowerSL2_eq_neg_one hd hyK hxyK
  have key : ∀ a b c : semilinearFixedSubfield σ,
      (scaledFrame hG hd hQ₀ h01 h02 h12).longSL2 (show (0 : Fin 2) ≠ 1 by decide) true true
        (upperSL2 (d * a) * lowerSL2 (d⁻¹ * b) * upperSL2 (d * c)) ∈
          (fixElem hG (d • quadOdd 3 K)).comap (spinAction (quadOdd 3 K)) := fun a b c => by
    rw [map_mul, map_mul]
    exact mul_mem (mul_mem (scaledFrame_upper_true hG hd hQ₀ h01 h02 h12 a)
      (scaledFrame_lower_true hG hd hQ₀ h01 h02 h12 b))
      (scaledFrame_upper_true hG hd hQ₀ h01 h02 h12 c)
  have eI : upperSL2 d * lowerSL2 (-d⁻¹) * upperSL2 d =
      upperSL2 (d * ((1 : semilinearFixedSubfield σ) : K)) *
        lowerSL2 (d⁻¹ * ((-1 : semilinearFixedSubfield σ) : K)) *
          upperSL2 (d * ((1 : semilinearFixedSubfield σ) : K)) := by
    simp
  have s1 : ((x : K) - 1) * d / y = d * (((x - 1) / y : semilinearFixedSubfield σ) : K) := by
    push_cast
    ring
  have s2 : (y : K) / d = d⁻¹ * ((y : semilinearFixedSubfield σ) : K) := by ring
  have s3 : (-(x : K) - 1) * d / y = d * (((-x - 1) / y : semilinearFixedSubfield σ) : K) := by
    push_cast
    ring
  rw [← hc', map_commutatorElement, eI, s1, s2, s3]
  exact Subgroup.commutator_mem_commutator (key _ _ _) (key _ _ _)

theorem scaledFrame_neg_one_false_mem [Finite K]
    (hkodd : Odd (Nat.card (semilinearFixedSubfield σ))) :
    (scaledFrame hG hd hQ₀ h01 h02 h12).longSL2 (show (0 : Fin 2) ≠ 1 by decide) true false (-1) ∈
      ⁅(fixElem hG (d • quadOdd 3 K)).comap (spinAction (quadOdd 3 K)),
        (fixElem hG (d • quadOdd 3 K)).comap (spinAction (quadOdd 3 K))⁆ := by
  obtain ⟨x, y, hy, hxy⟩ := exists_sq_add_sq_eq_neg_one hkodd
  have hyK : (y : K) ≠ 0 := fun h => hy (Subtype.ext h)
  have hxyK : (x : K) ^ 2 + (y : K) ^ 2 = -1 := by
    have := congrArg (fun t : semilinearFixedSubfield σ => (t : K)) hxy
    simpa using this
  have hc' := commutatorElement_upperSL2_lowerSL2_eq_neg_one (one_ne_zero : (1 : K) ≠ 0) hyK
    hxyK
  have key : ∀ a b c : semilinearFixedSubfield σ,
      (scaledFrame hG hd hQ₀ h01 h02 h12).longSL2 (show (0 : Fin 2) ≠ 1 by decide) true false
        (upperSL2 (a : K) * lowerSL2 (b : K) * upperSL2 (c : K)) ∈
          (fixElem hG (d • quadOdd 3 K)).comap (spinAction (quadOdd 3 K)) := fun a b c => by
    rw [map_mul, map_mul]
    exact mul_mem (mul_mem (scaledFrame_upper_false hG hd hQ₀ h01 h02 h12 a)
      (scaledFrame_lower_false hG hd hQ₀ h01 h02 h12 b))
      (scaledFrame_upper_false hG hd hQ₀ h01 h02 h12 c)
  have eI : upperSL2 (1 : K) * lowerSL2 (-(1 : K)⁻¹) * upperSL2 (1 : K) =
      upperSL2 ((1 : semilinearFixedSubfield σ) : K) *
        lowerSL2 ((-1 : semilinearFixedSubfield σ) : K) *
          upperSL2 ((1 : semilinearFixedSubfield σ) : K) := by
    simp
  have s1 : ((x : K) - 1) * 1 / y = (((x - 1) / y : semilinearFixedSubfield σ) : K) := by
    push_cast
    ring
  have s2 : (y : K) / 1 = ((y : semilinearFixedSubfield σ) : K) := by ring
  have s3 : (-(x : K) - 1) * 1 / y = (((-x - 1) / y : semilinearFixedSubfield σ) : K) := by
    push_cast
    ring
  rw [← hc', map_commutatorElement, eI, s1, s2, s3]
  exact Subgroup.commutator_mem_commutator (key _ _ _) (key _ _ _)

include hd hQ₀ h01 h02 h12 in
theorem spinZ_mem_commutator_comap_fixElem [Finite K]
    (hkodd : Odd (Nat.card (semilinearFixedSubfield σ))) :
    spinZ K ∈ ⁅(fixElem hG (d • quadOdd 3 K)).comap (spinAction (quadOdd 3 K)),
      (fixElem hG (d • quadOdd 3 K)).comap (spinAction (quadOdd 3 K))⁆ := by
  have hnot := longSL2_neg_one_not (scaledFrame hG hd hQ₀ h01 h02 h12)
    (show (0 : Fin 2) ≠ 1 by decide) (nondegenerate_quadOdd 3 K).ne_zero true true
  simp only [Bool.not_true] at hnot
  have hz : spinZ K = (scaledFrame hG hd hQ₀ h01 h02 h12).longSL2
      (show (0 : Fin 2) ≠ 1 by decide) true false (-1) *
        ((scaledFrame hG hd hQ₀ h01 h02 h12).longSL2
          (show (0 : Fin 2) ≠ 1 by decide) true true (-1))⁻¹ := by
    rw [hnot, mul_inv_cancel_right]
  rw [hz]
  exact mul_mem (scaledFrame_neg_one_false_mem hG hd hQ₀ h01 h02 h12 hkodd)
    (inv_mem (scaledFrame_neg_one_true_mem hG hd hQ₀ h01 h02 h12 hkodd))

include hQ₀ h01 h02 h12 in
theorem card_pow_four_dvd_card_fixElem :
    Nat.card (semilinearFixedSubfield σ) ^ 4 ∣ Nat.card ↥(fixElem hG (d • quadOdd 3 K)) := by
  have hQ₀' : ∀ w, ((Q₀ w : semilinearFixedSubfield σ) : K) = (d • quadOdd 3 K) w := fun w => by
    rw [hQ₀ w, smul_apply, smul_eq_mul]
  let ρ₀ : semilinearFixedSubfield σ × semilinearFixedSubfield σ × semilinearFixedSubfield σ ×
      semilinearFixedSubfield σ →+ semilinearFixedSubmodule σ G hG :=
    { toFun := fun t => t.1 • P1.e + t.2.1 • P1.f + t.2.2.1 • P2.e + t.2.2.2 • P2.f
      map_zero' := by simp
      map_add' := fun s t => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel }
  let ρ := (semilinearFixedSubmodule σ G hG).subtype.toAddMonoidHom.comp ρ₀
  have hρ0e : ∀ t, polar Q₀ P0.e (ρ₀ t) = 0 := fun t => by
    change polar Q₀ P0.e (t.1 • P1.e + t.2.1 • P1.f + t.2.2.1 • P2.e + t.2.2.2 • P2.f) = 0
    simp only [polar_add_right, polar_smul_right, h01.ee, h01.ef, h02.ee, h02.ef, smul_zero,
      add_zero]
  have hρ0f : ∀ t, polar Q₀ P0.f (ρ₀ t) = 0 := fun t => by
    change polar Q₀ P0.f (t.1 • P1.e + t.2.1 • P1.f + t.2.2.1 • P2.e + t.2.2.2 • P2.f) = 0
    simp only [polar_add_right, polar_smul_right, h01.fe, h01.ff, h02.fe, h02.ff, smul_zero,
      add_zero]
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b', c', e'⟩ ht
    have ht0 : ρ₀ (a, b', c', e') = 0 := Subtype.ext ht
    change a • P1.e + b' • P1.f + c' • P2.e + e' • P2.f = 0 at ht0
    have q1 : polar Q₀ P2.e P1.f = 0 := by rw [polar_comm]; exact h12.fe
    have q2 : polar Q₀ P2.f P1.f = 0 := by rw [polar_comm]; exact h12.ff
    have q3 : polar Q₀ P2.e P1.e = 0 := by rw [polar_comm]; exact h12.ee
    have q4 : polar Q₀ P2.f P1.e = 0 := by rw [polar_comm]; exact h12.ef
    have p1 := congrArg (fun w => polar Q₀ w P1.f) ht0
    have p2 := congrArg (fun w => polar Q₀ w P1.e) ht0
    have p3 := congrArg (fun w => polar Q₀ w P2.f) ht0
    have p4 := congrArg (fun w => polar Q₀ w P2.e) ht0
    simp only [polar_add_left, polar_smul_left, polar_zero_left, P1.polar_ef, P1.polar_ff,
      P2.polar_ef, P2.polar_ff, P1.polar_fe, P1.polar_ee, P2.polar_fe, P2.polar_ee, q1, q2, q3,
      q4, h12.ef, h12.ff, h12.ee, h12.fe, smul_eq_mul, mul_one, mul_zero, add_zero,
      zero_add] at p1 p2 p3 p4
    rw [p1, p2, p3, p4]
    rfl
  have hρe : ∀ t, polar (d • quadOdd 3 K) (P0.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (ρ t) = 0 :=
    fun t => by
      change polar (d • quadOdd 3 K) (P0.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K)
        (ρ₀ t : semilinearFixedSubmodule σ G hG) = 0
      rw [← coe_polar_of_restrict hG hQ₀', hρ0e, ZeroMemClass.coe_zero]
  have hρf : ∀ t, polar (d • quadOdd 3 K) (P0.f : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (ρ t) = 0 :=
    fun t => by
      change polar (d • quadOdd 3 K) (P0.f : Fin 3 ⊕ Fin 3 ⊕ Unit → K)
        (ρ₀ t : semilinearFixedSubmodule σ G hG) = 0
      rw [← coe_polar_of_restrict hG hQ₀', hρ0f, ZeroMemClass.coe_zero]
  have hQe : (d • quadOdd 3 K) (P0.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 0 := by
    rw [← hQ₀', P0.Q_e, ZeroMemClass.coe_zero]
  have hef : polar (d • quadOdd 3 K) (P0.e : Fin 3 ⊕ Fin 3 ⊕ Unit → K)
      (P0.f : Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≠ 0 := by
    rw [← coe_polar_of_restrict hG hQ₀', P0.polar_ef, OneMemClass.coe_one]
    exact one_ne_zero
  have h1 := card_dvd_of_eichler_mem ρ hρ hQe hef hρe hρf fun t =>
    eichler_mem_fixElem hG (Q' := d • quadOdd 3 K) P0.e (ρ₀ t)
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_prod,
    show ∀ n : ℕ, n * (n * (n * n)) = n ^ 4 from fun n => by ring] at h1

end KForm

section Field

variable {K : Type} [Field K]

theorem u1_field_core [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {α : MulAut (spinGroup (quadOdd 3 K))}
    {σ : K ≃+* K} (hσo : orderOf σ = 2)
    {G : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hG : ∀ (a : K) v, G (a • v) = σ a • G v) (hGG : ∀ v, G (G v) = v) {η : K}
    (hQG : ∀ v, quadOdd 3 K (G v) = η * σ (quadOdd 3 K v))
    (hπ : ∀ s v, spinAction (quadOdd 3 K) (α s) v = G (spinAction (quadOdd 3 K) s (G.symm v))) :
    ∃ J : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (fixedSubgroup α) ∧
      spinZ K ∈ J ∧ ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_spin hp hp2 hK
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at h5
      omega
    · exact h
  have hnd := nondegenerate_polarBilin_quadOdd 3 K h2
  have hap : ∀ v, (⇑G)^[2] v = v := fun v => hGG v
  obtain ⟨h2f, hkcard, d, Q₀, hQ₀, hnd₀, hfr, Φ, hΦ1, -⟩ :=
    exists_descent hp hf hK σ hσo G hG hap (quadOdd 3 K) hnd η hQG
  have : FiniteDimensional (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ G hG) :=
    Module.Finite.of_finite
  have hfr' : Module.finrank (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ G hG) = 7 :=
    hfr.trans (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp)
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hnd₀
  have hdim : 2 * m + δ = 7 := H.finrank_eq.symm.trans hfr'
  obtain rfl : δ = 1 := by omega
  obtain rfl : m = 3 := by omega
  have hd0 : (d : K) ≠ 0 := d.ne_zero
  have h01 := H.hypPair_orth (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := H.hypPair_orth (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := H.hypPair_orth (show (1 : Fin 3) ≠ 2 by decide)
  have hQ₀' : ∀ w, ((Q₀ w : semilinearFixedSubfield σ) : K) = ((d : K) • quadOdd 3 K) w :=
    fun w => by rw [hQ₀ w, smul_apply, smul_eq_mul]
  have hσd : σ (d : K) = d * η := by
    obtain ⟨w, hw⟩ : ∃ w : semilinearFixedSubmodule σ G hG,
        w = (H.hypPair 0).e + (H.hypPair 0).f := ⟨_, rfl⟩
    have hw1 : Q₀ w = 1 := by
      rw [hw, QuadraticMap.map_add Q₀, (H.hypPair 0).Q_e, (H.hypPair 0).Q_f,
        (H.hypPair 0).polar_ef, zero_add, zero_add]
    have h1 := hQ₀ w
    rw [hw1, OneMemClass.coe_one] at h1
    have hfix : G (w : Fin 3 ⊕ Fin 3 ⊕ Unit → K) = w := w.2
    have h3 := hQG (w : Fin 3 ⊕ Fin 3 ⊕ Unit → K)
    rw [hfix] at h3
    have h4 : σ ((d : K) * quadOdd 3 K w) = 1 := by rw [← h1, map_one]
    rw [map_mul] at h4
    have hne : σ (quadOdd 3 K w) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h4
      exact zero_ne_one h4
    apply mul_right_cancel₀ hne
    rw [h4]
    calc (1 : K) = (d : K) * quadOdd 3 K w := h1
      _ = d * η * σ (quadOdd 3 K w) := by
        conv_lhs => rw [h3]
        ring
  have hQ'G : ∀ x, ((d : K) • quadOdd 3 K) (G x) = σ (((d : K) • quadOdd 3 K) x) := fun x => by
    rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, hQG, map_mul, hσd]
    ring
  let bK : Module.Basis (Fin 3 ⊕ Fin 3 ⊕ Fin 1) K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
    (H.b.baseChange K).map Φ
  have hbK : ∀ a, bK a = ((H.b a : semilinearFixedSubmodule σ G hG) :
      Fin 3 ⊕ Fin 3 ⊕ Unit → K) := by
    intro a
    show Φ ((H.b.baseChange K) a) = _
    rw [Module.Basis.baseChange_apply, hΦ1, one_smul]
  have hext : ∀ g h : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K),
      (∀ x : semilinearFixedSubmodule σ G hG, g x = h x) → g = h := fun g h hgh =>
    LinearEquiv.toLinearMap_injective (bK.ext fun a => by
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, hbK]
      exact hgh _)
  have eE : fixElem hG ((d : K) • quadOdd 3 K) ≃* elementaryGroup Q₀ :=
    fixElemEquiv hG hQ'G hQ₀' hext
  have h2k : (2 : semilinearFixedSubfield σ) ≠ 0 := fun h => h2 (by
    rw [← map_ofNat (semilinearFixedSubfield σ).subtype 2, h, map_zero])
  obtain ⟨hsE, a, b, hab⟩ := isSimpleGroup_elementaryGroup_of_hypPairs h2k hnd₀
    (by rw [hfr']; exact ⟨3, rfl⟩) h01 h02 h12
  have hsE₀ : IsSimpleGroup ↥(fixElem hG ((d : K) • quadOdd 3 K)) := eE.isSimpleGroup
  have hncE₀ : ∃ a b : ↥(fixElem hG ((d : K) • quadOdd 3 K)), a * b ≠ b * a := by
    refine ⟨eE.symm a, eE.symm b, fun h => hab ?_⟩
    have h' := congrArg eE h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  obtain ⟨hE₀q, hE₀Z⟩ := LocalCores.isQuasisimple_of_isSimpleGroup hncE₀
  have hrange : (spinAction (quadOdd 3 K)).range = elementaryGroup (quadOdd 3 K) := by
    rw [range_spinAction_quadOdd_eq_commutator h2 (le_refl 3),
      commutator_orthogonalGroup_quadOdd h2 (le_refl 3)]
  have hEr : fixElem hG ((d : K) • quadOdd 3 K) ≤ (spinAction (quadOdd 3 K)).range := by
    rw [hrange, fixElem, Subgroup.closure_le]
    rintro _ ⟨u, w, -, -, rfl⟩
    rw [eichler_smul_form hd0]
    exact eichler_mem_elementaryGroup _ _ _
  have hkodd : Odd (Nat.card (semilinearFixedSubfield σ)) := by
    rw [hkcard]
    exact (hp.odd_of_ne_two hp2).pow
  have hdvd : (p ^ f) ^ 2 ∣ Nat.card ↥(fixElem hG ((d : K) • quadOdd 3 K)) := by
    have h1 := card_pow_four_dvd_card_fixElem hG hQ₀ h01 h02 h12
    rw [hkcard] at h1
    obtain ⟨t, ht⟩ := h2f
    rw [ht, Nat.mul_div_cancel_left t two_pos] at h1
    rw [ht]
    convert h1 using 1
    ring
  exact u1_of_comap hp hp2 hK h5 hπ hE₀q hE₀Z hEr
    (fun g hg v => mem_commGroup.mp (fixElem_le_commGroup hG hQ'G hg) v)
    (fun g hg hgc h hh => conj_mem_fixElem hG
      (mem_orthogonalGroup_smul_form (elementaryGroup_le_orthogonalGroup _ (hrange ▸ hg)) _)
      (mem_commGroup.mpr hgc) hh)
    (spinZ_mem_commutator_comap_fixElem hG hd0 hQ₀ h01 h02 h12 hkodd) hdvd

theorem u1_field [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) {α : MulAut (spinGroup (quadOdd 3 K))} {σ : K ≃+* K}
    (hσ2 : ∀ c, σ (σ c) = c) (hσ1 : σ ≠ 1)
    {F : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hF : ∀ (c : K) v, F (c • v) = σ c • F v) {μ : K}
    (hQF : ∀ v, quadOdd 3 K (F v) = μ * σ (quadOdd 3 K v)) {c : K} (hc : c ≠ 0)
    (hFF : ∀ v, F (F v) = c • v)
    (hπ : ∀ s v, spinAction (quadOdd 3 K) (α s) v = F (spinAction (quadOdd 3 K) s (F.symm v))) :
    ∃ J : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (fixedSubgroup α) ∧
      spinZ K ∈ J ∧ ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσo : orderOf σ = 2 := by
    have hsq : σ ^ 2 = 1 := RingEquiv.ext fun x => by
      rw [pow_two]
      exact hσ2 x
    exact orderOf_eq_prime hsq hσ1
  have hz0 : F (oddZ 3 K) ≠ 0 := by
    intro h0
    have h1 := F.injective (h0.trans (map_zero F).symm)
    have hQ := quadOdd_oddZ 3 K
    rw [h1, QuadraticMap.map_zero] at hQ
    exact zero_ne_one hQ
  have hσc : σ c = c := by
    have h1 : F (F (F (oddZ 3 K))) = c • F (oddZ 3 K) := hFF _
    rw [hFF (oddZ 3 K), hF] at h1
    have : (σ c - c) • F (oddZ 3 K) = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz0)
  obtain ⟨l, hl⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ (c := c⁻¹) (by rw [map_inv₀, hσc])
  rw [hσo, Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one] at hl
  have hl' : l * σ l = c⁻¹ := hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hl'
    exact inv_ne_zero hc hl'.symm
  set G : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
    F.trans (LinearEquiv.smulOfNeZero K _ l hl0).toAddEquiv with hGdef
  have hGv : ∀ v, G v = l • F v := fun v => rfl
  have hG : ∀ (a : K) v, G (a • v) = σ a • G v := fun a v => by
    rw [hGv, hGv, hF, smul_comm]
  have hGG : ∀ v, G (G v) = v := fun v => by
    rw [hGv, hGv, hF, hFF, smul_smul, smul_smul, hl', inv_mul_cancel₀ hc, one_smul]
  have hQG : ∀ v, quadOdd 3 K (G v) = (l * l * μ) * σ (quadOdd 3 K v) := fun v => by
    rw [hGv, QuadraticMap.map_smul, smul_eq_mul, hQF]
    ring
  have hGsymm : ∀ v, G.symm v = F.symm (l⁻¹ • v) := fun v => G.injective (by
    rw [AddEquiv.apply_symm_apply, hGv, AddEquiv.apply_symm_apply, smul_smul,
      mul_inv_cancel₀ hl0, one_smul])
  have hπG : ∀ s v, spinAction (quadOdd 3 K) (α s) v =
      G (spinAction (quadOdd 3 K) s (G.symm v)) := fun s v => by
    rw [hGsymm, hGv, ← hπ, map_smul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  exact u1_field_core hp hp2 hK h5 hσo hG hGG hQG hπG

end Field

end CFSG.ComponentClassification.HarrisLit.T1
