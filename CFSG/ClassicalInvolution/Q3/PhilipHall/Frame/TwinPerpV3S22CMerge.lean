module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22CStmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf11Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf65TransW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf66Class
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf67Print
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf68Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf16Orbit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

section

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Asc77.C22G

variable {n : ℕ}

theorem adapted_boundsAllC (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hT4 : Thm4RTwinBelow 3 n)
    (h5 : V3Fourth n) (hαF : V3FourthAlphaF n) (hS : V3Hyp51StarF n) (hG : V3LayerGenAllC n)
    {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hα : A7T22.AlphaConst (CoreAssembly.conjClass (tightCore R)) t)
    {L L' L₃ : Subgroup Y} {x₁ x₂ x₃ : Y}
    (hd' : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) L L' L₃ t x₁ x₂ x₃)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (hx₁ : x₁ ∈ W)
    (hx₂ : x₂ ∈ W) :
    rLayer (CoreAssembly.conjClass (tightCore R)) (x₁ * x₂) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y) ∧
      Subgroup.centralizer ({x₁ * x₂} : Set Y) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y) := by
  have hd := hStd.datum
  have hCore := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hCore.hyp
  have hP' := hCore.partIHypG
  have hq8 := q8_all_of_core hCore
  have hCz := centralizer_le_normalizer_alpha hα hd
  have std' : V3Std n Y R S t L L' L₃ x₁ x₂ x₃ := ⟨hStd.perp, hStd.two, hStd.exit, hd', hStd.wyl⟩
  obtain ⟨K₄', hF'⟩ := h5 Y R S t L L' L₃ x₁ x₂ x₃ std'
  have hperp' := kPerp_datum hStd.perp hd'.mem hd'.hz
  have hzW : t ∈ W := hd'.sq₁ ▸ W.mul_mem hx₁ hx₁
  obtain ⟨a₁, a₂, a₃, a₄, y, h1, o1, h2, o2, h3, o3, h4, o4, c12, c13, c14, c23, c24, c34, hy, hne,
    ha₁W, ha₂W, ha₃W, ha₄W, hyc, j, hj1, hj2, hj3, hj4⟩ :=
    exists_fuse_cent2W hP' hd' hperp' hF'.1 hF'.2.1 hF'.2.2.1 hF'.2.2.2.1 hStd.wyl hW hzW
  have core : A7T22.Hyp22Core (CoreAssembly.conjClass (tightCore R)) L L' L₃ t a₁ a₂ a₃ :=
    ⟨hd'.hyp, hd'.mem, hd'.hK'.1, hd'.hK₃.1, hd'.hz, hd'.hzK', hd'.hzK₃, hd'.hne, hd'.hK₃K,
      hd'.hK₃K', ⟨h1, o1⟩, ⟨h2, o2⟩, ⟨h3, o3⟩, c12, c13, c23⟩
  have dstar := A7T22.Hyp22G.of_core core hd'.subn
  have stdstar : V3Std n Y R S t L L' L₃ a₁ a₂ a₃ :=
    ⟨hStd.perp, hStd.two, hStd.exit, dstar, hStd.wyl⟩
  have fr : V3Frame R t L L' L₃ a₁ a₂ K₄' a₃ a₄ y :=
    ⟨hF'.1, hF'.2.1, hF'.2.2.1, hF'.2.2.2.1, h3, o3, h4, o4, c13, c14, c23, c24, c34, hy, hne,
      hyc, ⟨j, hj1, hj2, hj3, hj4⟩⟩
  have hLn := v3LayerNormFrAllC hS hG stdstar fr hW ha₁W ha₂W ha₃W ha₄W
  have hCn := v3CentUFrAllC hT4 hαF hS hG stdstar fr hW ha₁W ha₂W ha₃W ha₄W
  have heq := hd.alpha_eq_of_datum hα dstar
  rw [← heq] at hLn hCn
  have hz : IsUniqueInvolution L t := hd'.hz
  have hUL : L ⊓ W ∈ USet (CoreAssembly.conjClass (tightCore R)) := by
    have c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W :=
      Q3CL.T8.ctxOf hP' hW
    obtain ⟨ρ, hρ⟩ := Q3.TL4.exists_rep_of_involution_mem_gen c hP'.cls hd'.mem hz hzW
    have := Q3CL.Thompson.inf_W_of_mem_D hΩ hW ρ.hR ρ.hK ρ.hRK
    rw [hρ] at this
    exact this.2.1
  have hUL' : L' ⊓ W ∈ USet (CoreAssembly.conjClass (tightCore R)) := by
    have c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W :=
      Q3CL.T8.ctxOf hP' hW
    obtain ⟨ρ, hρ⟩ := Q3.TL4.exists_rep_of_involution_mem_gen c hP'.cls hd'.hK'.1 hd'.hzK' hzW
    have := Q3CL.Thompson.inf_W_of_mem_D hΩ hW ρ.hR ρ.hK ρ.hRK
    rw [hρ] at this
    exact this.2.1
  have ε₁ := eq_or_inv_of_mem_USet hΩ hq8 hUL (Subgroup.mem_inf.mpr ⟨h1, ha₁W⟩)
    (Subgroup.mem_inf.mpr ⟨hd'.hu₁.1, hx₁⟩) o1 hd'.hu₁.2
  have ε₂ := eq_or_inv_of_mem_USet hΩ hq8 hUL' (Subgroup.mem_inf.mpr ⟨h2, ha₂W⟩)
    (Subgroup.mem_inf.mpr ⟨hd'.hu₂.1, hx₂⟩) o2 hd'.hu₂.2
  have hx1sq : x₁ * x₁ = t := hd'.sq₁
  have hx2sq : x₂ * x₂ = t := hd'.sq₂
  have ht2 : t * t = 1 := hz.sq
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ha1sq : a₁ * a₁ = t := T7A.sq_eq_of_orderOf_four hz h1 o1
  have ha2sq : a₂ * a₂ = t := T7A.sq_eq_of_orderOf_four hd'.hzK' h2 o2
  have hinv : x₁⁻¹ * x₁⁻¹ = x₂⁻¹ * x₂⁻¹ := by
    calc x₁⁻¹ * x₁⁻¹ = (x₁ * x₁)⁻¹ := by group
      _ = (x₂ * x₂)⁻¹ := by rw [hx1sq, hx2sq]
      _ = x₂⁻¹ * x₂⁻¹ := by group
  have hcc : (x₁ * x₂)⁻¹ * (a₁ * a₂) = 1 ∨ (x₁ * x₂)⁻¹ * (a₁ * a₂) = t := by
    rcases ε₁ with e1 | e1 <;> rcases ε₂ with e2 | e2 <;> rw [e1, e2]
    · left; group
    · right
      calc (x₁ * x₂)⁻¹ * (x₁ * x₂⁻¹) = (x₂ * x₂)⁻¹ := by group
        _ = t := by rw [hx2sq, hti]
    · right
      calc (x₁ * x₂)⁻¹ * (x₁⁻¹ * x₂) = x₂⁻¹ * (x₁⁻¹ * x₁⁻¹) * x₂ := by group
        _ = x₂⁻¹ * (x₂⁻¹ * x₂⁻¹) * x₂ := by rw [hinv]
        _ = (x₂ * x₂)⁻¹ := by group
        _ = t := by rw [hx2sq, hti]
    · left
      calc (x₁ * x₂)⁻¹ * (x₁⁻¹ * x₂⁻¹) = x₂⁻¹ * (x₁⁻¹ * x₁⁻¹) * x₂⁻¹ := by group
        _ = x₂⁻¹ * (x₂⁻¹ * x₂⁻¹) * x₂⁻¹ := by rw [hinv]
        _ = (x₂ * x₂ * (x₂ * x₂))⁻¹ := by group
        _ = 1 := by rw [hx2sq, ht2]; simp
  rcases hcc with hc1 | hc1
  · have : x₁ * x₂ = a₁ * a₂ := inv_mul_eq_one.mp hc1
    rw [this]
    exact ⟨hLn, hCn⟩
  · have hxa : x₁ * x₂ = j * (a₁ * a₂) * j⁻¹ := by
      have e1 : a₁ * a₂ = (x₁ * x₂) * t := inv_mul_eq_iff_eq_mul.mp hc1
      have e2 : j * (a₁ * a₂) * j⁻¹ = (j * a₁ * j⁻¹) * (j * a₂ * j⁻¹) := by group
      have e3 : a₁⁻¹ = a₁ * t := by
        apply inv_eq_of_mul_eq_one_right
        calc a₁ * (a₁ * t) = (a₁ * a₁) * t := by group
          _ = 1 := by rw [ha1sq]; exact ht2
      have e4 : t * a₂ = a₂ * t := by
        calc t * a₂ = (a₂ * a₂) * a₂ := by rw [ha2sq]
          _ = a₂ * (a₂ * a₂) := by group
          _ = a₂ * t := by rw [ha2sq]
      rw [e2, hj1, hj2, e3]
      calc x₁ * x₂ = (x₁ * x₂) * t * t := by rw [mul_assoc, ht2, mul_one]
        _ = (a₁ * a₂) * t := by rw [← e1]
        _ = a₁ * (a₂ * t) := by group
        _ = a₁ * (t * a₂) := by rw [e4]
        _ = a₁ * t * a₂ := by group
    have hjt : j * t * j⁻¹ = t := by
      rw [← ha2sq]
      calc j * (a₂ * a₂) * j⁻¹ = (j * a₂ * j⁻¹) * (j * a₂ * j⁻¹) := by group
        _ = a₂ * a₂ := by rw [hj2]
    have hjC : j ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc j * t = (j * t * j⁻¹) * j := by group
        _ = t * j := by rw [hjt]
    exact layer_cent_transfer hΩ.conjInvariant (hCz hjC) hxa.symm hLn hCn

end

section

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77.Thompson

variable {n : ℕ}

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW in
theorem v3Alpha1_of_partsWAllC (hEW : ThmEQ8) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n)
    (h51 : V3Hyp51B n) (h5 : V3Fourth n) (hαF : V3FourthAlphaF n) (hS : V3Hyp51StarF n)
    (hG : V3LayerGenAllC n) : V3Alpha13 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hL
  have hα := alphaConst h51 hStd.perp hStd.two hStd.exit
  have hd := hStd.datum
  have hCore := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hCore.hyp
  have hCz := centralizer_le_normalizer_alpha hα hd
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have hq8 := q8_all_of_core hCore
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g K = J := by
    obtain ⟨a, ha⟩ := hd.mem
    rintro _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, conjSub_mul, conjSub_inv_conjSub]
  have hY : ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)), ∀ (L₃ : Subgroup Y)
      (x₁ x₂ x₃ : Y), A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' L₃ t x₁ x₂ x₃ →
      x₁ ∈ W' → x₂ ∈ W' → rLayer (CoreAssembly.conjClass (tightCore R)) (x₁ * x₂) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y) :=
    fun W' hW' L₃ x₁ x₂ x₃ hd' hx₁ hx₂ =>
      (adapted_boundsAllC hcit hP h4 h5 hαF hS hG hStd hα hd' hW' hx₁ hx₂).1
  have hkey := exists_conj_of_dstarCompW hCore.partIHypG hd hperp hCz hY
  have htrans : ∀ J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K,
      ∃ h' ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y), conjSub h' K = J := by
    intro J hJ
    obtain ⟨w, hw, y, hy, hyw⟩ := hkey J hJ
    have hJΩ : J ∈ CoreAssembly.conjClass (tightCore R) :=
      (T3.mem_dstarComp_symm hd.mem hJ).1
    have hM₀ : conjSub y⁻¹ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := by
      refine ⟨hΩ.conjInvariant y⁻¹ J hJΩ, t, hd.hz, ?_⟩
      have := hw.conj y⁻¹
      have e : y⁻¹ * w * y⁻¹⁻¹ = t := by rw [← hyw]; group
      rwa [e] at this
    obtain ⟨g, hg⟩ := htr (conjSub y⁻¹ J) hM₀.1
    have hgz : g * t * g⁻¹ = t := by
      have h1 := hd.hz.conj g
      rw [hg] at h1
      exact (isUniqueInvolution_of_mem_twinSet hd.hz hM₀).eq h1 |>.symm
    have hgC : g ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [hgz]
    refine ⟨y * g, Subgroup.mul_mem _ hy (hCz hgC), ?_⟩
    rw [conjSub_mul, hg, conjSub_conjSub_inv]
  have hCent : ∀ (J L₃ : Subgroup Y) (x₁ x₂ x₃ : Y),
      A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K J L₃ t x₁ x₂ x₃ →
      (∃ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)), x₁ ∈ W' ∧ x₂ ∈ W') →
      Subgroup.centralizer ({x₁ * x₂} : Set Y) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y) := by
    intro J L₃ x₁ x₂ x₃ hd'' ⟨W', hW', hx₁, hx₂⟩
    exact (adapted_boundsAllC hcit hP h4 h5 hαF hS hG hStd hα hd'' hW' hx₁ hx₂).2
  obtain ⟨W, hWP, hKW⟩ := exists_printedWT hΩ hd.mem hd.hK' hd.hne
  obtain ⟨S₀, hWP'⟩ := hWP
  have hcentAll : CentAll (CoreAssembly.conjClass (tightCore R)) W
      (Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y)) := by
    obtain ⟨R₀, -, -, hWΩ, -⟩ := id hWP'
    refine centAll_of_centAllK hΩ hd.mem hWΩ hKW htrans ?_
    intro x hx hU
    exact centralizersPrinted_of_adapted hCore.partIHypG hd hperp hq8 hCz hCent
      (WSet.conj hΩ.conjInvariant hWΩ x) hU
  have htop := twinThmEPrintedAllT_of_thmEQ8 hEW hcit hP Y R S t hStd.perp.core.toHyp K _ W S₀ hd.mem
    hWP' ⟨htrans, hcentAll.toPairs _⟩
  have hnorm : (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp htop
  have hle : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) ≤
      classicalInvolutionOddCore Y := le_sSup ⟨hnorm, (hα K K' K₃ u₁ u₂ u₃ hd).1⟩
  rw [hCore.oddFree] at hle
  exact le_bot_iff.mp hle

end

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
