module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddRotGen
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddRotAlg

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

variable {L : Type} [Field L] [IsAlgClosed L]


section Curves

@[expose] def xOWord : List (Letter TwistTag.D4.tag × Polynomial L) :=
  [(((0 : Fin TwistTag.D4.tag.rank), true), Polynomial.X),
   (((1 : Fin TwistTag.D4.tag.rank), true), Polynomial.X),
   (((3 : Fin TwistTag.D4.tag.rank), true), Polynomial.X)]

@[expose] def yOWord : List (Letter TwistTag.D4.tag × Polynomial L) :=
  [(((0 : Fin TwistTag.D4.tag.rank), false), Polynomial.X),
   (((1 : Fin TwistTag.D4.tag.rank), false), Polynomial.X),
   (((3 : Fin TwistTag.D4.tag.rank), false), Polynomial.X)]

theorem wordUnit_mapWord_xOWord (z : Polynomial L →+* L) :
    wordUnit TwistTag.D4.tag L (mapWord z xOWord) = xO (z Polynomial.X) := by
  simp [xOWord, mapWord, wordUnit, letterUnit, xO, mul_assoc]

theorem wordUnit_mapWord_yOWord (z : Polynomial L →+* L) :
    wordUnit TwistTag.D4.tag L (mapWord z yOWord) = yO (z Polynomial.X) := by
  simp [yOWord, mapWord, wordUnit, letterUnit, yO, mul_assoc]

@[expose] def xOCurve : WordCurve TwistTag.D4.tag L :=
  WordCurve.ofWord (Polynomial L) xOWord (Polynomial.aeval 0) (by
    rw [wordUnit_mapWord_xOWord]
    simp [xO_zero])

@[expose] def yOCurve : WordCurve TwistTag.D4.tag L :=
  WordCurve.ofWord (Polynomial L) yOWord (Polynomial.aeval 0) (by
    rw [wordUnit_mapWord_yOWord]
    simp [yO_zero])

theorem values_xOCurve : (xOCurve (L := L)).values = Set.range (xO (L := L)) := by
  rw [xOCurve, WordCurve.values_ofWord]
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z Polynomial.X, (wordUnit_mapWord_xOWord _).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Polynomial.aeval c, (wordUnit_mapWord_xOWord _).trans (by simp)⟩

theorem values_yOCurve : (yOCurve (L := L)).values = Set.range (yO (L := L)) := by
  rw [yOCurve, WordCurve.values_ofWord]
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z Polynomial.X, (wordUnit_mapWord_yOWord _).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Polynomial.aeval c, (wordUnit_mapWord_yOWord _).trans (by simp)⟩

@[expose] def conjCurve (F : WordCurve TwistTag.D4.tag L) (w w' : List (Letter TwistTag.D4.tag × L))
    (h : wordUnit TwistTag.D4.tag L w * wordUnit TwistTag.D4.tag L w' = 1) :
    WordCurve TwistTag.D4.tag L :=
  ⟨F.D, mapWord (algebraMap L F.D : L →+* F.D) w ++ F.word ++
      mapWord (algebraMap L F.D : L →+* F.D) w', F.base, by
    have hb : ∀ w : List (Letter TwistTag.D4.tag × L),
        mapWord (F.base : F.D →+* L) (mapWord (algebraMap L F.D : L →+* F.D) w) = w := by
      intro w
      rw [mapWord_mapWord]
      have : (F.base : F.D →+* L).comp (algebraMap L F.D : L →+* F.D) = RingHom.id L := by
        ext c; simp
      rw [this]
      simp [mapWord]
    rw [mapWord_append, mapWord_append, hb, hb, wordUnit_append, wordUnit_append, F.base_eq,
      mul_one, h]⟩

theorem mapWord_mapWord_algebraMap (F : WordCurve TwistTag.D4.tag L) (z : F.D →ₐ[L] L)
    (w : List (Letter TwistTag.D4.tag × L)) :
    mapWord (z : F.D →+* L) (mapWord (algebraMap L F.D : L →+* F.D) w) = w := by
  rw [mapWord_mapWord]
  have : (z : F.D →+* L).comp (algebraMap L F.D : L →+* F.D) = RingHom.id L := by
    ext c; simp
  rw [this]
  simp [mapWord]

theorem conjCurve_eval (F : WordCurve TwistTag.D4.tag L) (w w' : List (Letter TwistTag.D4.tag × L))
    (h : wordUnit TwistTag.D4.tag L w * wordUnit TwistTag.D4.tag L w' = 1) (z : F.D →ₐ[L] L) :
    wordUnit TwistTag.D4.tag L (mapWord (z : F.D →+* L) (conjCurve F w w' h).word) =
      wordUnit TwistTag.D4.tag L w * wordUnit TwistTag.D4.tag L (mapWord (z : F.D →+* L) F.word) *
        wordUnit TwistTag.D4.tag L w' := by
  show wordUnit TwistTag.D4.tag L (mapWord (z : F.D →+* L)
    (mapWord (algebraMap L F.D : L →+* F.D) w ++ F.word ++
      mapWord (algebraMap L F.D : L →+* F.D) w')) = _
  rw [mapWord_append, mapWord_append, mapWord_mapWord_algebraMap, mapWord_mapWord_algebraMap,
    wordUnit_append, wordUnit_append]

theorem values_conjCurve (F : WordCurve TwistTag.D4.tag L) (w w' : List (Letter TwistTag.D4.tag × L))
    (h : wordUnit TwistTag.D4.tag L w * wordUnit TwistTag.D4.tag L w' = 1) :
    (conjCurve F w w' h).values =
      (fun v => wordUnit TwistTag.D4.tag L w * v * wordUnit TwistTag.D4.tag L w') '' F.values := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, (conjCurve_eval F w w' h z).symm⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, conjCurve_eval F w w' h z⟩


theorem exists_wordUnit_eq {ζ : ModGL TwistTag.D4.tag L} (hζ : ζ ∈ adjointGroup TwistTag.D4.tag L) :
    ∃ w : List (Letter TwistTag.D4.tag × L), wordUnit TwistTag.D4.tag L w = ζ := by
  obtain ⟨w, hw⟩ := exists_wordElt_eq (τ := TwistTag.D4.tag) (k := L) ⟨ζ, hζ⟩
  refine ⟨w, ?_⟩
  have := congrArg (fun g : adjointGroup TwistTag.D4.tag L => (g : ModGL TwistTag.D4.tag L)) hw
  simpa [coe_wordElt] using this

theorem mul_wordUnit_invWord (w : List (Letter TwistTag.D4.tag × L)) :
    wordUnit TwistTag.D4.tag L w * wordUnit TwistTag.D4.tag L (invWord w) = 1 := by
  rw [wordUnit_invWord, mul_inv_cancel]

@[expose] def rotCurves (w : List (Letter TwistTag.D4.tag × L)) : Fin 5 → WordCurve TwistTag.D4.tag L :=
  ![d4FixedTorusCurve L, xOCurve, yOCurve,
    conjCurve xOCurve w (invWord w) (mul_wordUnit_invWord w),
    conjCurve yOCurve w (invWord w) (mul_wordUnit_invWord w)]

theorem iUnion_values_rotCurves {ζ : ModGL TwistTag.D4.tag L}
    (w : List (Letter TwistTag.D4.tag × L)) (hw : wordUnit TwistTag.D4.tag L w = ζ) :
    (⋃ i, (rotCurves w i).values) = rotGen ζ := by
  have hw' : wordUnit TwistTag.D4.tag L (invWord w) = ζ⁻¹ := by rw [wordUnit_invWord, hw]
  have h0 : (rotCurves w 0).values = (rotS L : Set (ModGL TwistTag.D4.tag L)) :=
    values_d4FixedTorusCurve
  have h1 : (rotCurves w 1).values = Set.range (xO (L := L)) := values_xOCurve
  have h2 : (rotCurves w 2).values = Set.range (yO (L := L)) := values_yOCurve
  have h3 : (rotCurves w 3).values = Set.range (fun c : L => ζ * xO c * ζ⁻¹) := by
    show (conjCurve xOCurve w (invWord w) (mul_wordUnit_invWord w)).values = _
    rw [values_conjCurve, values_xOCurve, hw, hw']
    ext g; simp
  have h4 : (rotCurves w 4).values = Set.range (fun c : L => ζ * yO c * ζ⁻¹) := by
    show (conjCurve yOCurve w (invWord w) (mul_wordUnit_invWord w)).values = _
    rw [values_conjCurve, values_yOCurve, hw, hw']
    ext g; simp
  ext g
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · change g ∈ (rotCurves w 0).values at hi; rw [h0] at hi; exact rotGen_S hi
    · change g ∈ (rotCurves w 1).values at hi; rw [h1] at hi; obtain ⟨c, rfl⟩ := hi; exact rotGen_x c
    · change g ∈ (rotCurves w 2).values at hi; rw [h2] at hi; obtain ⟨c, rfl⟩ := hi; exact rotGen_y c
    · change g ∈ (rotCurves w 3).values at hi; rw [h3] at hi; obtain ⟨c, rfl⟩ := hi; exact rotGen_xc c
    · change g ∈ (rotCurves w 4).values at hi; rw [h4] at hi; obtain ⟨c, rfl⟩ := hi; exact rotGen_yc c
  · intro hg
    rcases hg with (((hg | hg) | hg) | hg) | hg
    · exact ⟨0, by rw [h0]; exact hg⟩
    · exact ⟨1, by rw [h1]; exact hg⟩
    · exact ⟨2, by rw [h2]; exact hg⟩
    · exact ⟨3, by rw [h3]; exact hg⟩
    · exact ⟨4, by rw [h4]; exact hg⟩

theorem isPointIrreducible_rotR {ζ : ModGL TwistTag.D4.tag L}
    (hζ : ζ ∈ adjointGroup TwistTag.D4.tag L) :
    IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (rotR ζ : Set (ModGL TwistTag.D4.tag L))) := by
  obtain ⟨w, hw⟩ := exists_wordUnit_eq hζ
  have hw' : wordUnit TwistTag.D4.tag L (invWord w) = ζ⁻¹ := by rw [wordUnit_invWord, hw]
  have h0 : (rotCurves w 0).values = (rotS L : Set (ModGL TwistTag.D4.tag L)) :=
    values_d4FixedTorusCurve
  have h1 : (rotCurves w 1).values = Set.range (xO (L := L)) := values_xOCurve
  have h2 : (rotCurves w 2).values = Set.range (yO (L := L)) := values_yOCurve
  have h3 : (rotCurves w 3).values = Set.range (fun c : L => ζ * xO c * ζ⁻¹) := by
    show (conjCurve xOCurve w (invWord w) (mul_wordUnit_invWord w)).values = _
    rw [values_conjCurve, values_xOCurve, hw, hw']
    ext g; simp
  have h4 : (rotCurves w 4).values = Set.range (fun c : L => ζ * yO c * ζ⁻¹) := by
    show (conjCurve yOCurve w (invWord w) (mul_wordUnit_invWord w)).values = _
    rw [values_conjCurve, values_yOCurve, hw, hw']
    ext g; simp
  have hinv : ∀ i, ∀ g ∈ (rotCurves w i).values, g⁻¹ ∈ (rotCurves w i).values := by
    intro i
    fin_cases i
    · intro g hg; change g ∈ (rotCurves w 0).values at hg; change g⁻¹ ∈ (rotCurves w 0).values; rw [h0] at hg ⊢; exact inv_mem hg
    · intro g hg; change g ∈ (rotCurves w 1).values at hg; change g⁻¹ ∈ (rotCurves w 1).values; rw [h1] at hg ⊢; obtain ⟨c, rfl⟩ := hg; exact ⟨-c, (xO_inv c).symm⟩
    · intro g hg; change g ∈ (rotCurves w 2).values at hg; change g⁻¹ ∈ (rotCurves w 2).values; rw [h2] at hg ⊢; obtain ⟨c, rfl⟩ := hg; exact ⟨-c, (yO_inv c).symm⟩
    · intro g hg; change g ∈ (rotCurves w 3).values at hg; change g⁻¹ ∈ (rotCurves w 3).values; rw [h3] at hg ⊢; obtain ⟨c, rfl⟩ := hg
      refine ⟨-c, ?_⟩
      show ζ * xO (-c) * ζ⁻¹ = _
      rw [← xO_inv]; group
    · intro g hg; change g ∈ (rotCurves w 4).values at hg; change g⁻¹ ∈ (rotCurves w 4).values; rw [h4] at hg ⊢; obtain ⟨c, rfl⟩ := hg
      refine ⟨-c, ?_⟩
      show ζ * yO (-c) * ζ⁻¹ = _
      rw [← yO_inv]; group
  have := isPointIrreducible_closure_wordCurves (rotCurves w) hinv
  rwa [iUnion_values_rotCurves w hw] at this

end Curves


section Main

theorem rot_core {p : ℕ} [Fact p.Prime] [CharP L p] {f : ℕ} (hf : 1 ≤ f)
    (Q : ModGL TwistTag.D4.tag L) {F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {e : ℤ}
    (hF : RotFrame F e) (hFQ : ∀ g, F g = frobTwistGL TwistTag.D4.tag L p f Q g)
    {b : Lˣ} (hbe : b ^ e = b) {ζ : ModGL TwistTag.D4.tag L}
    (hζ : ζ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b))
    (hm : ζ ∈ monomialSubgroup TwistTag.D4.tag L)
    (hrot : (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = d4MatThreeA *ᵥ x) ∨
      (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = d4MatThreeB *ᵥ x)) :
    ∃ z ∈ graphCentralizer TwistTag.D4.tag L (rotElt b), z⁻¹ * F z = ζ := by
  obtain ⟨M, Mi, hMMi, hconj, hMP, hMw⟩ : ∃ M Mi : D4Mat, M * Mi = 1 ∧
      d4MatShort * (M * (d4MatShort * Mi)) = M ∧ M * d4PermMat = d4PermMat * M ∧
      ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = M *ᵥ x := by
    rcases hrot with h | h
    · exact ⟨_, _, d4MatThree_mul, d4_rot_conj_A, d4_rotA_perm, h⟩
    · exact ⟨_, _, d4MatThree_mul', d4_rot_conj_B, d4_rotB_perm, h⟩
  have hξ := hF.exists_frob_eq hbe hζ hm hMP hMw
  have hRζ : ζ ∈ rotR ζ := zeta_mem_rotR hζ hm hMMi hconj hMw
  have hadj : ζ ∈ adjointGroup TwistTag.D4.tag L := (Subgroup.mem_inf.1 hζ).1
  have hirr := isPointIrreducible_rotR hadj
  have hclosed := isPointClosed_graphCentralizer (τ := TwistTag.D4.tag) (k := L) (rotElt b)
  have hstab : ∀ g ∈ rotR ζ, frobTwistGL TwistTag.D4.tag L p f Q g ∈ rotR ζ := fun g hg => by
    rw [← hFQ]; exact rotR_stable hF hξ g hg
  obtain ⟨z, hz, hzc⟩ := exists_frobTwist_of_isPointIrreducible (p := p) hclosed (rotR_le b hζ)
    hirr hf Q hstab ζ hRζ
  exact ⟨z, hz, by rw [hFQ]; exact hzc⟩

theorem twistHom_eq_frobTwistGL {p : ℕ} [Fact p.Prime] [CharP L p] (f : ℕ)
    (g : ModGL TwistTag.D4.tag L) :
    twistHom TwistTag.D4 L (iterateFrobenius L p f) g =
      frobTwistGL TwistTag.D4.tag L p f (diagramMap TwistTag.D4 L) g := rfl

theorem twistHomOppHom_eq_frobTwistGL {p : ℕ} [Fact p.Prime] [CharP L p] (f : ℕ)
    (g : ModGL TwistTag.D4.tag L) :
    twistHomOppHom (iterateFrobenius L p f) g =
      frobTwistGL TwistTag.D4.tag L p f (trialityOpposition L * diagramMap TwistTag.D4 L) g := by
  rw [twistHomOppHom_apply, twistHomOpp, frobTwistGL_apply]
  have : twistHom TwistTag.D4 L (iterateFrobenius L p f) g =
      diagramMap TwistTag.D4 L * entrywiseFrobGL TwistTag.D4.tag L p f g *
        (diagramMap TwistTag.D4 L)⁻¹ := rfl
  rw [this]
  group

theorem rotLang_holds : RotLang := by
  intro p f _ hp5 hf L _ _ _ b hb3 hb1 ζ hζ _ hrot
  obtain ⟨hm, hrot⟩ := hrot
  have hq : 2 ≤ p ^ f := by
    have h1 : 5 ≤ p ^ f := le_trans hp5 (Nat.le_self_pow (by omega) p)
    omega
  refine ⟨fun hmod => ?_, fun hmod => ?_⟩
  · have he : (((p ^ f : ℕ) : ℤ)) % 3 = 1 := by
      generalize p ^ f = q at hmod ⊢
      omega
    obtain ⟨z, hz, hzc⟩ := rot_core hf (diagramMap TwistTag.D4 L) (rotFrame_one f hq)
      (fun g => twistHom_eq_frobTwistGL f g) (zpow_eq_self_of_emod_three hb3 he) hζ hm hrot
    exact ⟨z, hz, hzc⟩
  · have he : (-(((p ^ f : ℕ) : ℤ))) % 3 = 1 := by
      generalize p ^ f = q at hmod ⊢
      omega
    obtain ⟨z, hz, hzc⟩ := rot_core hf (trialityOpposition L * diagramMap TwistTag.D4 L)
      (rotFrame_two f hq) (fun g => twistHomOppHom_eq_frobTwistGL f g)
      (zpow_eq_self_of_emod_three hb3 he) hζ hm hrot
    refine ⟨z, hz, ?_⟩
    rw [← twistHomOppHom_apply]
    exact hzc

end Main

end CFSG.HardMathSupport.Lang.E6Descent
