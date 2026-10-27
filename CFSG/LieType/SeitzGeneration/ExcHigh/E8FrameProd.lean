module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameTorus

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TableBExcTwo CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification CFSG.HardMathSupport.Lang.AnisoE8


section Prod

variable (L : Type) [Field L]

theorem range_rootSL2_frame8 (i : Fin 8) :
    (rootSL2 Tag.E8 L (frameE8Root i)).range =
      (rootPairE8 L (frameE8Root i)).map (adjointGroup Tag.E8 L).subtype := by
  have h1 := map_subtype_rootGroup (K := L) (rootOperatorFamily Tag.E8) (e8Frame_isRoot i)
  have h2 := map_subtype_rootGroup (K := L) (rootOperatorFamily Tag.E8)
    (IsRoot.neg (e8Frame_isRoot i))
  rw [range_rootSL2_of_isRoot (e8Frame_isRoot i), ← h1, ← h2, ← Subgroup.map_sup]

theorem frame_rootSL2_commute8 (i j : Fin 8) (hij : i ≠ j) (A B : SL2 L) :
    Commute (rootSL2 Tag.E8 L (frameE8Root i) A) (rootSL2 Tag.E8 L (frameE8Root j) B) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := e8Frame_facts i j hij
  have hc := commutes_rootPair_of_noG2 (K := L) (fun _ => Or.inl (by simp [Tag.symmetrizer]))
    (e8Frame_isRoot i) (e8Frame_isRoot j) h1 h2 h3 h4 h5
  obtain ⟨x, hx, hxA⟩ : rootSL2 Tag.E8 L (frameE8Root i) A ∈
      (rootPairE8 L (frameE8Root i)).map (adjointGroup Tag.E8 L).subtype := by
    rw [← range_rootSL2_frame8]
    exact ⟨A, rfl⟩
  obtain ⟨y, hy, hyB⟩ : rootSL2 Tag.E8 L (frameE8Root j) B ∈
      (rootPairE8 L (frameE8Root j)).map (adjointGroup Tag.E8 L).subtype := by
    rw [← range_rootSL2_frame8]
    exact ⟨B, rfl⟩
  rw [← hxA, ← hyB]
  exact congrArg Subtype.val (hc x hx y hy)

theorem frame_rootSL2_pairwise8 : Pairwise fun i j : Fin 8 => ∀ (x y : SL2 L),
    Commute (rootSL2 Tag.E8 L (frameE8Root i) x) (rootSL2 Tag.E8 L (frameE8Root j) y) :=
  fun _ _ hij x y => frame_rootSL2_commute8 L _ _ hij x y

@[expose] def frameProd8 : (Fin 8 → SL2 L) →* ModGL Tag.E8 L :=
  MonoidHom.noncommPiCoprod (fun i => rootSL2 Tag.E8 L (frameE8Root i))
    (frame_rootSL2_pairwise8 L)

theorem frameProd8_mulSingle (i : Fin 8) (A : SL2 L) :
    frameProd8 L (Pi.mulSingle i A) = rootSL2 Tag.E8 L (frameE8Root i) A := by
  unfold frameProd8
  rw [MonoidHom.noncommPiCoprod_mulSingle]

theorem frameProd8_range : (frameProd8 L).range = frameSpan8 L :=
  MonoidHom.noncommPiCoprod_range _

theorem frameProd8_ker_center {k : Fin 8 → SL2 L} (hk : frameProd8 L k = 1) (i : Fin 8) :
    k i ∈ Subgroup.center (SL2 L) := by
  classical
  rw [Subgroup.mem_center_iff]
  intro A
  have hc : frameProd8 L (Pi.mulSingle i A * k * (Pi.mulSingle i A)⁻¹ * k⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk, inv_one, mul_one, mul_one,
      mul_inv_cancel]
  have hc' : Pi.mulSingle i A * k * (Pi.mulSingle i A)⁻¹ * k⁻¹ =
      Pi.mulSingle i (A * k i * A⁻¹ * (k i)⁻¹) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [hc', frameProd8_mulSingle] at hc
  have h1 : A * k i * A⁻¹ * (k i)⁻¹ = 1 :=
    rootSL2_injective_of_field (frameE8Root i) (hc.trans (map_one _).symm)
  have h2 : A * k i * A⁻¹ = k i := mul_inv_eq_one.1 h1
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem sq_eq_one_of_mem_center_SL2_E8 {z : SL2 L} (hz : z ∈ Subgroup.center (SL2 L)) :
    z ^ 2 = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem frameProd8_ker_sq {k : Fin 8 → SL2 L} (hk : frameProd8 L k = 1) :
    (∀ x : Fin 8 → SL2 L, Commute k x) ∧ k ^ 2 = 1 := by
  refine ⟨fun x => funext fun i => ?_, funext fun i => ?_⟩
  · exact ((Subgroup.mem_center_iff.1 (frameProd8_ker_center L hk i)) (x i)).symm
  · exact sq_eq_one_of_mem_center_SL2_E8 L (frameProd8_ker_center L hk i)

theorem map_frameProd8 {L' : Type} [Field L'] (f : ModGL Tag.E8 L →* ModGL Tag.E8 L')
    (g : SL2 L →* SL2 L')
    (hfg : ∀ i A, f (rootSL2 Tag.E8 L (frameE8Root i) A) = rootSL2 Tag.E8 L' (frameE8Root i) (g A))
    (x : Fin 8 → SL2 L) : f (frameProd8 L x) = frameProd8 L' (fun i => g (x i)) := by
  rw [frameProd8, frameProd8, MonoidHom.noncommPiCoprod_apply, MonoidHom.noncommPiCoprod_apply,
    Finset.map_noncommProd]
  exact Finset.noncommProd_congr rfl (fun i _ => hfg i (x i)) _

end Prod

section Descent

theorem exists_SL2_of_entries8 {K L : Type} [Field K] [Field L] (ι : K →+* L) (A : SL2 L)
    (h : ∀ a b, A a b ∈ Set.range ι) :
    ∃ B : SL2 K, Matrix.SpecialLinearGroup.map ι B = A := by
  choose M hM using h
  have hdet : (Matrix.of M).det = 1 := by
    apply ι.injective
    rw [RingHom.map_det, map_one]
    have : ι.mapMatrix (Matrix.of M) = (A : Matrix (Fin 2) (Fin 2) L) := by
      ext a b
      exact hM a b
    rw [this, A.2]
  exact ⟨⟨Matrix.of M, hdet⟩, Subtype.ext (by ext a b; exact hM a b)⟩

theorem mem_e8FrameGroup_of_frameProd {K : Type} [Field K] {y : adjointGroup Tag.E8 K}
    {u : Fin 8 → SL2 K} (hu : frameProd8 K u = (y : ModGL Tag.E8 K)) : y ∈ e8FrameGroup K := by
  have hmem : (y : ModGL Tag.E8 K) ∈ (e8FrameGroup K).map (adjointGroup Tag.E8 K).subtype := by
    rw [e8FrameGroup, Subgroup.map_iSup, ← hu]
    have h : frameProd8 K u ∈ (frameProd8 K).range := ⟨u, rfl⟩
    rw [frameProd8_range, frameSpan8] at h
    simpa only [range_rootSL2_frame8] using h
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hmem
  rwa [Subtype.ext hzy] at hz

theorem mem_e8FrameGroup_of_frameSpan {K L : Type} [Field K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFrK : ∀ c : K, Fr (algebraMap K L c) = algebraMap K L c)
    (hfix : ∀ c : L, Fr c = c → c ∈ Set.range (algebraMap K L))
    {y : adjointGroup Tag.E8 K} (hy6 : y ^ 6 = y)
    (hy : baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K) ∈ frameSpan8 L) :
    y ∈ e8FrameGroup K := by
  have hFY : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K)) =
      baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K) := by
    have e : Fr.comp (algebraMap K L) = algebraMap K L := RingHom.ext fun b => hFrK b
    rw [units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, e]
  rw [← frameProd8_range] at hy
  obtain ⟨x, hx⟩ := hy
  have hFx : Units.map (entrywiseHom Fr) (frameProd8 L x) =
      frameProd8 L (fun i => Matrix.SpecialLinearGroup.map Fr (x i)) :=
    map_frameProd8 L (Units.map (entrywiseHom Fr)) (Matrix.SpecialLinearGroup.map Fr)
      (fun i A => entrywise_rootSL2_of_field Fr (frameE8Root i) A) x
  let FrP : (Fin 8 → SL2 L) →* (Fin 8 → SL2 L) :=
    (Matrix.SpecialLinearGroup.map Fr).compLeft (Fin 8)
  have hFrP : ∀ z, FrP z = fun i => Matrix.SpecialLinearGroup.map Fr (z i) := fun _ => rfl
  have hk : frameProd8 L (x⁻¹ * FrP x) = 1 := by
    rw [map_mul, map_inv, hFrP, ← hFx, hx, hFY, inv_mul_cancel]
  obtain ⟨hkc, hk2⟩ := frameProd8_ker_sq L hk
  have hFrx : FrP x = x * (x⁻¹ * FrP x) := by rw [mul_inv_cancel_left]
  have hk6 : (x⁻¹ * FrP x) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hk2, one_pow]
  have hx6 : FrP (x ^ 6) = x ^ 6 := by
    rw [map_pow, hFrx, (hkc x).symm.mul_pow, hk6, mul_one]
  have hrat : ∀ i, ∃ B : SL2 K,
      Matrix.SpecialLinearGroup.map (algebraMap K L) B = (x ^ 6) i := by
    intro i
    refine exists_SL2_of_entries8 (algebraMap K L) _ fun a b => hfix _ ?_
    have h := congrArg
      (fun z : Fin 8 → SL2 L => ((z i : SL2 L) : Matrix (Fin 2) (Fin 2) L) a b) hx6
    exact h
  choose u hu using hrat
  have h1 : frameProd8 L (x ^ 6) = baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K) := by
    rw [map_pow, hx, ← map_pow, ← Subgroup.coe_pow, hy6]
  have hYeq : baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K) =
      baseChangeGL (algebraMap K L) (frameProd8 K u) := by
    rw [← h1, map_frameProd8 K (baseChangeGL (algebraMap K L))
      (Matrix.SpecialLinearGroup.map (algebraMap K L))
      (fun i A => baseChangeGL_rootSL2_of_field (algebraMap K L) (frameE8Root i) A) u]
    exact congrArg (frameProd8 L) (funext fun i => (hu i).symm)
  have hyu : frameProd8 K u = (y : ModGL Tag.E8 K) :=
    baseChangeGL_injective (algebraMap K L) hYeq.symm
  exact mem_e8FrameGroup_of_frameProd hyu

end Descent

end CFSG.LieType.SeitzGeneration.ExcHigh
