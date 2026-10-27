module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7FrameTorus

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TableBExcTwo CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification


section Prod

variable (L : Type) [Field L]

theorem range_rootSL2_frame (i : Fin 7) :
    (rootSL2 Tag.E7 L (frameE7Root i)).range =
      (rootPairE7 L (frameE7Root i)).map (adjointGroup Tag.E7 L).subtype := by
  have h1 := map_subtype_rootGroup (K := L) (rootOperatorFamily Tag.E7) (e7Frame_isRoot i)
  have h2 := map_subtype_rootGroup (K := L) (rootOperatorFamily Tag.E7)
    (IsRoot.neg (e7Frame_isRoot i))
  rw [range_rootSL2_of_isRoot (e7Frame_isRoot i), ← h1, ← h2, ← Subgroup.map_sup]

theorem frame_rootSL2_commute (i j : Fin 7) (hij : i ≠ j) (A B : SL2 L) :
    Commute (rootSL2 Tag.E7 L (frameE7Root i) A) (rootSL2 Tag.E7 L (frameE7Root j) B) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := e7Frame_facts i j hij
  have hc := commutes_rootPair_of_noG2 (K := L) (fun _ => Or.inl (by simp [Tag.symmetrizer]))
    (e7Frame_isRoot i) (e7Frame_isRoot j) h1 h2 h3 h4 h5
  obtain ⟨x, hx, hxA⟩ : rootSL2 Tag.E7 L (frameE7Root i) A ∈
      (rootPairE7 L (frameE7Root i)).map (adjointGroup Tag.E7 L).subtype := by
    rw [← range_rootSL2_frame]
    exact ⟨A, rfl⟩
  obtain ⟨y, hy, hyB⟩ : rootSL2 Tag.E7 L (frameE7Root j) B ∈
      (rootPairE7 L (frameE7Root j)).map (adjointGroup Tag.E7 L).subtype := by
    rw [← range_rootSL2_frame]
    exact ⟨B, rfl⟩
  rw [← hxA, ← hyB]
  exact congrArg Subtype.val (hc x hx y hy)

theorem frame_rootSL2_pairwise : Pairwise fun i j : Fin 7 => ∀ (x y : SL2 L),
    Commute (rootSL2 Tag.E7 L (frameE7Root i) x) (rootSL2 Tag.E7 L (frameE7Root j) y) :=
  fun _ _ hij x y => frame_rootSL2_commute L _ _ hij x y

@[expose] def frameProd : (Fin 7 → SL2 L) →* ModGL Tag.E7 L :=
  MonoidHom.noncommPiCoprod (fun i => rootSL2 Tag.E7 L (frameE7Root i))
    (frame_rootSL2_pairwise L)

theorem frameProd_mulSingle (i : Fin 7) (A : SL2 L) :
    frameProd L (Pi.mulSingle i A) = rootSL2 Tag.E7 L (frameE7Root i) A := by
  unfold frameProd
  rw [MonoidHom.noncommPiCoprod_mulSingle]

theorem frameProd_range : (frameProd L).range = frameSpan L :=
  MonoidHom.noncommPiCoprod_range _

theorem frameProd_ker_center {k : Fin 7 → SL2 L} (hk : frameProd L k = 1) (i : Fin 7) :
    k i ∈ Subgroup.center (SL2 L) := by
  classical
  rw [Subgroup.mem_center_iff]
  intro A
  have hc : frameProd L (Pi.mulSingle i A * k * (Pi.mulSingle i A)⁻¹ * k⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk, inv_one, mul_one, mul_one,
      mul_inv_cancel]
  have hc' : Pi.mulSingle i A * k * (Pi.mulSingle i A)⁻¹ * k⁻¹ =
      Pi.mulSingle i (A * k i * A⁻¹ * (k i)⁻¹) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [hc', frameProd_mulSingle] at hc
  have h1 : A * k i * A⁻¹ * (k i)⁻¹ = 1 :=
    rootSL2_injective_of_field (frameE7Root i) (hc.trans (map_one _).symm)
  have h2 : A * k i * A⁻¹ = k i := mul_inv_eq_one.1 h1
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem sq_eq_one_of_mem_center_SL2 {z : SL2 L} (hz : z ∈ Subgroup.center (SL2 L)) :
    z ^ 2 = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem frameProd_ker_sq {k : Fin 7 → SL2 L} (hk : frameProd L k = 1) :
    (∀ x : Fin 7 → SL2 L, Commute k x) ∧ k ^ 2 = 1 := by
  refine ⟨fun x => funext fun i => ?_, funext fun i => ?_⟩
  · exact ((Subgroup.mem_center_iff.1 (frameProd_ker_center L hk i)) (x i)).symm
  · exact sq_eq_one_of_mem_center_SL2 L (frameProd_ker_center L hk i)

theorem map_frameProd {L' : Type} [Field L'] (f : ModGL Tag.E7 L →* ModGL Tag.E7 L')
    (g : SL2 L →* SL2 L')
    (hfg : ∀ i A, f (rootSL2 Tag.E7 L (frameE7Root i) A) = rootSL2 Tag.E7 L' (frameE7Root i) (g A))
    (x : Fin 7 → SL2 L) : f (frameProd L x) = frameProd L' (fun i => g (x i)) := by
  rw [frameProd, frameProd, MonoidHom.noncommPiCoprod_apply, MonoidHom.noncommPiCoprod_apply,
    Finset.map_noncommProd]
  exact Finset.noncommProd_congr rfl (fun i _ => hfg i (x i)) _

end Prod

section Descent

theorem exists_SL2_of_entries {K L : Type} [Field K] [Field L] (ι : K →+* L) (A : SL2 L)
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

theorem mem_e7FrameGroup_of_frameProd {K : Type} [Field K] {y : adjointGroup Tag.E7 K}
    {u : Fin 7 → SL2 K} (hu : frameProd K u = (y : ModGL Tag.E7 K)) : y ∈ e7FrameGroup K := by
  have hmem : (y : ModGL Tag.E7 K) ∈ (e7FrameGroup K).map (adjointGroup Tag.E7 K).subtype := by
    rw [e7FrameGroup, Subgroup.map_iSup, ← hu]
    have h : frameProd K u ∈ (frameProd K).range := ⟨u, rfl⟩
    rw [frameProd_range, frameSpan] at h
    simpa only [range_rootSL2_frame] using h
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hmem
  rwa [Subtype.ext hzy] at hz

theorem mem_e7FrameGroup_of_frameSpan {K L : Type} [Field K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFrK : ∀ c : K, Fr (algebraMap K L c) = algebraMap K L c)
    (hfix : ∀ c : L, Fr c = c → c ∈ Set.range (algebraMap K L))
    {y : adjointGroup Tag.E7 K} (hy8 : y ^ 8 = y)
    (hy : baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K) ∈ frameSpan L) :
    y ∈ e7FrameGroup K := by
  have hFY : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K)) =
      baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K) := by
    have e : Fr.comp (algebraMap K L) = algebraMap K L := RingHom.ext fun b => hFrK b
    rw [units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, e]
  rw [← frameProd_range] at hy
  obtain ⟨x, hx⟩ := hy
  have hFx : Units.map (entrywiseHom Fr) (frameProd L x) =
      frameProd L (fun i => Matrix.SpecialLinearGroup.map Fr (x i)) :=
    map_frameProd L (Units.map (entrywiseHom Fr)) (Matrix.SpecialLinearGroup.map Fr)
      (fun i A => entrywise_rootSL2_of_field Fr (frameE7Root i) A) x
  let FrP : (Fin 7 → SL2 L) →* (Fin 7 → SL2 L) :=
    (Matrix.SpecialLinearGroup.map Fr).compLeft (Fin 7)
  have hFrP : ∀ z, FrP z = fun i => Matrix.SpecialLinearGroup.map Fr (z i) := fun _ => rfl
  have hk : frameProd L (x⁻¹ * FrP x) = 1 := by
    rw [map_mul, map_inv, hFrP, ← hFx, hx, hFY, inv_mul_cancel]
  obtain ⟨hkc, hk2⟩ := frameProd_ker_sq L hk
  have hFrx : FrP x = x * (x⁻¹ * FrP x) := by rw [mul_inv_cancel_left]
  have hk8 : (x⁻¹ * FrP x) ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hk2, one_pow]
  have hx8 : FrP (x ^ 8) = x ^ 8 := by
    rw [map_pow, hFrx, (hkc x).symm.mul_pow, hk8, mul_one]
  have hrat : ∀ i, ∃ B : SL2 K,
      Matrix.SpecialLinearGroup.map (algebraMap K L) B = (x ^ 8) i := by
    intro i
    refine exists_SL2_of_entries (algebraMap K L) _ fun a b => hfix _ ?_
    have h := congrArg
      (fun z : Fin 7 → SL2 L => ((z i : SL2 L) : Matrix (Fin 2) (Fin 2) L) a b) hx8
    exact h
  choose u hu using hrat
  have h1 : frameProd L (x ^ 8) = baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K) := by
    rw [map_pow, hx, ← map_pow, ← Subgroup.coe_pow, hy8]
  have hYeq : baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K) =
      baseChangeGL (algebraMap K L) (frameProd K u) := by
    rw [← h1, map_frameProd K (baseChangeGL (algebraMap K L))
      (Matrix.SpecialLinearGroup.map (algebraMap K L))
      (fun i A => baseChangeGL_rootSL2_of_field (algebraMap K L) (frameE7Root i) A) u]
    exact congrArg (frameProd L) (funext fun i => (hu i).symm)
  have hyu : frameProd K u = (y : ModGL Tag.E7 K) :=
    baseChangeGL_injective (algebraMap K L) hYeq.symm
  exact mem_e7FrameGroup_of_frameProd hyu

end Descent

end CFSG.LieType.SeitzGeneration.ExcHigh
