module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.PurityLang

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

section Datum

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Chevalley CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


theorem datum_PTR {K : Type} [Field K] [Finite K] {E₀ : Subgroup (adjointGroup Tag.F4 K)}
    (D : LangPlaneData Tag.F4 K E₀) (hreg : ∀ α : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α → ¬ D.Kills α) :
    ∃ P : ModGL Tag.F4 (AlgebraicClosure K), P ∈ adjointGroup Tag.F4 (AlgebraicClosure K) ∧
      (∀ x ∈ E₀, ∃ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ, rootDiagUnit Tag.F4 a =
        P⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) * P) ∧
      (∀ α : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α → ∃ x ∈ E₀,
        ∀ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
          rootDiagUnit Tag.F4 a = P⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL Tag.F4 K) * P → rootChar a α ≠ 1) := by
  set L := AlgebraicClosure K with hL
  set P : ModGL Tag.F4 L := (baseChangeGL (algebraMap K L) (D.c : ModGL Tag.F4 K))⁻¹ * D.g0 with hPdef
  have hP : P ∈ adjointGroup Tag.F4 L :=
    mul_mem (inv_mem (CFSG.HardMathSupport.Lang.AnisoE6.baseChangeGL_mem_adjointGroup_of_mem
      (algebraMap K L) D.c.2)) D.hg0C
  have key : ∀ x : adjointGroup Tag.F4 K, P⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.F4 K) * P =
      D.g0⁻¹ * baseChangeGL (algebraMap K L)
        ((D.c * x * D.c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * D.g0 := by
    intro x
    simp only [hPdef, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    group
  refine ⟨P, hP, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.1 (D.hc x hx)
    have htor : t ∈ torusGroup Tag.F4 L := ((mem_twistedTorusOf).1 ht).1
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htor
    refine ⟨a, ?_⟩
    rw [key x, ← ha, ← hteq]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro α hα
    by_contra hcon
    push_neg at hcon
    apply hreg α hα
    intro x hx
    obtain ⟨a, ha, hca⟩ := hcon x hx
    exact ⟨a, by rw [← key x]; exact ha, hca⟩

theorem transport_PTR {K L Ω : Type} [Field K] [Finite K] [Field L] [Field Ω] [Algebra K L]
    [Algebra K Ω] (ι : L →+* Ω) (hι : ∀ c : K, ι (algebraMap K L c) = algebraMap K Ω c)
    {E₀ : Subgroup (adjointGroup Tag.F4 K)} (P : ModGL Tag.F4 L) (hP : P ∈ adjointGroup Tag.F4 L)
    (hT : ∀ x ∈ E₀, ∃ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit Tag.F4 a =
      P⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.F4 K) * P)
    (hR : ∀ α : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α → ∃ x ∈ E₀, ∀ a : Fin Tag.F4.rank → Lˣ,
      rootDiagUnit Tag.F4 a = P⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.F4 K) * P →
        rootChar a α ≠ 1) :
    baseChangeGL ι P ∈ adjointGroup Tag.F4 Ω ∧
    (∀ x ∈ E₀, ∃ a : Fin Tag.F4.rank → Ωˣ, rootDiagUnit Tag.F4 a =
      (baseChangeGL ι P)⁻¹ * baseChangeGL (algebraMap K Ω) (x : ModGL Tag.F4 K) *
        baseChangeGL ι P) ∧
    (∀ α : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α → ∃ x ∈ E₀, ∀ a : Fin Tag.F4.rank → Ωˣ,
      rootDiagUnit Tag.F4 a = (baseChangeGL ι P)⁻¹ * baseChangeGL (algebraMap K Ω)
        (x : ModGL Tag.F4 K) * baseChangeGL ι P → rootChar a α ≠ 1) := by
  have hcomp : ∀ y : ModGL Tag.F4 K, baseChangeGL ι (baseChangeGL (algebraMap K L) y) =
      baseChangeGL (algebraMap K Ω) y := fun y => by
    rw [baseChangeGL_baseChangeGL, show ι.comp (algebraMap K L) = algebraMap K Ω from RingHom.ext hι]
  have hdiag : ∀ (x : adjointGroup Tag.F4 K) (a : Fin Tag.F4.rank → Lˣ),
      rootDiagUnit Tag.F4 a = P⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.F4 K) * P →
      rootDiagUnit Tag.F4 (fun i => Units.map ι.toMonoidHom (a i)) =
        (baseChangeGL ι P)⁻¹ * baseChangeGL (algebraMap K Ω) (x : ModGL Tag.F4 K) *
          baseChangeGL ι P := by
    intro x a ha
    rw [← baseChangeGL_rootDiagUnit ι a, ha, map_mul, map_mul, map_inv, hcomp]
  have hchar : ∀ (a : Fin Tag.F4.rank → Lˣ) (α : Fin Tag.F4.rank → ℤ),
      rootChar (fun i => Units.map ι.toMonoidHom (a i)) α =
        Units.map ι.toMonoidHom (rootChar a α) := by
    intro a α
    unfold rootChar
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow]
  refine ⟨CFSG.HardMathSupport.Lang.AnisoE6.baseChangeGL_mem_adjointGroup_of_mem ι hP, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha⟩ := hT x hx
    exact ⟨fun i => Units.map ι.toMonoidHom (a i), hdiag x a ha⟩
  · intro α hα
    obtain ⟨x, hxE, hxa⟩ := hR α hα
    refine ⟨x, hxE, fun a' ha' => ?_⟩
    obtain ⟨a0, ha0⟩ := hT x hxE
    have heq : a' = fun i => Units.map ι.toMonoidHom (a0 i) :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective (ha'.trans (hdiag x a0 ha0).symm)
    intro h1
    apply hxa a0 ha0
    rw [heq, hchar] at h1
    apply Units.ext
    apply ι.injective
    have h3 := congrArg Units.val h1
    simpa using h3

theorem card_eq_ringChar_pow (K : Type) [Field K] [Finite K] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = ringChar K ^ f ∧ (ringChar K).Prime := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  refine ⟨n, n.pos, ?_, hp⟩
  rw [Nat.card_eq_fintype_card, hcard]

theorem ringChar_ne_three (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hq : Nat.card K = ringChar K ^ f) (h3 : ¬ 3 ∣ Nat.card K) : ringChar K ≠ 3 := by
  intro h
  apply h3
  rw [hq, h]
  exact dvd_pow_self 3 (by omega)

theorem f4PureSplit_holds : F4PureSplit := by
  intro K _ _ hK ω hω E₀ hexp hcard D hreg e he he1
  obtain ⟨f, hf1, hq, hp⟩ := card_eq_ringChar_pow K
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  have hp3 : ringChar K ≠ 3 := ringChar_ne_three K hf1 hq (by omega)
  obtain ⟨P, hP, hT, hR⟩ := datum_PTR D hreg
  have hω' : orderOf (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ω) = 3 := by
    rw [orderOf_injective _ (Units.map_injective (algebraMap K (AlgebraicClosure K)).injective) ω]
    exact hω
  have hz : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((zSplit K ω : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
      1 * rootDiagUnit Tag.F4 (Pi.mulSingle 1 (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ω)) * 1⁻¹ := by
    rw [inv_one, mul_one, one_mul]
    show baseChangeGL _ (rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω)) = _
    rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    by_cases hi : i = 1
    · subst hi
      simp
    · simp [Pi.mulSingle_eq_of_ne hi]
  obtain ⟨g, hg⟩ := lang_core_three hp3 hf1 hq _ hω' 1 1 (one_mem _) (one_mem _) (s := 1)
    (by norm_num) (by rw [map_one, mul_one]) (by simp) (zSplit K ω) hz E₀ hcard hexp P hP hT hR
    e he he1
  exact ⟨g, hg⟩

theorem f4PureTwisted_holds : F4PureTwisted := by
  intro K _ _ hK3q hK3 D₁ ω hω z hz E₀ hexp hcard D hreg e he he1
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  obtain ⟨f, hf1, hq, hp⟩ := card_eq_ringChar_pow K
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  have hp3 : ringChar K ≠ 3 := ringChar_ne_three K hf1 hq hnd
  haveI : IsAlgClosed D₁.L := IsAlgClosure.isAlgClosed K
  haveI : CharP D₁.L (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K D₁.L).injective (ringChar K)
  obtain ⟨P, hP, hT, hR⟩ := datum_PTR D hreg
  let ι : AlgebraicClosure K →ₐ[K] D₁.L := IsAlgClosed.lift (M := D₁.L)
  have hι : ∀ c : K, ι.toRingHom (algebraMap K (AlgebraicClosure K) c) = algebraMap K D₁.L c :=
    fun c => ι.commutes c
  obtain ⟨hPΩ, hTΩ, hRΩ⟩ := transport_PTR ι.toRingHom hι P hP hT hR
  have hFr_eq : iterateFrobenius D₁.L (ringChar K) f = D₁.Fr :=
    RingHom.ext fun x => by rw [iterateFrobenius_def, D₁.hFr, hq]
  have hFDz : entrywiseFrobGL TwClass.f4Six.tag D₁.L (ringChar K) f D₁.g =
      D₁.g * canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w := by
    show Units.map (entrywiseHom (iterateFrobenius D₁.L (ringChar K) f)) D₁.g = _
    rw [hFr_eq, D₁.lang]
  have hDz : D₁.g ∈ adjointGroup TwClass.f4Six.tag D₁.L :=
    parabolicLevi_le_adjointGroup (K := D₁.L) (τ := TwClass.f4Six.tag) _ D₁.g_mem
  have hQ : canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w ∈ adjointGroup TwClass.f4Six.tag D₁.L :=
    canonicalRep_mem_adjointGroup (τ := TwClass.f4Six.tag) (coxeterSystem TwClass.f4Six.tag) D₁.L _
  have hQd : canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w *
      rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) *
      (canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w)⁻¹ =
      rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) ^ 2 := by
    have hconj := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit
      (K := D₁.L) TwClass.f4Six.w (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω)
    rw [weylAct_twice_threeA ω hω] at hconj
    refine hconj.trans ?_
    exact map_pow (rootDiagUnitHom TwClass.f4Six.tag D₁.L) _ 2
  obtain ⟨g, hg⟩ := lang_core_three hp3 hf1 hq ω hω D₁.g
    (canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w) hDz hQ (s := 2) (by decide) hFDz hQd
    z hz E₀ hcard hexp (baseChangeGL ι.toRingHom P) hPΩ hTΩ hRΩ e he he1
  exact ⟨g, hg⟩

end Datum

end CFSG.LieType.SeitzGeneration.ExcHighThree
