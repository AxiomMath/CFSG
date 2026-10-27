module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieConj

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

section Frame

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint


local notation "θ₀" => CFSG.LieType.Chevalley.e6HighestRoot

theorem exists_lang_twisted_familyGroup {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    (p f : ℕ) [Fact p.Prime] [CharP L p] (hf : 1 ≤ f) (a : ι → Fin TwistTag.E6.tag.rank → Lˣ)
    (himg : (fun α => permLattice TwistTag.E6.perm α) '' familyKernel (τ := TwistTag.E6.tag) a =
      familyKernel a)
    {j : ModGL TwistTag.E6.tag L}
    (hj : j ∈ Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL TwistTag.E6.tag L)))
    {c : ModGL TwistTag.E6.tag L} (hc : c ∈ familyGroup (K := L) a) :
    ∃ z ∈ familyGroup (K := L) a,
      z⁻¹ * (j * twistHom TwistTag.E6 L (iterateFrobenius L p f) z * j⁻¹) = c := by
  have hFstab : ∀ g ∈ familyGroup (K := L) a,
      twistHom TwistTag.E6 L (iterateFrobenius L p f) g ∈ familyGroup (K := L) a :=
    fun g hg => twistHom_mem_familyGroup p f a himg hg
  have hst : ∀ g ∈ familyGroup (K := L) a, frobTwistGL TwistTag.E6.tag L p f
      (j * diagramMap TwistTag.E6 L) g ∈ familyGroup (K := L) a := by
    intro g hg
    have e : frobTwistGL TwistTag.E6.tag L p f (j * diagramMap TwistTag.E6 L) g =
        j * twistHom TwistTag.E6 L (iterateFrobenius L p f) g * j⁻¹ := by
      rw [frobTwistGL_apply, CFSG.LieType.Chevalley.twistHom_apply]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hj _).1 (hFstab g hg)
  obtain ⟨z, hz, hzc⟩ := lang_familyGroup_of_mapsTo p a f hf (j * diagramMap TwistTag.E6 L) hst c hc
  refine ⟨z, hz, ?_⟩
  have e : (j * diagramMap TwistTag.E6 L) * entrywiseFrobGL TwistTag.E6.tag L p f z *
      (j * diagramMap TwistTag.E6 L)⁻¹ =
      j * twistHom TwistTag.E6 L (iterateFrobenius L p f) z * j⁻¹ := by
    rw [CFSG.LieType.Chevalley.twistHom_apply]
    group
  rw [e] at hzc
  exact hzc

theorem permLattice_add_E6 (x y : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (x + y) =
      permLattice TwistTag.E6.perm x + permLattice TwistTag.E6.perm y := rfl

theorem rootReflection_smul_E6 {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (x : Fin TwistTag.E6.tag.rank → ℤ) : rootReflection β • x = x - iform β x • β := by
  rw [rootReflection_smul hβ, corootPair,
    CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two (τ := TwistTag.E6.tag)
      (Or.inr (Or.inl rfl)) hβ,
    Int.mul_ediv_cancel_left _ two_ne_zero]

theorem iform_eq_neg_one_of_isRoot_add {β₁ β₂ : Fin TwistTag.E6.tag.rank → ℤ}
    (h₁ : IsRoot TwistTag.E6.tag β₁) (h₂ : IsRoot TwistTag.E6.tag β₂)
    (h₁₂ : IsRoot TwistTag.E6.tag (β₁ + β₂)) : iform β₁ β₂ = -1 := by
  have hsl : TwistTag.E6.tag = Tag.D4 ∨ TwistTag.E6.tag = Tag.E6 ∨ TwistTag.E6.tag = Tag.E7 ∨
      TwistTag.E6.tag = Tag.E8 := Or.inr (Or.inl rfl)
  have e := CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two hsl h₁₂
  rw [iform_add_left, iform_add_right, iform_add_right,
    CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two hsl h₁,
    CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two hsl h₂, iform_comm β₂ β₁] at e
  omega

theorem iform_theta_delta {w : WeylGroup TwistTag.E6.tag} {β₁ β₂ : Fin TwistTag.E6.tag.rank → ℤ}
    (h₁ : IsRoot TwistTag.E6.tag β₁) (h₂ : IsRoot TwistTag.E6.tag β₂)
    (h₁₂ : IsRoot TwistTag.E6.tag (β₁ + β₂)) (hw : w • θ₀ = β₁ + β₂) :
    iform θ₀ (w⁻¹ • β₁) = 1 ∧ iform θ₀ (w⁻¹ • β₂) = 1 ∧ w⁻¹ • β₁ + w⁻¹ • β₂ = θ₀ := by
  have hθw : w⁻¹ • (β₁ + β₂) = θ₀ := by rw [← hw, inv_smul_smul]
  refine ⟨?_, ?_, by rw [← smul_add, hθw]⟩
  · rw [← hθw, iform_smul, iform_add_left, iform_comm β₂ β₁,
      iform_eq_neg_one_of_isRoot_add h₁ h₂ h₁₂,
      CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two (τ := TwistTag.E6.tag)
        (Or.inr (Or.inl rfl)) h₁]
    norm_num
  · rw [← hθw, iform_smul, iform_add_left, iform_eq_neg_one_of_isRoot_add h₁ h₂ h₁₂,
      CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two (τ := TwistTag.E6.tag)
        (Or.inr (Or.inl rfl)) h₂]
    norm_num

theorem uJ_root_perm {w v : WeylGroup TwistTag.E6.tag} {β₁ β₂ : Fin TwistTag.E6.tag.rank → ℤ}
    (h₁ : IsRoot TwistTag.E6.tag β₁) (h₂ : IsRoot TwistTag.E6.tag β₂)
    (h₁₂ : IsRoot TwistTag.E6.tag (β₁ + β₂)) (hw : w • θ₀ = β₁ + β₂)
    (hv₁ : v • permLattice TwistTag.E6.perm β₁ = -β₁)
    (hv₂ : v • permLattice TwistTag.E6.perm β₂ = -β₂)
    {uJ : WeylGroup TwistTag.E6.tag}
    (huJ : uJ = (rootReflection θ₀)⁻¹ * (w⁻¹ * v * weylTwist TwistTag.E6 w)) :
    uJ • permLattice TwistTag.E6.perm (w⁻¹ • β₁) = w⁻¹ • β₂ ∧
      uJ • permLattice TwistTag.E6.perm (w⁻¹ • β₂) = w⁻¹ • β₁ ∧
      uJ • permLattice TwistTag.E6.perm θ₀ = θ₀ := by
  set s := rootReflection θ₀ with hs
  have hθ : IsRoot TwistTag.E6.tag θ₀ := isRoot_e6HighestRoot
  have hθw : w⁻¹ • (β₁ + β₂) = θ₀ := by rw [← hw, inv_smul_smul]
  have hneg : ∀ {β : Fin TwistTag.E6.tag.rank → ℤ},
      v • permLattice TwistTag.E6.perm β = -β →
      (w⁻¹ * v * weylTwist TwistTag.E6 w) • permLattice TwistTag.E6.perm (w⁻¹ • β) =
        -(w⁻¹ • β) := by
    intro β hvβ
    rw [mul_smul, mul_smul, weylTwist_smul_permLattice, smul_inv_smul, hvβ, smul_neg]
  obtain ⟨hpair₁, hpair₂, hsum⟩ := iform_theta_delta h₁ h₂ h₁₂ hw
  have key : ∀ {x y : Fin TwistTag.E6.tag.rank → ℤ}, x = s • y → s⁻¹ • x = y := fun h => by
    rw [h, inv_smul_smul]
  refine ⟨?_, ?_, ?_⟩
  · rw [huJ, mul_smul, hneg hv₁]
    refine key ?_
    rw [rootReflection_smul_E6 hθ, hpair₂, one_smul, ← hsum]
    abel
  · rw [huJ, mul_smul, hneg hv₂]
    refine key ?_
    rw [rootReflection_smul_E6 hθ, hpair₁, one_smul, ← hsum]
    abel
  · rw [huJ, mul_smul, permLattice_θ₀]
    have hu : (w⁻¹ * v * weylTwist TwistTag.E6 w) • θ₀ = -θ₀ :=
      smul_cocycleWeyl_highRoot hw (by
        rw [permLattice_add_E6, smul_add, hv₁, hv₂]
        abel)
    rw [hu]
    refine key ?_
    rw [hs, rootReflection_smul_self hθ]

theorem conj_mem_sup_of_mem_normalizer {Γ : Type*} [Group Γ] {A B : Subgroup Γ} {g : Γ}
    (hA : g ∈ Subgroup.normalizer (A : Set Γ)) (hB : g ∈ Subgroup.normalizer (B : Set Γ))
    {x : Γ} (hx : x ∈ A ⊔ B) : g * x * g⁻¹ ∈ A ⊔ B := by
  have h1 : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]
  exact h1 ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem mem_normalizer_sup {Γ : Type*} [Group Γ] {A B : Subgroup Γ} {g : Γ}
    (hA : g ∈ Subgroup.normalizer (A : Set Γ)) (hB : g ∈ Subgroup.normalizer (B : Set Γ)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_sup_of_mem_normalizer hA hB, fun hx => ?_⟩
  have := conj_mem_sup_of_mem_normalizer ((Subgroup.normalizer (A : Set Γ)).inv_mem hA)
    ((Subgroup.normalizer (B : Set Γ)).inv_mem hB) hx
  simpa [mul_assoc] using this

theorem exists_lie_frame {L : Type} [Field L] [IsAlgClosed L] (p f : ℕ) [Fact p.Prime]
    [CharP L p] (hf : 1 ≤ f) (hp3 : p ≠ 3) {v : WeylGroup TwistTag.E6.tag}
    {g0 : ModGL TwistTag.E6.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag L)
    (hg0 : twistHom TwistTag.E6 L (iterateFrobenius L p f) g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
    {β₁ β₂ : Fin TwistTag.E6.tag.rank → ℤ} (hβ₁ : IsRoot TwistTag.E6.tag β₁)
    (hβ₂ : IsRoot TwistTag.E6.tag β₂) (hβ₁₂ : IsRoot TwistTag.E6.tag (β₁ + β₂))
    (hv₁ : v • permLattice TwistTag.E6.perm β₁ = -β₁)
    (hv₂ : v • permLattice TwistTag.E6.perm β₂ = -β₂) :
    ∃ (w uJ : WeylGroup TwistTag.E6.tag) (κ z : ModGL TwistTag.E6.tag L),
      w • θ₀ = β₁ + β₂ ∧
      κ ∈ torusGroup TwistTag.E6.tag L ⊔ rootSpan TwistTag.E6.tag L {θ₀, -θ₀} ∧
      z ∈ torusGroup TwistTag.E6.tag L ⊔
        rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag e6LeviNodes) ∧
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w * κ * z ∈
        adjointGroup TwistTag.E6.tag L ∧
      twistHom TwistTag.E6 L (iterateFrobenius L p f)
          (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w * κ * z) =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w * κ * z ∧
      twistHom TwistTag.E6 L (iterateFrobenius L p f) z =
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L uJ)⁻¹ * z ∧
      uJ • permLattice TwistTag.E6.perm (w⁻¹ • β₁) = w⁻¹ • β₂ ∧
      uJ • permLattice TwistTag.E6.perm (w⁻¹ • β₂) = w⁻¹ • β₁ ∧
      uJ • permLattice TwistTag.E6.perm θ₀ = θ₀ ∧
      (rootSpan TwistTag.E6.tag L {θ₀, -θ₀}).map
          (MulAut.conj (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w * κ * z)).toMonoidHom =
        (rootSpan TwistTag.E6.tag L {β₁ + β₂, -(β₁ + β₂)}).map (MulAut.conj g0).toMonoidHom := by
  classical
  obtain ⟨ζ₉, hζ₉⟩ := exists_primitiveRoot_nine (L := L) p hp3
  have hζ₃ : IsPrimitiveRoot (ζ₉ ^ 3) 3 := hζ₉.pow (by norm_num) (by norm_num)
  obtain ⟨w, hw0⟩ := CFSG.SeitzReduction.EPilot.exists_smul_highRoot_eq (τ := TwistTag.E6.tag)
    (Or.inl rfl) hβ₁₂
  have hw : w • θ₀ = β₁ + β₂ := hw0
  have hφ : v • permLattice TwistTag.E6.perm (β₁ + β₂) = -(β₁ + β₂) := by
    rw [permLattice_add_E6, smul_add, hv₁, hv₂]
    abel
  obtain ⟨τ, hτ, uJ, huJ, hnJ, hm⟩ := cocycle_decomp (L := L) hζ₃ hw hφ
  obtain ⟨hu1, hu2, hu3⟩ := uJ_root_perm hβ₁ hβ₂ hβ₁₂ hw hv₁ hv₂ huJ
  have hroots : ∀ α ∈ ({θ₀, -θ₀} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      IsRoot TwistTag.E6.tag α := by
    intro α hα
    rcases hα with rfl | rfl
    · exact isRoot_e6HighestRoot
    · exact IsRoot.neg isRoot_e6HighestRoot
  have hM₂eq : familyGroup (K := L) (zpowFamily ζ₉ e6SepVec) =
      torusGroup TwistTag.E6.tag L ⊔ rootSpan TwistTag.E6.tag L {θ₀, -θ₀} := by
    unfold familyGroup
    rw [familyKernel_a2 hζ₉]
  have hMJeq : familyGroup (K := L) (zpowFamily (ζ₉ ^ 3) (Pi.single (e6Idx 1) 1)) =
      torusGroup TwistTag.E6.tag L ⊔
        rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag e6LeviNodes) := by
    unfold familyGroup
    rw [familyKernel_aJ hζ₃]
  have himgJ : (fun α => permLattice TwistTag.E6.perm α) ''
      familyKernel (τ := TwistTag.E6.tag) (zpowFamily (ζ₉ ^ 3) (Pi.single (e6Idx 1) 1)) =
      familyKernel (zpowFamily (ζ₉ ^ 3) (Pi.single (e6Idx 1) 1)) := by
    rw [familyKernel_aJ hζ₃]
    exact image_permLattice_parabolicRoots
  have himg₂ : (fun α => permLattice TwistTag.E6.perm α) ''
      familyKernel (τ := TwistTag.E6.tag) (zpowFamily ζ₉ e6SepVec) =
      familyKernel (zpowFamily ζ₉ e6SepVec) := by
    rw [familyKernel_a2 hζ₉]
    exact image_permLattice_pair
  have hMJN : familyGroup (K := L) (zpowFamily (ζ₉ ^ 3) (Pi.single (e6Idx 1) 1)) ≤
      Subgroup.normalizer (rootSpan TwistTag.E6.tag L {θ₀, -θ₀} : Set (ModGL TwistTag.E6.tag L)) :=
    familyGroup_aJ_le_normalizer hζ₃
  have hM₂N : familyGroup (K := L) (zpowFamily ζ₉ e6SepVec) ≤
      Subgroup.normalizer (rootSpan TwistTag.E6.tag L {θ₀, -θ₀} : Set (ModGL TwistTag.E6.tag L)) := by
    rw [hM₂eq]
    exact sup_le (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan hroots)
      Subgroup.le_normalizer
  have hns : canonicalRep (coxeterSystem TwistTag.E6.tag) L (rootReflection θ₀) ∈
      familyGroup (K := L) (zpowFamily ζ₉ e6SepVec) := by
    rw [hM₂eq]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.canonicalRep_rootReflection_mem
      (τ := TwistTag.E6.tag) (k := L) isRoot_e6HighestRoot
  have hτM₂ : τ ∈ familyGroup (K := L) (zpowFamily ζ₉ e6SepVec) := torus_le_familyGroup _ hτ
  have hnuJ : canonicalRep (coxeterSystem TwistTag.E6.tag) L uJ ∈
      Subgroup.normalizer (familyGroup (K := L) (zpowFamily ζ₉ e6SepVec) :
        Set (ModGL TwistTag.E6.tag L)) := by
    rw [hM₂eq]
    exact mem_normalizer_sup (canonicalRep_mem_normalizer uJ) (hMJN hnJ)
  have hmN : (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹ *
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
      canonicalRep (coxeterSystem TwistTag.E6.tag) L (weylTwist TwistTag.E6 w) ∈
      Subgroup.normalizer (familyGroup (K := L) (zpowFamily ζ₉ e6SepVec) :
        Set (ModGL TwistTag.E6.tag L)) := by
    rw [hm]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hτM₂)
      (Subgroup.mul_mem _ (Subgroup.le_normalizer hns) hnuJ)
  obtain ⟨κ, hκM, hκ⟩ := exists_lang_twisted_familyGroup (L := L) p f hf _ himg₂ hmN
    (c := (τ * canonicalRep (coxeterSystem TwistTag.E6.tag) L (rootReflection θ₀))⁻¹)
    (Subgroup.inv_mem _ (Subgroup.mul_mem _ hτM₂ hns))
  obtain ⟨z, hzM, hz⟩ := exists_lang_cocycle_familyGroup (L := L) p f hf _ himgJ hnJ
  have hh₀ : twistHom TwistTag.E6 L (iterateFrobenius L p f)
      (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w) =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
        ((canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹ *
          canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
          canonicalRep (coxeterSystem TwistTag.E6.tag) L (weylTwist TwistTag.E6 w)) := by
    rw [map_mul, hg0, twistHom_canonicalRep]
    group
  obtain ⟨m, hmdef⟩ : ∃ m : ModGL TwistTag.E6.tag L,
      m = (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹ *
        canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        canonicalRep (coxeterSystem TwistTag.E6.tag) L (weylTwist TwistTag.E6 w) := ⟨_, rfl⟩
  rw [← hmdef] at hκ hm hh₀
  obtain ⟨F, hF⟩ : ∃ F : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L,
      F = twistHom TwistTag.E6 L (iterateFrobenius L p f) := ⟨_, rfl⟩
  rw [← hF] at hκ hz hh₀
  obtain ⟨nw, hnwdef⟩ : ∃ nw : ModGL TwistTag.E6.tag L,
      nw = canonicalRep (coxeterSystem TwistTag.E6.tag) L w := ⟨_, rfl⟩
  obtain ⟨nJ, hnJdef⟩ : ∃ nJ : ModGL TwistTag.E6.tag L,
      nJ = canonicalRep (coxeterSystem TwistTag.E6.tag) L uJ := ⟨_, rfl⟩
  obtain ⟨ns, hnsdef⟩ : ∃ ns : ModGL TwistTag.E6.tag L,
      ns = canonicalRep (coxeterSystem TwistTag.E6.tag) L (rootReflection θ₀) := ⟨_, rfl⟩
  rw [← hnJdef, ← hnsdef] at hm
  rw [← hnJdef] at hz
  rw [← hnwdef] at hh₀
  have h2 : m * F κ = κ * (τ * ns)⁻¹ * m := by
    rw [← hnsdef] at hκ
    calc m * F κ = κ * (κ⁻¹ * (m * F κ * m⁻¹)) * m := by group
      _ = κ * (τ * ns)⁻¹ * m := by rw [hκ]
  have h3 : (τ * ns)⁻¹ * m = nJ := by rw [hm]; group
  have h4 : nJ * F z = z := by
    calc nJ * F z = z * (z⁻¹ * nJ * F z) := by group
      _ = z := by rw [hz, mul_one]
  have hFfix : F (g0 * nw * κ * z) = g0 * nw * κ * z := by
    calc F (g0 * nw * κ * z) = F (g0 * nw) * F κ * F z := by simp only [map_mul]
      _ = g0 * nw * m * F κ * F z := by rw [hh₀]
      _ = g0 * nw * (m * F κ) * F z := by group
      _ = g0 * nw * (κ * (τ * ns)⁻¹ * m) * F z := by rw [h2]
      _ = g0 * nw * κ * ((τ * ns)⁻¹ * m) * F z := by group
      _ = g0 * nw * κ * nJ * F z := by rw [h3]
      _ = g0 * nw * κ * (nJ * F z) := by group
      _ = g0 * nw * κ * z := by rw [h4]
  refine ⟨w, uJ, κ, z, hw, hM₂eq ▸ hκM, hMJeq ▸ hzM, ?_, ?_, ?_, hu1, hu2, hu3, ?_⟩
  · rw [← hnwdef]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg0C
      (hnwdef ▸ canonicalRep_mem_adjointGroup _ L w)) (familyGroup_le_adjoint _ hκM))
      (familyGroup_le_adjoint _ hzM)
  · rw [← hnwdef, ← hF]
    exact hFfix
  · rw [← hnJdef, ← hF]
    exact eq_inv_mul_iff_mul_eq.2 h4
  · rw [← hnwdef]
    have hzN : κ * z ∈ Subgroup.normalizer
        (rootSpan TwistTag.E6.tag L {θ₀, -θ₀} : Set (ModGL TwistTag.E6.tag L)) :=
      Subgroup.mul_mem _ (hM₂N hκM) (hMJN hzM)
    have hconj : (MulAut.conj (g0 * nw * κ * z)).toMonoidHom =
        (MulAut.conj (g0 * nw)).toMonoidHom.comp (MulAut.conj (κ * z)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hconj, ← Subgroup.map_map, map_conj_eq_of_mem_normalizer hzN]
    have hconj' : (MulAut.conj (g0 * nw)).toMonoidHom =
        (MulAut.conj g0).toMonoidHom.comp (MulAut.conj nw).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hconj', ← Subgroup.map_map]
    congr 1
    rw [hnwdef, (canonical_weyl_root_transport TwistTag.E6.tag L).1 w {θ₀, -θ₀} hroots]
    congr 1
    ext α
    simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_neg, hw]

end Frame

end CFSG.LieType.SeitzGeneration.ExcWideThree
