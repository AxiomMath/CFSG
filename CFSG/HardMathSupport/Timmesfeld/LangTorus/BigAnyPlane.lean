module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyGen
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section Plane

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def planeKernel (D₁ : Subgroup (ModGL τ L)) : Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ → rootChar a γ = 1}

theorem isClosedRoots_planeKernel (D₁ : Subgroup (ModGL τ L)) :
    IsClosedRoots (planeKernel D₁) where
  isRoot _ h := h.1
  neg_mem γ h := ⟨IsRoot.neg h.1, fun a ha => by
    have := rootChar_sub a 0 γ
    rw [zero_sub, rootChar_zero, h.2 a ha, inv_one, one_mul] at this
    exact this⟩
  add_mem α hα β hβ hr := ⟨hr, fun a ha => by
    rw [rootChar_add, hα.2 a ha, hβ.2 a ha, one_mul]⟩

@[expose] def rootCharAt (γ : Fin τ.rank → ℤ) : (Fin τ.rank → Lˣ) →* Lˣ where
  toFun a := rootChar a γ
  map_one' := by simp [rootChar]
  map_mul' a b := by
    simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootDiagUnitHom_apply' (a : Fin τ.rank → Lˣ) : rootDiagUnitHom τ L a = rootDiagUnit τ a :=
  rfl

theorem LangSetup.exists_rootDiagUnit_of_mem_E (S : LangSetup τ L p) {x : ModGL τ L}
    (hx : x ∈ S.E) : ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = x := by
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (S.E_le hx).1).1
  exact ⟨a, ha.symm⟩

theorem LangSetup.exists_nontrivial_killing (S : LangSetup τ L p) {D₁ : Subgroup (ModGL τ L)}
    (hD₁E : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) (γ : Fin τ.rank → ℤ) :
    ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ ∧ rootDiagUnit τ a ≠ 1 ∧ rootChar a γ = 1 := by
  classical
  have : NeZero p := ⟨S.hp.ne_zero⟩
  have hex : ∀ x : D₁, ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = x.1 :=
    fun x => S.exists_rootDiagUnit_of_mem_E (hD₁E x.2)
  choose A hA using hex
  have hAp : ∀ x : D₁, (A x) ^ p = 1 := by
    intro x
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := τ) (K := L)
    rw [rootDiagUnit_one]
    have h1 : rootDiagUnit τ ((A x) ^ p) = (rootDiagUnit τ (A x)) ^ p :=
      map_pow (rootDiagUnitHom τ L) (A x) p
    rw [h1, hA x]
    exact S.E_exp x.1 (hD₁E x.2)
  have hroot : ∀ x : D₁, (rootChar (A x) γ) ^ p = 1 := by
    intro x
    have h1 : rootChar ((A x) ^ p) γ = (rootChar (A x) γ) ^ p :=
      map_pow (rootCharAt (L := L) γ) (A x) p
    rw [← h1, hAp x]
    exact (rootCharAt (L := L) γ).map_one
  let f : D₁ → rootsOfUnity p L := fun x => ⟨rootChar (A x) γ, (mem_rootsOfUnity _ _).2 (hroot x)⟩
  have hlt : Nat.card (rootsOfUnity p L) < Nat.card D₁ := by
    have h1 := card_rootsOfUnity L p
    rw [hc]
    have : p < p ^ 2 := by
      have := S.hp.one_lt
      nlinarith
    omega
  have hnot : ¬ Function.Injective f := fun hinj =>
    absurd (Nat.card_le_card_of_injective f hinj) (not_le.2 hlt)
  obtain ⟨x, y, hf, hxy⟩ := Function.not_injective_iff.1 hnot
  have hfe : rootChar (A x) γ = rootChar (A y) γ := congrArg Subtype.val hf
  have hmul : rootDiagUnit τ (A x * (A y)⁻¹) = x.1 * (y.1)⁻¹ := by
    have := map_mul (rootDiagUnitHom τ L) (A x) (A y)⁻¹
    rw [map_inv] at this
    simpa [rootDiagUnitHom_apply', hA] using this
  refine ⟨A x * (A y)⁻¹, ?_, ?_, ?_⟩
  · rw [hmul]
    exact D₁.mul_mem x.2 (D₁.inv_mem y.2)
  · rw [hmul]
    intro h
    apply hxy
    exact Subtype.ext (mul_inv_eq_one.1 h)
  · have h1 := map_mul (rootCharAt (L := L) γ) (A x) (A y)⁻¹
    rw [map_inv] at h1
    change rootChar (A x * (A y)⁻¹) γ = _ at h1
    rw [h1]
    change rootChar (A x) γ * (rootChar (A y) γ)⁻¹ = 1
    rw [hfe, mul_inv_cancel]

theorem LangSetup.exists_root_not_mem_planeKernel (S : LangSetup τ L p)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) :
    ∃ γ, IsRoot τ γ ∧ γ ∉ planeKernel D₁ := by
  have hp1 : 1 < p ^ 2 := by
    have := S.hp.one_lt
    nlinarith
  have hfin : Finite D₁ := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  have hnt : Nontrivial D₁ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; exact hp1)
  obtain ⟨g, hg⟩ := exists_ne (1 : D₁)
  obtain ⟨a, ha⟩ := S.exists_rootDiagUnit_of_mem_E (hD₁E g.2)
  by_contra hno
  push Not at hno
  have ha1 : a = 1 := by
    funext j
    have hj : Pi.single j 1 ∈ planeKernel D₁ := hno _ (isRoot_single τ j)
    have h1 := hj.2 a (by rw [ha]; exact g.2)
    have h2 := rootChar_nsmul_single a j 1
    rw [one_smul, pow_one] at h2
    rw [h2] at h1
    exact h1
  apply hg
  apply Subtype.ext
  rw [← ha, ha1]
  exact rootDiagUnit_one

@[expose] def BigAnyPBig (S : LangSetup τ L p) : Prop :=
  ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
    ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ → ∀ a' : Fin τ.rank → Lˣ,
      rootDiagUnit τ a' ∈ D₁ → ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → rootChar a γ = 1 →
        rootChar a' γ ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
          γ ∈ componentRoots (rootCharHom a) i →
            ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i))

theorem LangSetup.mem_bigAnyRoots_of_pbig (S : LangSetup τ L p) (hq4 : 4 ≤ S.D.q)
    (hP : BigAnyPBig S) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ {γ | IsRoot τ γ ∧ γ ∉ planeKernel D₁}) :
    γ ∈ bigAnyRoots S D₁ := by
  obtain ⟨hγr, hγn⟩ := hγ
  obtain ⟨a', ha'D, ha'1⟩ : ∃ a', rootDiagUnit τ a' ∈ D₁ ∧ rootChar a' γ ≠ 1 := by
    by_contra h
    push Not at h
    exact hγn ⟨hγr, h⟩
  obtain ⟨a, haD, ha1, hγa⟩ := S.exists_nontrivial_killing hD₁E hc γ
  have hmem : γ ∈ kernelRoots (rootCharHom a) := ⟨hγr, hγa⟩
  refine ⟨a, haD, ha1, (⟦⟨γ, hmem⟩⟧ : KernelComponent (rootCharHom a)), ?_, ?_, ⟨hmem, rfl⟩⟩
  · exact hP D₁ hD₁E hc a haD a' ha'D γ hγr hγa ha'1 _ ⟨hmem, rfl⟩
  · have hE : rootDiagUnit τ a ∈ S.E := hD₁E haD
    have hpos := (componentOrbitLength_spec S hE (⟦⟨γ, hmem⟩⟧ : KernelComponent (rootCharHom a))).1
    exact hq4.trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hpos) _)

theorem bigAnyComponentsGenerate_of_pbig (S : LangSetup τ L p) (hτ : SimplyLacedTag τ)
    (hq4 : 4 ≤ S.D.q) (hP : BigAnyPBig S) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E)
    (hc : Nat.card D₁ = p ^ 2) : BigAnyComponentsGenerate S D₁ :=
  (adjointGroup_le_rootSpan_compl hτ (isClosedRoots_planeKernel D₁)
    (S.exists_root_not_mem_planeKernel hD₁E hc)).trans
    (biSup_mono fun _ hγ => S.mem_bigAnyRoots_of_pbig hq4 hP hD₁E hc hγ)

theorem hasBigAnyComponent_of_pbig (S : LangSetup τ L p) (hq4 : 4 ≤ S.D.q) (hP : BigAnyPBig S)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) :
    HasBigAnyComponent S D₁ := by
  obtain ⟨γ, hγr, hγn⟩ := S.exists_root_not_mem_planeKernel hD₁E hc
  obtain ⟨a, haD, ha1, i, hbig, hQ, -⟩ := S.mem_bigAnyRoots_of_pbig hq4 hP hD₁E hc ⟨hγr, hγn⟩
  exact ⟨a, haD, ha1, i, hbig, hQ⟩

end Plane

end CFSG.HardMathSupport.Timmesfeld.LangTorus
