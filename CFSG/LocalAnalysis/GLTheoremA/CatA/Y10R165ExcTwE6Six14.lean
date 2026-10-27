module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six10
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6ThreeDvd

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Lang.TwE6Step3 CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

section TwoLayers


variable {Ω : Type} [Field Ω] {n : ModGL Tag.E6 Ω} {Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω}
  {K : Type} [Field K] [Algebra K Ω]

private theorem two_a2_layers_normalizer_commutant {S S₀ S₁ : Set (Fin Tag.E6.rank → ℤ)}
    {w : WeylGroup Tag.E6} {P₀ P₁ : Subgroup (ModGL Tag.E6 Ω)}
    (hw : ((w • ·) '' S) = parabolicRoots Tag.E6 supportA2A2)
    (hS₀ : ((w • ·) '' S₀) = parabolicRoots Tag.E6 CFSG.RankThree.E6.support13)
    (hS₁ : ((w • ·) '' S₁) = parabolicRoots Tag.E6 CFSG.RankThree.E6.support56)
    (hP₀ : P₀ = rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ)
    (hP₁ : P₁ = rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ)
    (hcomm₀ : e6Commutant ((P₀.map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω CFSG.RankThree.E6.support13 : Set (ModGL Tag.E6 Ω)))
    (hcomm₁ : e6Commutant ((P₁.map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω CFSG.RankThree.E6.support56 : Set (ModGL Tag.E6 Ω))) :
    (∀ k : Fin 2, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S,
      y ∈ twistedFixedPoints n Φ → ∀ u ∈ ![P₀, P₁] k, y * u * y⁻¹ ∈ ![P₀, P₁] k) ∧
    e6Commutant ((((⨆ k : Fin 2, ![P₀, P₁] k).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
        Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω supportA2A2 : Set (ModGL Tag.E6 Ω)) := by
  classical
  have hS : ∀ α ∈ S, IsRoot Tag.E6 α := by
    intro α hα
    have h : w • α ∈ parabolicRoots Tag.E6 supportA2A2 := hw ▸ Set.mem_image_of_mem _ hα
    simpa using IsRoot.smul h.1 w⁻¹
  have hS₀root : ∀ α ∈ S₀, IsRoot Tag.E6 α := by
    intro α hα
    have h : w • α ∈ parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 :=
      hS₀ ▸ Set.mem_image_of_mem _ hα
    simpa using IsRoot.smul h.1 w⁻¹
  have hS₁root : ∀ α ∈ S₁, IsRoot Tag.E6 α := by
    intro α hα
    have h : w • α ∈ parabolicRoots Tag.E6 CFSG.RankThree.E6.support56 :=
      hS₁ ▸ Set.mem_image_of_mem _ hα
    simpa using IsRoot.smul h.1 w⁻¹
  have hQ : (rootSpan Tag.E6 Ω S).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω supportA2A2 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hS, hw, subsystemGroup_eq_rootSpan]
  have hQ₀ : (rootSpan Tag.E6 Ω S₀).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω CFSG.RankThree.E6.support13 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S₀ hS₀root, hS₀, subsystemGroup_eq_rootSpan]
  have hQ₁ : (rootSpan Tag.E6 Ω S₁).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω CFSG.RankThree.E6.support56 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S₁ hS₁root, hS₁, subsystemGroup_eq_rootSpan]
  have h13A : CFSG.RankThree.E6.support13 ⊆ supportA2A2 := by
    intro i hi
    rw [CFSG.RankThree.E6.mem_supportA2A2]
    rw [CFSG.RankThree.E6.mem_support13] at hi
    tauto
  have h56A : CFSG.RankThree.E6.support56 ⊆ supportA2A2 := by
    intro i hi
    rw [CFSG.RankThree.E6.mem_supportA2A2]
    rw [CFSG.RankThree.E6.mem_support56] at hi
    tauto
  have hsep₁₂ : IsSeparated CFSG.RankThree.E6.support13 CFSG.RankThree.E6.support56 := by
    intro a ha b hb
    rw [CFSG.RankThree.E6.mem_support13] at ha
    rw [CFSG.RankThree.E6.mem_support56] at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      exact ⟨by decide +kernel, by decide +kernel⟩
  have hsep₂₁ : IsSeparated CFSG.RankThree.E6.support56 CFSG.RankThree.E6.support13 := by
    intro a ha b hb
    rw [CFSG.RankThree.E6.mem_support56] at ha
    rw [CFSG.RankThree.E6.mem_support13] at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      exact ⟨by decide +kernel, by decide +kernel⟩
  have hunion : supportA2A2 = CFSG.RankThree.E6.support13 ∪ CFSG.RankThree.E6.support56 := by
    ext i
    simp only [CFSG.RankThree.E6.mem_supportA2A2, CFSG.RankThree.E6.mem_support13,
      CFSG.RankThree.E6.mem_support56, Set.mem_union]
    tauto
  have hle : ∀ k : Fin 2, ((![P₀, P₁] k).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom) ≤
      subsystemGroup Tag.E6 Ω (![CFSG.RankThree.E6.support13, CFSG.RankThree.E6.support56] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hP₀ ▸ hQ₀ ▸ Subgroup.map_mono inf_le_left,
      hP₁ ▸ hQ₁ ▸ Subgroup.map_mono inf_le_left⟩
  have hC : ∀ k : Fin 2, e6Commutant ((((![P₀, P₁] k).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
        Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω
          (![CFSG.RankThree.E6.support13, CFSG.RankThree.E6.support56] k) :
        Set (ModGL Tag.E6 Ω)) := by
    rw [Fin.forall_fin_two]
    exact ⟨hcomm₀, hcomm₁⟩
  have hsep : ∀ k l : Fin 2, k ≠ l → IsSeparated
      (![CFSG.RankThree.E6.support13, CFSG.RankThree.E6.support56] k)
      (![CFSG.RankThree.E6.support13, CFSG.RankThree.E6.support56] l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · exact hsep₁₂
    · exact hsep₂₁
    · exact absurd rfl hkl
  have hJ : supportA2A2 = ⋃ k, ![CFSG.RankThree.E6.support13, CFSG.RankThree.E6.support56] k := by
    rw [hunion]
    ext i
    simp [Set.mem_iUnion, Fin.exists_fin_two]
  obtain ⟨-, μ, -, hμrange, hμcomm, -, -⟩ := e6_product_layers (Ω := Ω) supportA2A2
    ![CFSG.RankThree.E6.support13, CFSG.RankThree.E6.support56] (fun k => (![P₀, P₁] k).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom) hsep hJ hle hC
  have hcommP : e6Commutant ((((⨆ k : Fin 2, ![P₀, P₁] k).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
        Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω supportA2A2 : Set (ModGL Tag.E6 Ω)) := by
    rw [Subgroup.map_iSup, ← hμrange]
    exact hμcomm
  have hnormF : ∀ k : Fin 2, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S,
      y ∈ twistedFixedPoints n Φ → ∀ u ∈ ![P₀, P₁] k, y * u * y⁻¹ ∈ ![P₀, P₁] k := by
    rw [Fin.forall_fin_two]
    constructor
    · intro y hy hyR u hu
      have hy' := conj_mem_torus_sup hS hQ hy
      rw [hunion] at hy'
      have hn₁ := torus_sup_subsystemGroup_le_normalizer (Ω := Ω)
        (J₁ := CFSG.RankThree.E6.support13) (J₂ := CFSG.RankThree.E6.support56) hsep₂₁ hy'
      exact hP₀ ▸ thetaQ_conj_mem (mem_normalizer_of_conj hQ₀ hn₁) hyR (hP₀ ▸ hu)
    · intro y hy hyR u hu
      have hy' := conj_mem_torus_sup hS hQ hy
      rw [hunion, Set.union_comm] at hy'
      have hn₂ := torus_sup_subsystemGroup_le_normalizer (Ω := Ω)
        (J₁ := CFSG.RankThree.E6.support56) (J₂ := CFSG.RankThree.E6.support13) hsep₁₂ hy'
      exact hP₁ ▸ thetaQ_conj_mem (mem_normalizer_of_conj hQ₁ hn₂) hyR (hP₁ ▸ hu)
  exact ⟨hnormF, hcommP⟩

private theorem two_a2_layers_span_fixed {S S₀ S₁ : Set (Fin Tag.E6.rank → ℤ)}
    {w : WeylGroup Tag.E6} {P₀ P₁ : Subgroup (ModGL Tag.E6 Ω)}
    (hw : ((w • ·) '' S) = parabolicRoots Tag.E6 supportA2A2)
    (hS₀ : ((w • ·) '' S₀) = parabolicRoots Tag.E6 CFSG.RankThree.E6.support13)
    (hS₁ : ((w • ·) '' S₁) = parabolicRoots Tag.E6 CFSG.RankThree.E6.support56)
    (hP₀ : P₀ = rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ)
    (hP₁ : P₁ = rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ) :
    (∀ k : Fin 2, ![P₀, P₁] k ≤ rootSpan Tag.E6 Ω S) ∧
      ∀ k : Fin 2, ![P₀, P₁] k ≤ twistedFixedPoints n Φ := by
  classical
  have h13A : CFSG.RankThree.E6.support13 ⊆ supportA2A2 := by
    intro i hi
    rw [CFSG.RankThree.E6.mem_supportA2A2]
    rw [CFSG.RankThree.E6.mem_support13] at hi
    tauto
  have h56A : CFSG.RankThree.E6.support56 ⊆ supportA2A2 := by
    intro i hi
    rw [CFSG.RankThree.E6.mem_supportA2A2]
    rw [CFSG.RankThree.E6.mem_support56] at hi
    tauto
  have hsub : ∀ {J : Set (Fin Tag.E6.rank)}, J ⊆ supportA2A2 →
      (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 J ⊆ S := by
    intro J hJ
    rintro _ ⟨β, hβ, rfl⟩
    have hβJ : β ∈ parabolicRoots Tag.E6 supportA2A2 :=
      ⟨hβ.1, fun i hi => hβ.2 i (fun hiJ => hi (hJ hiJ))⟩
    rw [← hw] at hβJ
    obtain ⟨α, hα, rfl⟩ := hβJ
    simpa using hα
  have hS₀' : S₀ = (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 := by
    rw [← hS₀, Set.image_image]
    simp
  have hS₁' : S₁ = (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 CFSG.RankThree.E6.support56 := by
    rw [← hS₁, Set.image_image]
    simp
  constructor
  · rw [Fin.forall_fin_two]
    constructor
    · exact hP₀ ▸ inf_le_left.trans (rootSpan_mono (hS₀' ▸ hsub h13A))
    · exact hP₁ ▸ inf_le_left.trans (rootSpan_mono (hS₁' ▸ hsub h56A))
  · rw [Fin.forall_fin_two]
    exact ⟨hP₀ ▸ inf_le_right, hP₁ ▸ inf_le_right⟩

theorem exists_kernelLayer_of_two_a2_layers {S S₀ S₁ : Set (Fin Tag.E6.rank → ℤ)}
    {w : WeylGroup Tag.E6}
    (hw : ((w • ·) '' S) = parabolicRoots Tag.E6 supportA2A2)
    (hS₀ : ((w • ·) '' S₀) = parabolicRoots Tag.E6 CFSG.RankThree.E6.support13)
    (hS₁ : ((w • ·) '' S₁) = parabolicRoots Tag.E6 CFSG.RankThree.E6.support56)
    (hfin₀ : Finite ↥(rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ))
    (hq₀ : CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ))
    (hcomm₀ : e6Commutant (((rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω CFSG.RankThree.E6.support13 : Set (ModGL Tag.E6 Ω)))
    (hsl₀ : ∃ (m : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω m (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
        rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ)
    (hfin₁ : Finite ↥(rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ))
    (hq₁ : CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ))
    (hcomm₁ : e6Commutant (((rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω CFSG.RankThree.E6.support56 : Set (ModGL Tag.E6 Ω))) :
    ∃ KL : KernelLayer n Φ S K (Fin 2),
      KL.P = ![rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ,
        rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ] := by
  classical
  have hS : ∀ α ∈ S, IsRoot Tag.E6 α := by
    intro α hα
    have h : w • α ∈ parabolicRoots Tag.E6 supportA2A2 := hw ▸ Set.mem_image_of_mem _ hα
    simpa using IsRoot.smul h.1 w⁻¹
  have hQ : (rootSpan Tag.E6 Ω S).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω supportA2A2 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hS, hw, subsystemGroup_eq_rootSpan]
  have hfinF : ∀ k : Fin 2,
      Finite ↥(![rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ,
        rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hfin₀, hfin₁⟩
  have hqF : ∀ k : Fin 2,
      CFSG.IsQuasisimple ↥(![rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ,
        rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hq₀, hq₁⟩
  obtain ⟨hnormF, hcommP⟩ := two_a2_layers_normalizer_commutant
    (P₀ := rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ)
    (P₁ := rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ) hw hS₀ hS₁ rfl rfl hcomm₀ hcomm₁
  obtain ⟨hspan, hfix⟩ := two_a2_layers_span_fixed
    (P₀ := rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ)
    (P₁ := rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ) hw hS₀ hS₁ rfl rfl
  obtain ⟨KL, hKL⟩ := NonsplitLayers.exists_kernelLayer_family_P
    ![rootSpan Tag.E6 Ω S₀ ⊓ twistedFixedPoints n Φ,
      rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints n Φ] hS hQ hfinF hqF hspan hfix hnormF hcommP
    (fun _ => by obtain ⟨m, h₀, hsl⟩ := hsl₀; exact ⟨0, m, h₀, hsl⟩)
  exact ⟨KL, hKL⟩

end TwoLayers

section Frame


theorem tw6SixFrame_kernelLayer {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {n : ℕ} [CharP Ω 2] {Fr : Ω →+* Ω} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (hq3 : 3 ≤ 2 ^ n) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr))
    (hW : ((tw6SixFrameWeyl • ·) '' torusRootKernel x) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.supportA2A2) :
    ∃ KL : KernelLayer (tw6N Ω) (twistE6 Ω Fr) (torusRootKernel x) K (Fin 2),
      ∀ i, KL.P i = tw6SixLayer (L := Ω) (Fr := Fr) tw6SixFrameWeyl i := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvS := tw6_torusRootKernel_smul_stable (Fr := Fr) hFr hx
  obtain ⟨h0, h1⟩ := tw6SixLayerRoots_smul hvS hW
  have hw₀ : ((tw6SixFrameWeyl • ·) '' tw6SixLayerRoots tw6SixFrameWeyl 0) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 := by
    rw [tw6SixLayerRoots, Set.image_image]; simp
  have hw₁ : ((tw6SixFrameWeyl • ·) '' tw6SixLayerRoots tw6SixFrameWeyl 1) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.support56 := by
    rw [tw6SixLayerRoots, Set.image_image]; simp
  have hS₀root : ∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 0, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 tw6SixFrameWeyl⁻¹
  have hS₁root : ∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 1, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 tw6SixFrameWeyl⁻¹
  obtain ⟨-, hfin₀, hq₀, hcomm₀, h₀, hsl₀⟩ :=
    tw6_A2_layer_gen (K := K) (Ω := Ω) (Fr := Fr) (ℓ := 2) (f := n) hn hK hq3 hFr
      hS₀root h0 hw₀
  obtain ⟨-, hfin₁, hq₁, hcomm₁, -⟩ :=
    tw6_A2_layer_gen₂ (K := K) (Ω := Ω) (Fr := Fr) (ℓ := 2) (f := n) hn hK hq3 hFr
      hS₁root h1 hw₁
  obtain ⟨KL, hKL⟩ := exists_kernelLayer_of_two_a2_layers (Ω := Ω) (n := tw6N Ω)
    (Φ := twistE6 Ω Fr) (S := torusRootKernel x) (S₀ := tw6SixLayerRoots tw6SixFrameWeyl 0)
    (S₁ := tw6SixLayerRoots tw6SixFrameWeyl 1) (w := tw6SixFrameWeyl) (K := K)
    hW hw₀ hw₁ hfin₀ hq₀ hcomm₀ ⟨e6Index 0, h₀, hsl₀⟩ hfin₁ hq₁ hcomm₁
  refine ⟨KL, fun i => ?_⟩
  rw [hKL]
  fin_cases i <;> rfl

end Frame

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
