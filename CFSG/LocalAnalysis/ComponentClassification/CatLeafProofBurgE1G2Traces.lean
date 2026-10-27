module

public import CFSG.RankThree.PartOne.KF4.F4Traces
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KF4
open CFSG.RankThree.PartOne.KF4 (closure_traces_of_formula trace_simpleRootSL2_of_counts')

@[expose] def g2Long : Fin Tag.G2.rank := ⟨0, by decide⟩

theorem rootExponents_G2_long :
    (rootExponents .G2 g2Long).toFinset = {-2, -1, 0, 1, 2} ∧
      (rootExponents .G2 g2Long).count (-2) = 1 ∧
      (rootExponents .G2 g2Long).count (-1) = 4 ∧ (rootExponents .G2 g2Long).count 0 = 2 ∧
      (rootExponents .G2 g2Long).count 1 = 4 ∧ (rootExponents .G2 g2Long).count 2 = 1 := by
  decide +kernel

theorem trace_simpleRootSL2_G2_long
    {k : Type} [Field k] (A : SL2 k) :
    LinearMap.trace k (RootModule .G2 k)
        (simpleRootSL2 .G2 k g2Long A : Module.End k (RootModule .G2 k)) =
      ((1 : ℕ) : k) * (A : Matrix (Fin 2) (Fin 2) k).trace ^ 2 +
        ((4 : ℕ) : k) * (A : Matrix (Fin 2) (Fin 2) k).trace + ((2 : ℕ) : k) := by
  rw [trace_simpleRootSL2_of_counts' (a := 1) (b := 4) (m := 2) g2Long rootExponents_G2_long A]
  have : ((Tag.G2.rank : ℕ) : k) = 2 := by norm_num [Tag.rank]
  rw [this]
  push_cast
  ring

theorem closure_trace_G2_long
    (k : Type) [Field k] [Finite k] (M : Type) [Field M] [Algebra k M] (P : GL (Fin 2) M)
    (g : ModGL Tag.G2 M) :
    Subfield.closure {x : M | ∃ A : SL2 k, x = LinearMap.trace M (RootModule .G2 M)
      ((g * simpleRootSL2 .G2 M g2Long
        (conjGL P (Matrix.SpecialLinearGroup.map (algebraMap k M) A)) *
        g⁻¹ : ModGL .G2 M) : Module.End M (RootModule .G2 M))} =
      (algebraMap k M).fieldRange :=
  closure_traces_of_formula g2Long 1 4 2 (fun M _ A => trace_simpleRootSL2_G2_long A) k
    (Or.inl (by simp)) (fun h2 _ => by
      have : CharP k 2 := ringChar.of_eq h2
      rw [show ((4 : ℕ) : k) = ((2 * 2 : ℕ) : k) by norm_num, Nat.cast_mul, Nat.cast_two,
        CharTwo.two_eq_zero, zero_mul]) M P g

theorem ringEquiv_eq_one_of_fixes_G2_root_SL2_traces
    {K : Type} [Field K] [Finite K]
    (M : Type) [Field M] [Algebra K M] (A : GL (Fin 2) M) (h : ModGL Tag.G2 M) (σ : K ≃+* K)
    (hσ : ∀ B : SL2 K, ∃ y : K, σ y = y ∧ algebraMap K M y = LinearMap.trace M
      (RootModule Tag.G2 M)
      ((h * simpleRootSL2 Tag.G2 M g2Long
        (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
        h⁻¹ : ModGL Tag.G2 M) : Module.End M (RootModule Tag.G2 M))) :
    σ = 1 := by
  have hcl := closure_trace_G2_long K M A h
  have hS : {x : M | ∃ B : SL2 K, x = LinearMap.trace M (RootModule Tag.G2 M)
      ((h * simpleRootSL2 Tag.G2 M g2Long
        (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
        h⁻¹ : ModGL Tag.G2 M) : Module.End M (RootModule Tag.G2 M))} ⊆
      (((RingHom.eqLocusField σ.toRingHom (RingHom.id K)).map (algebraMap K M) :
        Subfield M) : Set M) := by
    rintro _ ⟨B, rfl⟩
    obtain ⟨y, hy, hyB⟩ := hσ B
    exact ⟨y, hy, hyB⟩
  have hle := Subfield.closure_le.2 hS
  rw [hcl] at hle
  refine RingEquiv.ext fun c => ?_
  obtain ⟨y, hy, hyc⟩ := hle ⟨c, rfl⟩
  have hyc' : y = c := (algebraMap K M).injective hyc
  subst hyc'
  exact hy

theorem trace_apply_of_G2_expression
    {K : Type} [Field K] (η : MulAut (adjointGroup Tag.G2 K))
    (g : adjointGroup Tag.G2 K) (σ : K ≃+* K)
    (hexpr : ∀ x : adjointGroup Tag.G2 K, (η x : ModGL Tag.G2 K) = (g : ModGL Tag.G2 K) *
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.G2 K) * (g : ModGL Tag.G2 K)⁻¹)
    (x : adjointGroup Tag.G2 K) :
    LinearMap.trace K (RootModule Tag.G2 K)
        ((η x : ModGL Tag.G2 K) : Module.End K (RootModule Tag.G2 K)) =
      σ (LinearMap.trace K (RootModule Tag.G2 K)
        ((x : ModGL Tag.G2 K) : Module.End K (RootModule Tag.G2 K))) := by
  rw [hexpr x, Units.val_mul, Units.val_mul, LinearMap.trace_conj,
    units_map_entrywiseHom_eq_baseChangeGL, trace_baseChangeGL]
  rfl

theorem G2_descended_root_SL2_pointwise_inner
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (M : Type) [Field M] [Algebra K M] (A : GL (Fin 2) M) (h : ModGL Tag.G2 M)
    (hU : ∀ B : SL2 K, h * simpleRootSL2 Tag.G2 M g2Long (conjGL A
        (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) * h⁻¹ ∈
          (adjointGroup Tag.G2 K).map (baseChangeGL (algebraMap K M)))
    (Z : Subgroup (MulAut (adjointGroup Tag.G2 K)))
    (hZ : ∀ η ∈ Z, ∀ (u : adjointGroup Tag.G2 K) (B : SL2 K),
      baseChangeGL (algebraMap K M) (u : ModGL Tag.G2 K) =
        h * simpleRootSL2 Tag.G2 M g2Long
          (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
          h⁻¹ → η u = u) :
    ∀ η ∈ Z, η ∈ (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range := by
  intro η hη
  obtain ⟨huniq, Θ, hΘ, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ
    hℓ2 hf K hK .G2 (Or.inr ⟨rfl, hℓ3⟩)
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := huniq η
  have hexpr : ∀ x : adjointGroup Tag.G2 K, (η x : ModGL Tag.G2 K) = (g : ModGL Tag.G2 K) *
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.G2 K) * (g : ModGL Tag.G2 K)⁻¹ := hgσ
  have hΘη : Θ η = σ := hΘ η g σ hexpr
  have hσ : σ = 1 := by
    refine ringEquiv_eq_one_of_fixes_G2_root_SL2_traces M A h σ fun B => ?_
    obtain ⟨y, hyC, hy⟩ := hU B
    have hfix : η ⟨y, hyC⟩ = ⟨y, hyC⟩ := hZ η hη ⟨y, hyC⟩ B hy
    have h1 := trace_apply_of_G2_expression η g σ hexpr ⟨y, hyC⟩
    rw [hfix] at h1
    refine ⟨LinearMap.trace K (RootModule Tag.G2 K)
      ((y : ModGL Tag.G2 K) : Module.End K (RootModule Tag.G2 K)), h1.symm, ?_⟩
    rw [← hy, trace_baseChangeGL]
  have : η ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, hΘη, hσ]
  rwa [hker] at this

end CFSG.ComponentClassification.CatLeafProof
