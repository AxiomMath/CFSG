module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZFam
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZLang
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FTriality
public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeField

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Dickson.Bal207.D4Graph CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage)
open scoped Pointwise
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner


section DSet

variable {K : Type} [Field K] [Finite K]

theorem diagAut_sq_inner (b : Fin Tag.D4.rank → Kˣ) :
    ∃ y : adjointGroup Tag.D4 K, diagAut b * diagAut b = MulAut.conj y := by
  rw [diagAut_mul]
  obtain ⟨cc, hcc⟩ : ∃ cc, b * b = cartanChar cc := by
    refine cartan_of_squares ?_ ?_
    · exact ⟨(b 0 : K) * b 1, by simp only [Pi.mul_apply, Units.val_mul]; ring⟩
    · exact ⟨(b 0 : K) * b 3, by simp only [Pi.mul_apply, Units.val_mul]; ring⟩
  obtain ⟨y, hy⟩ := (diagAut_inner_iff (b * b)).2 ⟨cc, hcc⟩
  exact ⟨y, hy.symm⟩

@[expose] def diagSet (K : Type) [Field K] [Finite K] : Set (MulAut (adjointGroup Tag.D4 K)) :=
  {δ | ∃ (c : adjointGroup Tag.D4 K) (b : Fin Tag.D4.rank → Kˣ), δ = MulAut.conj c * diagAut b}

theorem diagSet_mul {δ δ' : MulAut (adjointGroup Tag.D4 K)} (h : δ ∈ diagSet K) (h' : δ' ∈ diagSet K) :
    δ * δ' ∈ diagSet K := by
  obtain ⟨c, b, rfl⟩ := h
  obtain ⟨c', b', rfl⟩ := h'
  refine ⟨c * diagAut b c', b * b', ?_⟩
  rw [map_mul, ← diagAut_mul]
  calc MulAut.conj c * diagAut b * (MulAut.conj c' * diagAut b')
      = MulAut.conj c * (diagAut b * MulAut.conj c') * diagAut b' := by group
    _ = MulAut.conj c * (MulAut.conj (diagAut b c') * diagAut b) * diagAut b' := by rw [mul_conj_eq (diagAut b) c']
    _ = MulAut.conj c * MulAut.conj (diagAut b c') * (diagAut b * diagAut b') := by group

theorem diagSet_sq {δ : MulAut (adjointGroup Tag.D4 K)} (h : δ ∈ diagSet K) :
    ∃ y : adjointGroup Tag.D4 K, δ * δ = MulAut.conj y := by
  obtain ⟨c, b, rfl⟩ := h
  obtain ⟨y, hy⟩ := diagAut_sq_inner (K := K) b
  refine ⟨c * diagAut b c * y, ?_⟩
  rw [map_mul, map_mul, ← hy]
  calc MulAut.conj c * diagAut b * (MulAut.conj c * diagAut b)
      = MulAut.conj c * (diagAut b * MulAut.conj c) * diagAut b := by group
    _ = MulAut.conj c * (MulAut.conj (diagAut b c) * diagAut b) * diagAut b := by
        rw [mul_conj_eq (diagAut b) c]
    _ = _ := by group

theorem diagSet_conj_inner (g : adjointGroup Tag.D4 K) {δ : MulAut (adjointGroup Tag.D4 K)}
    (h : δ ∈ diagSet K) : MulAut.conj g * δ * (MulAut.conj g)⁻¹ ∈ diagSet K := by
  obtain ⟨c, b, rfl⟩ := h
  refine ⟨g * c * diagAut b g⁻¹, b, ?_⟩
  have hinv : (MulAut.conj g)⁻¹ = MulAut.conj g⁻¹ := (map_inv MulAut.conj g).symm
  rw [hinv, map_mul, map_mul]
  calc MulAut.conj g * (MulAut.conj c * diagAut b) * MulAut.conj g⁻¹
      = MulAut.conj g * MulAut.conj c * (diagAut b * MulAut.conj g⁻¹) := by group
    _ = MulAut.conj g * MulAut.conj c * (MulAut.conj (diagAut b g⁻¹) * diagAut b) := by
      rw [mul_conj_eq (diagAut b) g⁻¹]
    _ = _ := by group

theorem diagSet_conj_of {ξ : MulAut (adjointGroup Tag.D4 K)}
    (hξ : ∀ b : Fin Tag.D4.rank → Kˣ, ∃ b', ξ * diagAut b * ξ⁻¹ = diagAut b')
    {δ : MulAut (adjointGroup Tag.D4 K)} (h : δ ∈ diagSet K) : ξ * δ * ξ⁻¹ ∈ diagSet K := by
  obtain ⟨c, b, rfl⟩ := h
  obtain ⟨b', hb'⟩ := hξ b
  refine ⟨ξ c, b', ?_⟩
  rw [← hb', ← mulAut_conj_conj]
  group

theorem diagSet_conj_normal (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    {δ : MulAut (adjointGroup Tag.D4 K)} (h : δ ∈ diagSet K) :
    exactNormalAut Tag.D4 K a σ 0 * δ * (exactNormalAut Tag.D4 K a σ 0)⁻¹ ∈ diagSet K := by
  refine diagSet_conj_of (fun b => ⟨fun j => Units.map σ.toRingHom.toMonoidHom (b j), ?_⟩) h
  rw [normal_mul_diag]
  group

theorem diagSet_conj_graph (ε : ℕ) {δ : MulAut (adjointGroup Tag.D4 K)} (h : δ ∈ diagSet K) :
    d4Graph K ε * δ * (d4Graph K ε)⁻¹ ∈ diagSet K := by
  refine diagSet_conj_of (fun b => ⟨fun j => b ((d4Rho ^ ε).symm j), ?_⟩) h
  rw [graph_mul_diag]
  group

theorem diagSet_conj_normalForm (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (ε : ℕ) {δ : MulAut (adjointGroup Tag.D4 K)} (h : δ ∈ diagSet K) :
    (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) * δ *
      (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))⁻¹ ∈ diagSet K := by
  have h1 := diagSet_conj_normal a σ (diagSet_conj_graph ε h)
  have h2 := diagSet_conj_inner g h1
  have e : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) * δ *
      (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))⁻¹ =
      MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * (d4Graph K ε * δ * (d4Graph K ε)⁻¹) *
        (exactNormalAut Tag.D4 K a σ 0)⁻¹) * (MulAut.conj g)⁻¹ := by
    simp only [mul_inv_rev]
    group
  rw [e]
  exact h2

end DSet

section Model

variable {K : Type} [Field K] [Finite K]

theorem hEA_of_card {n : ℕ} (hK : Nat.card K = 3 ^ n) :
    projectivePointFamilyAut (coordinateQuadPlus 4 K) = D4Img K := by
  have hf : 1 ≤ n := one_le_of_card_field hK
  let e0 : D4Model K ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedOmega (CFSG.Assembly.LowTwoRank.StatedQuadPlus 4 K)) :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance.statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (CFSG.LieType.Universal.Spin.quadPlus 4 K)
      (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)).symm
  have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel (D4Model K) .POmegaPlus 4 3 n :=
    ⟨⟨Nat.prime_three, hf, le_refl 4⟩, K, inferInstance, inferInstance, hK, ⟨e0⟩⟩
  exact coordinate_plus_family_eq_matrixImage hm K hK e0

theorem diagSet_mem_D4Img {n : ℕ} (hK : Nat.card K = 3 ^ n) (ψ : adjointGroup Tag.D4 K ≃* D4Model K)
    {t : MulAut (D4Model K)} (ht3 : t ^ 3 = 1) (htE : t ∉ D4Img K)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα : t = MulAut.congr ψ α)
    (hαD : ∀ δ ∈ diagSet K, α * δ * α⁻¹ ∈ diagSet K)
    (δ : MulAut (adjointGroup Tag.D4 K)) (hδ : δ ∈ diagSet K) :
    MulAut.congr ψ δ ∈ D4Img K := by
  have hEA := hEA_of_card hK
  set F := projectivePointFamily (coordinateQuadPlus 4 K) with hFdef
  have hE : ∀ {γ : MulAut (D4Model K)}, γ • F = F → γ ∈ D4Img K := by
    intro γ h
    rw [← hEA, mem_projectivePointFamilyAut_iff]
    exact h
  have hE' : ∀ {γ : MulAut (D4Model K)}, γ ∈ D4Img K → γ • F = F := by
    intro γ h
    rw [← hEA, mem_projectivePointFamilyAut_iff] at h
    exact h
  have hO0 : ∀ γ : MulAut (D4Model K),
      γ • F = F ∨ γ • F = plusCX 4 K ∨ γ • F = plusCXstar 4 K (by norm_num) := by
    intro γ
    have h := coordinate_plus_pointFamily_orbit_subset (K := K) (n := 4) rfl
      (MulAction.mem_orbit F γ)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have ht1 : t • F ≠ F := fun h => htE (hE h)
  have ht2 : (t ^ 2) • F ≠ F := by
    intro h
    apply htE
    have h2 := hE h
    have e : t = (t ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, ht3, one_mul]
    rw [e]
    exact pow_mem h2 2
  have h12 : t • F ≠ (t ^ 2) • F := by
    intro h
    apply ht1
    rw [pow_two, mul_smul] at h
    exact (MulAction.injective t h).symm
  have hO := orbit_three F _ _ t ht1 ht2 h12 hO0
  have hZ : ∀ γ ∈ Inn (D4Model K), ∀ β : MulAut (D4Model K), γ • (β • F) = β • F := by
    intro γ hγ β
    have hn : β⁻¹ * γ * β ∈ Inn (D4Model K) := by
      have := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal (D4Model K)).conj_mem γ hγ β⁻¹
      simpa using this
    have hmem : (β⁻¹ * γ * β) • F = F := by
      obtain ⟨x, hx⟩ := hn
      apply hE'
      rw [← hx]
      exact CFSG.HardMathSupport.Timmesfeld.DefChar.Orth.inner_mem_matrixProjectiveImage _ _
    calc γ • (β • F) = (γ * β) • F := (mul_smul _ _ _).symm
      _ = (β * (β⁻¹ * γ * β)) • F := by congr 1; group
      _ = β • ((β⁻¹ * γ * β) • F) := mul_smul _ _ _
      _ = β • F := by rw [hmem]
  let D : Set (MulAut (D4Model K)) := {γ | ∃ δ₀ ∈ diagSet K, γ = MulAut.congr ψ δ₀}
  have hD2 : ∀ γ ∈ D, γ * γ ∈ Inn (D4Model K) := by
    rintro _ ⟨δ₀, hδ₀, rfl⟩
    obtain ⟨y, hy⟩ := diagSet_sq hδ₀
    refine ⟨ψ y, ?_⟩
    rw [← map_mul, hy, d3f_congr_conj]
  have hDm : ∀ γ ∈ D, ∀ γ' ∈ D, γ * γ' ∈ D := by
    rintro _ ⟨δ₀, hδ₀, rfl⟩ _ ⟨δ₁, hδ₁, rfl⟩
    exact ⟨δ₀ * δ₁, diagSet_mul hδ₀ hδ₁, (map_mul _ _ _).symm⟩
  have hDt : ∀ γ ∈ D, t * γ * t⁻¹ ∈ D := by
    rintro _ ⟨δ₀, hδ₀, rfl⟩
    refine ⟨α * δ₀ * α⁻¹, hαD δ₀ hδ₀, ?_⟩
    rw [hα, map_mul, map_mul, map_inv]
  exact hE (fam_trivial F t ht3 ht1 ht2 h12 hO (Inn (D4Model K)) hZ D hD2 hDm hDt _ ⟨δ, hδ, rfl⟩)

end Model

section Eps

variable {K : Type} [Field K] [Finite K]

theorem fixE_eq_entrywiseAdjointAut (σ : K ≃+* K) : fixE σ = entrywiseAdjointAut Tag.D4 σ :=
  MulEquiv.ext fun x => Subtype.ext (by rw [coe_fixE]; rfl)

theorem eps_ne_zero {n : ℕ} (hK : Nat.card K = 3 ^ n) {t : MulAut (D4Model K)} (ht3 : t ^ 3 = 1)
    (htE : t ∉ D4Img K) (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (ht : t = MulAut.congr (coordinatePlusWitnessEquiv K (isoAdj K).symm)
      (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) : ε ≠ 0 := by
  rintro rfl
  apply htE
  set ψ := coordinatePlusWitnessEquiv K (isoAdj K).symm with hψ
  set α : MulAut (adjointGroup Tag.D4 K) :=
    MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0) with hαdef
  have hαD : ∀ δ ∈ diagSet K, α * δ * α⁻¹ ∈ diagSet K := fun δ h => diagSet_conj_normalForm g a σ 0 h
  have h1 : MulAut.congr ψ (diagAut a) ∈ D4Img K :=
    diagSet_mem_D4Img hK ψ ht3 htE α ht hαD _ ⟨1, a, by simp⟩
  have h2 : MulAut.congr ψ (fixE σ) ∈ D4Img K := by
    rw [fixE_eq_entrywiseAdjointAut]
    exact congr_entrywiseAdjointAut_mem σ
  have h3 : MulAut.congr ψ (MulAut.conj g) ∈ D4Img K := by
    rw [d3f_congr_conj]
    exact CFSG.HardMathSupport.Timmesfeld.DefChar.Orth.inner_mem_matrixProjectiveImage _ _
  have hdec : α = MulAut.conj g * (diagAut a * fixE σ) := by
    rw [hαdef, d3z_d4Graph_zero, mul_one]
    congr 1
    rw [diagAut, fixE, exactNormalAut_diag_mul, mul_one]
  rw [ht, hdec, map_mul, map_mul]
  exact mul_mem h3 (mul_mem h1 h2)

end Eps

end CFSG.LocalAnalysis.GLTheoremA
