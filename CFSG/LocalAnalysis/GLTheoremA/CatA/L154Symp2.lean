module

public import CFSG.LieType.SemisimpleCentralizers.HeldLang
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Models.PGLSimple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherNormShell
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinCore
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicSpecial
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155XSp

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial Polynomial
  CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.RankThree.Classical (spForm spEnd spLin spForm_isAlt spForm_nondegenerate spSupported
  SpPrimaryBlocks SpPairedBlock SpSelfDualBlock mem_spSupported reciprocalOrbits
  altPrimaryData_spLin symplectic_cross_prime_primary_centralizer_blocks)
open CFSG.RankThree.PartOne.KCPrimary (primaryFactors primaryComponent primaryComponent_ne_bot
  ext_primaryComponent apply_mem_primaryComponent primaryMultiplicity)
open CFSG.RankThree.PartOne.KCUnitary (blockGL blockApply blockGLDet kerImage mem_kerImage
  kerImage_eq_commutator)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.RankThree.PartOne.KCSpFull (spTransvection spEnd_spTransvection
  spTransvection_mem_spFixedFactor)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped MatrixGroups Matrix

@[expose] def L154sMarkD {r : ℕ} {K : Type} [Field K] (D : Subgroup (StatedSp r K)) : Prop :=
  ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ lab.tag ≠ .triD4 ∧ lab.tag ≠ .D ∧
    CFSG.Assembly.LargeEvenRawDatum lab fun R _ I _ => IsSimpleGroup R ∧
      ∃ Θ : ↥D →* R, Function.Surjective Θ ∧ Θ.ker ≤ Subgroup.center ↥D ∧
        ∀ α ∈ I, ∃ Q : GL (Fin r ⊕ Fin r) K, ∀ g : ↥D, ∃ g' : ↥D,
          ((g' : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
            Q * ((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * Q⁻¹ ∧ α (Θ g) = Θ g'

@[expose] def L154sKLine {r : ℕ} {K : Type} [Field K] (D : Subgroup (StatedSp r K)) : Prop :=
  ∃ N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, N ≠ 0 ∧ ∀ c : K, ∃ t ∈ D,
    (((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      1 + c • N

theorem l154s_false_of_conj_kline {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (D : Set (GL ι K)) (B Q : GL ι K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (h : ∀ g ∈ D, B * glMap σ g * B⁻¹ = Q * g * Q⁻¹)
    (N : Matrix ι ι K) (hN : N ≠ 0)
    (hT : ∀ c : K, ∃ t ∈ D, ((t : GL ι K) : Matrix ι ι K) = 1 + c • N) : False := by
  have hBB : (B : Matrix ι ι K) * ((B⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQQ : (Q : Matrix ι ι K) * ((Q⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQQ' : ((Q⁻¹ : GL ι K) : Matrix ι ι K) * (Q : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set X : Matrix ι ι K := (B : Matrix ι ι K) * N.map σ * ((B⁻¹ : GL ι K) : Matrix ι ι K) with hX
  set Y : Matrix ι ι K := (Q : Matrix ι ι K) * N * ((Q⁻¹ : GL ι K) : Matrix ι ι K) with hY
  have hmat : ∀ c : K, σ c • X = c • Y := by
    intro c
    obtain ⟨t, ht, hιt⟩ := hT c
    have h2 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (h t ht)
    have hγt : ((B * glMap σ t * B⁻¹ : GL ι K) : Matrix ι ι K) = 1 + σ c • X := by
      have e1 : ((glMap σ t : GL ι K) : Matrix ι ι K) = 1 + σ c • N.map σ := by
        rw [coe_glMap, hιt]
        ext i j
        simp [Matrix.one_apply, apply_ite σ]
      rw [Units.val_mul, Units.val_mul, e1, hX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBB,
        Matrix.mul_smul, Matrix.smul_mul]
    have hκt : ((Q * t * Q⁻¹ : GL ι K) : Matrix ι ι K) = 1 + c • Y := by
      rw [Units.val_mul, Units.val_mul, hιt, hY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        hQQ, Matrix.mul_smul, Matrix.smul_mul]
    rw [hγt, hκt] at h2
    exact add_left_cancel h2
  have hXY : X = Y := by
    have := hmat 1
    rwa [map_one, one_smul, one_smul] at this
  have hY0 : Y ≠ 0 := by
    intro h0
    apply hN
    have e : ((Q⁻¹ : GL ι K) : Matrix ι ι K) * Y * (Q : Matrix ι ι K) = N := by
      rw [hY]
      calc ((Q⁻¹ : GL ι K) : Matrix ι ι K) * ((Q : Matrix ι ι K) * N *
            ((Q⁻¹ : GL ι K) : Matrix ι ι K)) * (Q : Matrix ι ι K)
          = (((Q⁻¹ : GL ι K) : Matrix ι ι K) * (Q : Matrix ι ι K)) * N *
            (((Q⁻¹ : GL ι K) : Matrix ι ι K) * (Q : Matrix ι ι K)) := by
            simp only [Matrix.mul_assoc]
        _ = N := by rw [hQQ', Matrix.one_mul, Matrix.mul_one]
    rw [← e, h0, Matrix.mul_zero, Matrix.zero_mul]
  apply hσ
  ext c
  have h1 := hmat c
  rw [hXY] at h1
  have h2 : (σ c - c) • Y = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · exact absurd h3 hY0

theorem l154s_marking_of_hom {r : ℕ} {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {E : Type} [Field E] (A D : Subgroup (StatedSp r K)) (hDA : D ≤ A)
    (hDn : ∀ a ∈ A, ∀ g ∈ D, a * g * a⁻¹ ∈ D)
    (H : Subgroup (GL ι E)) (ε : ↥A →* GL ι E) (hεinj : Function.Injective ε)
    (hεD : ∀ g : ↥A, (g : StatedSp r K) ∈ D ↔ ε g ∈ H)
    (hεH : ∀ M ∈ H, ∃ g : ↥A, ε g = M)
    (G : Set (GL ι E))
    (hG : ∀ P ∈ G, ∃ (a : ↥A) (z : Eˣ), P = Matrix.GeneralLinearGroup.scalar ι z * ε a) :
    ∃ Θ : ↥D →* LargeEvenProj H, Function.Surjective Θ ∧ Θ.ker ≤ Subgroup.center ↥D ∧
      ∀ α ∈ LargeEvenMatConjImage (LargeEvenProjMk H) G, ∃ Q : GL (Fin r ⊕ Fin r) K,
        ∀ g : ↥D, ∃ g' : ↥D,
          (((g' : StatedSp r K) : GL (Fin r ⊕ Fin r) K)) =
            Q * ((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * Q⁻¹ ∧ α (Θ g) = Θ g' := by
  let εD : ↥D →* ↥H := MonoidHom.codRestrict (ε.comp (Subgroup.inclusion hDA)) H
    (fun g => (hεD (Subgroup.inclusion hDA g)).1 g.2)
  have hεD_apply : ∀ g : ↥D, ((εD g : ↥H) : GL ι E) = ε (Subgroup.inclusion hDA g) := fun g => rfl
  refine ⟨(LargeEvenProjMk H).comp εD, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨g, hg⟩ := hεH M M.2
    have hgD : (g : StatedSp r K) ∈ D := (hεD g).2 (hg ▸ M.2)
    refine ⟨⟨g, hgD⟩, ?_⟩
    have : εD ⟨g, hgD⟩ = M := Subtype.ext (by rw [hεD_apply]; exact hg)
    simp only [MonoidHom.comp_apply, this]
    rfl
  · intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
    have hmem : εD g ∈ (LargeEvenScalars ι E).subgroupOf H := (QuotientGroup.eq_one_iff _).1 hg
    rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at hmem
    obtain ⟨z, hz⟩ := hmem
    refine Subgroup.mem_center_iff.2 fun g' => ?_
    have h1 : ε (Subgroup.inclusion hDA g) = Matrix.GeneralLinearGroup.scalar ι z := by
      rw [← hεD_apply, hz]
    have h2 : ε (Subgroup.inclusion hDA (g' * g)) = ε (Subgroup.inclusion hDA (g * g')) := by
      rw [map_mul, map_mul, map_mul, map_mul, h1]
      exact (Matrix.GeneralLinearGroup.scalar_commute _ _).symm
    exact Subgroup.inclusion_injective hDA (hεinj h2)
  · rintro α ⟨P, hP, hgraph⟩
    obtain ⟨a, z, rfl⟩ := hG P hP
    refine ⟨((a : StatedSp r K) : GL (Fin r ⊕ Fin r) K), fun g => ?_⟩
    have hmem : (a : StatedSp r K) * (g : StatedSp r K) * (a : StatedSp r K)⁻¹ ∈ D :=
      hDn _ a.2 _ g.2
    refine ⟨⟨_, hmem⟩, rfl, ?_⟩
    simp only [MonoidHom.comp_apply]
    apply hgraph
    rw [hεD_apply, hεD_apply]
    have e1 : Subgroup.inclusion hDA ⟨_, hmem⟩ = a * Subgroup.inclusion hDA g * a⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv]
    have hc := Matrix.GeneralLinearGroup.scalar_commute (n := ι) z
      (ε a * ε (Subgroup.inclusion hDA g) * (ε a)⁻¹)
    calc ε a * ε (Subgroup.inclusion hDA g) * (ε a)⁻¹
        = ε a * ε (Subgroup.inclusion hDA g) * (ε a)⁻¹ * Matrix.GeneralLinearGroup.scalar ι z *
            (Matrix.GeneralLinearGroup.scalar ι z)⁻¹ := by group
      _ = Matrix.GeneralLinearGroup.scalar ι z * (ε a * ε (Subgroup.inclusion hDA g) * (ε a)⁻¹) *
            (Matrix.GeneralLinearGroup.scalar ι z)⁻¹ := by rw [hc]
      _ = _ := by group

theorem l154s_kline_of_lin {r : ℕ} {K : Type} [Field K] {D : Subgroup (StatedSp r K)}
    (N : Module.End K (Fin r ⊕ Fin r → K)) (hN : N ≠ 0)
    (h : ∀ c : K, ∃ t ∈ D, spEnd t = 1 + c • N) : L154sKLine D := by
  refine ⟨LinearMap.toMatrix' N, fun h0 => hN ?_, fun c => ?_⟩
  · exact LinearMap.toMatrix'.injective (by rw [h0, map_zero])
  · obtain ⟨t, ht, htc⟩ := h c
    refine ⟨t, ht, ?_⟩
    have e : spEnd t = Matrix.toLin' (((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := rfl
    have := congrArg LinearMap.toMatrix' (e.symm.trans htc)
    rw [LinearMap.toMatrix'_toLin', map_add, map_smul, LinearMap.toMatrix'_one] at this
    exact this

theorem l154s_kline_spTransvection {r : ℕ} {K : Type} [Field K] {D : Subgroup (StatedSp r K)}
    {u : Fin r ⊕ Fin r → K} (hu : u ≠ 0) (hD : ∀ c : K, spTransvection u c ∈ D) :
    L154sKLine D := by
  let N : Module.End K (Fin r ⊕ Fin r → K) := LinearMap.smulRight ((spForm r K).flip u) u
  have hN : ∀ y, N y = spForm r K y u • u := fun y => rfl
  refine l154s_kline_of_lin N ?_ fun c => ⟨spTransvection u c, hD c, ?_⟩
  · intro h0
    obtain ⟨y, hy⟩ : ∃ y, spForm r K y u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (spForm_nondegenerate.2 u hcon)
    have := congrArg (fun f : Module.End K (Fin r ⊕ Fin r → K) => f y) h0
    simp only [hN, LinearMap.zero_apply] at this
    exact hy ((smul_eq_zero.1 this).resolve_right hu)
  · refine LinearMap.ext fun y => ?_
    rw [spEnd_spTransvection, LinearMap.add_apply, LinearMap.smul_apply, hN, Module.End.one_apply,
      smul_smul]

theorem l154s_gspSet_decomp {s : ℕ} {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0)
    {P : GL (Fin s ⊕ Fin s) K} (hP : P ∈ LargeEvenGSpSet K s) :
    ∃ (z : Kˣ) (P₀ : GL (Fin s ⊕ Fin s) K), P₀ ∈ StatedSp s K ∧
      P = Matrix.GeneralLinearGroup.scalar (Fin s ⊕ Fin s) z * P₀ := by
  classical
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨μ, hμ, hPμ⟩ := hP
  obtain ⟨b, hb⟩ : ∃ b : K, μ = b * b :=
    FiniteField.isSquare_of_char_two (ringChar.eq (R := K) 2) μ
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hμ (by simpa using hb)
  let z : Kˣ := Units.mk0 b hb0
  have hP₀ : (((Matrix.GeneralLinearGroup.scalar (Fin s ⊕ Fin s) z⁻¹ * P : GL (Fin s ⊕ Fin s) K)) :
      Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) K) =
        b⁻¹ • (P : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) K) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
    simp [z]
  refine ⟨z, Matrix.GeneralLinearGroup.scalar _ z⁻¹ * P, ?_, ?_⟩
  · rw [StatedAPI.mem_statedSp_iff, hP₀]
    have hJ : LargeEvenSpForm K s = Matrix.fromBlocks 0 1 (-1) 0 := rfl
    rw [hJ] at hPμ
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hPμ, smul_smul,
      smul_smul, hb]
    have : b⁻¹ * b⁻¹ * (b * b) = 1 := by field_simp
    rw [this, one_smul]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem l154s_gl2_decomp {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0) (P : GL (Fin 2) F) :
    ∃ (z : Fˣ) (P₀ : GL (Fin 2) F), P₀ ∈ LargeEvenSLGroup (Fin 2) F ∧
      P = Matrix.GeneralLinearGroup.scalar (Fin 2) z * P₀ := by
  classical
  haveI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨b, hb⟩ : ∃ b : F, (P : Matrix (Fin 2) (Fin 2) F).det = b * b :=
    FiniteField.isSquare_of_char_two (ringChar.eq (R := F) 2) _
  have hb0 : b ≠ 0 := by
    rintro rfl
    have := P.det_ne_zero
    exact (Matrix.GeneralLinearGroup.det_ne_zero P) (by simpa using hb)
  let z : Fˣ := Units.mk0 b hb0
  have hP₀ : (((Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ * P : GL (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F) = b⁻¹ • (P : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
    simp [z]
  refine ⟨z, Matrix.GeneralLinearGroup.scalar _ z⁻¹ * P, ?_, ?_⟩
  · rw [largeEvenSLGroup_eq_statedSL, StatedAPI.mem_statedSL_iff, hP₀, Matrix.det_smul, hb,
      Fintype.card_fin]
    field_simp
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem l154s_marking_of_equiv {r : ℕ} {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {E : Type} [Field E] (D : Subgroup (StatedSp r K)) (H : Subgroup (GL ι E)) (ε₀ : ↥D ≃* ↥H)
    (G : Set (GL ι E))
    (hG : ∀ P ∈ G, ∃ (z : Eˣ) (P₀ : GL ι E), P₀ ∈ H ∧
      P = Matrix.GeneralLinearGroup.scalar ι z * P₀) :
    ∃ Θ : ↥D →* LargeEvenProj H, Function.Surjective Θ ∧ Θ.ker ≤ Subgroup.center ↥D ∧
      ∀ α ∈ LargeEvenMatConjImage (LargeEvenProjMk H) G, ∃ Q : GL (Fin r ⊕ Fin r) K,
        ∀ g : ↥D, ∃ g' : ↥D,
          (((g' : StatedSp r K) : GL (Fin r ⊕ Fin r) K)) =
            Q * ((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * Q⁻¹ ∧ α (Θ g) = Θ g' := by
  refine l154s_marking_of_hom D D le_rfl
    (fun a ha g hg => D.mul_mem (D.mul_mem ha hg) (D.inv_mem ha)) H
    (H.subtype.comp ε₀.toMonoidHom) (Subtype.val_injective.comp ε₀.injective)
    (fun g => ⟨fun _ => (ε₀ g).2, fun _ => g.2⟩) (fun M hM => ⟨ε₀.symm ⟨M, hM⟩, by simp⟩) G ?_
  intro P hP
  obtain ⟨z, P₀, hP₀, rfl⟩ := hG P hP
  exact ⟨ε₀.symm ⟨P₀, hP₀⟩, z, by simp⟩

theorem l154s_markD_sp {r : ℕ} {K : Type} [Field K] {D : Subgroup (StatedSp r K)} {s k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ k) (hk : 2 ≤ k) (hs : 2 ≤ s)
    (ε₀ : ↥D ≃* ↥(StatedSp s F)) : L154sMarkD D := by
  have h2 : (2 : F) = 0 := by
    have := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := k) (by rw [← Nat.card_eq_fintype_card, hF])
    exact_mod_cast CharP.cast_eq_zero F 2
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  refine ⟨⟨.C, s, k⟩, ⟨show 1 ≤ k by omega, hs, fun _ => hk⟩, by simp, by simp, ?_⟩
  refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
  refine ⟨CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F s (by omega)
    (Or.inl (Or.inr hF4)), ?_⟩
  exact l154s_marking_of_equiv D (LargeEvenSpGroup F s) ε₀ (LargeEvenGSpSet F s)
    (fun P hP => l154s_gspSet_decomp h2 hP)

theorem l154s_markD_sl2 {r : ℕ} {K : Type} [Field K] {D : Subgroup (StatedSp r K)} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ k) (hk : 2 ≤ k)
    (ε₀ : ↥D ≃* SL(2, F)) : L154sMarkD D := by
  have h2 : (2 : F) = 0 := by
    have := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := k) (by rw [← Nat.card_eq_fintype_card, hF])
    exact_mod_cast CharP.cast_eq_zero F 2
  have hF2 : Nat.card F ≠ 2 := by
    rw [hF]
    intro h
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hF3 : Nat.card F ≠ 3 := by
    rw [hF]
    intro h
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hsimp : ∀ H : Subgroup (GL (Fin 2) F), H = StatedSL 2 F →
      IsSimpleGroup (LargeEvenProj H) := by
    rintro H rfl
    exact CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F le_rfl (Or.inr hF2) (Or.inr hF3)
  refine ⟨⟨.A, 1, k⟩, ⟨show 1 ≤ k by omega, le_rfl, fun _ => hk⟩, by simp, by simp, ?_⟩
  refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
  refine ⟨hsimp _ (largeEvenSLGroup_eq_statedSL 2), ?_⟩
  exact l154s_marking_of_equiv D (LargeEvenSLGroup (Fin 2) F)
    (ε₀.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).trans
      (MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL 2).symm))) Set.univ
    (fun P _ => l154s_gl2_decomp h2 P)

theorem l154s_markD_top {r : ℕ} {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hr : 2 ≤ r) :
    L154sMarkD (⊤ : Subgroup (StatedSp r K)) :=
  l154s_markD_sp hK hn hr Subgroup.topEquiv

theorem l154s_kline_top {r : ℕ} {K : Type} [Field K] (hr : 1 ≤ r) :
    L154sKLine (⊤ : Subgroup (StatedSp r K)) := by
  refine l154s_kline_spTransvection (u := Pi.single (Sum.inl ⟨0, hr⟩) 1) ?_
    fun _ => Subgroup.mem_top _
  intro h
  have := congrFun h (Sum.inl ⟨0, hr⟩)
  simp at this
theorem l154s_fixed_block {r : ℕ} {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (blocks : SpPrimaryBlocks 2 n p x a) (hsq : Squarefree (minpoly K (spEnd x)))
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) :
    ⁅spSupported x {X - 1}, spSupported x {X - 1}⁆ = spSupported x {X - 1} ∧
      CFSG.IsQuasisimple ↥(spSupported x {X - 1}) ∧ L154sKLine (spSupported x {X - 1}) ∧
      L154sMarkD (spSupported x {X - 1}) := by
  set V₁ := primaryComponent (spEnd x) (X - 1) with hV₁
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨φ, hφ⟩ := blocks.fixedFactor hmem
  have hBalt : ((spForm r K).restrict V₁).IsAlt :=
    fun z => spForm_isAlt.self_eq_zero (z : Fin r ⊕ Fin r → K)
  have hnd := blocks.fixed_nondegenerate
  have hnt : V₁ ≠ ⊥ := primaryComponent_ne_bot hsq hmem
  obtain ⟨s, hs, ⟨ψ⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hBalt hnd
  have hpos : 0 < Module.finrank K V₁ := by
    rw [Module.finrank_pos_iff]
    exact Submodule.nontrivial_iff_ne_bot.mpr hnt
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, mul_zero] at hs
      omega
    · exact h0
  have hdim : 2 ≤ Module.finrank K V₁ := by rw [hs]; omega
  have hQS : CFSG.IsQuasisimple ↥(spSupported x {X - 1}) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
      (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hBalt hnd
        hdim (Or.inl hK4))
  refine ⟨CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect hQS.1, hQS, ?_, ?_⟩
  ·
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnt
    have hxu : spEnd x u = u := by
      have h1 : u ∈ LinearMap.ker (spEnd x - 1) := blocks.fixed_eq ▸ hu
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
      exact h1
    exact l154s_kline_spTransvection hu0 fun c => spTransvection_mem_spFixedFactor hxu c
  · rcases Nat.lt_or_ge s 2 with hs2 | hs2
    · obtain rfl : s = 1 := by omega
      exact l154s_markD_sl2 hK hn ((φ.trans ψ).trans
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm)
    · exact l154s_markD_sp hK hn hs2 (φ.trans ψ)

theorem l154s_toLin'_transvec_apply {E : Type} {W : Type*} [Field E] [AddCommGroup W]
    [Module E W] {m : ℕ} (b : Module.Basis (Fin m) E W) (i j : Fin m) (hij : i ≠ j) (c : E)
    (v : W) :
    ((Matrix.GeneralLinearGroup.toLin' b (K155X.l154TransvecGL i j hij c) :
      LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) v = v + (c * b.repr v j) • b i := by
  rw [CFSG.RankThree.CentralLift.toLin'_basis_apply]
  have hM : ((K155X.l154TransvecGL i j hij c : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      Matrix.transvection i j c := rfl
  rw [hM, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, map_add,
    LinearEquiv.symm_apply_apply, Matrix.single_mulVec]
  congr 1
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Module.Basis.equivFun_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Function.update_of_ne hk, Pi.zero_apply, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem l154s_conj_mem_commutator {G : Type*} [Group G] {A : Subgroup G} {a g : G} (ha : a ∈ A)
    (hg : g ∈ ⁅A, A⁆) : a * g * a⁻¹ ∈ ⁅A, A⁆ := by
  have hmap : A.map (MulAut.conj a).toMonoidHom = A := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact A.mul_mem (A.mul_mem ha hz) (A.inv_mem ha)
    · intro hy
      refine ⟨a⁻¹ * y * a, A.mul_mem (A.mul_mem (A.inv_mem ha) hy) ha, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have h1 : (⁅A, A⁆).map (MulAut.conj a).toMonoidHom = ⁅A, A⁆ := by
    rw [Subgroup.map_commutator, hmap]
  have h2 : (MulAut.conj a).toMonoidHom g ∈ (⁅A, A⁆).map (MulAut.conj a).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hg
  rw [h1] at h2
  exact h2

theorem l154s_not_isQuasisimple_commutator {G : Type*} [Group G] {A : Subgroup G}
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : ¬ CFSG.IsQuasisimple ↥⁅A, A⁆ := by
  intro hq
  obtain ⟨-, -, a, b, hne⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hne
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  have hle : ⁅A, A⁆ ≤ A := Subgroup.commutator_le_self A
  congr 1
  exact Subtype.ext (hab _ (hle a.2) _ (hle b.2))

theorem l154s_paired_block {r n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) {x : StatedSp r K} (hsq : Squarefree (minpoly K (spEnd x)))
    {h : primaryFactors (spEnd x)} (hP : SpPairedBlock 2 n p x h)
    (hq : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆) :
    L154sKLine ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ ∧
    L154sMarkD ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ := by
  classical
  set A := spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} with hA
  set E := AdjoinRoot (h : K[X])
  set W := primaryComponent (spEnd x) (h : K[X])
  obtain ⟨φ, hφ, hform⟩ := hP.factor
  have hdeg : 1 ≤ (h : K[X]).natDegree := Irreducible.natDegree_pos
    (CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors h.2)
  have hEcard : Nat.card E = 2 ^ (n * (h : K[X]).natDegree) := by
    rw [hP.card_field, pow_mul]
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n * (h : K[X]).natDegree) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hm : 2 ≤ Module.finrank E W := by
    by_contra hlt
    have hlt' : Module.finrank E W ≤ 1 := by omega
    refine l154s_not_isQuasisimple_commutator (A := A) (fun a ha b hb => ?_) hq
    have h1 : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ := by
      apply Units.ext
      exact (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one hlt' _ _).eq
    have h2 : (⟨a, ha⟩ : ↥A) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, h1]
    exact congrArg Subtype.val h2
  have hperf : Group.IsPerfect (blockGLDet (spEnd x) (h : K[X])).ker :=
    (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_ker_det hm
      (Or.inr (CFSG.RankThree.PartOne.KCSpIsotypic.exists_finset_card_four_of_card hE4))).1
  have hD : kerImage A φ (blockGLDet (spEnd x) (h : K[X])) = ⁅A, A⁆ :=
    kerImage_eq_commutator A φ _ hperf
  set m' := Module.finrank E W - 1 with hm'
  have hmm : Module.finrank E W = m' + 1 := by omega
  let b : Module.Basis (Fin (m' + 1)) E W := (Module.finBasis E W).reindex (finCongr hmm)
  let T : GL (Fin (m' + 1)) E ≃* blockGL (spEnd x) (h : K[X]) := Matrix.GeneralLinearGroup.toLin' b
  let ε : ↥A →* GL (Fin (m' + 1)) E := T.symm.toMonoidHom.comp φ.toMonoidHom
  have hεinj : Function.Injective ε := T.symm.injective.comp φ.injective
  have hdetT : ∀ M : GL (Fin (m' + 1)) E,
      LinearMap.det ((T M : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) =
        (M : Matrix (Fin (m' + 1)) (Fin (m' + 1)) E).det :=
    fun M => CFSG.RankThree.CentralLift.det_toLin'_basis b M
  have hεD : ∀ g : ↥A, (g : StatedSp r K) ∈ ⁅A, A⁆ ↔ ε g ∈ LargeEvenSLGroup (Fin (m' + 1)) E := by
    intro g
    rw [← hD, mem_kerImage, largeEvenSLGroup_eq_statedSL, StatedAPI.mem_statedSL_iff]
    have e1 : ((T (ε g) : LinearMap.GeneralLinearGroup E W)) = φ g := T.apply_symm_apply _
    constructor
    · rintro ⟨hg, hdet⟩
      have hdet' := congrArg Units.val hdet
      rw [← hdetT, e1]
      simpa [blockGLDet] using hdet'
    · intro hdet
      refine ⟨g.2, ?_⟩
      apply Units.ext
      rw [← hdetT, e1] at hdet
      simpa [blockGLDet] using hdet
  have hεH : ∀ M ∈ LargeEvenSLGroup (Fin (m' + 1)) E, ∃ g : ↥A, ε g = M :=
    fun M _ => ⟨φ.symm (T M), by simp [ε]⟩
  have h01 : (⟨0, by omega⟩ : Fin (m' + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set i0 : Fin (m' + 1) := ⟨0, by omega⟩
  set i1 : Fin (m' + 1) := ⟨1, by omega⟩
  let tg : K → ↥A := fun c => φ.symm (T (K155X.l154TransvecGL i0 i1 h01 (algebraMap K E c)))
  have htgD : ∀ c, ((tg c : ↥A) : StatedSp r K) ∈ ⁅A, A⁆ := by
    intro c
    rw [hεD]
    have : ε (tg c) = K155X.l154TransvecGL i0 i1 h01 (algebraMap K E c) := by simp [ε, tg]
    rw [this, largeEvenSLGroup_eq_statedSL]
    exact K155X.l154TransvecGL_mem i0 i1 h01 _
  let NV : W → (Fin r ⊕ Fin r → K) := fun v => ((b.repr v i1 • b i0 : W) : Fin r ⊕ Fin r → K)
  have hact : ∀ (c : K) (v : W), spEnd ((tg c : ↥A) : StatedSp r K) (v : Fin r ⊕ Fin r → K) =
      (v : Fin r ⊕ Fin r → K) + c • NV v := by
    intro c v
    rw [← hφ (tg c) v v.2]
    have e1 : φ (tg c) = T (K155X.l154TransvecGL i0 i1 h01 (algebraMap K E c)) := by simp [tg]
    rw [e1]
    change ((((T (K155X.l154TransvecGL i0 i1 h01 (algebraMap K E c)) :
      LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) v : W) : Fin r ⊕ Fin r → K) = _
    rw [l154s_toLin'_transvec_apply b i0 i1 h01, ← smul_smul, Submodule.coe_add,
      CFSG.RankThree.PartOne.KCPrimary.coe_algebraMap_smul_primaryComponent]
  let NW : W →ₗ[E] W := (b.coord i1).smulRight (b i0)
  have hNW : ∀ v : W, NW v = b.repr v i1 • b i0 := fun v => rfl
  have hNV : ∀ v : W, NV v = ((NW v : W) : Fin r ⊕ Fin r → K) := fun v => rfl
  have hNN : ∀ v : W, NW (NW v) = 0 := by
    intro v
    rw [hNW, hNW, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne h01.symm, smul_zero, zero_smul]
  have hcomm : ∀ g : ↥A, Commute (spEnd (g : StatedSp r K)) (spEnd x) := by
    intro g
    have h1 := (mem_spSupported.mp g.2).1
    have h2 := congrArg spEnd h1
    rw [CFSG.RankThree.PartOne.KCSpFull.spEnd_mul, CFSG.RankThree.PartOne.KCSpFull.spEnd_mul] at h2
    exact h2
  set M : Module.End K (Fin r ⊕ Fin r → K) := spEnd ((tg 1 : ↥A) : StatedSp r K) - 1 with hMdef
  have hglob : ∀ c : K, spEnd ((tg c : ↥A) : StatedSp r K) = 1 + c • M := by
    intro c
    refine ext_primaryComponent hsq fun a ha v hv => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply, hMdef, LinearMap.sub_apply,
      Module.End.one_apply]
    by_cases hah : a = h
    · subst hah
      rw [hact c ⟨v, hv⟩, hact 1 ⟨v, hv⟩, one_smul, add_sub_cancel_left]
    by_cases har : a = reciprocalPolynomial (h : K[X])
    · subst har
      set w := v
      set Dc : Fin r ⊕ Fin r → K := spEnd ((tg c : ↥A) : StatedSp r K) w - w -
        c • (spEnd ((tg 1 : ↥A) : StatedSp r K) w - w) with hDc
      have hmemw : ∀ g : ↥A, spEnd (g : StatedSp r K) w ∈
          primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])) :=
        fun g => apply_mem_primaryComponent (hcomm g) hv
      have hDmem : Dc ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])) :=
        Submodule.sub_mem _ (Submodule.sub_mem _ (hmemw _) hv)
          (Submodule.smul_mem _ c (Submodule.sub_mem _ (hmemw _) hv))
      have hpair : ∀ (c' : K) (u : W), spForm r K (u : Fin r ⊕ Fin r → K)
          (spEnd ((tg c' : ↥A) : StatedSp r K) w) =
            spForm r K (u : Fin r ⊕ Fin r → K) w - c' * spForm r K (NV u) w := by
        intro c' u
        set u' : W := u - c' • NW u with hu'
        have hu'act : spEnd ((tg c' : ↥A) : StatedSp r K) (u' : Fin r ⊕ Fin r → K) =
            (u : Fin r ⊕ Fin r → K) := by
          rw [hact c' u', hNV, hu', map_sub, LinearMap.map_smul_of_tower, hNN, smul_zero,
            sub_zero, Submodule.coe_sub, Submodule.coe_smul, sub_add_cancel]
        have h1 := hform (tg c') (u' : Fin r ⊕ Fin r → K) w u'.2 hv
        rw [hφ (tg c') _ u'.2, hu'act] at h1
        rw [h1, hu', Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul,
          LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hNV]
      have hD0 : Dc = 0 := by
        refine hP.perfect_right Dc hDmem fun u hu => ?_
        have h1 := hpair c ⟨u, hu⟩
        have h2 := hpair 1 ⟨u, hu⟩
        rw [hDc, map_sub, map_sub, map_smul, map_sub, smul_eq_mul]
        simp only at h1 h2
        rw [h1, h2]
        ring
      rw [hDc, sub_sub, sub_eq_zero] at hD0
      rw [hD0]
    ·
      have hnot : a ∉ ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) := by
        rintro (h1 | h1)
        · exact hah h1
        · exact har h1
      rw [(mem_spSupported.mp (tg c).2).2 a ha hnot v hv,
        (mem_spSupported.mp (tg 1).2).2 a ha hnot v hv, sub_self, smul_zero, add_zero]
  have hM0 : M ≠ 0 := by
    intro h0
    have h1 := congrArg (fun f : Module.End K (Fin r ⊕ Fin r → K) => f ((b i1 : W) :
      Fin r ⊕ Fin r → K)) h0
    simp only [hMdef, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply] at h1
    rw [hact 1 (b i1), one_smul, add_sub_cancel_left, hNV, hNW, Module.Basis.repr_self,
      Finsupp.single_eq_same, one_smul] at h1
    exact b.ne_zero i0 (Subtype.ext h1)
  refine ⟨l154s_kline_of_lin M hM0 fun c => ⟨_, htgD c, hglob c⟩, ?_⟩
  have hk2 : 2 ≤ n * (h : K[X]).natDegree := by nlinarith
  have hE2 : Nat.card E ≠ 2 := by omega
  have hE3 : Nat.card E ≠ 3 := by omega
  have hsimp : ∀ H : Subgroup (GL (Fin (m' + 1)) E), H = StatedSL (m' + 1) E →
      IsSimpleGroup (LargeEvenProj H) := by
    rintro H rfl
    exact CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL E (by omega) (Or.inr hE2)
      (Or.inr hE3)
  refine ⟨⟨.A, m', n * (h : K[X]).natDegree⟩, ⟨show 1 ≤ n * (h : K[X]).natDegree by omega,
    show 1 ≤ m' by omega, fun _ => hk2⟩, by simp, by simp, ?_⟩
  refine ⟨E, inferInstance, inferInstance, hEcard, hsimp _ (largeEvenSLGroup_eq_statedSL _), ?_⟩
  exact l154s_marking_of_hom A ⁅A, A⁆ (Subgroup.commutator_le_self A)
    (fun a ha g hg => l154s_conj_mem_commutator ha hg) _ ε hεinj hεD hεH Set.univ
    (fun P _ => ⟨φ.symm (T P), 1, by simp [ε]⟩)

theorem l154s_eq_one_of_sq_eq_one {E : Type*} [Field E] (h2 : (2 : E) = 0) {a : E}
    (ha : a * a = 1) : a = 1 := by
  have h1 : (a - 1) * (a - 1) = 0 := by linear_combination ha + (1 - a) * h2
  exact sub_eq_zero.1 (mul_self_eq_zero.1 h1)

theorem l154s_unitary_transvection {E : Type*} [Field E] {W : Type*} [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {σ : E →+* E} {Hf : W →ₛₗ[σ] W →ₗ[E] E}
    (hHf : Hf.IsSymm) (h2 : (2 : E) = 0) {u : W} (huu : Hf u u = 0) {a : E} (ha : σ a = a) :
    (1 + a • (Hf u).smulRight u) * (1 + a • (Hf u).smulRight u) = 1 ∧
      (∀ v w, Hf ((1 + a • (Hf u).smulRight u) v) ((1 + a • (Hf u).smulRight u) w) = Hf v w) ∧
      LinearMap.det (1 + a • (Hf u).smulRight u) = 1 := by
  set N : W →ₗ[E] W := (Hf u).smulRight u with hN
  have hNv : ∀ v, N v = Hf u v • u := fun v => rfl
  have hinv : (1 + a • N) * (1 + a • N) = 1 := by
    refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, hNv, map_add, map_smul, huu, smul_eq_mul, mul_zero, zero_smul,
      smul_zero, add_zero, smul_add]
    rw [add_assoc, ← add_smul, ← two_mul, h2, zero_mul, zero_smul, add_zero]
  refine ⟨hinv, fun v w => ?_, ?_⟩
  · simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, hNv, map_add,
      map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, huu, smul_eq_mul, map_mul, ha]
    have hs : σ (Hf u v) = Hf v u := hHf.eq u v
    rw [hs]
    linear_combination (a * (Hf u w * Hf v u)) * h2
  · have h1 := congrArg LinearMap.det hinv
    rw [map_mul, map_one] at h1
    exact l154s_eq_one_of_sq_eq_one h2 h1

theorem l154s_guSet_decomp {E : Type} [Field E] {f' : ℕ} (hE : UnitaryFieldData 2 f' E) {k : ℕ}
    {P : GL (Fin k) E} (hP : P ∈ LargeEvenGUSet (Fin k) E (2 ^ f')) :
    ∃ (z : Eˣ) (P₁ : GL (Fin k) E),
      ((P₁ : Matrix (Fin k) (Fin k) E).map hE.bar)ᵀ * (P₁ : Matrix (Fin k) (Fin k) E) = 1 ∧
        P = Matrix.GeneralLinearGroup.scalar (Fin k) z * P₁ := by
  obtain ⟨μ, hμ0, hμq, hPμ⟩ := hP
  have hbar : ∀ c : E, hE.bar c = c ^ 2 ^ f' := fun c => hE.bar_apply c
  have hμbar : hE.bar μ = μ := by rw [hbar]; exact hμq
  obtain ⟨l, hl⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_norm_eq hE hμbar
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hμ0
    rw [← hl]
    simp [UnitaryFieldData.norm]
  let z : Eˣ := Units.mk0 l hl0
  have hP₁ : (((Matrix.GeneralLinearGroup.scalar (Fin k) z⁻¹ * P : GL (Fin k) E)) :
      Matrix (Fin k) (Fin k) E) = l⁻¹ • (P : Matrix (Fin k) (Fin k) E) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
    simp [z]
  refine ⟨z, Matrix.GeneralLinearGroup.scalar (Fin k) z⁻¹ * P, ?_, ?_⟩
  · rw [hP₁]
    have hmap : (l⁻¹ • (P : Matrix (Fin k) (Fin k) E)).map hE.bar =
        hE.bar l⁻¹ • (P : Matrix (Fin k) (Fin k) E).map (· ^ 2 ^ f') := by
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply, hbar, mul_pow]
    rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hPμ, smul_smul, smul_smul]
    have hnorm : l * hE.bar l = μ := hl
    have : hE.bar l⁻¹ * l⁻¹ * μ = 1 := by
      rw [map_inv₀, ← hnorm]
      have hbl : hE.bar l ≠ 0 := by
        intro h0
        apply hμ0
        rw [← hnorm, h0, mul_zero]
      field_simp
    rw [this, one_smul]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem l154s_su_mem_iff {E : Type} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {f' : ℕ}
    (hE : UnitaryFieldData 2 f' E) {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} {k : ℕ}
    (e : Module.Basis (Fin (k + 1)) E W)
    (he : ∀ i j, Hf (e i) (e j) = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) E) i j)
    (M : GL (Fin (k + 1)) E) :
    M ∈ LargeEvenSUGroup (Fin (k + 1)) E (2 ^ f') ↔
      Matrix.GeneralLinearGroup.toLin' e M ∈ sesqSpecialUnitaryGroup Hf := by
  have h1 : M ∈ LargeEvenSUGroup (Fin (k + 1)) E (2 ^ f') ↔
      M ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f' E (k + 1) := Iff.rfl
  rw [h1, CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU hE (k + 1)]
  exact (CFSG.RankThree.CentralLift.toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU hE e he M).symm

theorem l154s_su_unitary {E : Type} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {f' : ℕ}
    (hE : UnitaryFieldData 2 f' E) {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} {k : ℕ}
    (e : Module.Basis (Fin (k + 1)) E W)
    (he : ∀ i j, Hf (e i) (e j) = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) E) i j)
    (P₁ : GL (Fin (k + 1)) E)
    (hP₁ : ((P₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).map hE.bar)ᵀ *
      (P₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) = 1) :
    Matrix.GeneralLinearGroup.toLin' e P₁ ∈ sesqUnitaryGroup Hf := by
  rw [mem_sesqUnitaryGroup]
  intro v w
  rw [CFSG.RankThree.CentralLift.form_eq_gramForm hE e he,
    CFSG.RankThree.CentralLift.form_eq_gramForm hE e he,
    CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply,
    CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply]
  have h1 : ((P₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).map hE.bar)ᵀ * 1 *
      (P₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) = 1 := by
    rw [Matrix.mul_one]; exact hP₁
  exact (CFSG.ClassicalGroups.UnitaryFlag.gramForm_isometry_iff hE 1 _).2 h1 _ _

theorem l154s_su_marking {r : ℕ} {K : Type} [Field K] {E : Type} [Field E] {W : Type*}
    [AddCommGroup W] [Module E W] {f' : ℕ} (hE : UnitaryFieldData 2 f' E)
    {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} {k : ℕ} (e : Module.Basis (Fin (k + 1)) E W)
    (he : ∀ i j, Hf (e i) (e j) = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) E) i j)
    (A D : Subgroup (StatedSp r K)) (hDA : D ≤ A) (hDn : ∀ a ∈ A, ∀ g ∈ D, a * g * a⁻¹ ∈ D)
    (φ : ↥A ≃* ↥(sesqUnitaryGroup Hf))
    (hD : ∀ g : ↥A, (g : StatedSp r K) ∈ D ↔
      LinearMap.det (((φ g : ↥(sesqUnitaryGroup Hf)) : LinearMap.GeneralLinearGroup E W) :
        W →ₗ[E] W) = 1) :
    ∃ Θ : ↥D →* LargeEvenProj (LargeEvenSUGroup (Fin (k + 1)) E (2 ^ f')),
      Function.Surjective Θ ∧ Θ.ker ≤ Subgroup.center ↥D ∧
      ∀ α ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (k + 1)) E (2 ^ f')))
          (LargeEvenGUSet (Fin (k + 1)) E (2 ^ f')), ∃ Q : GL (Fin r ⊕ Fin r) K,
        ∀ g : ↥D, ∃ g' : ↥D,
          (((g' : StatedSp r K) : GL (Fin r ⊕ Fin r) K)) =
            Q * ((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * Q⁻¹ ∧ α (Θ g) = Θ g' := by
  obtain ⟨T, hHmem, hTU⟩ : ∃ T : GL (Fin (k + 1)) E ≃* LinearMap.GeneralLinearGroup E W,
      (∀ M, M ∈ LargeEvenSUGroup (Fin (k + 1)) E (2 ^ f') ↔ T M ∈ sesqSpecialUnitaryGroup Hf) ∧
      (∀ P₁ : GL (Fin (k + 1)) E, ((P₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).map hE.bar)ᵀ *
        (P₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) = 1 → T P₁ ∈ sesqUnitaryGroup Hf) :=
    ⟨Matrix.GeneralLinearGroup.toLin' e, l154s_su_mem_iff hE e he, l154s_su_unitary hE e he⟩
  obtain ⟨ε, hεinj, hTε⟩ : ∃ ε : ↥A →* GL (Fin (k + 1)) E, Function.Injective ε ∧
      ∀ g : ↥A, T (ε g) = (φ g : ↥(sesqUnitaryGroup Hf)) :=
    ⟨T.symm.toMonoidHom.comp ((sesqUnitaryGroup Hf).subtype.comp φ.toMonoidHom),
      T.symm.injective.comp (Subtype.val_injective.comp φ.injective),
      fun g => T.apply_symm_apply _⟩
  have hεD : ∀ g : ↥A, (g : StatedSp r K) ∈ D ↔
      ε g ∈ LargeEvenSUGroup (Fin (k + 1)) E (2 ^ f') := by
    intro g
    refine (hD g).trans (Iff.trans ?_ (hHmem (ε g)).symm)
    rw [hTε g]
    exact ⟨fun h0 => mem_sesqSpecialUnitaryGroup.2 ⟨(φ g).2, h0⟩,
      fun h0 => (mem_sesqSpecialUnitaryGroup.1 h0).2⟩
  have hεH : ∀ M ∈ LargeEvenSUGroup (Fin (k + 1)) E (2 ^ f'), ∃ g : ↥A, ε g = M := by
    intro M hM
    rw [hHmem] at hM
    have hMU : T M ∈ sesqUnitaryGroup Hf := (mem_sesqSpecialUnitaryGroup.1 hM).1
    exact ⟨φ.symm ⟨T M, hMU⟩, T.injective ((hTε _).trans
      (congrArg Subtype.val (φ.apply_symm_apply ⟨T M, hMU⟩)))⟩
  have hG : ∀ P ∈ LargeEvenGUSet (Fin (k + 1)) E (2 ^ f'), ∃ (a : ↥A) (z : Eˣ),
      P = Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) z * ε a := by
    intro P hP
    obtain ⟨z, P₁, hP₁, rfl⟩ := l154s_guSet_decomp hE hP
    have hU := hTU P₁ hP₁
    refine ⟨φ.symm ⟨T P₁, hU⟩, z, ?_⟩
    have e1 : ε (φ.symm ⟨T P₁, hU⟩) = P₁ := T.injective ((hTε _).trans
      (congrArg Subtype.val (φ.apply_symm_apply ⟨T P₁, hU⟩)))
    rw [e1]
  exact l154s_marking_of_hom A D hDA hDn _ ε hεinj hεD hεH _ hG

theorem l154s_selfDual_block {r n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) {x : StatedSp r K} (hsq : Squarefree (minpoly K (spEnd x)))
    {h : primaryFactors (spEnd x)} (hS : SpSelfDualBlock 2 n p x h)
    (hq : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X])}, spSupported x {(h : K[X])}⁆) :
    L154sKLine ⁅spSupported x {(h : K[X])}, spSupported x {(h : K[X])}⁆ ∧
    L154sMarkD ⁅spSupported x {(h : K[X])}, spSupported x {(h : K[X])}⁆ := by
  classical
  set A := spSupported x {(h : K[X])} with hA
  set E := AdjoinRoot (h : K[X])
  set W := primaryComponent (spEnd x) (h : K[X])
  obtain ⟨d, hdeg, -, σ, -, -, -, -, -, hE, hbarσ, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, hφ⟩ :=
    hS.exists_half
  have hdeg1 : 1 ≤ (h : K[X]).natDegree := Irreducible.natDegree_pos
    (CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors h.2)
  have hd : 1 ≤ d := by omega
  haveI : Finite E := hE.finite
  have h2E : (2 : E) = 0 := by
    haveI : CharP E 2 := hE.charP
    exact_mod_cast CharP.cast_eq_zero E 2
  have hnd : 2 ≤ n * d := le_trans hn (Nat.le_mul_of_pos_right n hd)
  have hq4 : 4 ≤ 2 ^ (n * d) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n * d) := Nat.pow_le_pow_right (by norm_num) hnd
  have hm : 2 ≤ Module.finrank E W := by
    by_contra hlt
    have hlt' : Module.finrank E W ≤ 1 := by omega
    refine l154s_not_isQuasisimple_commutator (A := A) (fun a ha b hb => ?_) hq
    have h1 : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ := by
      apply Subtype.ext
      apply Units.ext
      exact (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one hlt' _ _).eq
    have h2 : (⟨a, ha⟩ : ↥A) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, h1]
    exact congrArg Subtype.val h2
  let ι : ↥(sesqUnitaryGroup Hf) →* blockGL (spEnd x) (h : K[X]) := (sesqUnitaryGroup Hf).subtype
  let Dt : ↥(sesqUnitaryGroup Hf) →* Eˣ := (blockGLDet (spEnd x) (h : K[X])).comp ι
  have hker : Dt.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h0
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h0
      simpa [Dt, ι, blockGLDet] using this
    · rintro ⟨-, h0⟩
      apply Units.ext
      simpa [Dt, ι, blockGLDet] using h0
  have hSUq : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup Hf) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm
      ⟨fun _ => hq4, fun _ => by omega⟩
  have hquasi : CFSG.IsQuasisimple ↥Dt.ker := by
    rw [hker]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm hSUq
  have hD : kerImage A φ Dt = ⁅A, A⁆ := kerImage_eq_commutator A φ Dt hquasi.1
  have hmemD : ∀ g : ↥A, (g : StatedSp r K) ∈ ⁅A, A⁆ ↔
      LinearMap.det (((φ g : ↥(sesqUnitaryGroup Hf)) : LinearMap.GeneralLinearGroup E W) :
        W →ₗ[E] W) = 1 := by
    intro g
    rw [← hD, mem_kerImage]
    constructor
    · rintro ⟨hg, h0⟩
      have := congrArg Units.val h0
      simpa [Dt, ι, blockGLDet] using this
    · intro h0
      refine ⟨g.2, ?_⟩
      apply Units.ext
      simpa [Dt, ι, blockGLDet] using h0
  have hm0 : 0 < primaryMultiplicity (spEnd x) (h : K[X]) := by
    change 0 < Module.finrank E W
    omega
  have hm1 : 1 < primaryMultiplicity (spEnd x) (h : K[X]) := by
    change 1 < Module.finrank E W
    omega
  set i0 : Fin (primaryMultiplicity (spEnd x) (h : K[X])) := ⟨0, hm0⟩
  set i1 : Fin (primaryMultiplicity (spEnd x) (h : K[X])) := ⟨1, hm1⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set u : W := e i0 + e i1 with hu
  have huu : Hf u u = 0 := by
    rw [hu]
    simp only [map_add, LinearMap.add_apply, he, if_neg h01, if_neg h01.symm,
      add_zero, zero_add, if_true]
    rw [one_add_one_eq_two]
    exact h2E
  have hfix : ∀ c : K, hE.bar (algebraMap K E c) = algebraMap K E c := by
    intro c
    rw [hbarσ]
    exact σ.commutes c
  let tv : K → Module.End E W := fun c => 1 + algebraMap K E c • (Hf u).smulRight u
  have htv : ∀ c, tv c * tv c = 1 ∧ (∀ v w, Hf (tv c v) (tv c w) = Hf v w) ∧
      LinearMap.det (tv c) = 1 :=
    fun c => l154s_unitary_transvection hHf h2E huu (hfix c)
  let tU : K → LinearMap.GeneralLinearGroup E W := fun c => ⟨tv c, tv c, (htv c).1, (htv c).1⟩
  have htU : ∀ c, tU c ∈ sesqUnitaryGroup Hf := fun c => (htv c).2.1
  let tg : K → ↥A := fun c => φ.symm ⟨tU c, htU c⟩
  have hφtg : ∀ c, φ (tg c) = ⟨tU c, htU c⟩ := fun c => φ.apply_symm_apply _
  have htgD : ∀ c, ((tg c : ↥A) : StatedSp r K) ∈ ⁅A, A⁆ := by
    intro c
    rw [hmemD, hφtg]
    exact (htv c).2.2
  let NV : W → (Fin r ⊕ Fin r → K) := fun v => ((Hf u v • u : W) : Fin r ⊕ Fin r → K)
  have hact : ∀ (c : K) (v : W), spEnd ((tg c : ↥A) : StatedSp r K) (v : Fin r ⊕ Fin r → K) =
      (v : Fin r ⊕ Fin r → K) + c • NV v := by
    intro c v
    rw [← hφ (tg c) v v.2, hφtg]
    change ((tv c v : W) : Fin r ⊕ Fin r → K) = _
    simp only [tv, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, Submodule.coe_add]
    rw [CFSG.RankThree.PartOne.KCPrimary.coe_algebraMap_smul_primaryComponent]
  set M : Module.End K (Fin r ⊕ Fin r → K) := spEnd ((tg 1 : ↥A) : StatedSp r K) - 1 with hMdef
  have hglob : ∀ c : K, spEnd ((tg c : ↥A) : StatedSp r K) = 1 + c • M := by
    intro c
    refine ext_primaryComponent hsq fun a ha v hv => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply, hMdef, LinearMap.sub_apply,
      Module.End.one_apply]
    by_cases hah : a = h
    · subst hah
      rw [hact c ⟨v, hv⟩, hact 1 ⟨v, hv⟩, one_smul, add_sub_cancel_left]
    · have hnot : a ∉ ({(h : K[X])} : Set K[X]) := hah
      rw [(mem_spSupported.mp (tg c).2).2 a ha hnot v hv,
        (mem_spSupported.mp (tg 1).2).2 a ha hnot v hv, sub_self, smul_zero, add_zero]
  have hM0 : M ≠ 0 := by
    intro h0
    have h1 := congrArg (fun f : Module.End K (Fin r ⊕ Fin r → K) => f ((e i1 : W) :
      Fin r ⊕ Fin r → K)) h0
    simp only [hMdef, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply] at h1
    rw [hact 1 (e i1), one_smul, add_sub_cancel_left] at h1
    have hHu : Hf u (e i1) = 1 := by
      rw [hu, map_add, LinearMap.add_apply, he, he, if_neg h01, if_pos rfl, zero_add]
    have hu0 : u ≠ 0 := by
      intro hu0
      have := congrArg (fun w => Hf w (e i1)) hu0
      rw [hHu, map_zero, LinearMap.zero_apply] at this
      exact one_ne_zero this
    simp only [NV, hHu, one_smul] at h1
    exact hu0 (Subtype.ext h1)
  refine ⟨l154s_kline_of_lin M hM0 fun c => ⟨_, htgD c, hglob c⟩, ?_⟩
  rcases Nat.lt_or_ge (Module.finrank E W) 3 with hm3 | hm3
  ·
    have hm2 : Module.finrank E W = 2 := by omega
    obtain ⟨eK⟩ := CFSG.RankThree.PartOne.KCUnitary.nonempty_kerImage_mulEquiv A φ Dt
    obtain ⟨eSL⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf
      hHfl hm2
    have hF : Nat.card ↥hE.fixedField = 2 ^ (n * d) := hE.card_fixedField
    refine l154s_markD_sl2 hF hnd ?_
    exact (((MulEquiv.subgroupCongr hD.symm).trans eK).trans ((MulEquiv.subgroupCongr hker).trans
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)))).trans eSL
  ·
    set m' := Module.finrank E W - 1 with hm'
    have hmm : primaryMultiplicity (spEnd x) (h : K[X]) = m' + 1 := by
      change Module.finrank E W = _
      omega
    have he' : ∀ i j, Hf ((e.reindex (finCongr hmm)) i) ((e.reindex (finCongr hmm)) j) =
        (1 : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (AdjoinRoot (h : K[X]))) i j := by
      intro i j
      simp only [Module.Basis.reindex_apply, he, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
    have hne : (m' + 1, 2 ^ (n * d)) ≠ (3, 2) := by
      intro h0
      have := congrArg Prod.snd h0
      simp only at this
      omega
    have hsimpSU : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin (m' + 1))
        (AdjoinRoot (h : K[X])) (2 ^ (n * d)))) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (AdjoinRoot (h : K[X])) 2
        (n * d) hE.card_eq_sq (m' + 1) (by omega) hne
    refine ⟨⟨.twA, m', n * d⟩, ⟨show 1 ≤ n * d by omega, show 2 ≤ m' by omega,
      fun _ => hnd⟩, by simp, by simp, ?_⟩
    refine ⟨AdjoinRoot (h : K[X]), inferInstance, inferInstance, hE.card_eq_sq, hsimpSU, ?_⟩
    exact l154s_su_marking hE (e.reindex (finCongr hmm)) he' A ⁅A, A⁆
      (Subgroup.commutator_le_self A)
      (fun a ha g hg => l154s_conj_mem_commutator ha hg) φ hmemD

theorem l154s_proj_injective {r : ℕ} {K : Type} [Field K] (h2 : (2 : K) = 0) :
    Function.Injective (proj r K) := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  rw [← MonoidHom.ker_eq_bot_iff, SymplecticHigher.ker_proj]
  exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := r) (K := K)

theorem l154s_block_data {r : ℕ} {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hr : 2 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x₀ : StatedSp r K) (hx₀ : x₀ ^ p = 1) {JP : Subgroup (StatedProj (StatedSp r K))}
    (hJP : GLAPComponent p (fixSubgroup (MulAut.conj (proj r K x₀))) JP) :
    ∃ D : Subgroup (StatedSp r K), CFSG.IsQuasisimple ↥D ∧ JP = D.map (proj r K) ∧
      L154sKLine D ∧ L154sMarkD D := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2K : (2 : K) = 0 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
    exact_mod_cast CharP.cast_eq_zero K 2
  have hπinj := l154s_proj_injective (r := r) h2K
  have hPIL := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_sp
    Nat.prime_two hn1 hK (by omega) hp hp2 hp2 x₀ hx₀
  have hperfJ := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJP
  have hJle := hPIL JP hJP.1 hperfJ
  have hJcomp :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJP hJle).1
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hSq : CFSG.IsQuasisimple ↥(StatedSp r K) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple r K (by omega) (Or.inl (Or.inr hK4))
  by_cases hx1 : x₀ = 1
  ·
    subst hx1
    have htop : ⁅(⊤ : Subgroup ↥(StatedSp r K)), (⊤ : Subgroup ↥(StatedSp r K))⁆ = ⊤ := by
      rw [← _root_.commutator_def]
      exact Group.isPerfect_def.mp hSq.1
    have hqtop : CFSG.IsQuasisimple ↥(⊤ : Subgroup (StatedSp r K)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hSq
    obtain ⟨-, -, hJeq⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family (proj r K)
        SymplecticHigher.proj_surjective hZc 1 (fun _ : Unit => (⊤ : Subgroup (StatedSp r K)))
        (fun i j hij => absurd (Subsingleton.elim i j) hij)
        (by ext g; simp [Subgroup.mem_centralizer_iff])
        (fun _ => Or.inl (by rw [htop]; exact hqtop)) JP hJcomp
    rw [htop] at hJeq
    exact ⟨⊤, hqtop, hJeq, l154s_kline_top (by omega), l154s_markD_top hK hn hr⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : orderOf x₀ = p := orderOf_eq_prime hx₀ hx1
  have hpx : orderOf (proj r K x₀) = p := by
    rw [orderOf_injective (proj r K) hπinj x₀, hxp]
  have blocks : SpPrimaryBlocks 2 n p x₀ (proj r K x₀) :=
    (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hn1 hK hp hp2 hp2 (by omega)
      _ hpx).2 x₀ rfl hxp
  have hpK : (p : K) ≠ 0 := by
    intro h0
    haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2K
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h0).symm
  have hsq := (altPrimaryData_spLin hpK hx₀).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x₀)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  obtain ⟨O, hq, hJeq⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family (proj r K)
      SymplecticHigher.proj_surjective hZc x₀
      (fun O : reciprocalOrbits (spEnd x₀) => spSupported x₀ (O : Set K[X]))
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hjoin (fun O =>
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
          (by have := hp.two_le; omega) (by omega) hsq blocks O) JP hJcomp
  refine ⟨_, hq, hJeq, ?_⟩
  obtain ⟨h, hh, hO'⟩ := O.2
  have hO : ({h, reciprocalPolynomial h} : Set K[X]) = O := hO'
  by_cases h1 : h = X - 1
  ·
    subst h1
    have hOset : (O : Set K[X]) = {X - 1} := by
      rw [← hO, CFSG.RankThree.PartOne.KCSpIsotypic.reciprocalPolynomial_X_sub_one,
        Set.pair_eq_singleton]
    rw [hOset] at hq ⊢
    obtain ⟨hcA, -, hkl, hmk⟩ := l154s_fixed_block hK hn blocks hsq hh
    rw [hcA]
    exact ⟨hkl, hmk⟩
  by_cases h2 : reciprocalPolynomial h = h
  ·
    have hOset : (O : Set K[X]) = {h} := by
      rw [← hO, h2, Set.pair_eq_singleton]
    rw [hOset] at hq ⊢
    exact l154s_selfDual_block (h := ⟨h, hh⟩) hK hn hsq (blocks.selfDual ⟨h, hh⟩ h1 h2) hq
  ·
    have hOset : (O : Set K[X]) = {h, reciprocalPolynomial h} := hO.symm
    rw [hOset] at hq ⊢
    exact l154s_paired_block (h := ⟨h, hh⟩) hK hn hsq (blocks.paired ⟨h, hh⟩ (Ne.symm h2)) hq

end CFSG.LocalAnalysis.GLTheoremA.K155XSp
