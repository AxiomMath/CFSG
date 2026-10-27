module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Inn
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFaithful
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.CentralExt CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.StandardType.TableBExc.E6Three


private lemma recipeChevalley_E6 {Q : LargeEvenRawCont} {r n : ℕ}
    (h : CFSG.Assembly.LargeEvenRawDatum (⟨.E6, r, n⟩ : GLALabel) Q) :
    LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false Q := by
  simpa only [CFSG.Assembly.LargeEvenRawDatum] using h

private lemma card_center_dvd_three_of_e6_cover {S₀ : Type} [Group S₀] [Finite S₀]
    (hperf : Group.IsPerfect S₀) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hcard : Nat.card K = 2 ^ 2 ∨ 5 ≤ Nat.card K) (h3 : 3 ∣ Nat.card K - 1)
    (e : S₀ ⧸ Subgroup.center S₀ ≃* AdjointQuotient .E6 K) :
    Nat.card (Subgroup.center S₀) ∣ 3 := by
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e
  have hmult_eq : Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E6 K) ≃*
      Multiplicative (ZMod (Nat.gcd 3 (Nat.card K - 1)))) := by
    rcases hcard with h4 | h5
    · exact (FieldFour.e6_four_hopfMultiplier (K := K) h4).2
    · exact (MinusculeClosed.e6_hopfMultiplier (K := K) h5).2
  obtain ⟨ψ⟩ := hmult_eq
  rw [Nat.card_congr ψ.toEquiv] at hdvd
  have hmult : Nat.card (Multiplicative (ZMod (Nat.gcd 3 (Nat.card K - 1)))) =
      Nat.gcd 3 (Nat.card K - 1) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hmult, Nat.gcd_eq_left h3] at hdvd
  exact hdvd

private lemma coe_mem_hatGroup_of_mem_diagAdj {K : Type} [Field K]
    {x : ↥(Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)))}
    (hx : x ∈ MpStdE6.diagAdj Tag.E6 K) : (x : ModGL Tag.E6 K) ∈ hatGroup Tag.E6 K := by
  obtain ⟨g, hg, a, hx'⟩ := hx
  exact ⟨g, hg, a, hx'⟩

private lemma exists_induced_hom {Ω : Type} [Group Ω] {S B : Subgroup Ω} {R : Type} [Group R]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) (hN : B ≤ Subgroup.normalizer (S : Set Ω))
    (hcomm : ∀ x y : ↥B, (x : Ω) * y = y * x) (φ : ↥B → MulAut R)
    (hφ : ∀ b : ↥B, GLAInduces θ (fun l l' => (l' : Ω) = (b : Ω)⁻¹ * l * b) (φ b)) :
    ∃ φh : ↥B →* MulAut R, ∀ b, φh b = φ b := by
  have hφ_mul : ∀ b₁ b₂ : ↥B, φ (b₁ * b₂) = φ b₁ * φ b₂ := by
    intro b₁ b₂
    refine rk2_induces_unique θ (hN (b₁ * b₂).2) (hφ (b₁ * b₂)) ?_
    intro l l' hll'
    have hl1 : (b₂ : Ω)⁻¹ * (l : Ω) * b₂ ∈ S := by
      simpa using (Subgroup.mem_normalizer_iff.1
        (Subgroup.inv_mem _ (hN b₂.2)) l).1 l.2
    have hl2 : (b₁ : Ω)⁻¹ * ((b₂ : Ω)⁻¹ * (l : Ω) * b₂) * b₁ ∈ S := by
      simpa using (Subgroup.mem_normalizer_iff.1
        (Subgroup.inv_mem _ (hN b₁.2)) _).1 hl1
    have e2 := hφ b₂ l ⟨_, hl1⟩ rfl
    have e1 := hφ b₁ ⟨_, hl1⟩ ⟨_, hl2⟩ rfl
    have hl' : l' = ⟨_, hl2⟩ := by
      apply Subtype.ext
      rw [hll', Subgroup.coe_mul, hcomm b₁ b₂, mul_inv_rev]
      group
    show (φ b₁ * φ b₂) (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')
    rw [MulAut.mul_apply, e2, e1, hl']
  exact ⟨MonoidHom.mk' φ hφ_mul, fun _ => rfl⟩

private lemma exists_lift_pointwise {Ω : Type} [Group Ω] {B : Subgroup Ω} {K : Type}
    [Field K] [Finite K]
    (T : ↥(adjointGroup Tag.E6 K) ≃* ↥(LargeEvenChevGroup Tag.E6.cartan K))
    (hTx : ∀ (i : Fin (Tag.rank .E6)) (c : K),
      ((T (xElement i c) : LargeEvenChevGL Tag.E6.cartan K) :
        Module.End K (LargeEvenChevModule Tag.E6.cartan K)) =
          LargeEvenXOp Tag.E6.cartan K i c)
    (hTy : ∀ (i : Fin (Tag.rank .E6)) (c : K),
      ((T (yElement i c) : LargeEvenChevGL Tag.E6.cartan K) :
        Module.End K (LargeEvenChevModule Tag.E6.cartan K)) =
          LargeEvenYOp Tag.E6.cartan K i c)
    (φ : ↥B →* MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)))
    (hφI : ∀ b, φ b ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false)) (b : ↥B) :
    ∃ x : ↥(hatGroup Tag.E6 K), hatAut .E6 K x =
      (MulAut.congr (MpStdE6.xiEquiv (RingEquiv.refl K) T) (φ b))⁻¹ := by
  have hmem : φ b ∈ ggInndiag
      (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
      (LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (hφI b))
  have hle := Subgroup.mem_comap.1
    (MpStdE6.ggInndiag_le (σ := RingEquiv.refl K) T hTx hTy hmem)
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hle
  let xh : ↥(hatGroup Tag.E6 K) :=
    ⟨(y : ModGL Tag.E6 K), coe_mem_hatGroup_of_mem_diagAdj hy⟩
  have hhat : hatAut .E6 K xh =
      (adjointGroup Tag.E6 K).normalizerMonoidHom y := by
    ext h
    rfl
  refine ⟨xh⁻¹, ?_⟩
  rw [map_inv, hhat, hyeq]
  rfl

private lemma exists_lift_induced {Ω : Type} [Group Ω] {B : Subgroup Ω} {K : Type}
    [Field K] [Finite K]
    (T : ↥(adjointGroup Tag.E6 K) ≃* ↥(LargeEvenChevGroup Tag.E6.cartan K))
    (hTx : ∀ (i : Fin (Tag.rank .E6)) (c : K),
      ((T (xElement i c) : LargeEvenChevGL Tag.E6.cartan K) :
        Module.End K (LargeEvenChevModule Tag.E6.cartan K)) =
          LargeEvenXOp Tag.E6.cartan K i c)
    (hTy : ∀ (i : Fin (Tag.rank .E6)) (c : K),
      ((T (yElement i c) : LargeEvenChevGL Tag.E6.cartan K) :
        Module.End K (LargeEvenChevModule Tag.E6.cartan K)) =
          LargeEvenYOp Tag.E6.cartan K i c)
    (hcomm : ∀ x y : ↥B, (x : Ω) * y = y * x)
    (φ : ↥B →* MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)))
    (hφI : ∀ b, φ b ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false)) :
    ∃ β : ↥B →* ↥(hatGroup Tag.E6 K), ∀ b,
      hatAut .E6 K (β b) =
        (MulAut.congr (MpStdE6.xiEquiv (RingEquiv.refl K) T) (φ b))⁻¹ := by
  have hφ_comm : ∀ b₁ b₂ : ↥B, φ b₁ * φ b₂ = φ b₂ * φ b₁ := by
    intro b₁ b₂
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (by simpa using hcomm b₁ b₂))
  choose β hβ using fun b => exists_lift_pointwise T hTx hTy φ hφI b
  refine ⟨MonoidHom.mk' β ?_, hβ⟩
  intro b₁ b₂
  apply NoOffE6Three.hatAut_injective
  rw [map_mul, hβ, hβ, hβ]
  rw [show φ (b₁ * b₂) = φ b₁ * φ b₂ from map_mul φ b₁ b₂]
  set C₁ := MulAut.congr (MpStdE6.xiEquiv (RingEquiv.refl K) T) (φ b₁)
  set C₂ := MulAut.congr (MpStdE6.xiEquiv (RingEquiv.refl K) T) (φ b₂)
  have hC : C₁ * C₂ = C₂ * C₁ := by
    rw [← map_mul (MulAut.congr (MpStdE6.xiEquiv (RingEquiv.refl K) T)) (φ b₁) (φ b₂),
      ← map_mul (MulAut.congr (MpStdE6.xiEquiv (RingEquiv.refl K) T)) (φ b₂) (φ b₁),
      hφ_comm b₁ b₂]
  rw [show MulAut.congr (MpStdE6.xiEquiv (RingEquiv.refl K) T) (φ b₁ * φ b₂) =
    C₁ * C₂ from map_mul _ _ _, mul_inv_rev]
  exact (mul_inv_rev C₁ C₂).symm.trans
    ((congrArg (fun x : MulAut ↥(adjointGroup Tag.E6 K) => x⁻¹) hC).trans
      (mul_inv_rev C₂ C₁))

private lemma conj_formula {Ω : Type} [Group Ω] {S B : Subgroup Ω} {K : Type}
    [Field K] [Finite K] {R : Type} [Group R]
    (Ξ : R ≃* ↥(adjointGroup Tag.E6 K)) (θ : ↥S ⧸ Subgroup.center ↥S ≃* R)
    (π : ↥S →* ↥(adjointGroup Tag.E6 K))
    (hπ : ∀ s, π s = Ξ (θ (QuotientGroup.mk s)))
    (φ : ↥B →* MulAut R)
    (hφ : ∀ b : ↥B, GLAInduces θ (fun l l' => (l' : Ω) = (b : Ω)⁻¹ * l * b) (φ b))
    (β : ↥B →* ↥(hatGroup Tag.E6 K))
    (hβ : ∀ b : ↥B, hatAut .E6 K (β b) = (MulAut.congr Ξ (φ b))⁻¹) :
    ∀ (b : ↥B) (s t : ↥S), (t : Ω) = (b : Ω)⁻¹ * s * b →
      ((π t : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
        ((β b : ↥(hatGroup Tag.E6 K)) : ModGL Tag.E6 K)⁻¹ *
          ((π s : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) *
          ((β b : ↥(hatGroup Tag.E6 K)) : ModGL Tag.E6 K) := by
  intro b s t hst
  have hid := hφ b s t hst
  have h1 : MulAut.congr Ξ (φ b) (π s) = π t := by
    rw [hπ s, hπ t]
    have hcongr : MulAut.congr Ξ (φ b) (Ξ (θ (QuotientGroup.mk s))) =
        Ξ ((φ b) (θ (QuotientGroup.mk s))) := by
      simp [MulAut.congr_apply]
    rw [hcongr, hid]
  have h2 : hatAut .E6 K (β b) (π t) = π s := by
    rw [hβ, ← h1]
    exact MulEquiv.symm_apply_apply _ _
  have h3 := congrArg (fun y : ↥(adjointGroup Tag.E6 K) => (y : ModGL Tag.E6 K)) h2
  rw [coe_hatAut_apply] at h3
  calc ((π t : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K)
      = ((β b : ↥(hatGroup Tag.E6 K)) : ModGL Tag.E6 K)⁻¹ *
          (((β b : ↥(hatGroup Tag.E6 K)) : ModGL Tag.E6 K) *
            ((π t : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) *
            ((β b : ↥(hatGroup Tag.E6 K)) : ModGL Tag.E6 K)⁻¹) *
          ((β b : ↥(hatGroup Tag.E6 K)) : ModGL Tag.E6 K) := by group
    _ = ((β b : ↥(hatGroup Tag.E6 K)) : ModGL Tag.E6 K)⁻¹ *
          ((π s : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) *
          ((β b : ↥(hatGroup Tag.E6 K)) : ModGL Tag.E6 K) := by rw [h3]

private lemma faithful_hatGroup {K : Type} [Field K] [Finite K] :
    ∀ g ∈ hatGroup Tag.E6 K,
      (∀ h ∈ adjointGroup Tag.E6 K, g * h = h * g) → g = 1 := by
  intro g hg hcomm
  have h1 : hatAut .E6 K ⟨g, hg⟩ = 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [coe_hatAut_apply]
    show (g * (h : ModGL Tag.E6 K) * g⁻¹ : ModGL Tag.E6 K) = (h : ModGL Tag.E6 K)
    rw [hcomm h h.2]
    group
  have h2 : (⟨g, hg⟩ : ↥(hatGroup Tag.E6 K)) = 1 :=
    NoOffE6Three.hatAut_injective (h1.trans (map_one _).symm)
  exact Subtype.ext_iff.mp h2

private lemma exists_pi {Ω : Type} [Group Ω] {S : Subgroup Ω} {K : Type}
    [Field K] [Finite K]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
    (T : ↥(adjointGroup Tag.E6 K) ≃* ↥(LargeEvenChevGroup Tag.E6.cartan K)) :
    ∃ π : ↥S →* ↥(adjointGroup Tag.E6 K), Function.Surjective π ∧
      π.ker = Subgroup.center ↥S ∧
      ∀ s, π s = MpStdE6.xiEquiv (RingEquiv.refl K) T (θ (QuotientGroup.mk s)) := by
  let Ξ : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) ≃*
      ↥(adjointGroup Tag.E6 K) := MpStdE6.xiEquiv (RingEquiv.refl K) T
  let π : ↥S →* ↥(adjointGroup Tag.E6 K) :=
    Ξ.toMonoidHom.comp (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S)))
  have hπ_surj : Function.Surjective π :=
    Ξ.surjective.comp (θ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hπ_ker : π.ker = Subgroup.center ↥S := by
    ext s
    rw [MonoidHom.mem_ker]
    show Ξ (θ (QuotientGroup.mk s)) = 1 ↔ s ∈ Subgroup.center ↥S
    constructor
    · intro h
      have h1 : θ (QuotientGroup.mk s) = 1 := by
        apply Ξ.injective
        rw [h]
        exact (map_one Ξ).symm
      have h2 : (QuotientGroup.mk s : ↥S ⧸ Subgroup.center ↥S) = 1 := by
        apply θ.injective
        rw [h1]
        exact (map_one θ).symm
      exact (QuotientGroup.eq_one_iff s).mp h2
    · intro hs
      have hs' : (QuotientGroup.mk s : ↥S ⧸ Subgroup.center ↥S) = 1 :=
        (QuotientGroup.eq_one_iff s).mpr hs
      rw [hs', map_one, map_one]
  exact ⟨π, hπ_surj, hπ_ker, fun _ => rfl⟩

private lemma exists_dmodel_E6_of_data {Ω : Type} [Group Ω] {S B : Subgroup Ω} {K : Type}
    [Field K] [Finite K] (hB : IsElemAbelian 3 B)
    (hN : B ≤ Subgroup.normalizer (S : Set Ω))
    (θ : ↥S ⧸ Subgroup.center ↥S ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
    (hind : ∀ b ∈ B, ∃ φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false),
      GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ) :
    Nonempty (S172DModel S B (adjointGroup Tag.E6 K) (hatGroup Tag.E6 K)) := by
  obtain ⟨T, hTx, hTy⟩ := InnerDiagE6.exists_largeEvenChevEquiv (τ := .E6) (K := K)
  obtain ⟨π, hπ_surj, hπ_ker, hπ⟩ := exists_pi θ T
  have hcommB : ∀ x y : ↥B, (x : Ω) * y = y * x :=
    fun x y => isElemAbelian_commute hB x.2 y.2
  choose φ hφI hφind using fun b : ↥B => hind b b.2
  obtain ⟨φh, hφh⟩ := exists_induced_hom θ hN hcommB φ hφind
  have hφIh : ∀ b, φh b ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false) := fun b => by
    rw [hφh b]
    exact hφI b
  obtain ⟨β, hβ⟩ := exists_lift_induced T hTx hTy hcommB φh hφIh
  have hφindh : ∀ b : ↥B, GLAInduces θ
      (fun l l' => (l' : Ω) = (b : Ω)⁻¹ * l * b) (φh b) := fun b => by
    rw [hφh b]
    exact hφind b
  let M : S172DModel S B (adjointGroup Tag.E6 K) (hatGroup Tag.E6 K) :=
    { π := π, β := β, surj := hπ_surj, ker_π := hπ_ker,
      conj := conj_formula (MpStdE6.xiEquiv (RingEquiv.refl K) T) θ π hπ φh hφindh β hβ,
      le := adjointGroup_le_hatGroup, faithful := faithful_hatGroup }
  exact ⟨M⟩

private lemma card_center_dvd_three_of_e6_data {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (T : ↥(adjointGroup Tag.E6 K) ≃* ↥(LargeEvenChevGroup Tag.E6.cartan K))
    (hKcard : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n - 1)
    (hqs : CFSG.Open.IsQuasisimple ↥S)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) :
    Nat.card (Subgroup.center ↥S) ∣ 3 := by
  have hperf : Group.IsPerfect ↥S := ⟨hqs.1⟩
  let Ξ : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) ≃*
      ↥(adjointGroup Tag.E6 K) := MpStdE6.xiEquiv (RingEquiv.refl K) T
  let χ : AdjointQuotient .E6 K ≃* ↥(adjointGroup Tag.E6 K) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) (K := K))).trans
      QuotientGroup.quotientBot
  have hcard5 : Nat.card K = 2 ^ 2 ∨ 5 ≤ Nat.card K := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn1 : n ≠ 1 := by
        intro h1
        rw [h1] at h3
        norm_num at h3
      have hn2 : n = 2 := by omega
      subst hn2
      exact Or.inl hKcard
    · right
      rw [hKcard]
      have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      omega
  have h3' : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact h3
  exact card_center_dvd_three_of_e6_cover hperf hcard5 h3' (θ.trans (Ξ.trans χ.symm))

theorem exists_dmodel_E6 {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 3 S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n - 1)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 3 lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ lab.n ∧ Nat.card (Subgroup.center ↥S) ∣ 3 ∧
      Nonempty (S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)) := by
  classical
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  obtain ⟨t, r, n⟩ := lab'
  cases t
  case E6 =>
    obtain ⟨K, hK, hKin, hKcard, hQ⟩ := recipeChevalley_E6 hraw
    dsimp only at hQ
    obtain ⟨_, _, θ, hlabEq, _, hN, hind⟩ := hQ
    subst hlabEq
    letI : Field K := hK
    letI : Finite K := hKin
    obtain ⟨T, -, -⟩ := InnerDiagE6.exists_largeEvenChevEquiv (τ := .E6) (K := K)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by
      rw [← Nat.card_eq_fintype_card, hKcard])
    have hdn : 1 ≤ n := hlab.1
    refine ⟨K, hK, hKin, ‹CharP K 2›, hKcard, ?_, ?_⟩
    · exact card_center_dvd_three_of_e6_data T hKcard hdn h3 hcfg.qs θ
    · exact exists_dmodel_E6_of_data hcfg.elem hN θ hind
  all_goals
    exfalso
    obtain ⟨R, _, I, F, hQ⟩ := rk2_rawDatum_exists hraw
    obtain ⟨-, -, θ, hlabEq, -⟩ := hQ
    subst hlabEq
    cases htag

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
