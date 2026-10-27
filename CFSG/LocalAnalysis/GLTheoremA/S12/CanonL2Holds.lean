module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriFacts
public import CFSG.LocalAnalysis.GLTheoremA.S12.Common
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneAutRank
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG CFSG.StandardType CFSG.Assembly
open scoped MatrixGroups

noncomputable def lsEquiv (F : Type) [Field F] : ↥(LargeEvenSLGroup (Fin 2) F) ≃* SL(2, F) :=
  (MulEquiv.subgroupCongr
    ((CFSG.Open.StatedAPI.statedSL_eq_ker_det 2 F).symm.trans
      (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 F))).trans
    (MonoidHom.ofInjective (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := F))).symm

theorem scalars_subgroupOf_eq_bot (F : Type) [Field F] [CharP F 2] :
    (LargeEvenScalars (Fin 2) F).subgroupOf (LargeEvenSLGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hdet : Matrix.GeneralLinearGroup.det (g : GL (Fin 2) F) = 1 := g.2
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar] at hdet
  simp only [Fintype.card_fin] at hdet
  have h1 : (c : F) ^ 2 = 1 := by simpa using congrArg Units.val hdet
  have h2 : ((c : F) - 1) ^ 2 = 0 := by
    have : ((c : F) - 1) ^ 2 = (c : F) ^ 2 - 2 * c + 1 := by ring
    have two0 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    rw [this, h1, two0]
    linear_combination two0
  have h3 : (c : F) = 1 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
  have hc1 : c = 1 := Units.ext h3
  rw [hc1, map_one] at hc
  exact Subgroup.mem_bot.mpr (Subtype.ext hc.symm)


noncomputable def projEquiv (F : Type) [Field F] [CharP F 2] :
    LargeEvenProj (LargeEvenSLGroup (Fin 2) F) ≃* SL(2, F) :=
  ((QuotientGroup.quotientMulEquivOfEq (scalars_subgroupOf_eq_bot F)).trans
    QuotientGroup.quotientBot).trans (lsEquiv F)

theorem mem_range_conj_of_graphAut (F : Type) [Field F] [Finite F] [CharP F 2]
    (M : GL (Fin 2) F) (φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)))
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F))
      (fun h h' => (h' : GL (Fin 2) F) = M * h * M⁻¹) φ) :
    φ ∈ (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin 2) F) →* MulAut _).range := by
  classical
  have hring : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hring
    ((Matrix.GeneralLinearGroup.det M : Fˣ) : F)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hr
    exact (Matrix.GeneralLinearGroup.det M).ne_zero hr
  let c : Fˣ := Units.mk0 r hr0
  have hc : c ^ 2 = Matrix.GeneralLinearGroup.det M := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, c, Units.val_mk0, hr]
    ring
  set s : GL (Fin 2) F := (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * M with hs_def
  have hs : s ∈ LargeEvenSLGroup (Fin 2) F := by
    show Matrix.GeneralLinearGroup.det s = 1
    rw [hs_def, map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hc]
    simp
  have hM : M = Matrix.GeneralLinearGroup.scalar (Fin 2) c * s := by
    rw [hs_def]; group
  refine ⟨LargeEvenProjMk _ ⟨s, hs⟩, ?_⟩
  ext r'
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective r'
  have hsh : s * (h : GL (Fin 2) F) * s⁻¹ ∈ LargeEvenSLGroup (Fin 2) F :=
    (LargeEvenSLGroup (Fin 2) F).mul_mem ((LargeEvenSLGroup (Fin 2) F).mul_mem hs h.2)
      ((LargeEvenSLGroup (Fin 2) F).inv_mem hs)
  have hrel : ((⟨s * (h : GL (Fin 2) F) * s⁻¹, hsh⟩ : ↥(LargeEvenSLGroup (Fin 2) F)) : GL (Fin 2) F) =
      M * h * M⁻¹ := by
    show s * (h : GL (Fin 2) F) * s⁻¹ = M * h * M⁻¹
    set z : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) c with hz
    have hzc := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 2) c (s * (h : GL (Fin 2) F) * s⁻¹)
    rw [← hz] at hzc
    calc s * (h : GL (Fin 2) F) * s⁻¹ = (s * (h : GL (Fin 2) F) * s⁻¹) * z * z⁻¹ := by group
      _ = z * (s * (h : GL (Fin 2) F) * s⁻¹) * z⁻¹ := by rw [hzc]
      _ = M * h * M⁻¹ := by rw [hM]; group
  have := hφ h _ hrel
  change (LargeEvenProjMk _ ⟨s, hs⟩) * (LargeEvenProjMk _ h) * (LargeEvenProjMk _ ⟨s, hs⟩)⁻¹ =
    φ (LargeEvenProjMk _ h)
  rw [this, ← map_inv, ← map_mul, ← map_mul]
  congr 1



theorem linear_datum {Γ : Type} [Group Γ] {K : Subgroup Γ} {m : ℕ} (h : LabelOf K ⟨.A, 1, m⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) := by
  obtain ⟨hperf, lab', hΛ, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, hna, θ, hlabeq⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst hlabeq
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨F, i1, i2, hF, hs', hna', θ', -⟩ := hraw
  exact ⟨F, i1, i2, hF, ⟨θ'⟩⟩



theorem three_dvd_card_sl2 (F : Type) [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m) :
    3 ∣ Nat.card SL(2, F) := by
  have h1 : Nat.card (StatedSL 2 F) = Nat.card SL(2, F) :=
    CFSG.Open.StatedAPI.card_statedSL 2 F
  rw [← h1, CFSG.Open.StatedAPI.card_statedSL_two, hF]
  refine Dvd.dvd.mul_left ?_ _
  have h2 : ((2 : ℕ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h2]
  have h3 : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  omega


section Holds


theorem l2Rank3_holds : L2Rank3 := by
  intro Γ _ _ K A m hK hAe hInn
  have hq : CFSG.Open.IsQuasisimple ↥K := isQuasisimple_of_marking hK
  have hperf : commutator ↥K = ⊤ := hK.1
  obtain ⟨F0, _, _, hF0, ⟨θ0⟩⟩ := linear_datum hK
  haveI : CharP F0 2 := charP_two_of_card hF0
  have hdvd : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [Nat.card_congr (θ0.trans (projEquiv F0)).toEquiv]
    exact three_dvd_card_sl2 F0 hF0
  have hL : GLAPComponent 3 K K :=
    S12.glaPComponent_of_quasisimple' Nat.prime_three (CFSG.Open.IsSubnormal.refl K) hq hdvd
  have hIM : CFSG.Yardstones.Md0ec50421ce4.InnerDiagMarking A K := S10.inner_of_innDiagOn hL hq hInn
  have hpin := innDiagIndepAt_holds Γ A K (fun lab _ _ _ _ _ => lab = ⟨.A, 1, m⟩) hIM hK
  obtain ⟨-, lab', hΛ, hraw⟩ := hpin
  obtain ⟨R0, _, I0, F0', hs0, hna0, θ0', hP0, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst hP0
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨F, i1, i2, hF, hs, hna, θ, hlabeq, hBN, hind⟩ := hraw
  haveI : CharP F 2 := charP_two_of_card hF
  have hcentR : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) = ⊥ :=
    center_eq_bot_of_mulEquiv (projEquiv F)
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2.center_eq_bot F)
  have hinj := conj_injective_of_center_eq_bot hcentR
  have hβI := ggBeta_mem K θ hBN hind
  have hker : (ggBeta K θ hBN).ker = (A ⊓ Subgroup.centralizer (K : Set Γ)).subgroupOf A := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h1
      exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one K θ hperf (g := ⟨b, hBN b.2⟩) h1⟩
    · rintro ⟨-, hc⟩
      exact ggLAut_eq_one_of_mem_centralizer K θ (g := ⟨b, hBN b.2⟩) hc
  have hcardker : Nat.card (ggBeta K θ hBN).ker = Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set Γ)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : IsElemAbelian 3 (ggBeta K θ hBN).range :=
    isElemAbelian_range_of_isElemAbelian hAe _
  have h2 := TableB.card_range_mul_card_ker (ggBeta K θ hBN)
  rw [hcardker] at h2
  have hSinn : (ggBeta K θ hBN).range ≤
      (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin 2) F) →* MulAut _).range := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨M, -, hM⟩ := hβI b
    exact mem_range_conj_of_graphAut F M _ hM
  set E : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) :=
    (ggBeta K θ hBN).range.comap
      (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin 2) F) →* MulAut _) with hE
  have hEab : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.comap hrange hinj
  have hEmap : E.map (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin 2) F) →* MulAut _) =
      (ggBeta K θ hBN).range := by
    rw [hE, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hSinn
  have hEcard : Nat.card E = Nat.card (ggBeta K θ hBN).range := by
    rw [← hEmap]
    exact (Subgroup.card_map_of_injective hinj).symm
  have h3 : Nat.card E ≤ 3 := by
    have hmap := CFSG.Open.IsElemAbelian.map hEab (projEquiv F).toMonoidHom
    have := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2.sl2_card_le_three
      (E.map (projEquiv F).toMonoidHom) hmap.1 hmap.2
    rwa [Subgroup.card_map_of_injective (projEquiv F).injective] at this
  rw [hEcard] at h3
  calc Nat.card A = Nat.card (ggBeta K θ hBN).range *
        Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set Γ)) := h2.symm
    _ ≤ 3 * Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set Γ)) := Nat.mul_le_mul_right _ h3

end Holds

end CFSG.LocalAnalysis.GLTheoremA
