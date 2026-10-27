module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks2
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticDiag
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.RankThree.PartOne.KFCL.SpPerm
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoRadical
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Glue
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.RankThree.Classical (spEnd spEnd_apply)
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul spEnd_one)
open CFSG.StandardType.TableBSymp

variable {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ n p : ℕ}

private theorem subtype_diagSp_eq_diagGL_pairedUnits (t : Fin ℓ → Fˣ) :
    (StatedSp ℓ F).subtype (diagSp F ℓ t) = TauCeti.diagGL (pairedUnits t) := by
  apply Units.ext
  change (mat ℓ F (diagSp F ℓ t) : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) =
    (TauCeti.diagGL (pairedUnits t) : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F)
  rw [TauCeti.diagGL_coe, mat_diagSp]
  congr 1
  funext a
  rcases a with i | i <;> rfl

theorem symplecticQTorus_eq_spTorus (hp0 : p ≠ 0) :
    CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p =
      CFSG.RankThree.PartOne.KFCL.Sp.spTorus p ℓ F := by
  ext g
  rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_symplecticQTorus,
    CFSG.RankThree.PartOne.KFCL.Sp.mem_spTorus_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => (t i : F), fun i => ?_, ?_⟩
    · rw [← Units.val_pow_eq_pow_val, ht i, Units.val_one]
    · rw [mat_diagSp]
      congr 1
      funext a
      rcases a with i | i <;> simp [diagSpEntry]
  · rintro ⟨x, hx, hxg⟩
    have hx0 : ∀ i, x i ≠ 0 := by
      intro i h
      have h1 := hx i
      rw [h, zero_pow hp0] at h1
      exact zero_ne_one h1
    refine ⟨fun i => Units.mk0 (x i) (hx0 i), fun i => ?_, ?_⟩
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hx i, Units.val_one]
    · apply mat_injective
      rw [mat_diagSp, hxg]
      congr 1

private theorem map_subtype_symplecticQTorus_eq_range_spTorusGL (hp0 : p ≠ 0) {ζ : Fˣ}
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p).map
        (StatedSp ℓ F).subtype = (spTorusGL (m := ℓ) hζ).range := by
  haveI : NeZero p := ⟨hp0⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ :=
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_symplecticQTorus (F := F) (ℓ := ℓ) (q := p)).1 hx
    have hprim : IsPrimitiveRoot ζ p := hζo ▸ IsPrimitiveRoot.orderOf ζ
    choose k hk using fun i =>
      hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p (t i)).mpr (ht i))
    refine ⟨fun i => Multiplicative.ofAdd ((k i : ℕ) : ZMod p), ?_⟩
    rw [spTorusGL_apply, subtype_diagSp_eq_diagGL_pairedUnits]
    congr 2
    funext i
    rw [zmodPowHom_natCast, (hk i).2]
  · rintro ⟨f, rfl⟩
    refine ⟨diagSp F ℓ (fun i => zmodPowHom hζ (f i)), ?_, ?_⟩
    · exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_symplecticQTorus (F := F) (ℓ := ℓ)
        (q := p)).2 ⟨_, fun i => by
          rw [zmodPowHom_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow], rfl⟩
    · rw [spTorusGL_apply]
      exact subtype_diagSp_eq_diagGL_pairedUnits _

theorem exists_conj_eq_symplecticQTorus_of_isBmax (hℓ : 1 ≤ ℓ) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    {A : Subgroup ↥(StatedSp ℓ F)} (hA : GLAIsBmax p A) :
    ∃ g : ↥(StatedSp ℓ F),
      A.map (MulAut.conj g).toMonoidHom =
        CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpK : (p : F) ≠ 0 := CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2
  have hpdvd : p ∣ Nat.card F - 1 := by rw [hn]; exact hpq
  have hrank : GLATwoLocalRank p ↥(StatedSp ℓ F) = ℓ :=
    twoLocalPrimeRank_statedSp_eq hℓ hp hp2 hpdvd
  have hAcard : Nat.card A = p ^ ℓ := by rw [hA.2.1, hrank]
  have hpdvd' : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpdvd'
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hmapcard : Nat.card (A.map (StatedSp ℓ F).subtype) = Nat.card A :=
    Nat.card_congr (Subgroup.equivMapOfInjective A (StatedSp ℓ F).subtype
      Subtype.coe_injective).symm.toEquiv
  obtain ⟨P, hP, hPconj⟩ :=
    CFSG.StandardType.TableBSymp.exists_conj_eq_range_spTorusGL (K := F) (m := ℓ)
      (hpF := ⟨hp⟩) hp2 hpK hζo hζ (E := A.map (StatedSp ℓ F).subtype)
      (by rintro _ ⟨a, -, rfl⟩; exact a.2) (CFSG.Open.IsElemAbelian.map hA.1 _)
      (by rw [hmapcard, hAcard])
  have hrange := map_subtype_symplecticQTorus_eq_range_spTorusGL (F := F) (ℓ := ℓ) hp0 hζ hζo
  refine ⟨⟨P⁻¹, (StatedSp ℓ F).inv_mem hP⟩, ?_⟩
  refine Subgroup.map_injective (f := (StatedSp ℓ F).subtype) (fun a b h => Subtype.ext h) ?_
  rw [Subgroup.map_map, hrange]
  have hcomp : (StatedSp ℓ F).subtype.comp
        (MulAut.conj (⟨P⁻¹, (StatedSp ℓ F).inv_mem hP⟩ : ↥(StatedSp ℓ F))).toMonoidHom =
      (MulAut.conj P⁻¹).toMonoidHom.comp (StatedSp ℓ F).subtype := by
    ext a
    rfl
  rw [hcomp, ← Subgroup.map_map, hPconj]

private theorem diagSpEntry_piMulSingle (i : Fin ℓ) (ζ : Fˣ) (c : Fin ℓ ⊕ Fin ℓ) :
    diagSpEntry (Pi.mulSingle i ζ) c =
      if c = Sum.inl i then (ζ : F) else if c = Sum.inr i then (((ζ⁻¹ : Fˣ) : F)) else 1 := by
  rcases c with j | j
  · by_cases h : j = i
    · subst h; simp [diagSpEntry]
    · simp [diagSpEntry, Pi.mulSingle_eq_of_ne h, h]
  · by_cases h : j = i
    · subst h; simp [diagSpEntry]
    · simp [diagSpEntry, Pi.mulSingle_eq_of_ne h, h]

private theorem spEnd_rootTorusHom_apply (i : Fin ℓ) (ζ : Fˣ) (v : Fin ℓ ⊕ Fin ℓ → F)
    (c : Fin ℓ ⊕ Fin ℓ) :
    spEnd (rootTorusHom F ℓ i ζ) v c =
      (if c = Sum.inl i then (ζ : F) else if c = Sum.inr i then (((ζ⁻¹ : Fˣ) : F)) else 1) *
        v c := by
  rw [spEnd_apply, ← mat_apply, rootTorusHom_apply, mat_diagSp, Matrix.mulVec_diagonal,
    diagSpEntry_piMulSingle]

private theorem sub_ne_zero_of_orderOf (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Fˣ}
    (hζo : orderOf ζ = p) :
    (ζ : F) - 1 ≠ 0 ∧ (ζ : F) - ((ζ⁻¹ : Fˣ) : F) ≠ 0 := by
  have h1 : (ζ : F) - 1 ≠ 0 := by
    refine sub_ne_zero.mpr (fun h => hp.ne_one ?_)
    rw [← hζo, orderOf_eq_one_iff]
    exact Units.ext h
  have h2 : (ζ : F) - ((ζ⁻¹ : Fˣ) : F) ≠ 0 := by
    refine sub_ne_zero.mpr (fun h => ?_)
    have hinv : ζ = ζ⁻¹ := Units.ext h
    have h2 : ζ ^ 2 = 1 := by
      have h : ζ * ζ⁻¹ = 1 := mul_inv_cancel ζ
      rw [← hinv] at h
      rwa [sq]
    have hdvd : p ∣ 2 := by rw [← hζo]; exact orderOf_dvd_iff_pow_eq_one.mpr h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  exact ⟨h1, h2⟩

private theorem smul_single_inl_mem {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)}
    (hW : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p,
      ∀ w ∈ W, spEnd g w ∈ W) (hp : p.Prime) (hp2 : p ≠ 2) {i : Fin ℓ} {ζ : Fˣ}
    (hζo : orderOf ζ = p) {w : Fin ℓ ⊕ Fin ℓ → F} (hw : w ∈ W) :
    w (Sum.inl i) • Pi.single (Sum.inl i) (1 : F) ∈ W := by
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hmem : rootTorusHom F ℓ i ζ ∈
      CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.rootTorusHom_mem_symplecticQTorus_gen hζo
  set lam : Fin ℓ ⊕ Fin ℓ → F := fun c =>
    if c = Sum.inl i then (ζ : F) else if c = Sum.inr i then (((ζ⁻¹ : Fˣ) : F)) else 1 with hlam
  have hstep : ∀ {u : Fin ℓ ⊕ Fin ℓ → F}, u ∈ W → ∀ a : F,
      (fun c => (lam c - a) * u c) ∈ W := by
    intro u hu a
    have h : (fun c => (lam c - a) * u c) = spEnd (rootTorusHom F ℓ i ζ) u - a • u := by
      funext c
      rw [Pi.sub_apply, Pi.smul_apply, spEnd_rootTorusHom_apply, smul_eq_mul, hlam]
      ring
    rw [h]
    exact W.sub_mem (hW _ hmem u hu) (W.smul_mem a hu)
  have hmem2 : (fun c => (lam c - 1) * ((lam c - ((ζ⁻¹ : Fˣ) : F)) * w c)) ∈ W :=
    hstep (hstep hw ((ζ⁻¹ : Fˣ) : F)) 1
  have hval : (fun c => (lam c - 1) * ((lam c - ((ζ⁻¹ : Fˣ) : F)) * w c)) =
      (((ζ : F) - ((ζ⁻¹ : Fˣ) : F)) * ((ζ : F) - 1) * w (Sum.inl i)) •
        Pi.single (Sum.inl i) (1 : F) := by
    funext c
    rcases c with j | j
    · by_cases h : j = i
      · subst h; simp [hlam, Pi.single_eq_same]; ring
      · simp [hlam, Pi.single_eq_of_ne (fun h' => h (Sum.inl_injective h')), h]
    · by_cases h : j = i
      · subst h; simp [hlam, Pi.single_eq_of_ne (Sum.inr_ne_inl)]
      · simp [hlam, Pi.single_eq_of_ne (fun h' => h (Sum.inr_injective h')), h]
  obtain ⟨hne1, hne2⟩ := sub_ne_zero_of_orderOf (F := F) hp hp2 hζo
  have hprod : ((ζ : F) - ((ζ⁻¹ : Fˣ) : F)) * ((ζ : F) - 1) ≠ 0 := mul_ne_zero hne2 hne1
  rw [hval] at hmem2
  have hstep2 := W.smul_mem (((ζ : F) - ((ζ⁻¹ : Fˣ) : F)) * ((ζ : F) - 1))⁻¹ hmem2
  rw [smul_smul, ← mul_assoc, inv_mul_cancel₀ hprod, one_mul] at hstep2
  exact hstep2

private theorem smul_single_inr_mem {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)}
    (hW : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p,
      ∀ w ∈ W, spEnd g w ∈ W) (hp : p.Prime) (hp2 : p ≠ 2) {i : Fin ℓ} {ζ : Fˣ}
    (hζo : orderOf ζ = p) {w : Fin ℓ ⊕ Fin ℓ → F} (hw : w ∈ W) :
    w (Sum.inr i) • Pi.single (Sum.inr i) (1 : F) ∈ W := by
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hmem : rootTorusHom F ℓ i ζ ∈
      CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.rootTorusHom_mem_symplecticQTorus_gen hζo
  set lam : Fin ℓ ⊕ Fin ℓ → F := fun c =>
    if c = Sum.inl i then (ζ : F) else if c = Sum.inr i then (((ζ⁻¹ : Fˣ) : F)) else 1 with hlam
  have hstep : ∀ {u : Fin ℓ ⊕ Fin ℓ → F}, u ∈ W → ∀ a : F,
      (fun c => (lam c - a) * u c) ∈ W := by
    intro u hu a
    have h : (fun c => (lam c - a) * u c) = spEnd (rootTorusHom F ℓ i ζ) u - a • u := by
      funext c
      rw [Pi.sub_apply, Pi.smul_apply, spEnd_rootTorusHom_apply, smul_eq_mul, hlam]
      ring
    rw [h]
    exact W.sub_mem (hW _ hmem u hu) (W.smul_mem a hu)
  have hmem2 : (fun c => (lam c - 1) * ((lam c - (ζ : F)) * w c)) ∈ W :=
    hstep (hstep hw (ζ : F)) 1
  have hval : (fun c => (lam c - 1) * ((lam c - (ζ : F)) * w c)) =
      ((((ζ⁻¹ : Fˣ) : F) - (ζ : F)) * (((ζ⁻¹ : Fˣ) : F) - 1) * w (Sum.inr i)) •
        Pi.single (Sum.inr i) (1 : F) := by
    funext c
    rcases c with j | j
    · by_cases h : j = i
      · subst h; simp [hlam, Pi.single_eq_of_ne (Sum.inl_ne_inr)]
      · simp [hlam, Pi.single_eq_of_ne (fun h' => h (Sum.inl_injective h')), h]
    · by_cases h : j = i
      · subst h; simp [hlam, Pi.single_eq_same]; ring
      · simp [hlam, Pi.single_eq_of_ne (fun h' => h (Sum.inr_injective h')), h]
  obtain ⟨hne1, hne2⟩ := sub_ne_zero_of_orderOf (F := F) hp hp2 hζo
  have hne2' : ((ζ⁻¹ : Fˣ) : F) - (ζ : F) ≠ 0 := by
    intro h
    exact hne2 (by linear_combination -h)
  have hne1' : ((ζ⁻¹ : Fˣ) : F) - 1 ≠ 0 := by
    refine sub_ne_zero.mpr (fun h => hne1 ?_)
    have h1 : (ζ⁻¹ : Fˣ) = 1 := Units.ext h
    have h2 : ζ = 1 := by rw [← inv_inv ζ, h1, inv_one]
    rw [h2]; simp
  have hprod : (((ζ⁻¹ : Fˣ) : F) - (ζ : F)) * (((ζ⁻¹ : Fˣ) : F) - 1) ≠ 0 :=
    mul_ne_zero hne2' hne1'
  rw [hval] at hmem2
  have hstep2 := W.smul_mem ((((ζ⁻¹ : Fˣ) : F) - (ζ : F)) * (((ζ⁻¹ : Fˣ) : F) - 1))⁻¹ hmem2
  rw [smul_smul, ← mul_assoc, inv_mul_cancel₀ hprod, one_mul] at hstep2
  exact hstep2

theorem single_mem_of_forall_symplecticQTorus (hn : Nat.card F = 2 ^ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)}
    (hW : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p,
      ∀ w ∈ W, spEnd g w ∈ W)
    {w : Fin ℓ ⊕ Fin ℓ → F} (hw : w ∈ W) (b : Fin ℓ ⊕ Fin ℓ) :
    Pi.single b (w b) ∈ W := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units]; rw [hn]; exact hpq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hsingle : (Pi.single b (w b) : Fin ℓ ⊕ Fin ℓ → F) =
      w b • (Pi.single b (1 : F) : Fin ℓ ⊕ Fin ℓ → F) := by
    funext c
    by_cases h : c = b
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [hsingle]
  rcases b with i | i
  · exact smul_single_inl_mem hW hp hp2 hζo hw
  · exact smul_single_inr_mem hW hp hp2 hζo hw

theorem permSp_spEnd_single (σ : Equiv.Perm (Fin ℓ)) (b : Fin ℓ ⊕ Fin ℓ) :
    spEnd (permSp F σ) (Pi.single b (1 : F)) = Pi.single (Sum.map σ σ b) (1 : F) := by
  rw [spEnd_apply, ← mat_apply, mat_permSp]
  funext a
  rw [mulVec_single_one_apply, spIncl_apply, Pi.single_apply]

private theorem diagSpEntry_comp_sumMap (σ : Equiv.Perm (Fin ℓ)) (t : Fin ℓ → Fˣ)
    (x : Fin ℓ ⊕ Fin ℓ) : diagSpEntry (t ∘ ⇑σ) x = diagSpEntry t (Sum.map σ σ x) := by
  rcases x with i | i <;> rfl

private theorem conj_inv_permSp_diagSp (σ : Equiv.Perm (Fin ℓ)) (t : Fin ℓ → Fˣ) :
    (permSp F σ)⁻¹ * diagSp F ℓ t * permSp F σ = diagSp F ℓ (t ∘ ⇑σ) := by
  refine mat_injective ?_
  ext a b
  rw [mat_conj_inv_permSp_apply, mat_diagSp_apply, mat_diagSp_apply]
  by_cases hab : a = b
  · subst hab
    rw [diagSpEntry_comp_sumMap]
    simp
  · have h' : Sum.map σ σ a ≠ Sum.map σ σ b :=
      fun h => hab ((sumMap_bijective σ).injective h)
    simp [hab, h']

theorem permSp_mem_normalizer_symplecticQTorus (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : Nat.card F = 2 ^ n) (hpq : p ∣ 2 ^ n - 1) (σ : Equiv.Perm (Fin ℓ)) :
    permSp F σ ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_symplecticQTorus,
    CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_symplecticQTorus]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t ∘ ⇑σ.symm, fun i => ht (σ.symm i), conj_permSp_diagSp σ t⟩
  · rintro ⟨t, ht, hx⟩
    refine ⟨t ∘ ⇑σ, fun i => ht (σ i), ?_⟩
    calc x = (permSp F σ)⁻¹ * (permSp F σ * x * (permSp F σ)⁻¹) * permSp F σ := by group
      _ = (permSp F σ)⁻¹ * diagSp F ℓ t * permSp F σ := by rw [hx]
      _ = diagSp F ℓ (t ∘ ⇑σ) := conj_inv_permSp_diagSp σ t

private theorem spEnd_diagSp_single (t : Fin ℓ → Fˣ) (b : Fin ℓ ⊕ Fin ℓ) :
    spEnd (diagSp F ℓ t) (Pi.single b (1 : F)) = diagSpEntry t b • Pi.single b (1 : F) := by
  rw [spEnd_apply, ← mat_apply, mat_diagSp]
  funext a
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h : a = b <;> simp [h]

private theorem diagSpEntry_update (t : Fin ℓ → Fˣ) (i : Fin ℓ) (b : Fin ℓ ⊕ Fin ℓ) :
    diagSpEntry (Function.update t i (t i)⁻¹) b = diagSpEntry t (pairSwap i b) := by
  rcases b with j | j
  · by_cases h : j = i
    · subst h; simp [diagSpEntry, pairSwap]
    · have h1 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := fun h' => h (Sum.inl_injective h')
      have h2 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := Sum.inl_ne_inr
      simp only [diagSpEntry, Sum.elim_inl, pairSwap, Equiv.swap_apply_of_ne_of_ne h1 h2,
        Function.update_of_ne h]
  · by_cases h : j = i
    · subst h; simp [diagSpEntry, pairSwap]
    · have h1 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := Sum.inr_ne_inl
      have h2 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := fun h' => h (Sum.inr_injective h')
      simp only [diagSpEntry, Sum.elim_inr, pairSwap, Equiv.swap_apply_of_ne_of_ne h1 h2,
        Function.update_of_ne h]

theorem spSwapSp_spEnd_single (i : Fin ℓ) (b : Fin ℓ ⊕ Fin ℓ) :
    spEnd (spSwapSp (K := F) i) (Pi.single b (1 : F)) = Pi.single (pairSwap i b) (1 : F) := by
  rw [spEnd_apply, spSwapSp_coe, TauCeti.permutationGL_coe, Matrix.permMatrix_mulVec]
  funext a
  rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
  rw [pairSwap_inv i]
  by_cases h : pairSwap i a = b
  · have h' : a = pairSwap i b := by
      rw [← h, show pairSwap i (pairSwap i a) = a from by simp [pairSwap]]
    rw [if_pos h, if_pos h']
  · have h' : ¬ a = pairSwap i b := by
      intro h2
      exact h (by rw [h2, show pairSwap i (pairSwap i b) = b from by simp [pairSwap]])
    rw [if_neg h, if_neg h']

private theorem spSwapSp_mul_self (i : Fin ℓ) :
    spSwapSp (K := F) i * spSwapSp (K := F) i = 1 := by
  refine CFSG.ComponentClassification.CatalogueBSymplecticTwo.eq_of_spAct_single
    (r := ℓ) (K := F) ?_
  intro c
  change spEnd (spSwapSp (K := F) i * spSwapSp (K := F) i) (Pi.single c (1 : F)) =
    spEnd (1 : ↥(StatedSp ℓ F)) (Pi.single c (1 : F))
  rw [spEnd_mul, Module.End.mul_apply, spSwapSp_spEnd_single, spSwapSp_spEnd_single,
    show pairSwap i (pairSwap i c) = c from by simp [pairSwap], spEnd_one, Module.End.one_apply]

private theorem conj_spSwapSp_diagSp (i : Fin ℓ) (t : Fin ℓ → Fˣ) :
    spSwapSp (K := F) i * diagSp F ℓ t * (spSwapSp (K := F) i)⁻¹ =
      diagSp F ℓ (Function.update t i (t i)⁻¹) := by
  have hinv : (spSwapSp (K := F) i)⁻¹ = spSwapSp i :=
    inv_eq_of_mul_eq_one_right (spSwapSp_mul_self i)
  refine CFSG.ComponentClassification.CatalogueBSymplecticTwo.eq_of_spAct_single
    (r := ℓ) (K := F) ?_
  intro c
  change spEnd (spSwapSp (K := F) i * diagSp F ℓ t * (spSwapSp (K := F) i)⁻¹)
      (Pi.single c (1 : F)) =
    spEnd (diagSp F ℓ (Function.update t i (t i)⁻¹)) (Pi.single c (1 : F))
  rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply, hinv,
    spSwapSp_spEnd_single, spEnd_diagSp_single, map_smul, spSwapSp_spEnd_single,
    spEnd_diagSp_single, show pairSwap i (pairSwap i c) = c from by simp [pairSwap],
    diagSpEntry_update]

theorem spSwapSp_mem_normalizer_symplecticQTorus (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : Nat.card F = 2 ^ n) (hpq : p ∣ 2 ^ n - 1) (i : Fin ℓ) :
    spSwapSp (K := F) i ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_symplecticQTorus,
    CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_symplecticQTorus]
  have hinv : (spSwapSp (K := F) i)⁻¹ = spSwapSp i :=
    inv_eq_of_mul_eq_one_right (spSwapSp_mul_self i)
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Function.update t i (t i)⁻¹, fun j => ?_, conj_spSwapSp_diagSp i t⟩
    by_cases hj : j = i
    · subst hj; rw [Function.update_self, inv_pow, ht j, inv_one]
    · rw [Function.update_of_ne hj]; exact ht j
  · rintro ⟨t, ht, hx⟩
    refine ⟨Function.update t i (t i)⁻¹, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; rw [Function.update_self, inv_pow, ht j, inv_one]
      · rw [Function.update_of_ne hj]; exact ht j
    · calc x = (spSwapSp i)⁻¹ * (spSwapSp i * x * (spSwapSp i)⁻¹) * spSwapSp i := by group
        _ = (spSwapSp i)⁻¹ * diagSp F ℓ t * spSwapSp i := by rw [hx]
        _ = diagSp F ℓ (Function.update t i (t i)⁻¹) := by
          simpa [hinv] using conj_spSwapSp_diagSp i t

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
