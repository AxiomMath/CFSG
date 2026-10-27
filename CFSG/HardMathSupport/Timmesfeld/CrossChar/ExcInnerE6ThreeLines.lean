module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SplitLineFix
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveSpringer

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Data

@[expose] def e6ThreeLineX : Fin 12 → Fin Tag.E6.rank → ℤ :=
  ![![1, 1, 1, 2, 1, 0], ![1, 0, 1, 1, 0, 0], ![1, 1, 2, 2, 1, 0], ![1, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 0], ![1, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0], ![1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0], ![0, 0, -1, 0, 0, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 1, 1, 0, 0]]

@[expose] def e6ThreeLineY : Fin 12 → Fin Tag.E6.rank → ℤ :=
  ![![0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 2, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 1, 1, 1],
    ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 2, 1, 1], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1],
    ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0]]

@[expose] def e6ThreeLineWord : Fin 12 → List (Fin Tag.E6.rank) :=
  ![[1, 3, 4, 5, 2, 1, 3, 4, 2, 1, 3], [3, 4, 5, 2, 3, 4, 1, 3], [2, 3, 4, 5, 1, 3, 4, 2, 1, 3],
    [5, 2, 1, 3, 4, 2, 1, 3], [4, 5, 3, 4, 2, 1, 3], [5, 3, 4, 1, 3], [4, 5, 1, 3, 4, 2, 3],
    [5, 4, 2, 3], [2, 3, 4, 0, 2, 1, 3], [0, 2, 1, 3, 0], [4, 2, 3, 0, 2, 1, 3], [3, 4, 0, 2, 3]]

theorem e6ThreeLine_words : ∀ k : Fin 12,
    wordMat Tag.E6 (e6ThreeLineWord k) *ᵥ (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) =
      e6ThreeLineX k ∧
    wordMat Tag.E6 (e6ThreeLineWord k) *ᵥ (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) =
      e6ThreeLineY k := by
  decide +kernel

theorem e6ThreeLine_M : ∀ k : Fin 12,
    toMat Tag.E6.rank e6ThreeMat *ᵥ e6ThreeLineX k = e6ThreeLineY k ∧
    toMat Tag.E6.rank e6ThreeMat *ᵥ e6ThreeLineY k = -(e6ThreeLineX k + e6ThreeLineY k) := by
  decide +kernel

theorem e6ThreeLine_cover : ∀ γ, IsRoot Tag.E6 γ → ∃ k : Fin 12,
    γ = e6ThreeLineX k ∨ γ = -e6ThreeLineX k ∨ γ = e6ThreeLineY k ∨ γ = -e6ThreeLineY k ∨
      γ = e6ThreeLineX k + e6ThreeLineY k ∨ γ = -(e6ThreeLineX k + e6ThreeLineY k) := by
  rw [forall_isRoot_iff]
  decide +kernel

noncomputable abbrev e6PhiThreeWeyl :
    WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd e6ThreeWord

end Data

section Frames

theorem e6ThreeLine_frame {L : Type} [Field L] (k : Fin 12) :
    ∃ (ρ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      IsSLFrame ρ σ ∧ Function.Injective ρ ∧ σ 0 1 = e6ThreeLineX k ∧
        σ 1 2 = e6ThreeLineY k := by
  obtain ⟨h1, h2⟩ := e6ThreeLine_words k
  obtain ⟨ρ, σ, hfr, h01, h12⟩ := exists_a2Frame_of_word (x := e6ThreeLineX k)
    (y := e6ThreeLineY k) (e6_base_frame (L := L)) (e6ThreeLineWord k)
    (by rw [e6_base_01]; exact h1) (by rw [e6_base_12]; exact h2)
  exact ⟨ρ, σ, IsSLFrame.of_isA2Frame hfr, hfr.injective, h01, h12⟩

theorem e6ThreeLine_sigma {L : Type} [Field L] {ρ : SL(3, L) →* ModGL Tag.E6 L}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (h : IsSLFrame ρ σ) {x y : Fin Tag.E6.rank → ℤ}
    (h01 : σ 0 1 = x) (h12 : σ 1 2 = y) :
    σ 0 2 = x + y ∧ σ 1 0 = -x ∧ σ 2 1 = -y ∧ σ 2 0 = -(x + y) := by
  have h02 : σ 0 2 = x + y := by rw [← h.add 0 1 2, h01, h12]
  exact ⟨h02, by rw [h.neg 0 1, h01], by rw [h.neg 1 2, h12], by rw [h.neg 0 2, h02]⟩

end Frames

section Rigid

theorem e6ThreeLine_exists_ne {K : Type} [Field K] [Finite K] (hK3 : 3 ≤ Nat.card K) :
    ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  classical
  let _ := Fintype.ofFinite K
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    (Fintype.two_lt_card_iff (α := K)).1 (by rw [← Nat.card_eq_fintype_card]; omega)
  by_cases ha : a ≠ 0 ∧ a ≠ 1
  · exact ⟨a, ha⟩
  by_cases hb : b ≠ 0 ∧ b ≠ 1
  · exact ⟨b, hb⟩
  have ha' : a = 0 ∨ a = 1 := by tauto
  have hb' : b = 0 ∨ b = 1 := by tauto
  refine ⟨c, fun hc => ?_, fun hc => ?_⟩ <;> subst hc <;>
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp_all

@[expose] def E6LineCommuteAt (K : Type) [Field K] : Prop :=
  ∀ (ρ : SL(3, AlgebraicClosure K) →* ModGL Tag.E6 (AlgebraicClosure K))
    (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ), IsSLFrame ρ σ →
    ∀ (H : SL(3, AlgebraicClosure K)) (g : ModGL Tag.E6 (AlgebraicClosure K)),
      (∀ Y : SL(3, K), Commute g
        (ρ (H * Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) Y * H⁻¹))) →
      ∀ x ∈ ρ.range, Commute g x

theorem e6LineCommuteAt_of_three_le {K : Type} [Field K] [Finite K] (hK3 : 3 ≤ Nat.card K) :
    E6LineCommuteAt K :=
  fun _ _ hfr _ _ hg => splitLine_commute_range (by decide) hfr (e6ThreeLine_exists_ne hK3) hg

theorem setupRigid_E6_three_of_commute {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6PhiThreeWeyl)
    (hcY : E6LineCommuteAt K) {p : ℕ} (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) p)
    (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiThreeWeyl hg0C hg0) :
    SetupRigid S := by
  classical
  set L := AlgebraicClosure K with hL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq : S.D.q = Nat.card K := by rw [hSD]; rfl
  have hfrob : FrobRootMap (LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiThreeWeyl hg0C hg0)
      S.ρ := hSD ▸ S.frob
  have hρM : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = toMat Tag.E6.rank e6ThreeMat *ᵥ γ := by
    intro γ hγ
    rw [frobRootMap_ofFrobenius_apply Nat.card_pos hFr hg0C hg0 hfrob hγ,
      wordProd_smul_eq_wordMat_mulVec, e6Three_wordMat]
  have hlines : ∀ k : Fin 12, ∃ (ρk : SL(3, L) →* ModGL Tag.E6 L)
      (σk : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ) (H : SL(3, L)),
      IsSLFrame ρk σk ∧
      (∀ X : SL(3, L), S.D.step (ρk X) = ρk X ↔
        ∃ Y : SL(3, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹) ∧
      ρk.range ⊓ S.D.step.eqLocus (MonoidHom.id _) ≤ S.Γ ∧
      ⁅ρk.range ⊓ S.D.step.eqLocus (MonoidHom.id _),
        ρk.range ⊓ S.D.step.eqLocus (MonoidHom.id _)⁆ =
          ρk.range ⊓ S.D.step.eqLocus (MonoidHom.id _) ∧
      (∃ x ∈ ρk.range ⊓ S.D.step.eqLocus (MonoidHom.id _), orderOf x = p) ∧
      ρk.range ⊓ S.D.step.eqLocus (MonoidHom.id _) ≤ rootSpan Tag.E6 L
        {γ | ∃ j : ℕ, γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (e6ThreeLineX k) ∨
          γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (-e6ThreeLineX k)} ∧
      (∀ γ, (γ = e6ThreeLineX k ∨ γ = -e6ThreeLineX k ∨ γ = e6ThreeLineY k ∨
          γ = -e6ThreeLineY k ∨ γ = e6ThreeLineX k + e6ThreeLineY k ∨
          γ = -(e6ThreeLineX k + e6ThreeLineY k)) → rootSubgroup Tag.E6 L γ ≤ ρk.range) ∧
      IsRoot Tag.E6 (e6ThreeLineX k) := by
    intro k
    obtain ⟨ρk, σk, hfr, hinj, h01, h12⟩ := e6ThreeLine_frame (L := L) k
    obtain ⟨h02, h10, h21, h20⟩ := e6ThreeLine_sigma hfr h01 h12
    obtain ⟨hMx, hMy⟩ := e6ThreeLine_M k
    have hxr : IsRoot Tag.E6 (e6ThreeLineX k) := by
      rw [← h01]
      exact hfr.isRoot 0 1 (by decide)
    have hyr : IsRoot Tag.E6 (e6ThreeLineY k) := by
      rw [← h12]
      exact hfr.isRoot 1 2 (by decide)
    have hxyr : IsRoot Tag.E6 (e6ThreeLineX k + e6ThreeLineY k) := by
      rw [← h02]
      exact hfr.isRoot 0 2 (by decide)
    have hρx : S.ρ (e6ThreeLineX k) = e6ThreeLineY k := by rw [hρM _ hxr, hMx]
    have hρy : S.ρ (e6ThreeLineY k) = -(e6ThreeLineX k + e6ThreeLineY k) := by
      rw [hρM _ hyr, hMy]
    have hρnx : S.ρ (-e6ThreeLineX k) = -e6ThreeLineY k := by
      rw [S.frob.neg_eq, hρx]
    have hρny : S.ρ (-e6ThreeLineY k) = e6ThreeLineX k + e6ThreeLineY k := by
      rw [S.frob.neg_eq, hρy, neg_neg]
    have hρxy : S.ρ (e6ThreeLineX k + e6ThreeLineY k) = -e6ThreeLineX k := by
      rw [hρM _ hxyr, Matrix.mulVec_add, hMx, hMy]
      abel
    have hρnxy : S.ρ (-(e6ThreeLineX k + e6ThreeLineY k)) = e6ThreeLineX k := by
      rw [S.frob.neg_eq, hρxy, neg_neg]
    have r0 : finRotate 3 0 = 1 := rfl
    have r1 : finRotate 3 1 = 2 := rfl
    have r2 : finRotate 3 2 = 0 := rfl
    have hπ : ∀ i j, i ≠ j → S.ρ (σk i j) = σk (finRotate 3 i) (finRotate 3 j) := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first | exact absurd rfl hij | skip
      · show S.ρ (σk 0 1) = σk (finRotate 3 0) (finRotate 3 1)
        rw [r0, r1, h01, h12, hρx]
      · show S.ρ (σk 0 2) = σk (finRotate 3 0) (finRotate 3 2)
        rw [r0, r2, h02, h10, hρxy]
      · show S.ρ (σk 1 0) = σk (finRotate 3 1) (finRotate 3 0)
        rw [r1, r0, h10, h21, hρnx]
      · show S.ρ (σk 1 2) = σk (finRotate 3 1) (finRotate 3 2)
        rw [r1, r2, h12, h20, hρy]
      · show S.ρ (σk 2 0) = σk (finRotate 3 2) (finRotate 3 0)
        rw [r2, r0, h20, h01, hρnxy]
      · show S.ρ (σk 2 1) = σk (finRotate 3 2) (finRotate 3 1)
        rw [r2, r1, h21, h02, hρny]
    obtain ⟨⟨H, hH⟩, hYΓ, hYp⟩ := splitLine_spec S (k := K) hq.symm hfr hinj (finRotate 3) hπ
    have hord := splitLine_exists_orderOf S hinj hH hp3 hpq
    have hframe : frameRoots σk ⊆ {γ | ∃ j : ℕ,
        γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (e6ThreeLineX k) ∨
          γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (-e6ThreeLineX k)} := by
      rintro _ ⟨i, j, hij, rfl⟩
      fin_cases i <;> fin_cases j
      all_goals first | exact absurd rfl hij | skip
      · exact ⟨0, Or.inl (by simpa using h01)⟩
      · refine ⟨2, Or.inr ?_⟩
        show σk 0 2 = S.ρ (S.ρ (-e6ThreeLineX k))
        rw [hρnx, hρny, h02]
      · exact ⟨0, Or.inr (by simpa using h10)⟩
      · refine ⟨1, Or.inl ?_⟩
        show σk 1 2 = S.ρ (e6ThreeLineX k)
        rw [hρx, h12]
      · refine ⟨2, Or.inl ?_⟩
        show σk 2 0 = S.ρ (S.ρ (e6ThreeLineX k))
        rw [hρx, hρy, h20]
      · refine ⟨1, Or.inr ?_⟩
        show σk 2 1 = S.ρ (-e6ThreeLineX k)
        rw [hρnx, h21]
    have hmem : ∀ i j, i ≠ j → rootSubgroup Tag.E6 L (σk i j) ≤ ρk.range := by
      intro i j hij
      rw [hfr.range]
      exact rootSubgroup_le_rootSpan ⟨i, j, hij, rfl⟩
    refine ⟨ρk, σk, H, hfr, hH, hYΓ, hYp, hord, ?_, ?_, hxr⟩
    · exact inf_le_left.trans (hfr.range ▸ rootSpan_mono hframe)
    · rintro γ (rfl | rfl | rfl | rfl | rfl | rfl)
      · rw [← h01]; exact hmem 0 1 (by decide)
      · rw [← h10]; exact hmem 1 0 (by decide)
      · rw [← h12]; exact hmem 1 2 (by decide)
      · rw [← h21]; exact hmem 2 1 (by decide)
      · rw [← h02]; exact hmem 0 2 (by decide)
      · rw [← h20]; exact hmem 2 0 (by decide)
  choose ρk σk Hk hfr hH hYΓ hYp hYord hYspan hU hxr using hlines
  have hsub : ∀ D₁ : Subgroup (ModGL Tag.E6 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 → ∀ k,
      (((ρk k).range ⊓ S.D.step.eqLocus (MonoidHom.id _) : Subgroup (ModGL Tag.E6 L)) :
        Set (ModGL Tag.E6 L)) ⊆ bigComponentSet S D₁ := by
    intro D₁ hD₁ hc k
    obtain ⟨x, hxY, hxp⟩ := hYord k
    exact subset_bigComponentSet_of_perfect S hD₁ hc (hxr k) (hYΓ k) (hYp k) (hYspan k) hxY hxp
  have hcomm : ∀ D₁ : Subgroup (ModGL Tag.E6 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      ∀ g : ModGL Tag.E6 L, (∀ x ∈ rigidTestSet S D₁, Commute g x) →
        ∀ h ∈ adjointGroup Tag.E6 L, Commute g h := by
    intro D₁ hD₁ hc g hg
    have hk : ∀ k, ∀ y ∈ (ρk k).range, Commute g y := fun k =>
      hcY (ρk k) (σk k) (hfr k) (Hk k) g fun Y =>
        hg _ (Or.inl (hsub D₁ hD₁ hc k ⟨⟨_, rfl⟩, (hH k _).2 ⟨Y, rfl⟩⟩))
    have hle : adjointGroup Tag.E6 L ≤ Subgroup.centralizer {g} := by
      rw [adjointGroup_eq_rootSpan]
      refine iSup₂_le fun γ hγ => ?_
      obtain ⟨k, hγk⟩ := e6ThreeLine_cover γ hγ
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.2 (hk k y (hU k γ hγk hy)).eq.symm
    intro h hh
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hh)).symm
  have hF : ∀ D₁ : Subgroup (ModGL Tag.E6 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁ := by
    intro D₁ hD₁ hc r f j _ hr hqf hj0 hjf z hz
    obtain ⟨a, haD, ha1, i, hbig, -⟩ := hsub D₁ hD₁ hc 0
      (one_mem ((ρk 0).range ⊓ S.D.step.eqLocus (MonoidHom.id _)))
    exact outer_false_of_component_fixed_by_twist_of_E S (by decide) (hD₁ haD) i hr hqf
      (Or.inr (Or.inr (Or.inl rfl))) hj0 hjf z
      (fun x hx => hz x (Or.inl ⟨a, haD, ha1, i, hbig, hx⟩))
  have hI : ∀ D₁ : Subgroup (ModGL Tag.E6 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁ := by
    intro D₁ hD₁ hc z hzC hz
    have hcent : (⟨z, hzC⟩ : adjointGroup Tag.E6 L) ∈ Subgroup.center (adjointGroup Tag.E6 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm D₁ hD₁ hc z hz g g.2).eq.symm
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  have hIg : ∀ D₁ : Subgroup (ModGL Tag.E6 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      GraphCentralizerEmpty S D₁ := by
    intro D₁ hD₁ hc w hw hz
    exact not_forall_commute_mul_diagramMap_E6 (K := K) hw (hcomm D₁ hD₁ hc _ hz)
  have hd : S.Descends := by
    have hd7 : LangDescent S.D 7 ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E6 K).subtype) := by
      rw [hSD]
      exact langDescent_ofFrobenius (Or.inr (Or.inl rfl)) e6PhiThreeWeyl K hFr hg0C hg0
    have hι : Function.Injective ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E6 K).subtype) :=
      (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
    exact ⟨K, inferInstance, inferInstance, inferInstance, hd7.mulEquiv' hι, hq.symm,
      fun x => hd7.coe_mulEquiv' hι x⟩
  exact setupRigid_of_descends_E6 S hd hF hI hIg

end Rigid

theorem e6ThreeLine_dvd_of_orderOf {p n : ℕ} (hp : p.Prime)
    (h : orderOf ((n : ℕ) : ZMod p) = 3) : p ∣ n ^ 2 + n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((n : ℕ) : ZMod p) ^ 3 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h2 : ((n : ℕ) : ZMod p) ≠ 1 := fun h' => by
    rw [h', orderOf_one] at h
    omega
  have h3 : (((n : ℕ) : ZMod p) - 1) * (((n : ℕ) : ZMod p) ^ 2 + ((n : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd (sub_eq_zero.1 h4) h2
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact h4

section Consumer

theorem springer_exists_langSetup_E6_three (hF : FrobeniusOnRoots) (K : Type) [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
      (g0 : ModGL Tag.E6 (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6PhiThreeWeyl)
      (S : LangSetup Tag.E6 (AlgebraicClosure K) p),
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiThreeWeyl hg0C hg0 ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (adjointGroup Tag.E6 K ≃* S.Γ) :=
  springer_exists_lang_untw_of_blocks hF 3 (Or.inl ⟨rfl, rfl⟩) K hp (by omega) hpK
    e6PhiThreeWeyl (wordProd_smul_eq_wordMat_mulVec Tag.E6 e6ThreeWord) [3, 3, 3]
    e6Three_charpoly e6Three_pow he (not_dvd_of_blocks hp h7 (by decide))
    (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K).1

theorem innerPlaneBalance_E6_three_of_commute (hcp : LangComponentPieces)
    (q : TauCeti.PrimePower) (hv : (excIndex .E6 q).Valid) {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hpq : p ≠ q.p) (he : orderOf ((q.card : ℕ) : ZMod p) = 3)
    (hcY : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card → E6LineCommuteAt K) :
    InnerPlaneBalance p (CatT ⟨excIndex .E6 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨eq⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hcK := hcY K hK
  rw [← hK] at he
  obtain ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, ⟨ε⟩⟩ :=
    springer_exists_langSetup_E6_three frobeniusOnRoots_proved K hp hp7 hpK he
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hpq1 : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := e6ThreeLine_dvd_of_orderOf hp he
  have hrig := setupRigid_E6_three_of_commute hFr hg0C hg0 hcK (by omega) hpq1 S hSD
  have hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) :=
    conj_injective_of_mulEquiv ε.symm (mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K))
  exact InnerPlaneBalance.of_mulEquiv (eq.trans ε)
    (innerPlaneBalance_of_langSetup_rigid S hsyl hrig hcp hinj)

end Consumer

end CFSG.HardMathSupport.Timmesfeld.CrossChar
