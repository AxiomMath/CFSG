module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13a
public import CFSG.LocalAnalysis.GL83PartI.I_22_5
public import CFSG.HardMathSupport.Solomon.Proving.Prop68InfEq

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

namespace Sec13c

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_mem' {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A) {a : G}
    (ha : a ∈ A) : A ≤ Subgroup.centralizer ({a} : Set G) :=
  fun _ hb => Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hA hb ha)

theorem isLThreeFour_quotient_center_of_L34 {X : Type} [Group X] (h : IsLThreeFour X) :
    IsLThreeFour (X ⧸ Subgroup.center X) :=
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeFour.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.HardMathSupport.Solomon.Proving.center_eq_bot_of_isLThreeFour' h)).trans
      QuotientGroup.quotientBot).symm h

theorem isLThreeFour_quotient_center_of_SL {X : Type} [Group X] (h : IsSLThreeFour X) :
    IsLThreeFour (X ⧸ Subgroup.center X) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  exact ⟨F, inferInstance, inferInstance, hcard,
    ⟨(QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)⟩⟩

theorem cex117_false_of_base (h117 : Prop117_cex_falseStatement) {m p : ℕ}
    {B M E A K : Subgroup G} {a : G} (hb : Cex117Base G m p B M E A a K) : False := by
  classical
  by_cases hex : ∃ (E' A' : Subgroup G) (a' : G) (K' : Subgroup G),
      Cex117Base G m p B M E' A' a' K' ∧ ¬ NormalizesCyc M A' a'
  · obtain ⟨E', A', a', K', hb', hn'⟩ := hex
    exact h117 ⟨hb', fun _ => hn'⟩
  · exact h117 ⟨hb, fun h' => absurd h' hex⟩

end Sec13c

theorem prop132_of_inputs (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h126 : Prop126Statement) (h127 : Prop127_of_cexStatement)
    (h117 : Prop117_cex_falseStatement) (hR9a : Clause_d_of_clause_cStatement) :
    Prop132Statement := by
  intro G _ _ m p B M E A h
  by_contra hcon
  have hpA : inDp p M A := h.pair.1.2.1
  have hSC : IsSCstar p M A := hpA.1
  have hAM : A ≤ M := hSC.1.1
  have hA : IsElemAbelian p A := hSC.1.2.1
  have hA3 : 3 ≤ CFSG.Open.pRank p A := hSC.2
  have hc : ∀ D : Subgroup G, D ≤ A → IsPPlane p D →
      pCoreOf 2 M ≤ gammaStar p D ∧ ∀ T : Subgroup G, pCoreOf 2 M ≤ T → T ≤ gammaStar p D →
        Subgroup.normalizer (T : Set G) ≤ M := by
    intro D hDA hDp
    have hD : IsEkIn p 2 A D := ⟨hDA, hDp.1, hDp.2⟩
    have h131 := prop131_of_inputs h111 h1117 (prop121_cor_of h121) h127 h hD
    refine ⟨h131.1, fun T hT1 hT2 => ?_⟩
    by_contra hN
    exact hcon ⟨D, T, hD, hT1, hT2, hN⟩
  have hd : GLBCore p 2 A ≤ M := hR9a h.pre.1 hAM hA (by omega) hc
  have ha : ∀ a ∈ A, a ≠ 1 →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) ⊔ piOf p a ≤ M :=
    fun a haA ha1 => sup_le (h111 h haA ha1) (h1117 h haA ha1)
  have hb : ∀ a ∈ A, a ≠ 1 → pCoreOf 2 (alphaOf p M ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) := by
    intro a haA ha1
    by_contra hbad
    exact h121 (⟨h, ⟨haA, ha1⟩, hbad⟩ : Cex121 G m p B M E A a)
  have hf : p = 3 → ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup G,
      IsTwoPrimeComp (alphaOf p M ⊓ Subgroup.centralizer ({a} : Set G)) J →
        IsTwoPrimeComp (Subgroup.centralizer ({a} : Set G)) J := by
    rintro rfl a haA ha1 J hJ
    exact h126 h haA ha1 hJ
  have he : p = 3 → ∀ a ∈ A, a ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) L →
        (IsLThreeFour (↥L ⧸ GLAPPrimeCore 3 ↥L) ∨ IsSLThreeFour (↥L ⧸ GLAPPrimeCore 3 ↥L)) →
          L ≤ M := by
    rintro rfl a haA ha1 L hL hty
    by_cases h3 : CFSG.Open.pRank 3 A = 3
    · by_cases hA1 : ∃ A1 : Subgroup G, inD 3 M A1 ∧ a ∈ A1
      · obtain ⟨A1, hA1D, haA1⟩ := hA1
        exact hA1D.2.clause_e rfl a haA1 ha1 L hL hty
      · by_contra hLM
        have hT : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) := by
          rcases hty with hL34 | hSL
          · exact Sec13c.isLThreeFour_quotient_center_of_L34 hL34
          · exact Sec13c.isLThreeFour_quotient_center_of_SL hSL
        exact Sec13c.cex117_false_of_base h117
          (⟨h, ⟨haA, ha1⟩, hL, Or.inr (Or.inr ⟨rfl, h3, hT⟩), hLM, hA1⟩ :
            Cex117Base G m 3 B M E A a L)
    · have h4 : 4 ≤ CFSG.Open.pRank 3 A := by omega
      have hp3 : Nat.Prime 3 := Nat.prime_three
      have hAp : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup hA
      have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := Sec13c.le_centralizer_of_mem' hA haA
      have hK : IsComponentOf (barX 3 (Subgroup.centralizer ({a} : Set G)) L) ⊤ := hL.2.2.1
      have hperf : commutator ↥(barX 3 (Subgroup.centralizer ({a} : Set G)) L) = ⊤ := hK.2.2.1
      have hty' : IsLThreeFour ↥(barX 3 (Subgroup.centralizer ({a} : Set G)) L) ∨
          IsSLThreeFour ↥(barX 3 (Subgroup.centralizer ({a} : Set G)) L) := by
        let e := quotEquivBarX hp3 hL.1 hL.2.1
        rcases hty with ⟨F, _, _, hcard, ⟨f⟩⟩ | ⟨F, _, _, hcard, ⟨f⟩⟩
        · exact Or.inl ⟨F, inferInstance, inferInstance, hcard, ⟨e.symm.trans f⟩⟩
        · exact Or.inr ⟨F, inferInstance, inferInstance, hcard, ⟨e.symm.trans f⟩⟩
      have hm2 := pRank_mulAut_le_two_of_L34 hty' hperf
      have hrA : CFSG.Open.pRank 3 (barX 3 (Subgroup.centralizer ({a} : Set G)) A) =
          CFSG.Open.pRank 3 A :=
        rank_barX_of_isPGroup hp3 hAp hAC
      have hgen := GL83.I_22_5_proved (↥(Subgroup.centralizer ({a} : Set G)) ⧸
          GLAPPrimeCore 3 ↥(Subgroup.centralizer ({a} : Set G))) 3 hp3
        (glaPPrimeCore_quotient_eq_bot hp3) (barX 3 (Subgroup.centralizer ({a} : Set G)) L) hK
        (barX 3 (Subgroup.centralizer ({a} : Set G)) A) (isElemAbelian_barX hA) (by omega) 2
        (by norm_num) (by omega)
      refine le_of_barX_le_glbCore hp3 2 hAp hAC hL.1 ?_ (h111 h haA ha1) hgen
      intro E hEA hE2
      exact (le_sSup ⟨E, hEA, hE2, rfl⟩ :
        Subgroup.normalizer (E : Set G) ≤ GLBCore 3 2 A).trans hd
  have hU : IsUniquenessTwoLocal p A M :=
    { maxTwoLocal := h.pre.1
      le := hAM
      elemAbelian := hA
      two_le_rank := by omega
      clause_a := ha
      clause_b := hb
      clause_c := hc
      clause_d := hd
      clause_e := he
      clause_f := hf }
  exact hpA.2 hU

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
