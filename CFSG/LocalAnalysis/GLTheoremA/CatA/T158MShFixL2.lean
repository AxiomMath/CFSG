module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevAutFieldGraph
public import CFSG.LocalAnalysis.GLTheoremA.CatB.L2CentBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldBasic
public import CFSG.Quasithin.Vol2.Ch11SecBK10J
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Dickson.Sec6

@[expose] def L2cFieldCaseCube : Prop :=
  ∀ {Q : Type} [Group Q] [Finite Q] {n : ℕ} {F : Type} [Field F] [Finite F],
    Subgroup.center Q = ⊥ → Nat.card F = 2 ^ n → 1 ≤ n →
    (Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSL 2 F)) →
    ∀ {a : MulAut Q}, a ^ 3 = 1 → a ≠ 1 →
      ∀ {S : Subgroup Q},
        GLAPComponent 3 (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub a) S →
        ∃ (k : ℕ) (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), 2 ≤ k ∧ 3 * k = n ∧
          Nat.card F₀ = 2 ^ k ∧ Nonempty (PSimple 3 S ≃* StatedProj (StatedSL 2 F₀))

theorem t158FixL2_holds_of_cube (hcube : L2cFieldCaseCube) : T158FixL2 := by
  intro X _ _ J x n hx3 hFG hcat M hM
  have hp : Nat.Prime 3 := Nat.prime_three
  have hxN : x ∈ Subgroup.normalizer (J : Set X) := hFG.elim (fun h => h.1) (fun h => h.1.1)
  have hap : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  obtain ⟨hm1, F, hFf, hFfin, hF, ⟨e⟩⟩ := l2c_isTypeL2_of_catalog (n := 3 * n) hcat
  letI := hFf
  letI := hFfin
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨-, hZs⟩ := l2fld_isQuasisimple_psl2 (F := F) h4
  have hZ : Subgroup.center (PSimple 3 J) = ⊥ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.center_eq_bot_of_mulEquiv' e hZs
  let eZ : (PSimple 3 J ⧸ Subgroup.center (PSimple 3 J)) ≃* PSimple 3 J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e' : (PSimple 3 J ⧸ Subgroup.center (PSimple 3 J)) ≃* StatedProj (StatedSL 2 F) :=
    eZ.trans e
  have ha3 : chevAut 3 J ⟨x, hxN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 J hxN hx3
  have hev : Even (Nat.card (PSimple 3 J)) := by
    rw [Nat.card_congr e.toEquiv, even_iff_two_dvd,
      ← Nat.card_congr
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).toEquiv]
    exact CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2.two_dvd_card_psl2
  have ha1 : chevAut 3 J ⟨x, hxN⟩ ≠ 1 := chevAut_ne_one_of_fgOn hp (by norm_num) hxN hev hFG
  have hS : GLAPComponent 3
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub (chevAut 3 J ⟨x, hxN⟩))
      (chevTransfer 3 J M) := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.fixSub_eq_fixSubgroup_up34]
    exact glaPComponent_chevTransfer hp hxN hap hM
  obtain ⟨k, F₀, hF₀f, hF₀fin, hk2, hk3, hcard₀, ⟨ψ⟩⟩ :=
    hcube hZ hF hm1 e' ha3 ha1 hS
  have hkn : k = n := by omega
  obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hxN hap hM
  have hF₀card : Nat.card F₀ = 2 ^ n := by rw [hcard₀, hkn]
  exact l2c_catalog_of_iso (by omega : 2 ≤ n) hF₀card (g.trans ψ)

end CFSG.LocalAnalysis.GLTheoremA.T158

end
