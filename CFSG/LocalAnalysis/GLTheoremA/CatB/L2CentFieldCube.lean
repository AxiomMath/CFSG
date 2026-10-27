module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.L2CentField
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldAut3
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ClassicalModels CFSG.Assembly.LowTwoRank

local notation "fixS" => CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub

theorem l2c_field_case_cube {Q : Type} [Group Q] [Finite Q] (hZ : Subgroup.center Q = ⊥)
    {n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (e : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSL 2 F))
    {a : MulAut Q} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {S : Subgroup Q}
    (hS : GLAPComponent 3 (fixS a) S) :
    ∃ (k : ℕ) (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), 2 ≤ k ∧ 3 * k = n ∧
      Nat.card F₀ = 2 ^ k ∧ Nonempty (PSimple 3 S ≃* StatedProj (StatedSL 2 F₀)) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  let eZ : (Q ⧸ Subgroup.center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let θ : Q ≃* StatedProj (StatedSL 2 F) := eZ.symm.trans e
  let β : MulAut (StatedProj (StatedSL 2 F)) := MulAut.congr θ a
  have hβ3 : β ^ 3 = 1 := by
    show MulAut.congr θ a ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply ha1
    apply (MulAut.congr θ).injective
    rw [map_one]
    exact h
  have hfix : fixS β = (fixS a).map θ.toMonoidHom :=
    CFSG.HardMathSupport.Solomon.Coordinator.fixSub_congr θ a
  let ψ₀ : fixS a ≃* fixS β :=
    (θ.subgroupMap (fixS a)).trans (MulEquiv.subgroupCongr hfix.symm)
  have hcontra : Group.IsSolvable (fixS β) → False := fun hs => by
    haveI : Group.IsSolvable (fixS a) :=
      Group.isSolvable_of_surjective (f := ψ₀.symm.toMonoidHom) ψ₀.symm.surjective
    exact CFSG.HardMathSupport.Dickson.KD.false_of_glaPComponent_of_solvable hS inferInstance
  rcases l2Aut3Classification_holds F β hβ3 with hb | hsol | ⟨σ, φ, γ, hφ, hβγ⟩
  · exact (hβ1 hb).elim
  · exact (hcontra hsol).elim
  obtain ⟨F₀, hF₀f, hF₀fin, hcube, ⟨ψ⟩⟩ := l2FieldFixed_holds F β hβ3 hβ1 σ φ γ hφ hβγ
  have hcube' : (Nat.card F₀) ^ 3 = 2 ^ n := by rw [← hF, hcube]
  obtain ⟨k, hk, hk3⟩ := l2c_pow_two_of_cube hcube'
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · simp at hk; omega
    ·
      have hT : Group.IsSolvable (StatedProj (StatedSL 2 F₀)) := l2c_solvable_two (by rw [hk])
      haveI := hT
      exact (hcontra (Group.isSolvable_of_surjective (f := ψ.symm.toMonoidHom)
        ψ.symm.surjective)).elim
  have hT4 : 4 ≤ Nat.card F₀ := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  let τ : fixS a ≃* StatedProj (StatedSL 2 F₀) := ψ₀.trans ψ
  have hTs : IsSimpleGroup (StatedProj (StatedSL 2 F₀)) :=
    (MulEquiv.isSimpleGroup_congr (projectiveSpecialLinearGroupEquivStatedProj 2 F₀)).1
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hT4)
  have hSimpFix : IsSimpleGroup ↥(fixS a) := (MulEquiv.isSimpleGroup_congr τ).2 hTs
  rcases eq_bot_or_eq_of_isSubnormal_of_simple hSimpFix hS.2.1 with hb | hSeq
  · exact (l2c_ne_bot_of_comp hS hb).elim
  subst hSeq
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥(fixS a)) with hO' | hO'
  · let eQ : PQuot 3 (fixS a) ≃* ↥(fixS a) :=
      (QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot
    have hsPQ : IsSimpleGroup (PQuot 3 (fixS a)) :=
      (MulEquiv.isSimpleGroup_congr (eQ.trans τ)).2 hTs
    obtain ⟨φ⟩ := l2c_pSimple_iso hq hsPQ
    exact ⟨k, F₀, hF₀f, hF₀fin, hk2, hk3, hk, ⟨φ.trans (eQ.trans τ)⟩⟩
  · exact (l2c_core_ne_top hq hO').elim

end CFSG.LocalAnalysis.GLTheoremA

end
