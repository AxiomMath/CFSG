module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenPair
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem centGen_of_data {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (hcard : (Nat.card M).factorization p = 2) {e f s₁ s₂ a b : M}
    (hab : Subgroup.closure ({a, b} : Set M) = ⊤) (he : e ^ p = 1) (hf : f ^ p = 1)
    (hef : e * f = f * e) (he1 : e ≠ 1) (hfe : ∀ k < p, f ≠ e ^ k) (h₁ : s₁ * e = e * s₁)
    (h₂ : s₂ * f = f * s₂) (ha : a ∈ Subgroup.closure ({s₁, s₂} : Set M))
    (hb : b ∈ Subgroup.closure ({s₁, s₂} : Set M)) : CentGen p M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hG : ¬ p ^ 3 ∣ Nat.card M := by
    intro h
    have h0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
    have := (hp.pow_dvd_iff_le_factorization h0).1 h
    omega
  have hP : Nat.card (Subgroup.closure ({e, f} : Set M)) = p ^ 2 :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair.card_closure_pair_eq_sq
      hef he hf he1 hfe hG
  refine centGen_of_sylow hp hcard hP ?_
  have heP : e ∈ Subgroup.closure ({e, f} : Set M) := Subgroup.subset_closure (by simp)
  have hfP : f ∈ Subgroup.closure ({e, f} : Set M) := Subgroup.subset_closure (by simp)
  have hf1 : f ≠ 1 := by simpa using hfe 0 hp.pos
  have hs : ({s₁, s₂} : Set M) ⊆ centSet (Subgroup.closure ({e, f} : Set M)) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨e, heP, he1, h₁⟩
    · exact ⟨f, hfP, hf1, h₂⟩
  rw [eq_top_iff, ← hab, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact Subgroup.closure_mono hs ha
  · exact Subgroup.closure_mono hs hb

theorem factorization_sq_of_eq {n m p : ℕ} (hp : p.Prime) (hn : n = p ^ 2 * m) (hm : ¬ p ∣ m) :
    n.factorization p = 2 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [hn, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm]

theorem sporCentGen_of_model {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) {M : Type} [Group M] [Finite M]
    (eM : NativeSporadic.Carrier name ≃* M) (hcard : (Nat.card M).factorization p = 2)
    (hCG : CentGen p M) : SporCentGen name p := by
  intro S _ _ hsimple hnab ⟨e⟩
  haveI := hsimple
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hO : Nat.card (Outer S) ≤ 2 := hOut S hsimple hnab name ⟨e⟩
  have eS : S ≃* M := e.trans ((hBr name).some.symm.trans eM)
  have h3 : ¬ p ^ 3 ∣ Nat.card S := by
    rw [Nat.card_congr eS.toEquiv]
    intro h
    have h0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
    have := (hp.pow_dvd_iff_le_factorization h0).1 h
    omega
  exact ⟨autRankLe2_of_noCube hp (noElemAbelianCubeAut_of_not_dvd hp hp2 hcen hO h3), hO,
    hCG.of_mulEquiv eS.symm⟩

theorem sporPair_five_of_model {name : TauCeti.SporadicName}
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) {M : Type} [Group M] [Finite M]
    (eM : NativeSporadic.Carrier name ≃* M) (hcard : (Nat.card M).factorization 5 = 2)
    (hCG : CentGen 5 M) : SporPair name 5 :=
  sporPair_of_centGen hSpM le_rfl
    (sporCentGen_of_model Nat.prime_five (by norm_num) hOut hBr eM hcard hCG)

end CFSG.HardMathSupport.Dickson.I271
