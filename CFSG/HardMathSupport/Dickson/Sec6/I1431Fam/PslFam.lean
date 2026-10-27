module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Low
public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem scalars_pow_three_eq_one_trivial {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n)
    (hcop : Nat.Coprime 3 (Nat.gcd n (Nat.card K - 1))) :
    ∀ z ∈ scalars n K, z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  obtain ⟨c, hcn, hzc⟩ := mem_scalars.1 hz
  have : Fintype K := Fintype.ofFinite K
  have hc3 : c ^ 3 = 1 := by
    have h1 : ((z ^ 3 : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [hz3]; rfl
    rw [Matrix.SpecialLinearGroup.coe_pow, hzc, ← map_pow] at h1
    have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact h2
  have hcK : c ^ (Nat.card K - 1) = 1 := by
    have := pow_card_eq_one' (x := c)
    rwa [Nat.card_units] at this
  have hd1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
  have hd2 : orderOf c ∣ Nat.gcd n (Nat.card K - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcn) (orderOf_dvd_of_pow_eq_one hcK)
  have hd3 : orderOf c ∣ Nat.gcd 3 (Nat.gcd n (Nat.card K - 1)) := Nat.dvd_gcd hd1 hd2
  rw [hcop, Nat.dvd_one] at hd3
  have hc1 : c = 1 := orderOf_eq_one_iff.1 hd3
  apply Subtype.ext
  rw [hzc, hc1]
  simp

theorem descendHom_isInnerAut {Y P : Type} [Group Y] [Finite Y] [Group P] [Finite P]
    (e : (Y ⧸ Subgroup.center Y) ≃* P) {a : MulAut Y} (ha : a ∈ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut Y) :
    IsInnerAut (descendHom e a) := by
  obtain ⟨y, rfl⟩ := ha
  refine ⟨descendProj e y, ?_⟩
  ext p
  obtain ⟨y', rfl⟩ := descendProj_surjective e p
  rw [← descendHom_compat e (MulAut.conj y) y', MulAut.conj_apply, MulAut.conj_apply, map_mul,
    map_mul, map_inv]

theorem y1431_noCfg_pslGoodHigh_ne3
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    Y1431NoCfgAt (fun t n p f => FamPslGoodHigh t n p f ∧ p ≠ 3) := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨⟨rfl, hn3, hcop, -⟩, hp3⟩ := hF
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  let e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
  have hin := c.mem_innerAut_of_outDerived (MulEquiv.refl _)
    (fun _ => outDerived3_pslGood (Y ⧸ Subgroup.center Y) .PSL n p f hadm ht ⟨rfl, hn3, hcop⟩ hm)
  have cS := c.descend e
  have hcopK : Nat.Coprime 3 (Nat.gcd n (Nat.card K - 1)) := by rw [hK]; exact hcop
  have hpk : (3 : K) ≠ 0 := CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card hadm.1 hp3 hK
  have hZ := scalars_pow_three_eq_one_trivial (by omega) hcopK
  refine s1431_false_psl hn3 hpk hZ hO cS (ten_le_of_cube hq0 hqq) ?_
  rintro a ⟨a', ha', rfl⟩
  exact descendHom_isInnerAut e (hin a' ha')

end CFSG.HardMathSupport.Dickson.Sec6.I1431
