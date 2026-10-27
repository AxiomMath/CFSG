module

public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.LieType.Steinberg.CentralExt.SLClosed

theorem psl_two_hopfMultiplier_of_mulEquiv
    {k : Type} [Field k] [Fintype k] (hk : 5 ≤ Fintype.card k) (hk9 : Fintype.card k ≠ 9)
    {X : Type} [Group X] (e : PSL(2, k) ≃* X) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Fintype.card k - 1)))) := by
  have hk' : 5 ≤ Nat.card k := by rwa [← Fintype.card_eq_nat_card]
  have hk9' : Nat.card k ≠ 9 := by rwa [← Fintype.card_eq_nat_card]
  set q : SpecialLinearGroup (Fin 2) k →* X :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) k)))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center (SpecialLinearGroup (Fin 2) k) := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) k) :=
    LinearGroups.special_linear_dimension_two_perfect (SL2Closed.exists_four_of_five_le hk')
  have hperf : Group.IsPerfect X := Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  obtain ⟨e1⟩ := SL2Closed.sl2_hopfMultiplier_mulEquiv_ker hk' hk9' q hq hker.le
  have hroots : rootsOfUnity (max (Fintype.card (Fin 2)) 1) k = rootsOfUnity 2 k := by simp
  let e2 : q.ker ≃* rootsOfUnity 2 k :=
    (MulEquiv.subgroupCongr hker).trans ((SpecialLinearGroup.center_equiv_rootsOfUnity).trans
      (MulEquiv.subgroupCongr hroots))
  have hcyc : IsCyclic (rootsOfUnity 2 k) := inferInstance
  rw [← SL2Closed.card_rootsOfUnity_two]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans (e2.trans (zmodCyclicMulEquiv hcyc).symm))⟩

@[expose] def zmodTwoEquivProd : ZMod 2 ≃+ ZMod 1 × ZMod 2 × ZMod 1 :=
  (AddEquiv.prodUnique (M := ZMod 2) (N := ZMod 1)).symm.trans
    (AddEquiv.uniqueProd (M := ZMod 2 × ZMod 1) (N := ZMod 1)).symm

theorem psl_two_four_hopfMultiplier :
    commutator PSL(2, GaloisField 2 2) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(2, GaloisField 2 2) ≃*
        Multiplicative (ZMod 2)) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e4⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hc4)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (ZMod 5) (Or.inr (by rw [Nat.card_zmod]))
  let e : PSL(2, ZMod 5) ≃* PSL(2, GaloisField 2 2) :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 5)).trans
      (e5.trans (e4.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
          (GaloisField 2 2)).symm))
  have h := psl_two_hopfMultiplier_of_mulEquiv (k := ZMod 5) (by rw [ZMod.card])
    (by rw [ZMod.card]; norm_num) e
  rw [ZMod.card] at h
  exact h

theorem psl_three_two_hopfMultiplier :
    commutator PSL(3, GaloisField 2 1) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(3, GaloisField 2 1) ≃*
        Multiplicative (ZMod 2)) := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let e₂ : PSL(3, ZMod 2) ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod 2) = Fintype.card (GaloisField 2 1) := by
    rw [ZMod.card, Fintype.card_eq_nat_card, GaloisField.card 2 1 one_ne_zero, pow_one]
  let φ : ZMod 2 ≃+* GaloisField 2 1 := FiniteField.ringEquivOfCardEq hcard
  let e : PSL(2, ZMod 7) ≃* PSL(3, GaloisField 2 1) :=
    e₄.symm.trans (e₃.symm.trans (e₂.symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 3))))
  have h := psl_two_hopfMultiplier_of_mulEquiv (k := ZMod 7) (by rw [ZMod.card]; norm_num)
    (by rw [ZMod.card]; norm_num) e
  rw [ZMod.card] at h
  exact h

theorem psl_three_four_lieModel : CFSG.Blueprint.LieModel PSL(3, GaloisField 2 2) .PSL 3 2 2 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
    GaloisField 2 2, inferInstance, inferInstance, GaloisField.card 2 2 (by norm_num),
    ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField 2 2)⟩⟩

theorem psl_three_four_hopfMultiplier :
    commutator PSL(3, GaloisField 2 2) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(3, GaloisField 2 2) ≃*
        Multiplicative (ZMod 3 × ZMod 4 × ZMod 4)) :=
  CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four _ psl_three_four_lieModel

theorem prime_eq_two_of_pow_eq {p f : ℕ} (hp : p.Prime) (hf : 0 < f) {e : ℕ}
    (h : p ^ f = 2 ^ e) : p = 2 := by
  have hdvd : p ∣ 2 ^ e := h ▸ dvd_pow_self p hf.ne'
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)

theorem griess_psl_of_ne
    (p f n : ℕ) [Fact p.Prime] (hf : 0 < f) (hn : 2 ≤ n)
    (hsmall : n = 2 → 4 ≤ p ^ f) (h29 : ¬(n = 2 ∧ p ^ f = 9)) (h42 : ¬(n = 4 ∧ p ^ f = 2)) :
    commutator PSL(n, GaloisField p f) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(n, GaloisField p f) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ f - 1)) ×
          ZMod (CFSG.Open.griessPSLExceptional n (p ^ f)).1 ×
            ZMod (CFSG.Open.griessPSLExceptional n (p ^ f)).2)) := by
  have hp := (Fact.out : p.Prime)
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow hf.ne' p)
  have hpf : ∀ e, 0 < e → p ^ f = 2 ^ e → p = 2 ∧ f = e := fun e he h => by
    have hp2 := prime_eq_two_of_pow_eq hp hf h
    subst hp2
    exact ⟨rfl, Nat.pow_right_injective le_rfl h⟩
  by_cases h24 : n = 2 ∧ p ^ f = 4
  · obtain ⟨rfl, h4⟩ := h24
    obtain ⟨rfl, rfl⟩ := hpf 2 (by norm_num) (by rw [h4]; norm_num)
    obtain ⟨hperf, ⟨e⟩⟩ := psl_two_four_hopfMultiplier
    refine ⟨hperf, ⟨e.trans (AddEquiv.toMultiplicative ?_)⟩⟩
    rw [show CFSG.Open.griessPSLExceptional 2 (2 ^ 2) = (2, 1) by decide,
      show Nat.gcd 2 (2 ^ 2 - 1) = 1 by norm_num]
    exact zmodTwoEquivProd
  by_cases h32 : n = 3 ∧ p ^ f = 2
  · obtain ⟨rfl, h2⟩ := h32
    obtain ⟨rfl, rfl⟩ := hpf 1 (by norm_num) (by rw [h2]; norm_num)
    obtain ⟨hperf, ⟨e⟩⟩ := psl_three_two_hopfMultiplier
    refine ⟨hperf, ⟨e.trans (AddEquiv.toMultiplicative ?_)⟩⟩
    rw [show CFSG.Open.griessPSLExceptional 3 (2 ^ 1) = (2, 1) by decide,
      show Nat.gcd 3 (2 ^ 1 - 1) = 1 by norm_num]
    exact zmodTwoEquivProd
  by_cases h34 : n = 3 ∧ p ^ f = 4
  · obtain ⟨rfl, h4⟩ := h34
    obtain ⟨rfl, rfl⟩ := hpf 2 (by norm_num) (by rw [h4]; norm_num)
    obtain ⟨hperf, ⟨e⟩⟩ := psl_three_four_hopfMultiplier
    refine ⟨hperf, ⟨e.trans (AddEquiv.toMultiplicative ?_)⟩⟩
    rw [show CFSG.Open.griessPSLExceptional 3 (2 ^ 2) = (4, 4) by decide,
      show Nat.gcd 3 (2 ^ 2 - 1) = 3 by norm_num]
  refine griess_psl_generic p f n hf hn ?_
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | hn5
  · have := hsmall rfl
    exact Or.inl ⟨rfl, by omega, fun h => h29 ⟨rfl, h⟩⟩
  · exact Or.inr (Or.inl ⟨le_rfl, by omega, h34⟩)
  · exact Or.inr (Or.inl ⟨by norm_num, by omega, by omega⟩)
  · exact Or.inr (Or.inr hn5)

end CFSG.LieType.Steinberg.CentralExt.SLClosed
