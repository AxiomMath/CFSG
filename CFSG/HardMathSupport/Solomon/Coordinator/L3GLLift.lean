module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3GLModelL
public import CFSG.HardMathSupport.Solomon.Coordinator.L3GLModelU
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511
import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma58
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.GH74.Statements
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.Quasithin.Background.A3StructureFacts
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne.KCUnitaryModel

theorem l3gl_transport {Y P : Type*} [Group Y] [Group P] (e : Y ≃* P) {D H : Subgroup (MulAut Y)}
    (hD : IsEkIn 3 2 ⊤ D) (hH : innerAut Y ≤ H) (hne : localDeltaIn 3 H D ≠ ⊥) (y : Y)
    (hy : ∀ d ∈ D, d * MulAut.conj y = MulAut.conj y * d) :
    IsElemAbelian 3 (D.map (MulAut.congr e).toMonoidHom) ∧
      Nat.card (D.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 ∧
      innerAut P ≤ H.map (MulAut.congr e).toMonoidHom ∧
      localDeltaIn 3 (H.map (MulAut.congr e).toMonoidHom) (D.map (MulAut.congr e).toMonoidHom) ≠ ⊥ ∧
      ∀ d ∈ D.map (MulAut.congr e).toMonoidHom,
        d * MulAut.conj (e y) = MulAut.conj (e y) * d := by
  have hD' := isEkIn_map_mulEquiv 3 2 (MulAut.congr e) hD
  refine ⟨hD'.2.1, hD'.2.2, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨MulAut.conj (e.symm x), hH ⟨_, rfl⟩, ?_⟩
    change MulAut.congr e (MulAut.conj (e.symm x)) = MulAut.conj x
    rw [CFSG.HardMathSupport.Timmesfeld.Balance.congr_conj_apply, MulEquiv.apply_symm_apply]
  · rw [localDeltaIn_map_mulEquiv]
    exact fun h => hne ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.congr e).injective).1 h)
  · rintro _ ⟨d, hd, rfl⟩
    change MulAut.congr e d * MulAut.conj (e y) = MulAut.conj (e y) * MulAut.congr e d
    rw [← CFSG.HardMathSupport.Timmesfeld.Balance.congr_conj_apply, ← map_mul, ← map_mul, hy d hd]

theorem l3gl_lift_L {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (θ : Y ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F)) {D H : Subgroup (MulAut Y)} (hD : IsEkIn 3 2 ⊤ D)
    (hH : innerAut Y ≤ H) (hne : localDeltaIn 3 H D ≠ ⊥) (y : Y)
    (hy : ∀ d ∈ D, d * MulAut.conj y = MulAut.conj y * d) :
    ∃ ŷ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F), ŷ ^ 3 = 1 ∧ θ y = QuotientGroup.mk ŷ := by
  set e : Y ≃* projectiveSL 3 F := θ.trans (psiPSL F) with he
  obtain ⟨h1, h2, h3, h4, h5⟩ := l3gl_transport e hD hH hne y hy
  obtain ⟨s, hs⟩ := proj_surjective 3 F (e y)
  have hcube := l3gl_cube_of_localDeltaIn_ne_bot h1 (by rw [h2]; norm_num) h3 h4 s
    (by rw [hs]; exact h5)
  refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F s, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hcube
  · apply (psiPSL F).injective
    rw [psiPSL_mk, hs]
    rfl

theorem l3gl_two_lt {p f : ℕ} {K : Type} [Field K] {Y : Type*} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (h : UnitaryFieldData p f K)
    (θ : Y ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) : 2 < p ^ f := by
  have := h.finite
  have hp := h.prime
  have hf := h.one_le
  by_contra hle
  push Not at hle
  have h2 : p ^ f = 2 := by
    have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [h.card, show 2 * f = f * 2 from mul_comm _ _, pow_mul, h2]
    norm_num
  have e' : Y ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) := by
    have := θ
    rw [show p ^ f = 2 ^ 1 from h2] at this
    exact this
  have hsolP : Group.IsSolvable (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K)) :=
    CFSG.Quasithin.isSolvable_statedProj_one hF
  have hsolY : Group.IsSolvable Y :=
    Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
  have : Group.IsPerfect Y := (Group.isPerfect_def (G := Y)).2 hY.1
  have : Nontrivial Y := by
    have := hY.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
  exact Group.IsPerfect.not_isSolvable Y hsolY

theorem l3gl_lift_U {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {K : Type} [Field K] [Finite K] {q : ℕ} (hcard : Nat.card K = q ^ 2) (hq3 : q % 3 = 2)
    (hq8 : q ≠ 8) (θ : Y ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 q K)) {D H : Subgroup (MulAut Y)}
    (hD : IsEkIn 3 2 ⊤ D) (hH : innerAut Y ≤ H) (hne : localDeltaIn 3 H D ≠ ⊥) (y : Y)
    (hy : ∀ d ∈ D, d * MulAut.conj y = MulAut.conj y * d) :
    ∃ ŷ : ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 q K), ŷ ^ 3 = 1 ∧ θ y = QuotientGroup.mk ŷ := by
  obtain ⟨p, f, rfl, ⟨h⟩⟩ := exists_unitaryFieldData hcard
  have hq := l3gl_two_lt hY h θ
  set e : Y ≃* primeFormP h (idGram K 3) :=
    θ.trans ((unitaryPSUEquiv h (n := 3) (by norm_num)).symm.trans (psuToPrimeForm h)) with he
  obtain ⟨h1, h2, h3, h4, h5⟩ := l3gl_transport e hD hH hne y hy
  obtain ⟨s, hs⟩ := unitaryProj_surjective h 3
    ((unitaryPSUEquiv h (n := 3) (by norm_num)).symm (θ y))
  set g : gramSU h (idGram K 3) := ⟨(s : GL (Fin 3) K),
    (SetLike.ext_iff.mp (unitarySU_eq_gramSU h 3) (s : GL (Fin 3) K)).mp s.2⟩ with hg
  have hey : e y = (g : primeFormP h (idGram K 3)) := by
    have : e y = psuToPrimeForm h ((unitaryPSUEquiv h (n := 3) (by norm_num)).symm (θ y)) := rfl
    rw [this, ← hs]
    rfl
  have hcube := l3gl_cube_of_localDeltaIn_ne_bot_U h hq hq8 (by omega) h1 h2 h3 h4 g
    (by rw [← hey]; exact h5)
  refine ⟨s, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hcube
  · have := congrArg (unitaryPSUEquiv h (n := 3) (by norm_num)) hs
    rw [MulEquiv.apply_symm_apply, unitaryPSUEquiv_unitaryProj] at this
    exact this.symm

theorem hasOrderThreeLift_of_localDeltaIn_ne_bot {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (hty : IsExtremalType Y) {D H : Subgroup (MulAut Y)}
    (hD : IsEkIn 3 2 ⊤ D) (hH : innerAut Y ≤ H) (hne : localDeltaIn 3 H D ≠ ⊥) (y : Y)
    (hy1 : y ≠ 1) (hy : ∀ d ∈ D, d * MulAut.conj y = MulAut.conj y * d) :
    HasOrderThreeLift Y y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hty with ⟨K, _, _, hK3, ⟨θ⟩⟩ | ⟨K, _, _, q, hcard, hq3, hq8, ⟨θ⟩⟩
  · obtain ⟨ŷ, h3, hθ⟩ := l3gl_lift_L θ hD hH hne y hy
    have hne1 : ŷ ≠ 1 := by
      rintro rfl
      exact hy1 (θ.injective (hθ.trans ((QuotientGroup.mk_one _).trans (map_one θ).symm)))
    exact Or.inl ⟨K, inferInstance, inferInstance, θ, hK3, ŷ, orderOf_eq_prime h3 hne1, hθ⟩
  · obtain ⟨ŷ, h3, hθ⟩ := l3gl_lift_U hY hcard hq3 hq8 θ hD hH hne y hy
    have hne1 : ŷ ≠ 1 := by
      rintro rfl
      exact hy1 (θ.injective (hθ.trans ((QuotientGroup.mk_one _).trans (map_one θ).symm)))
    exact Or.inr ⟨K, inferInstance, inferInstance, q, θ, hcard, hq3, ŷ, orderOf_eq_prime h3 hne1,
      hθ⟩

end CFSG.HardMathSupport.Solomon.Coordinator
