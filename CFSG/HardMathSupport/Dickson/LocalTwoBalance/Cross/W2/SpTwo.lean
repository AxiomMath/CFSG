module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Centralizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3ResidualQ
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem isLocallyBalancedAbs_two_psp_three_two {r : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (hr : 3 ≤ r) :
    IsLocallyBalancedAbs 3 2 (StatedProj (StatedSp r K)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  intro D hD hcard H hH _
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hrq : ¬ (r = 2 ∧ 2 ^ 1 = 2) := fun h => by omega
  obtain ⟨-, -, hinj⟩ := spProj_facts Nat.prime_two le_rfl hK' (by omega) hrq
  have hker : (proj r K).ker = ⊥ :=
    eq_bot_iff.2 ((CFSG.RankThree.PartOne.KCSpFull.ker_proj_le_center).trans
      (W2.center_statedSp_eq_bot hK r).le)
  have hprojinj : Function.Injective (proj r K) := (MonoidHom.ker_eq_bot_iff _).1 hker
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hno
    push Not at hno
    have : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 hno
    rw [this, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hd3 : d ^ 3 = 1 := hD.2 d hdD
  obtain ⟨x, hx⟩ := exists_spInnerLift_eq hK hr d
  have hdx : d = MulAut.conj (proj r K x) := hx
  have hx3 : x ^ 3 = 1 := by
    apply hprojinj
    apply hinj
    rw [map_one, map_one, map_pow, map_pow, ← hdx]
    exact hd3
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hd1 (by rw [hdx, map_one, map_one])
  have hCH : H ⊓ Subgroup.centralizer ({d} : Set (MulAut (StatedProj (StatedSp r K)))) =
      (Subgroup.centralizer ({proj r K x} : Set (StatedProj (StatedSp r K)))).map
        (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) := by
    ext g
    constructor
    · rintro ⟨-, hg⟩
      obtain ⟨y, rfl⟩ := exists_spInnerLift_eq hK hr g
      refine ⟨proj r K y, ?_, rfl⟩
      have hg' : spInnerLift r K y * d = d * spInnerLift r K y :=
        Subgroup.mem_centralizer_singleton_iff.1 hg
      have h1 : MulAut.conj (proj r K y * proj r K x) = MulAut.conj (proj r K x * proj r K y) := by
        rw [map_mul, map_mul, ← hdx]
        exact hg'
      exact Subgroup.mem_centralizer_singleton_iff.2 (hinj h1)
    · rintro ⟨t, ht, rfl⟩
      refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have ht' : t * proj r K x = proj r K x * t := Subgroup.mem_centralizer_singleton_iff.1 ht
      rw [hdx, ← map_mul, ← map_mul, ht']
  have hNN : NoNormalPPrime 3 (Subgroup.centralizer ({proj r K x} :
      Set (StatedProj (StatedSp r K)))) := by
    have blocks := spBlocks_three_two hK hr hx3 hx1
    rw [blocks.centralizer_eq, W2.noNormalPPrime_map_iff _ hprojinj]
    exact W2.noNormalPPrime_three_centralizer_statedSp hK hr hx3 hx1
  have hcore : GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer
      ({d} : Set (MulAut (StatedProj (StatedSp r K))))) = ⊥ := by
    rw [hCH]
    exact W2.core_eq_bot_of_noNormalPPrime Nat.prime_three
      ((W2.noNormalPPrime_map_iff _ hinj _).2 hNN)
  exact localDeltaIn_eq_bot_of_core_bot hdD hd1 hcore

theorem spTwoThreeBalance_holds : SpTwoThreeBalance := by
  rintro ⟨d, hv⟩ _ ⟨r, q, hd, hr3, hq⟩ _ _
  change d = _ at hd
  subst hd
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = 2 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simpa [TauCeti.ValidLieTypeIndex.fieldOrder] using hq
  have hqp : q.p = 2 := primePower_p_eq_two_of_card_eq_two hq
  exact IsLocallyBalancedAbs.of_mulEquiv
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hqp hr3)
    (isLocallyBalancedAbs_two_psp_three_two hK hr3)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
