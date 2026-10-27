module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4LocalOne
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalAbs
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.Arith
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Centralizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCore
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Generic

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem isLocallyBalancedAbs_one_of_inner_outer_good (hp : p.Prime)
    (hcen : Subgroup.center K = ⊥) {M : Type*} [Group M] (Θ : MulAut K →* M)
    (hΘ : ∀ α : MulAut K, Θ α = 1 ↔ α ∈ innerAut K)
    (hM : ∀ y : M, Nat.Coprime p (orderOf y) → y ^ 2 = 1)
    (hin : ∀ s : K, s ^ p = 1 → s ≠ 1 →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K)) = ⊥ ∧
        ∀ σ : MulAut K, σ ^ 2 = 1 → σ ∉ innerAut K → ∃ t : K, s * t = t * s ∧ σ t ≠ t)
    (hout : ∀ x : MulAut K, x ^ p = 1 → x ∉ innerAut K → FieldCoreAt p x ∨ CoreFreeAt p x) :
    IsLocallyBalancedAbs p 1 K := by
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot hcen
  intro D hD hcard H hH _
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_prime hp hcard
  have hdp : d ^ p = 1 := hD.2 d hdD
  by_cases hdin : d ∈ innerAut K
  · obtain ⟨s, rfl⟩ := hdin
    have hsp : s ^ p = 1 := hinj (by rw [map_pow, hdp, map_one])
    have hs1 : s ≠ 1 := fun h => hd1 (by rw [h, map_one])
    obtain ⟨h1, h2⟩ := hin s hsp hs1
    exact localDeltaIn_eq_bot_of_core_eq_bot hdD hd1
      (F4LocalOneAux.oneBalanced_at_of_good hp hcen Θ hΘ hM h1 h2 H hH)
  · rcases hout d hdp hdin with hfc | hcf
    · exact localDeltaIn_eq_bot_of_fieldCore hp hinj hH hdD hd1 hfc
    · exact localDeltaIn_eq_bot_of_coreFree hp hinj hH hdD hd1 hcf

end Generic

section SpTwo

open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem isLocallyBalancedAbs_one_psp_three_two {r : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (hr : 3 ≤ r) :
    IsLocallyBalancedAbs 3 1 (StatedProj (StatedSp r K)) := by
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
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_prime Nat.prime_three hcard
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
  exact localDeltaIn_eq_bot_of_core_eq_bot hdD hd1 hcore

theorem isLocallyBalancedAbs_three_one_B_two {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq : IsTwoPow q 1) (hr : 3 ≤ r) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  have hq2 : q.card = 2 := by
    rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
    norm_num
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = 2 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simpa [TauCeti.ValidLieTypeIndex.fieldOrder] using hq2
  exact IsLocallyBalancedAbs.of_mulEquiv
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq.1 hr)
    (isLocallyBalancedAbs_one_psp_three_two hK hr)

end SpTwo

end CFSG.HardMathSupport.Dickson.Bal207

end
