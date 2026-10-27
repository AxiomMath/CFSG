module

public import CFSG.RankThree.PartTwo.KFacts.AutG2
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank
import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.Adapters.TauCetiExceptional.BridgeG2
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut
import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley

theorem card_le_pow_succ_of_pRank_mulAut_le {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}
    (hp : p.Prime) {S B : Subgroup Ω} (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {n : ℕ}
    (hn : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p S))) ≤ n) :
    Nat.card B ≤ p ^ (n + 1) := by
  have h := CFSG.LocalAnalysis.GLTheoremA.S267.card_le_card_inf_centMod_mul_pow hp hS hperf hB
  rw [hBC] at h
  calc Nat.card B ≤ p * p ^ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p S))) := h
    _ ≤ p * p ^ n := Nat.mul_le_mul_left p (Nat.pow_le_pow_right hp.pos hn)
    _ = p ^ (n + 1) := by rw [pow_succ, mul_comm]

theorem pRank_mulAut_le_of_cyclic {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {p n : ℕ} (hp : p.Prime) (hX : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card F ≤ p ^ n)
    {C : Type} [Group C] [IsCyclic C] (Θ : MulAut X →* C)
    (hΘ : Θ.ker = (MulAut.conj : X →* MulAut X).range) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ n + 1 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.LocalAnalysis.RankFourTheoremC.conj_injective_of_center_eq_bot hZ
  have h1 : Nat.card (E.map Θ) ≤ p := by
    haveI : Finite ↥(E.map Θ) := Finite.of_surjective
      (fun e : ↥E => (⟨Θ e, Subgroup.mem_map_of_mem Θ e.2⟩ : ↥(E.map Θ)))
      (fun x => by
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 x.2
        exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩)
    refine CFSG.LocalAnalysis.RankFourTheoremC.card_le_of_isCyclic_of_pow_eq_one hp.pos
      fun x => ?_
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyx, ← map_pow, hE.2 y hy, map_one]
  have h2 : Nat.card ↥(E ⊓ Θ.ker) ≤ p ^ n := by
    have hEK : IsElemAbelian p (E ⊓ Θ.ker) := hE.mono inf_le_left
    set F := (E ⊓ Θ.ker).comap (MulAut.conj : X →* MulAut X) with hF
    have hFE : F.map (MulAut.conj : X →* MulAut X) = E ⊓ Θ.ker :=
      Subgroup.map_comap_eq_self (inf_le_right.trans hΘ.le)
    have hFc : Nat.card F = Nat.card ↥(E ⊓ Θ.ker) := by
      rw [← hFE, Subgroup.card_map_of_injective hinj]
    have hFel : IsElemAbelian p F := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
      · have := congrArg Subtype.val (hEK.1.is_comm.comm
          (⟨MulAut.conj (a : X), a.2⟩ : ↥(E ⊓ Θ.ker)) ⟨MulAut.conj (b : X), b.2⟩)
        simpa only [Subgroup.coe_mul, map_mul] using this
      · rw [map_pow, hEK.2 _ hx, map_one]
    rw [← hFc]
    exact hX F hFel
  have h3 := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Θ E
  calc Nat.card E = Nat.card (E.map Θ) * Nat.card ↥(E ⊓ Θ.ker) := h3.symm
    _ ≤ p * p ^ n := Nat.mul_le_mul h1 h2
    _ = p ^ (n + 1) := by rw [pow_succ, mul_comm]

theorem pRank_mulAut_adjointGroup_G2_le
    {K : Type} [Field K] [Finite K] (hK4 : ringChar K ≠ 3 → 4 ≤ Nat.card K) {p n : ℕ}
    (hp : p.Prime)
    (hX : ∀ F : Subgroup ↥(adjointGroup .G2 K), IsElemAbelian p F → Nat.card F ≤ p ^ n) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(adjointGroup .G2 K))) ≤ n + 1 := by
  classical
  haveI : Finite ↥(adjointGroup .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  by_cases h3 : ringChar K = 3
  ·
    haveI : CharP K 3 := ringChar.of_eq h3
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨f, hf, hK⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 3 ^ f := by
      obtain ⟨n', hpr, hcard⟩ := FiniteField.card K 3
      exact ⟨n', n'.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩
    haveI : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := ‹CharP K 3›
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
      CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form hf K hK
    exact pRank_mulAut_le_of_cyclic hZ hp hX Θ hker
  ·
    obtain ⟨hnf, -⟩ :=
      CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form h3 (hK4 h3) (K := K)
    set N := CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup .G2 K) with hN
    haveI : IsCyclic (K ≃+* K) :=
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
    haveI : IsCyclic (MulAut ↥(adjointGroup .G2 K) ⧸ N) := by
      refine isCyclic_of_surjective
        ((QuotientGroup.mk' N).comp (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K)) fun y => ?_
      obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective N y
      obtain ⟨g, σ, rfl⟩ := hnf α
      refine ⟨σ, ?_⟩
      have h1 : QuotientGroup.mk' N (MulAut.conj g) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact ⟨g, rfl⟩
      rw [MonoidHom.comp_apply, map_mul, h1, one_mul]
    exact pRank_mulAut_le_of_cyclic hZ hp hX (QuotientGroup.mk' N) (QuotientGroup.ker_mk' N)

section Exclusions

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem exists_adjointGroup_G2_equiv_psimple {p : ℕ} {Q : TauCeti.PrimePower} (hQ2 : Q.p ≠ 2)
    (hv : (TauCeti.LieTypeIndex.G2 Q).Valid)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 Q, hv⟩).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Q.p ^ Q.exponent ∧ CharP K Q.p ∧
      Nonempty (↥(adjointGroup .G2 K) ≃* PSimple p S) := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hK : Nat.card (GaloisField Q.p Q.exponent) = Q.card := by
    rw [GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨eb⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 Q hv hQ2 (GaloisField Q.p Q.exponent) hK
  have hZX : Subgroup.center ↥(adjointGroup .G2 (GaloisField Q.p Q.exponent)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  refine ⟨GaloisField Q.p Q.exponent, inferInstance, inferInstance, ?_, inferInstance,
    ⟨(((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot).symm.trans
      eb).trans e.symm⟩⟩
  rw [hK, TauCeti.PrimePower.card_def]

theorem false_of_badExcLie_G2_three (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hB : IsElemAbelian 3 B) (hB4 : 3 ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) (hB81 : Nat.card B ≠ 3 ^ 4)
    {Q : TauCeti.PrimePower} (hQ2 : Q.p ≠ 2) (hQ3 : Q.p ≠ 3)
    (hv : (TauCeti.LieTypeIndex.G2 Q).Valid)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 Q, hv⟩).Group) : False := by
  obtain ⟨K, _, _, hK, -, ⟨eX⟩⟩ := exists_adjointGroup_G2_equiv_psimple hQ2 hv e
  have hQ5 : 5 ≤ Q.p := by
    have h2 := Q.prime_p.two_le
    have h4 : Q.p ≠ 4 := by
      intro h4
      have := Q.prime_p
      rw [h4] at this
      exact absurd this (by norm_num)
    omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ Q.p := by omega
      _ = Q.p ^ 1 := (pow_one _).symm
      _ ≤ Q.p ^ Q.exponent := Nat.pow_le_pow_right Q.prime_p.pos Q.exponent_pos
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hQ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hrk := pRank_mulAut_adjointGroup_G2_le (fun _ => hK4) Nat.prime_three
    (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.card_le_nine_of_isElemAbelian_three K h3K)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr eX)] at hrk
  have hle := card_le_pow_succ_of_pRank_mulAut_le Nat.prime_three hS hperf hB hBC hrk
  exact hB81 (le_antisymm hle hB4)

end Exclusions

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
