module

public import CFSG.LieType.OutStructureA2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SBasic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
open CFSG.RankThree.PartOne.OutStructure

theorem exists_pow_eq_of_ringAut {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) : ∃ n : ℕ, ∀ x : K, σ x = x ^ (ringChar K ^ n) := by
  classical
  let p := ringChar K
  have hp : p.Prime := CharP.char_is_prime K p
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := ringChar.of_eq rfl
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Algebra.IsAlgebraic (ZMod p) K := Algebra.IsAlgebraic.of_finite _ _
  let σa : K ≃ₐ[ZMod p] K := AlgEquiv.ofRingEquiv (f := σ) (fun x => by
    have h : (σ : K →+* K).comp (algebraMap (ZMod p) K) = algebraMap (ZMod p) K :=
      RingHom.ext_zmod _ _
    exact congrFun (congrArg DFunLike.coe h) x)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) K).2 σa
  refine ⟨n, fun x => ?_⟩
  have hx := congrArg (fun e : K ≃ₐ[ZMod p] K => e x) hn
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    ZMod.card] at hx
  exact hx.symm

theorem exists_fieldPart_of_outPChain_outLift {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hChain : OutPChain p X) (hLift : OutLift p X)
    (hSylow : ∀ S : Sylow p (Outer X), (S : Subgroup (Outer X)).Normal) :
    ∃ F : Subgroup (MulAut X),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner X = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F).index ∧
      ∀ x : MulAut X, (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F := by
  obtain ⟨R, hRp, hRI, hidx⟩ := hLift
  obtain ⟨D, E, hID, hD2, hpE, hcomp⟩ := hChain
  have hRD : R ⊓ D = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro x ⟨hxR, hxD⟩
    by_contra hx1
    have hxR' : x ∈ R := hxR
    obtain ⟨k, hk⟩ := hRp ⟨x, hxR'⟩
    have hk1 : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hxI : x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
      hD2 x hxD k (by rw [hk1]; exact (CFSG.ComponentClassification.OuterAutomorphisms.inner X).one_mem)
    exact hx1 ((Subgroup.mem_bot).mp (hRI ▸ ⟨hxR, hxI⟩))
  have hcompR : ∀ x ∈ R, ∀ y ∈ R, (∃ m : ℤ, x * y ^ m = 1) ∨ ∃ m : ℤ, y * x ^ m = 1 := by
    intro x hxR y hyR
    have hxE : x ∈ E := hpE x (by
      obtain ⟨k, hk⟩ := hRp ⟨x, hxR⟩
      exact ⟨k, by rw [show x ^ (p ^ k) = 1 by simpa using congrArg Subtype.val hk]; exact hID (one_mem _)⟩)
    have hyE : y ∈ E := hpE y (by
      obtain ⟨k, hk⟩ := hRp ⟨y, hyR⟩
      exact ⟨k, by rw [show y ^ (p ^ k) = 1 by simpa using congrArg Subtype.val hk]; exact hID (one_mem _)⟩)
    have hxk : ∃ k : ℕ, x ^ (p ^ k) ∈ D := by
      obtain ⟨k, hk⟩ := hRp ⟨x, hxR⟩
      exact ⟨k, by rw [show x ^ (p ^ k) = 1 by simpa using congrArg Subtype.val hk]; exact hID (one_mem _)⟩
    have hyk : ∃ k : ℕ, y ^ (p ^ k) ∈ D := by
      obtain ⟨k, hk⟩ := hRp ⟨y, hyR⟩
      exact ⟨k, by rw [show y ^ (p ^ k) = 1 by simpa using congrArg Subtype.val hk]; exact hID (one_mem _)⟩
    rcases hcomp x hxE y hyE hxk hyk with ⟨m, hm⟩ | ⟨m, hm⟩
    · left
      refine ⟨m, ?_⟩
      have hmem : x * y ^ m ∈ R ⊓ D := ⟨R.mul_mem hxR (R.zpow_mem hyR m), hm⟩
      rw [hRD, Subgroup.mem_bot] at hmem
      exact hmem
    · right
      refine ⟨m, ?_⟩
      have hmem : y * x ^ m ∈ R ⊓ D := ⟨R.mul_mem hyR (R.zpow_mem hxR m), hm⟩
      rw [hRD, Subgroup.mem_bot] at hmem
      exact hmem
  have hRcyc : IsCyclic ↥R := by
    classical
    haveI : Fintype R := Fintype.ofFinite R
    obtain ⟨r, hr⟩ := Finite.exists_max (fun x : R => orderOf x)
    have hgen : ∀ y : R, y ∈ Subgroup.zpowers r := by
      intro y
      rcases hcompR r.1 r.2 y.1 y.2 with ⟨m, hm⟩ | ⟨m, hm⟩
      ·
        have hr_mem : r ∈ Subgroup.zpowers y := by
          have hmX : (r : MulAut X) * (y : MulAut X) ^ m = 1 := hm
          have hX : (r : MulAut X) = (y : MulAut X) ^ (-m) := by
            rw [zpow_neg]
            exact eq_inv_of_mul_eq_one_left hmX
          have hR : r = y ^ (-m) := by
            apply Subtype.ext
            simpa using hX
          rw [hR]
          exact (Subgroup.zpowers y).zpow_mem (Subgroup.mem_zpowers y) (-m)
        have hle : Subgroup.zpowers r ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hr_mem
        have hcard : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers r) := by
          rw [Nat.card_zpowers, Nat.card_zpowers]
          exact hr y
        have heq : Subgroup.zpowers r = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge hle hcard
        rw [heq]
        exact Subgroup.mem_zpowers y
      ·
        have hmX : (y : MulAut X) * (r : MulAut X) ^ m = 1 := hm
        have hX : (y : MulAut X) = (r : MulAut X) ^ (-m) := by
          rw [zpow_neg]
          exact eq_inv_of_mul_eq_one_left hmX
        have hR : y = r ^ (-m) := by
          apply Subtype.ext
          simpa using hX
        rw [hR]
        exact (Subgroup.zpowers r).zpow_mem (Subgroup.mem_zpowers r) (-m)
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨r, eq_top_iff.mpr (fun x _ => hgen x)⟩
  exact exists_fieldPart_of_isPGroup hp R hRp hRcyc hRI hSylow hidx

end CFSG.LieType.OutStructure
