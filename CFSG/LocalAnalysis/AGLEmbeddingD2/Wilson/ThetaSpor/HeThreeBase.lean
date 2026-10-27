
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeSmall
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.CertPBridge
public import CFSG.Sporadic.HeldB.CertPBridgeCheckInputs
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Data.CFSGNative.He.Certificate

@[expose] public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

open CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.LocalRank
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

@[expose] def heThrees : Set (Equiv.Perm (Fin 8330)) := {x | x ∈ heP ∧ orderOf x = 3}

theorem heThrees_conj {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heThrees)
    {h : Equiv.Perm (Fin 8330)} (hh : h ∈ heP) : h * x * h⁻¹ ∈ heThrees :=
  ⟨heP.mul_mem (heP.mul_mem hh hx.1) (heP.inv_mem hh), by rw [orderOf_conj_eq, hx.2]⟩

theorem exists_fix_of_orderOf_three {n : ℕ} (hn : ¬ 3 ∣ n) {x : Equiv.Perm (Fin n)}
    (hx : orderOf x = 3) : ∃ q, x q = q := by
  have hp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨q, hq⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card (α := Fin n) (by simpa using hn)
  refine ⟨q, ?_⟩
  have := MulAction.mem_fixedPoints.1 hq ⟨x, Subgroup.mem_zpowers x⟩
  simpa using this

theorem conjClass_subset_heThrees {t : Equiv.Perm (Fin 8330)} (ht : t ∈ heP)
    (ht3 : orderOf t = 3) : conjClass heP t ⊆ heThrees := by
  rintro x ⟨c, hc, rfl⟩
  exact heThrees_conj ⟨ht, ht3⟩ hc

theorem conjClass_subset_of_mem {s t : Equiv.Perm (Fin 8330)} (h : t ∈ conjClass heP s) :
    conjClass heP t ⊆ conjClass heP s := by
  rintro x ⟨c, hc, rfl⟩
  obtain ⟨d, hd, e⟩ := conj_mem_of_conj hc h
  exact ⟨d, hd, e⟩

theorem sum_fixCard_conjClass {t : Equiv.Perm (Fin 8330)} (hf : (conjClass heP t).Finite) :
    ∑ x ∈ hf.toFinset, fixCard x = (conjClass heP t).ncard * fixCard t := by
  rw [Finset.sum_congr rfl (g := fun _ => fixCard t) fun x hx => ?_]
  · rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hf]
  · rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact fixCard_conj c t

theorem theta_bot_of_mulEquiv {H K : Type*} [Group H] [Group K] [Finite H] (ψ : H ≃* K)
    (h : aschbacherSolvableCore 3 K = ⊥) : aschbacherSolvableCore 3 H = ⊥ := by
  have := CFSG.AGLEmbeddingD2.Wilson.Proving.aschbacherSolvableCore_map_mulEquiv
    Nat.prime_three ψ
  rw [h] at this
  exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 this.symm

theorem pow_three_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {b : X}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) : e b ^ 3 = 1 ∧ e b ≠ 1 :=
  ⟨by rw [← map_pow, hb3, map_one], fun h => hb1 (e.injective (by rw [h, map_one]))⟩

theorem theta_centralizerIn_conj {c u : Equiv.Perm (Fin 8330)} (hc : c ∈ heP)
    (h : aschbacherSolvableCore 3 (centralizerIn heP u) = ⊥) :
    aschbacherSolvableCore 3 (centralizerIn heP (c * u * c⁻¹)) = ⊥ :=
  theta_bot_of_mulEquiv (infCentralizerConjEquiv hc u) h

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

end
