module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4N3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4N2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {n₀ : ℕ}
  {W : Subgroup (hypPSU h 2 0)}

variable [Finite K] [Fact n₀.Prime] [CharP K n₀]

theorem exists_ne_zero_mem (hp2 : n₀ ≠ 2) (hW : W ≠ ⊥) (hWp : IsPGroup n₀ ↥W) :
    ∃ v ∈ fixSp h n₀ W ⊓ comSp h n₀ W, v ≠ 0 := by
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  obtain ⟨g, hg⟩ := hypProj_surjective h 2 0 (w : hypPSU h 2 0)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hWp
  have hwn : (w : hypPSU h 2 0) ^ n₀ ^ n = 1 := by
    have : w ^ Nat.card ↥W = 1 := pow_card_eq_one'
    rw [hn] at this
    exact congrArg Subtype.val this
  set x : GL (HypIndex 2 0) K := ((g ^ 4 : hypSU h 2 0) : GL (HypIndex 2 0) K) with hxdef
  have hgW : hypProj h 2 0 g ∈ W := hg ▸ w.2
  have hxW : x ∈ preGL h W := ⟨g ^ 4, by
    show hypProj h 2 0 (g ^ 4) ∈ W
    rw [map_pow]; exact pow_mem hgW 4, rfl⟩
  have hgs : g ^ n₀ ^ n ∈ hypScalars h 2 0 := by
    have : g ^ n₀ ^ n ∈ (hypProj h 2 0).ker := by rw [MonoidHom.mem_ker, map_pow, hg, hwn]
    rwa [ker_hypProj] at this
  have hxp : x ^ n₀ ^ n = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, pow_four_of_mem_hypScalars hgs,
      Subgroup.coe_one]
  have hx1 : x ≠ 1 := by
    intro h1
    have hg4 : g ^ 4 = 1 := Subtype.ext h1
    have hww : (w : hypPSU h 2 0) ^ 4 = 1 := by rw [← hg, ← map_pow, hg4, map_one]
    have hd4 : orderOf (w : hypPSU h 2 0) ∣ 4 := orderOf_dvd_of_pow_eq_one hww
    have hdp : orderOf (w : hypPSU h 2 0) ∣ n₀ ^ n := orderOf_dvd_of_pow_eq_one hwn
    have hcop : Nat.Coprime 4 (n₀ ^ n) := by
      refine Nat.Coprime.pow_right n ?_
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2
        ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2))
    exact hw1 (Subtype.ext (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd4 hdp)))
  have hD : ∃ v, (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v - v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx1
    apply Units.ext
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simp only [Pi.sub_apply, mulVec_single_one, Pi.zero_apply, sub_eq_zero, Matrix.col_apply]
      at this
    rw [Units.val_one, Matrix.one_apply, this, Pi.single_apply]
  obtain ⟨v₀, hv₀⟩ := hD
  have hv₀D : (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v₀ - v₀ ∈ comSp h n₀ W :=
    Submodule.subset_span ⟨x, v₀, ⟨hxW, n, hxp⟩, rfl⟩
  have : Nontrivial ↥(comSp h n₀ W) := ⟨⟨⟨_, hv₀D⟩, 0, fun h0 => hv₀ (congrArg Subtype.val h0)⟩⟩
  have hnil := isNilpotent_comap (h := h) hWp
  obtain ⟨S⟩ : Nonempty (Sylow n₀ ↥(W.comap (hypProj h 2 0))) := inferInstance
  have hHD : ∀ t : ↥(W.comap (hypProj h 2 0)), ∀ v ∈ comSp h n₀ W,
      Matrix.mulVecLin (((t : hypSU h 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) v ∈ comSp h n₀ W :=
    fun t v hv => mulVec_mem_comSp (Subgroup.le_normalizer ⟨t.1, t.2, rfl⟩) hv
  let ρ : ↥(W.comap (hypProj h 2 0)) →* Module.End K ↥(comSp h n₀ W) :=
    { toFun := fun t => (Matrix.mulVecLin (((t : hypSU h 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K)).restrict (hHD t)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp [mulVec_mulVec] }
  obtain ⟨⟨v, hvD⟩, hv0, hvfix⟩ :=
    CFSG.LieType.BorelTits.exists_fixed_ne_zero ρ n₀ (S : Subgroup _) S.isPGroup'
  refine ⟨v, ⟨fun y hy => ?_, hvD⟩, fun h0 => hv0 (Subtype.ext h0)⟩
  obtain ⟨⟨t, ht, rfl⟩, m, hm⟩ := hy
  have htS : (⟨t, ht⟩ : ↥(W.comap (hypProj h 2 0))) ∈ S := by
    refine mem_sylow_of_normal S ⟨m, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hm
  exact congrArg Subtype.val (hvfix _ htS)

theorem exists_subspace (hp2 : n₀ ≠ 2) (hW : W ≠ ⊥) (hWp : IsPGroup n₀ ↥W) :
    ∃ N : Submodule K (HypIndex 2 0 → K), N ≠ ⊥ ∧
      (∀ x ∈ N, ∀ y ∈ N, hypForm h 2 0 x y = 0) ∧
      (∀ A : GL (HypIndex 2 0) K, A ∈ normalizer ((preGL h W : Subgroup (GL (HypIndex 2 0) K)) :
          Set (GL (HypIndex 2 0) K)) →
        ∀ v ∈ N, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v ∈ N) ∧
      ∀ (A : GL (HypIndex 2 0) K) (σ : K ≃+* K), (∀ c, σ c = h.bar c) →
        ∀ hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0,
        (∀ w ∈ W, semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ w ∈ W) →
        (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1 →
        ∀ v ∈ N, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ barV h v ∈ N := by
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem hp2 hW hWp
  refine ⟨fixSp h n₀ W ⊓ comSp h n₀ W, fun h0 => hv0 (by rw [h0] at hv; exact hv),
    fun x hx y hy => hypForm_fixSp_comSp hx.1 hy.2, fun A hA u hu =>
      ⟨mulVec_mem_fixSp hA hu.1, mulVec_mem_comSp hA hu.2⟩,
    fun A σ hσ hx hWA hAA u hu =>
      ⟨semilin_mem_fixSp (isPElt_semilin hσ hx hWA) hAA hu.1,
        semilin_mem_comSp (isPElt_semilin hσ hx hWA) hu.2⟩⟩

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
