module

import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieSU
public import CFSG.Timmesfeld.LieEmbed.UnitaryWittN

public section

namespace CFSG.LieType.Universal.Unitary

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F]

theorem card_rootHom_range [Finite F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) :
    Nat.card (rootHom σ hσ hij hi hj).range = Nat.card F := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (CFSG.AGLEmbedding.P1Lie.rootHom_injective hσ hij hi hj hji)).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

private theorem longRootHom_injective {σ : F ≃+* F} {n : ℕ} {i : Fin n}
    (hi : i ≠ Fin.rev i) : Function.Injective (longRootHom σ hi) := by
  intro c d h
  have hm := congrArg (fun x : SU σ n => ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h
  rw [coe_longRootHom, coe_longRootHom] at hm
  have h1 : (c.toAdd : traceZero σ) = d.toAdd := by
    simpa [longRootMatrix_apply hi] using congrFun (congrFun hm i) (Fin.rev i)
  exact congrArg Multiplicative.ofAdd h1

theorem card_longRootHom_range {σ : F ≃+* F} {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) :
    Nat.card (longRootHom σ hi).range = Nat.card (traceZero σ) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (longRootHom_injective hi)).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

private theorem heisenbergMatrix_apply_i_rev {σ : F ≃+* F} {n : ℕ}
    {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) (a b : F) :
    heisenbergMatrix σ i k a b i (Fin.rev i) = b := by
  have hki : k ≠ Fin.rev i := fun h => hik (by rw [← Fin.rev_rev i, ← h, hk])
  simp [heisenbergMatrix, hi, hik.symm, hki]

private noncomputable def heisenbergParamOfSubgroup {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}
    {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    (x : heisenbergSubgroup σ hσ hi hik hk) :
    {ab : F × F // ab.2 + σ ab.2 + σ ab.1 * ab.1 = 0} :=
  ⟨(mat σ n x.1 i k, mat σ n x.1 i (Fin.rev i)), by
    obtain ⟨a, b, hab, hmat⟩ := x.2
    have h1 : mat σ n x.1 i k = a := by
      rw [mat_apply, hmat]
      exact heisenbergMatrix_apply_ik hik hk a b
    have h2 : mat σ n x.1 i (Fin.rev i) = b := by
      rw [mat_apply, hmat]
      exact heisenbergMatrix_apply_i_rev hi hik hk a b
    rwa [h1, h2]⟩

private noncomputable def heisenbergEltOfParam {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}
    {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    (ab : {ab : F × F // ab.2 + σ ab.2 + σ ab.1 * ab.1 = 0}) :
    heisenbergSubgroup σ hσ hi hik hk :=
  ⟨heisElt σ hσ hi hik hk ab.2, by
    refine ⟨ab.1.1, ab.1.2, ab.2, ?_⟩
    simpa [suMat_apply] using suMat_heisElt σ hσ hi hik hk ab.2⟩

private theorem heisenbergEltOfParam_paramOfSubgroup {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}
    {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    (x : heisenbergSubgroup σ hσ hi hik hk) :
    heisenbergEltOfParam (σ := σ) (hσ := hσ) hi hik hk
      (heisenbergParamOfSubgroup hi hik hk x) = x := by
  obtain ⟨a, b, hab, hmat⟩ := x.2
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change ((heisElt σ hσ hi hik hk (heisenbergParamOfSubgroup hi hik hk x).2 : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = ((x.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have h1 : mat σ n x.1 i k = a := by
    rw [mat_apply, hmat]
    exact heisenbergMatrix_apply_ik hik hk a b
  have h2 : mat σ n x.1 i (Fin.rev i) = b := by
    rw [mat_apply, hmat]
    exact heisenbergMatrix_apply_i_rev hi hik hk a b
  rw [show ((heisElt σ hσ hi hik hk (heisenbergParamOfSubgroup hi hik hk x).2 :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      heisenbergMatrix σ i k (mat σ n x.1 i k) (mat σ n x.1 i (Fin.rev i)) by
    simpa [suMat_apply, heisenbergParamOfSubgroup] using
      suMat_heisElt σ hσ hi hik hk (heisenbergParamOfSubgroup hi hik hk x).2]
  rw [h1, h2]
  exact hmat.symm

private theorem paramOfSubgroup_heisenbergEltOfParam {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}
    {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    (ab : {ab : F × F // ab.2 + σ ab.2 + σ ab.1 * ab.1 = 0}) :
    heisenbergParamOfSubgroup hi hik hk
      (heisenbergEltOfParam (σ := σ) (hσ := hσ) hi hik hk ab) = ab := by
  apply Subtype.ext
  apply Prod.ext
  · change mat σ n (heisElt σ hσ hi hik hk ab.2) i k = ab.1.1
    rw [mat_apply]
    rw [show ((heisElt σ hσ hi hik hk ab.2 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        heisenbergMatrix σ i k ab.1.1 ab.1.2 by
      simpa [suMat_apply] using suMat_heisElt σ hσ hi hik hk ab.2]
    exact heisenbergMatrix_apply_ik hik hk ab.1.1 ab.1.2
  · change mat σ n (heisElt σ hσ hi hik hk ab.2) i (Fin.rev i) = ab.1.2
    rw [mat_apply]
    rw [show ((heisElt σ hσ hi hik hk ab.2 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        heisenbergMatrix σ i k ab.1.1 ab.1.2 by
      simpa [suMat_apply] using suMat_heisElt σ hσ hi hik hk ab.2]
    exact heisenbergMatrix_apply_i_rev hi hik hk ab.1.1 ab.1.2

private noncomputable def heisenbergSubgroupEquivParam {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}
    {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) :
    heisenbergSubgroup σ hσ hi hik hk ≃
      {ab : F × F // ab.2 + σ ab.2 + σ ab.1 * ab.1 = 0} where
  toFun := heisenbergParamOfSubgroup hi hik hk
  invFun := heisenbergEltOfParam hi hik hk
  left_inv := heisenbergEltOfParam_paramOfSubgroup hi hik hk
  right_inv := paramOfSubgroup_heisenbergEltOfParam hi hik hk

theorem nonempty_heisenbergSubgroup_equiv {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
    {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) :
    Nonempty (heisenbergSubgroup σ hσ hi hik hk ≃
      {ab : F × F // ab.2 + σ ab.2 + σ ab.1 * ab.1 = 0}) :=
  ⟨heisenbergSubgroupEquivParam hi hik hk⟩

theorem card_heisenbergSubgroup [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) :
    Nat.card (heisenbergSubgroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF)
      hi hik hk) = (p ^ f) ^ 3 := by
  obtain ⟨e0⟩ := nonempty_heisenbergSubgroup_equiv (σ := unitaryInvolution F p f)
    (unitaryInvolution_involutive hF) hi hik hk
  have hσ := unitaryInvolution_involutive hF
  rw [Nat.card_congr e0]
  have htr : ∀ a : F, ∃ c : F, c + unitaryInvolution F p f c =
      -(unitaryInvolution F p f a * a) := by
    intro a
    refine CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq hF ?_
    rw [map_neg, map_mul, hσ, mul_comm]
  choose c hc using htr
  let e : {ab : F × F // ab.2 + unitaryInvolution F p f ab.2 +
      unitaryInvolution F p f ab.1 * ab.1 = 0} ≃
      F × traceZero (unitaryInvolution F p f) :=
    { toFun := fun ab => (ab.1.1, ⟨ab.1.2 - c ab.1.1, by
        rw [mem_traceZero, map_sub]
        linear_combination ab.2 - hc ab.1.1⟩)
      invFun := fun az => ⟨(az.1, az.2 + c az.1), by
        have h := (mem_traceZero (unitaryInvolution F p f)).1 az.2.2
        simp only [map_add]
        linear_combination h + hc az.1⟩
      left_inv := fun ab => by ext <;> simp
      right_inv := fun az => by ext <;> simp }
  rw [Nat.card_congr e, Nat.card_prod, hF, CFSG.LieType.Steinberg.card_traceZero hF]
  ring

end CFSG.LieType.Universal.Unitary
