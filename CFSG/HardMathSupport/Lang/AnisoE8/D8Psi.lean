module

public import CFSG.HardMathSupport.Lang.AnisoE8.D8Conj

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE8

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups

@[expose] def E8D8Family (K : Type) [Field K] [Finite K] :
    Prop :=
  ∃ ρ : Fin 8 → SL(2, K) →* adjointGroup .E8 K,
    (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = e8D8Chain K k) ∧
    (∀ i j : Fin 8, i ≠ j → ¬ edgeD 8 i j → ¬ edgeD 8 j i →
      ∀ u ∈ e8D8Chain K i, ∀ v ∈ e8D8Chain K j, u * v = v * u) ∧
    (∀ i j : Fin 8, edgeD 8 i j → ∃ ψ : SL(3, K) →* adjointGroup .E8 K,
      ψ.comp (CFSG.ClassicalInvolution.WeakCT.blk K 0) = ρ i ∧
        ψ.comp (CFSG.ClassicalInvolution.WeakCT.blk K 1) = ρ j)

section Main


theorem exists_psi_D8_E8_of_family {K : Type} [Field K] [Finite K] (hfam : E8D8Family K) :
    ∃ Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)) ∧
      Ψ.range = ⨆ k, e8D8Chain K k := by
  obtain ⟨ρ, hρ', hcomm, hψ⟩ := hfam
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus 8 (ringChar K) n :=
    ⟨hℓ, n.pos, by norm_num⟩
  obtain ⟨Ψ, h1, h2, -, -⟩ := spinPlus_frame_subgroup hadm (by norm_num) hK hcomm
    hρ' hψ
  exact ⟨Ψ, h1, h2⟩

theorem exists_conj_plane_d8_of_family {K : Type} [Field K] [Finite K] (hfam : E8D8Family K)
    {p : ℕ} [Fact p.Prime] (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8)
    {e : adjointGroup .E8 K} (he1 : e ∈ ⨆ k, e8D8Chain K k) (heo : orderOf e = p)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) :
    ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ ⨆ k, e8D8Chain K k ∧
      e ∈ E₀.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family hfam
  exact exists_conj_plane_d8_of_psi he Ψ hker hrange he1 heo E₀ hE₀p hE₀c

end Main

end CFSG.HardMathSupport.Lang.AnisoE8
