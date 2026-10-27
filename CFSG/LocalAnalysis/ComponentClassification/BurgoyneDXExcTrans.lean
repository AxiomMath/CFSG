module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcComp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (commutatorElement_mul_mem_center)
open scoped commutatorElement

theorem autFixed_congr {P P' : Type*} [Group P] [Group P'] (Θ : P ≃* P') (κ : MulAut P) :
    autFixed (MulAut.congr Θ κ) = (autFixed κ).map Θ.toMonoidHom := by
  ext y
  rw [mem_autFixed_iff, Subgroup.mem_map]
  constructor
  · intro hy
    refine ⟨Θ.symm y, ?_, by simp⟩
    rw [mem_autFixed_iff]
    apply Θ.injective
    rw [MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    rw [mem_autFixed_iff] at hx
    change Θ (κ (Θ.symm (Θ x))) = Θ x
    rw [MulEquiv.symm_apply_apply, hx]

variable {K : Type} [Field K] {d : ℕ}

theorem transport_comp [Finite K] {R R' : GL (Fin d) K} {M : Subgroup (GL (Fin d) K)}
    (hM : M ≤ matrixDerived (oQ R)) (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, oQ R' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * oQ R v)
    {g : similarityPairs (oQ R)}
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ g))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ g)))) :
    ((M.map (MulAut.conj S).toMonoidHom).subgroupOf (matrixDerived (oQ R'))).map (projH _) ≤
        autFixed (oκ _ (transPair S ν hS g)) ∧
      IsPComponent 2 ((((M.map (MulAut.conj S).toMonoidHom).subgroupOf
        (matrixDerived (oQ R'))).map (projH _)).subgroupOf
          (autFixed (oκ _ (transPair S ν hS g)))) := by
  set Θ := oTransport S ν hS with hΘ
  have hQ : ((M.map (MulAut.conj S).toMonoidHom).subgroupOf (matrixDerived (oQ R'))).map
      (projH _) = ((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).map Θ.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨X', hX', rfl⟩
      obtain ⟨m, hm, hmX⟩ := mem_subgroupOf.1 hX'
      refine ⟨projH _ ⟨m, hM hm⟩, ⟨⟨m, hM hm⟩, mem_subgroupOf.2 hm, rfl⟩, ?_⟩
      change Θ (projH _ ⟨m, hM hm⟩) = projH _ X'
      rw [hΘ, oTransport_proj]
      congr 1
      apply Subtype.ext
      rw [coe_derivedTransport, ← hmX]
      rfl
    · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩
      refine ⟨derivedTransport S ν hS X, mem_subgroupOf.2 ⟨X, mem_subgroupOf.1 hX, ?_⟩, ?_⟩
      · rw [coe_derivedTransport]
        rfl
      · change projH _ (derivedTransport S ν hS X) = Θ (projH _ X)
        rw [hΘ, oTransport_proj]
  have hF : autFixed (oκ _ (transPair S ν hS g)) = (autFixed (oκ _ g)).map Θ.toMonoidHom := by
    rw [← oTransport_kappa, autFixed_congr]
  rw [hQ, hF]
  exact ⟨map_mono hQs,
    (isPComponent_subgroupOf_map_iff 2 Nat.prime_two (f := Θ.toMonoidHom) Θ.injective).1 hQc⟩

theorem conj_le_of_map_le {Q : QuadraticForm K (Fin d → K)} {M : Subgroup (GL (Fin d) K)}
    (hperf : ⁅M, M⁆ = M) (B : GL (Fin d) K)
    (hBH : ∀ X ∈ M, B * X * B⁻¹ ∈ matrixDerived Q)
    (hB : ∀ X (hX : X ∈ M), projH _ (⟨B * X * B⁻¹, hBH X hX⟩ : matrixDerived Q) ∈
      (M.subgroupOf (matrixDerived Q)).map (projH _)) :
    ∀ X ∈ M, B * X * B⁻¹ ∈ M := by
  set H := matrixDerived Q with hH
  have hlift : ∀ X (hX : X ∈ M), ∃ m ∈ M.subgroupOf H, ∃ z ∈ center H,
      (⟨B * X * B⁻¹, hBH X hX⟩ : H) = m * z := by
    intro X hX
    obtain ⟨m, hm, hmX⟩ := hB X hX
    exact ⟨m, hm, m⁻¹ * ⟨_, hBH X hX⟩,
      scalars_subgroupOf_le_center ((projH_eq_projH_iff).1 hmX), by group⟩
  have hperfN : ⁅M.map (MulAut.conj B).toMonoidHom, M.map (MulAut.conj B).toMonoidHom⁆ =
      M.map (MulAut.conj B).toMonoidHom := by
    rw [← Subgroup.map_commutator, hperf]
  have hN : M.map (MulAut.conj B).toMonoidHom ≤ M := by
    rw [← hperfN, commutator_le]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨m₁, hm₁, z₁, hz₁, e₁⟩ := hlift a ha
    obtain ⟨m₂, hm₂, z₂, hz₂, e₂⟩ := hlift b hb
    have e : ⁅(⟨B * a * B⁻¹, hBH a ha⟩ : H), ⟨B * b * B⁻¹, hBH b hb⟩⁆ = ⁅m₁, m₂⁆ := by
      rw [e₁, e₂, commutatorElement_mul_mem_center m₁ m₂ hz₁ hz₂]
    have e' := congrArg Subtype.val e
    change ⁅B * a * B⁻¹, B * b * B⁻¹⁆ = ⁅(m₁ : GL (Fin d) K), (m₂ : GL (Fin d) K)⁆ at e'
    change ⁅B * a * B⁻¹, B * b * B⁻¹⁆ ∈ M
    rw [e', ← hperf]
    exact commutator_mem_commutator (mem_subgroupOf.1 hm₁) (mem_subgroupOf.1 hm₂)
  intro X hX
  exact hN ⟨X, hX, rfl⟩

end CFSG.ComponentClassification.Burgoyne.DX
