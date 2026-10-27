module

public import CFSG.HardMathSupport.Foote.E27.Q2Sp

public section

namespace CFSG.HardMathSupport.Foote.E27.Q2

open CFSG.Assembly.LowTwoRank Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F L : Type} [Field F] [Field L]
  (σ : F ≃+* L) (QF : (ι → F) → F) (QL : (ι → L) → L)

theorem mulVec_map_comp (A : Matrix ι ι F) (v : ι → F) :
    (A.map σ) *ᵥ (fun i => σ (v i)) = fun i => σ ((A *ᵥ v) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem isom_iff (hQ : ∀ v, QL (fun i => σ (v i)) = σ (QF v)) (A : GL ι F) :
    (∀ w, QL ((glMap σ A : Matrix ι ι L) *ᵥ w) = QL w) ↔
      ∀ v, QF ((A : Matrix ι ι F) *ᵥ v) = QF v := by
  have e : ((glMap σ A : GL ι L) : Matrix ι ι L) = (A : Matrix ι ι F).map σ := rfl
  rw [e]
  constructor
  · intro h v
    have := h (fun i => σ (v i))
    rw [mulVec_map_comp, hQ, hQ] at this
    exact σ.injective this
  · intro h w
    obtain ⟨v, rfl⟩ : ∃ v, (fun i => σ (v i)) = w := ⟨fun i => σ.symm (w i), by funext i; simp⟩
    rw [mulVec_map_comp, hQ, hQ, h]

theorem glMap_statedOmega (hQ : ∀ v, QL (fun i => σ (v i)) = σ (QF v)) :
    (StatedOmega QF).map (glMap σ).toMonoidHom = StatedOmega QL := by
  unfold StatedOmega
  rw [Subgroup.map_commutator, MonoidHom.map_closure]
  have hset : (glMap σ).toMonoidHom '' {A : GL ι F | ∀ v, QF ((A : Matrix ι ι F) *ᵥ v) = QF v} =
      {A : GL ι L | ∀ v, QL ((A : Matrix ι ι L) *ᵥ v) = QL v} := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact (isom_iff σ QF QL hQ A).mpr hA
    · intro hB
      refine ⟨(glMap σ).symm B, ?_, by simp⟩
      refine (isom_iff σ QF QL hQ _).mp ?_
      simpa using hB
  rw [hset]

noncomputable def statedOmegaEquiv (hQ : ∀ v, QL (fun i => σ (v i)) = σ (QF v)) :
    ↥(StatedOmega QF) ≃* ↥(StatedOmega QL) :=
  (MulEquiv.subgroupMap (glMap σ) (StatedOmega QF)).trans
    (MulEquiv.subgroupCongr (glMap_statedOmega σ QF QL hQ))


noncomputable def statedProjOmegaEquiv [Finite F] (hF : Nat.card F = 2)
    (QZ : (ι → ZMod 2) → ZMod 2)
    (hQ : ∀ v : ι → F, ∀ σ : F ≃+* ZMod 2, QZ (fun i => σ (v i)) = σ (QF v)) :
    StatedProj (StatedOmega QF) ≃* ↥(StatedOmega QZ) := by
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rw [Fintype.card_eq_nat_card]; exact hF
  have hbot : (StatedScalars ι F).subgroupOf (StatedOmega QF) = ⊥ := by
    rw [statedScalars_eq_bot hF]; simp
  let σ : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF').symm
  exact (QuotientGroup.quotientMulEquivOfEq hbot).trans
    (QuotientGroup.quotientBot.trans (statedOmegaEquiv σ QF QZ (fun v => hQ v σ)))

end CFSG.HardMathSupport.Foote.E27.Q2

end
