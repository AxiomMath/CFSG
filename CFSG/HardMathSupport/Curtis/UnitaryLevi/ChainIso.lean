module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LinearGroups Matrix
open scoped Pointwise

theorem exists_chain_iso {K : Type} [Field K] [Finite K] [CharP K 2] {r ε f : ℕ}
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (J : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K))
    (S₀ : Sylow 2 (StatedSU (2 * r + ε) (2 ^ f) K))
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) :
      Set (StatedSU (2 * r + ε) (2 ^ f) K)) ≤ J) (hJ : J ≠ ⊤) :
    ∃ (I : Set ℕ) (ψ : hypSU (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε ≃*
        StatedSU (2 * r + ε) (2 ^ f) K),
      I.Nonempty ∧ I ⊆ Set.Icc 1 r ∧
      J = (flagStabilizer (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε I).map
        ψ.toMonoidHom ∧
      (hypScalars (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε).map ψ.toMonoidHom =
        (StatedScalars (Fin (2 * r + ε)) K).subgroupOf (StatedSU (2 * r + ε) (2 ^ f) K) ∧
      ∃ W : ℕ → Submodule K (Fin (2 * r + ε) → K),
        (∀ i ∈ I, Module.finrank K (W i) = i ∧ IsTotallyIsotropicSU (2 ^ f) (W i)) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≤ j → W i ≤ W j) ∧
        ∀ y : StatedSU (2 * r + ε) (2 ^ f) K, y ∈ J ↔
          ∀ i ∈ I, ∀ w ∈ W i, ((y : GL (Fin (2 * r + ε)) K) : Matrix _ _ K) *ᵥ w ∈ W i := by
  set h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf with hh
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := r) (ε := ε)
  set φ : hypSU h r ε ≃* StatedSU (2 * r + ε) (2 ^ f) K := hypTransport h hR with hφ
  set J' : Subgroup (hypSU h r ε) := J.comap φ.toMonoidHom with hJ'
  have hmemJ' : ∀ x, x ∈ J' ↔ φ x ∈ J := fun x => Iff.rfl
  let T : Sylow 2 (hypSU h r ε) :=
    Sylow.mapSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective S₀
  have hTc : (T : Subgroup (hypSU h r ε)) = (S₀ : Subgroup _).map φ.symm.toMonoidHom := rfl
  have hTJ : Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set (hypSU h r ε)) ≤ J' := by
    intro x hx
    rw [hTc, ← Subgroup.map_equiv_normalizer_eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hmemJ']
    simpa using hNJ hy
  obtain ⟨g, I, hI, hJI⟩ := ToralCensus.exists_eq_stab_hypFlag_of_normalizer_le h hr hε T J' hTJ
  have hchain := isIsotropicChain_hypFlag h (r := r) hε
  set ψ : hypSU h r ε ≃* StatedSU (2 * r + ε) (2 ^ f) K := (MulAut.conj g).trans φ with hψ
  have hψapp : ∀ x, ψ x = φ (g * x * g⁻¹) := fun x => rfl
  have hJ'Q : ∀ y : hypSU h r ε, y ∈ J' ↔ g⁻¹ * y * g ∈ flagStabilizer h r ε I := by
    intro y
    rw [hJI, mem_flagStabilizer]
    refine forall₂_congr fun i _ => ?_
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  have hJψ : J = (flagStabilizer h r ε I).map ψ.toMonoidHom := by
    ext y
    constructor
    · intro hy
      refine ⟨ψ.symm y, ?_, by simp⟩
      have h1 : φ.symm y ∈ J' := by rw [hmemJ', MulEquiv.apply_symm_apply]; exact hy
      rw [hJ'Q] at h1
      have : ψ.symm y = g⁻¹ * φ.symm y * g := by
        rw [MulEquiv.symm_apply_eq, hψapp]
        have e : g * (g⁻¹ * φ.symm y * g) * g⁻¹ = φ.symm y := by group
        rw [e, MulEquiv.apply_symm_apply]
      rw [this]
      exact h1
    · rintro ⟨x, hx, rfl⟩
      show ψ x ∈ J
      have h1 : g * x * g⁻¹ ∈ J' := by
        rw [hJ'Q]
        have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [e]
        exact hx
      exact (hmemJ' _).mp h1
  have hNonempty : I.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    refine hJ (eq_top_iff.mpr fun y _ => ?_)
    have hy : φ.symm y ∈ J' := (hJI _).mpr fun i hi => by rw [hne] at hi; exact absurd hi id
    rwa [hmemJ', MulEquiv.apply_symm_apply] at hy
  refine ⟨I, ψ, hNonempty, fun i hi => hI hi, hJψ, ?_, ?_⟩
  ·
    have hcomm : ∀ z ∈ hypScalars h r ε, g * z * g⁻¹ = z := by
      intro z hz
      obtain ⟨c, hc, hcn, hyc⟩ := hz
      have hcz : Commute z g := by
        rw [Commute, SemiconjBy]
        refine Subtype.ext (Units.ext ?_)
        have := (commute_scalar c ((g : hypSU h r ε) : GL (HypIndex r ε) K)).eq
        simp only [Subgroup.coe_mul, Units.val_mul]
        rw [hyc]
        have h3 := congrArg (fun x : GL (HypIndex r ε) K => (x : Matrix (HypIndex r ε) (HypIndex r ε) K)) this.symm
        simpa [Units.val_mul] using h3
      calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [← hcz.eq]
        _ = z := by group
    have h1 : (hypScalars h r ε).map (MulAut.conj g).toMonoidHom = hypScalars h r ε := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [hcomm y hy] using hy
      · intro hz
        exact ⟨z, hz, by simpa using hcomm z hz⟩
    have h2 : ((hypScalars h r ε).map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
        (hypScalars h r ε).map ψ.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [← h2, h1]
    have := map_hypScalars_hypTransport hR
    rw [hφ]
    exact this.trans (unitaryScalars_eq h (by omega))
  · refine ⟨fun i => transportSubspace h hR (g • hypFlag h r ε i), ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨hi1, hir⟩ := hI hi
      refine ⟨?_, ?_⟩
      · rw [finrank_transportSubspace hR, finrank_smul, hchain.1 i hir]
      · rw [ToralCensus.isTotallyIsotropicSU_iff h]
        exact (isTotallyIsotropic_transportSubspace hR _).mp
          (smul_isotropic g (hchain.2.2 i hir))
    · intro i hi j hj hij
      obtain ⟨-, hir⟩ := hI hi
      obtain ⟨-, hjr⟩ := hI hj
      refine (transportSubspace h hR).monotone ?_
      intro v hv
      obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v g _).mp hv
      exact (Submodule.mem_smul_pointwise_iff_exists _ g _).mpr ⟨w, hchain.le hij hjr hw, rfl⟩
    · intro y
      have hy : y ∈ J ↔ φ.symm y ∈ J' := by rw [hmemJ', MulEquiv.apply_symm_apply]
      rw [hy, hJI]
      refine forall₂_congr fun i _ => ?_
      rw [← ToralCensus.smul_eq_iff_mulVec_mem, ← Subgroup.smul_def]
      have e := transportSubspace_smul hR (φ.symm y) (g • hypFlag h r ε i)
      rw [← hφ, MulEquiv.apply_symm_apply] at e
      rw [← e, (transportSubspace h hR).injective.eq_iff]

end CFSG.HardMathSupport.Curtis.UnitaryLevi
