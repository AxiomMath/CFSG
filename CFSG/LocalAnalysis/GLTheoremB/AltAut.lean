module

public import CFSG.LocalAnalysis.GLTheoremB.S7Facts
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open Equiv Equiv.Perm CFSG.Open

namespace S7

@[expose] noncomputable def conjEquiv : S ≃* MulAut ↥Alt7 :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := Alt7))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))

@[expose] noncomputable def permOfAut {K : Type*} [Group K] (e : K ≃* ↥Alt7) : MulAut K →* S :=
  conjEquiv.symm.toMonoidHom.comp (MulAut.congr e).toMonoidHom

theorem permOfAut_injective {K : Type*} [Group K] (e : K ≃* ↥Alt7) :
    Function.Injective (permOfAut e) :=
  conjEquiv.symm.injective.comp (MulAut.congr e).injective

theorem permOfAut_spec {K : Type*} [Group K] (e : K ≃* ↥Alt7) (φ : MulAut K) (k : K) :
    ((e (φ k) : ↥Alt7) : S) = permOfAut e φ * (e k : S) * (permOfAut e φ)⁻¹ := by
  have h : conjEquiv (permOfAut e φ) = MulAut.congr e φ := by
    simp [permOfAut]
  have h2 := congrArg (fun ψ : MulAut ↥Alt7 => ((ψ (e k) : ↥Alt7) : S)) h
  simpa [conjEquiv, MulAut.conjNormal_apply] using h2.symm

theorem exists_pCores_of_aut {K D : Type*} [Group K] [Group D] [Finite D] (e : K ≃* ↥Alt7)
    (ρ : D →* MulAut K) (hρ : Function.Injective ρ) (hD : Nat.card D = 9) :
    ∃ W : D → Subgroup K,
      (∀ d : D, d ≠ 1 → IsPGroup 2 ↥(W d) ∧ (∀ k ∈ W d, ρ d k = k) ∧
        ∀ c : K, ρ d c = c → c ∈ Subgroup.normalizer (W d : Set K)) ∧
      (⊤ : Subgroup K) ≤ ⨆ d : D, ⨆ (_ : d ≠ 1), W d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : D →* S := (permOfAut e).comp ρ with hπ
  have hπi : Function.Injective π := (permOfAut_injective e).comp hρ
  have hR : Nat.card ↥π.range = 9 := by
    rw [← hD]
    exact (Nat.card_congr (MonoidHom.ofInjective hπi).toEquiv).symm
  have hspec : ∀ (d : D) (k : K), ((e (ρ d k) : ↥Alt7) : S) =
      π d * (e k : S) * (π d)⁻¹ := fun d k => permOfAut_spec e (ρ d) k
  refine ⟨fun d => (pCoreOf 2 (cA (π d))).map e.symm.toMonoidHom, ?_, ?_⟩
  · intro d hd1
    refine ⟨(CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (cA (π d))).map _, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hwc : (w : S) * π d = π d * w :=
        mem_cA.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 (cA (π d)) hw)
      apply e.injective
      apply Subtype.ext
      rw [hspec]
      have : (e (e.symm.toMonoidHom w) : S) = w := by simp
      rw [this]
      calc (π d) * (w : S) * (π d)⁻¹ = (w : S) * π d * (π d)⁻¹ := by rw [hwc]
        _ = w := by group
    · intro c hc
      have hcc : (e c : S) * π d = π d * (e c : S) := by
        have h1 := hspec d c
        rw [hc] at h1
        calc (e c : S) * π d = π d * (e c : S) * (π d)⁻¹ * π d := by rw [← h1]
          _ = π d * (e c : S) := by group
      have hn : e c ∈ Subgroup.normalizer (pCoreOf 2 (cA (π d)) : Set ↥Alt7) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (cA (π d)) (mem_cA.2 hcc)
      refine Subgroup.mem_normalizer_iff.2 fun k => ?_
      have h2 := Subgroup.mem_normalizer_iff.1 hn (e k)
      have hmem : ∀ z : K, z ∈ (pCoreOf 2 (cA (π d))).map e.symm.toMonoidHom ↔
          e z ∈ pCoreOf 2 (cA (π d)) := fun z => by
        rw [Subgroup.mem_map_equiv]
        simp
      rw [hmem, hmem, map_mul, map_mul, map_inv]
      exact h2
  · intro z _
    have hz : e z ∈ ⨆ σ ∈ π.range, ⨆ (_ : σ ≠ 1), pCoreOf 2 (cA σ) :=
      top_le_iSup_pCoreOf hR (Subgroup.mem_top _)
    have hle : (⨆ σ ∈ π.range, ⨆ (_ : σ ≠ 1), pCoreOf 2 (cA σ)) ≤
        ⨆ d : D, ⨆ (_ : d ≠ 1), pCoreOf 2 (cA (π d)) := by
      refine iSup₂_le fun σ hσ => iSup_le fun hσ1 => ?_
      obtain ⟨d, rfl⟩ := hσ
      have hd1 : d ≠ 1 := fun h => hσ1 (by rw [h, map_one])
      exact le_iSup_of_le d (le_iSup_of_le hd1 le_rfl)
    have hz2 := hle hz
    have hz3 : z ∈ (⨆ d : D, ⨆ (_ : d ≠ 1), pCoreOf 2 (cA (π d))).map e.symm.toMonoidHom :=
      ⟨e z, hz2, by simp⟩
    simpa only [Subgroup.map_iSup] using hz3

end S7

end CFSG.LocalAnalysis.GLTheoremB
