module

public import CFSG.ClassicalGroups.Symplectic.PointRadicalNormal
public import CFSG.ClassicalGroups.Alternating.PointRadicalStabilizer

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.PCoreSection
open Matrix

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem le_LspGL_and_transvections_or_eq (hK : 2 < Nat.card K) {u : Fin m ⊕ Fin m → K}
    (hu : u ≠ 0) (S : Subgroup (GL (Fin m ⊕ Fin m) K)) (hS : S ≤ StatedSp m K)
    (hfix : ∀ s ∈ S, (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u)
    (h2 : IsPGroup 2 S)
    (hSn : ∀ g ∈ StatedSp m K,
      (∃ c : K, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    S ≤ LspGL m K u ∧
      ((∀ s ∈ S, ∃ c : K, ∀ x : Fin m ⊕ Fin m → K,
        (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = x + (c * spForm m K x u) • u) ∨
        S = LspGL m K u) := by
  classical
  let e : StatedSp m K ≃* Gsp (spForm m K) := spEquiv
  let S' : Subgroup (Gsp (spForm m K)) := (S.comap (StatedSp m K).subtype).map e.toMonoidHom
  have hS'mem : ∀ g : Gsp (spForm m K), g ∈ S' ↔ (e.symm g : GL (Fin m ⊕ Fin m) K) ∈ S := by
    intro g
    constructor
    · rintro ⟨s, hs, rfl⟩
      show ((e.symm (e s) : StatedSp m K) : GL (Fin m ⊕ Fin m) K) ∈ S
      rw [MulEquiv.symm_apply_apply]
      exact hs
    · intro h
      exact ⟨e.symm g, h, by simp⟩
  have happ : ∀ (g : Gsp (spForm m K)) (v : Fin m ⊕ Fin m → K), g.app v =
      ((e.symm g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v := by
    intro g v
    have := spEquiv_app (e.symm g) v
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hS'fix : S' ≤ pointStabilizer (spForm m K) u := by
    intro g hg
    refine ⟨1, ?_⟩
    rw [happ, hfix _ ((hS'mem g).mp hg), one_smul]
  have hS'n : ∀ g ∈ pointStabilizer (spForm m K) u, ∀ s ∈ S', g * s * g⁻¹ ∈ S' := by
    intro g ⟨c, hc⟩ s hs
    rw [hS'mem] at hs ⊢
    have hgS := (e.symm g).2
    have h1 := hSn (e.symm g : GL (Fin m ⊕ Fin m) K) hgS ⟨c, ?_⟩ _ hs
    · simpa using h1
    · rw [← happ]; exact hc
  have hS'p : IsPGroup 2 S' := by
    intro g
    obtain ⟨s, hs, hsg⟩ := g.2
    obtain ⟨k, hk⟩ := h2 ⟨(s : GL (Fin m ⊕ Fin m) K), hs⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : ((s : GL (Fin m ⊕ Fin m) K)) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have : (g : Gsp (spForm m K)) = e s := hsg.symm
    show (g : Gsp (spForm m K)) ^ (2 ^ k) = 1
    rw [this, ← map_pow]
    have : (s : StatedSp m K) ^ (2 ^ k) = 1 := Subtype.ext hk'
    rw [this, map_one]
  have hS'L : S' ≤ Lsp (spForm m K) spForm_isAlt u := by
    rw [Lsp_eq_pCoreOf_pointStabilizer spForm_isAlt spForm_nondegenerate hu]
    exact le_pCoreOf hS'fix hS'n hS'p
  have hSL : S ≤ LspGL m K u := by
    intro s hs
    have hsSp : s ∈ StatedSp m K := hS hs
    have h1 : e ⟨s, hsSp⟩ ∈ S' := (hS'mem _).mpr (by simpa using hs)
    have h2 := (mem_LspGL_iff.mpr ⟨hsSp, hS'L h1⟩)
    simpa using h2
  refine ⟨hSL, ?_⟩
  by_cases hnT : ∃ s ∈ S, ∀ c : K, ∃ x : Fin m ⊕ Fin m → K,
      (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x ≠ x + (c * spForm m K x u) • u
  · exact Or.inr (eq_LspGL_of_normalized hK hu S hSL hSn hnT)
  · left
    push Not at hnT
    exact hnT

end CFSG.ClassicalGroups.Symplectic
