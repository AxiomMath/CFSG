module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerShape
public import CFSG.LieType.Chevalley.RationalToralSignDiagramDefs

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.ToralSign

section Certificate

variable {τ : Tag}

abbrev ShapeOKAt (C : RootCertificate τ) (b : Fin τ.rank → Bool) (pe : ℕ) (ch par : List ℕ)
    (h₃ : ℕ) : Prop :=
  pe < C.roots.length ∧ Even (maskPairing b (C.root pe)) ∧
  (∀ p < C.roots.length, Even (maskPairing b (C.root p)) →
    List.ofFn (C.root p) = List.ofFn (C.root pe) ∨
    List.ofFn (C.root p) = List.ofFn (-(C.root pe)) ∨
    ∃ i < ch.length, ch.getD i 0 = p) ∧
  (∀ p < C.roots.length, Even (maskPairing b (C.root p)) →
    List.ofFn (C.root p) ≠ List.ofFn (C.root pe) →
    List.ofFn (C.root p) ≠ List.ofFn (-(C.root pe)) →
    iform (C.root pe) (C.root p) = 0) ∧
  0 < ch.length ∧
  (∀ i < ch.length, ch.getD i 0 < C.roots.length ∧ Even (maskPairing b (C.root (ch.getD i 0))) ∧
    List.ofFn (C.root (ch.getD i 0)) ≠ List.ofFn (C.root pe) ∧
    List.ofFn (C.root (ch.getD i 0)) ≠ List.ofFn (-(C.root pe))) ∧
  ChainOK C ch par ∧
  (h₃ < C.roots.length ∧ Even (maskPairing b (C.root h₃)) ∧
    List.ofFn (C.root h₃) ≠ List.ofFn (C.root pe) ∧
    List.ofFn (C.root h₃) ≠ List.ofFn (-(C.root pe)) ∧
    List.ofFn (C.root h₃) ≠ List.ofFn (C.root (ch.getD 0 0)) ∧
    List.ofFn (C.root h₃) ≠ List.ofFn (-(C.root (ch.getD 0 0))))

theorem LayerShape.of_shapeOKAt {C : RootCertificate τ} (hC : C.check = true)
    {b : Fin τ.rank → Bool} {pe : ℕ} {ch par : List ℕ} {h₃ : ℕ}
    (h : ShapeOKAt C b pe ch par h₃) :
    LayerShape (maskChar b) (C.root pe) (C.root (ch.getD 0 0)) (C.root h₃) := by
  obtain ⟨hpe, he, hcover, hiso, h0, hchain, hch, h3⟩ := h
  have hmem : ∀ p < C.roots.length, Even (maskPairing b (C.root p)) →
      C.root p ∈ kernelRoots (maskChar b) := fun p hp hev =>
    mem_kernelRoots_maskChar.2 ⟨(RootCertificate.isRoot_iff hC).2 ⟨p, hp, rfl⟩, hev⟩
  have hker : ∀ i < ch.length, C.root (ch.getD i 0) ∈ kernelRoots (maskChar b) := fun i hi =>
    hmem _ (hchain i hi).1 (hchain i hi).2.1
  have hne : ∀ {u v : Fin τ.rank → ℤ}, List.ofFn u ≠ List.ofFn v → u ≠ v := fun h e =>
    h (by rw [e])
  have hmemE : C.root pe ∈ kernelRoots (maskChar b) := hmem pe hpe he
  have hrootcases : ∀ γ ∈ kernelRoots (maskChar b), γ = C.root pe ∨ γ = -(C.root pe) ∨
      ∃ i < ch.length, C.root (ch.getD i 0) = γ := by
    intro γ hγ
    obtain ⟨hγr, hγev⟩ := mem_kernelRoots_maskChar.1 hγ
    obtain ⟨p, hp, rfl⟩ := (RootCertificate.isRoot_iff hC).1 hγr
    rcases hcover p hp hγev with h1 | h1 | ⟨i, hi, hip⟩
    · exact Or.inl (List.ofFn_injective h1)
    · exact Or.inr (Or.inl (List.ofFn_injective h1))
    · exact Or.inr (Or.inr ⟨i, hi, by rw [hip]⟩)
  refine ⟨hmemE, ?_, hker 0 h0, ?_, ?_, ?_, hmem _ h3.1 h3.2.1, ?_, ?_, ?_, ?_⟩
  · intro δ hδ hδe hδe'
    obtain ⟨hδr, hδev⟩ := mem_kernelRoots_maskChar.1 hδ
    obtain ⟨p, hp, rfl⟩ := (RootCertificate.isRoot_iff hC).1 hδr
    exact hiso p hp hδev (fun h => hδe (List.ofFn_injective h))
      (fun h => hδe' (List.ofFn_injective h))
  · exact hne (hchain 0 h0).2.2.1
  · exact hne (hchain 0 h0).2.2.2
  · intro γ hγ hγe hγe'
    rcases hrootcases γ hγ with h1 | h1 | ⟨i, hi, rfl⟩
    · exact absurd h1 hγe
    · exact absurd h1 hγe'
    · exact hch.class_eq hker h0 i hi
  · exact hne h3.2.2.1
  · exact hne h3.2.2.2.1
  · exact hne h3.2.2.2.2.1
  · exact hne h3.2.2.2.2.2

end Certificate

section Instance

@[expose] def e6Theta : Fin TwistTag.E6.tag.rank → ℤ := (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)

theorem e6Certificate_root_theta : e6Certificate.root 70 = e6Theta :=
  List.ofFn_injective (by decide : List.ofFn (e6Certificate.root 70) = List.ofFn e6Theta)

theorem isRoot_e6Theta : IsRoot .E6 e6Theta :=
  (RootCertificate.isRoot_iff e6Certificate_check).2 ⟨70, by decide, e6Certificate_root_theta⟩

theorem shapeOKAt_E6_mask2 :
    ShapeOKAt e6Certificate (natBits (τ := .E6) 2) 70
      [3, 2, 4, 7, 10, 11, 12, 13, 14, 15, 17, 18, 22, 24, 25, 26, 27, 36, 0, 6, 23, 34, 35, 45,
        5, 16, 29, 38, 40, 47]
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]
      2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem layerShape_E6_mask2 :
    LayerShape (signMaskChar .E6 2) e6Theta (Pi.single ⟨3, by decide⟩ 1)
      (Pi.single ⟨2, by decide⟩ 1) := by
  have h := LayerShape.of_shapeOKAt e6Certificate_check shapeOKAt_E6_mask2
  have e1 : e6Certificate.root 70 = e6Theta := e6Certificate_root_theta
  have e2 : e6Certificate.root 3 = (Pi.single ⟨3, by decide⟩ 1 : Fin Tag.E6.rank → ℤ) := by
    decide
  have e3 : e6Certificate.root 2 = (Pi.single ⟨2, by decide⟩ 1 : Fin Tag.E6.rank → ℤ) := by
    decide
  change LayerShape (maskChar (natBits 2)) (e6Certificate.root 70) (e6Certificate.root 3)
    (e6Certificate.root 2) at h
  rw [e1, e2, e3] at h
  exact h

end Instance

end CFSG.ClassicalInvolution.RouteD.Exotic
