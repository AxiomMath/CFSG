module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Chevalley.SignCharacterMasks

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

section Mask

@[expose] def zMask (τ : Tag) (k : Fin τ.rank) : Fin τ.rank → Bool :=
  fun j => decide (¬ Even (τ.cartan k j))

@[expose] noncomputable def zChar (τ : Tag) (k : Fin τ.rank) :
    Multiplicative (Fin τ.rank → ℤ) →* ℤˣ :=
  maskChar (zMask τ k)

end Mask

section Shape

variable {τ : Tag}

structure LayerShape (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (e δ₂ δ₃ : Fin τ.rank → ℤ) :
    Prop where
  mem_e : e ∈ kernelRoots χ
  iso : ∀ δ ∈ kernelRoots χ, δ ≠ e → δ ≠ -e → iform e δ = 0
  mem₂ : δ₂ ∈ kernelRoots χ
  ne₂ : δ₂ ≠ e
  ne₂' : δ₂ ≠ -e
  conn : ∀ (γ : Fin τ.rank → ℤ) (h : γ ∈ kernelRoots χ), γ ≠ e → γ ≠ -e →
    (Quotient.mk (kernelRootSetoid χ) ⟨γ, h⟩ : KernelComponent χ) =
      Quotient.mk (kernelRootSetoid χ) ⟨δ₂, mem₂⟩
  mem₃ : δ₃ ∈ kernelRoots χ
  ne₃ : δ₃ ≠ e
  ne₃' : δ₃ ≠ -e
  ne₃₂ : δ₃ ≠ δ₂
  ne₃₂' : δ₃ ≠ -δ₂

end Shape

section Classes

variable {τ : Tag} {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} {e δ₂ δ₃ : Fin τ.rank → ℤ}

theorem LayerShape.mk_e_ne (hS : LayerShape χ e δ₂ δ₃) :
    (Quotient.mk (kernelRootSetoid χ) ⟨e, hS.mem_e⟩ : KernelComponent χ) ≠
      Quotient.mk (kernelRootSetoid χ) ⟨δ₂, hS.mem₂⟩ := by
  intro h
  have hQ : ∀ x y : kernelRoots χ, Relation.EqvGen (fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y →
      (((x : Fin τ.rank → ℤ) = e ∨ (x : Fin τ.rank → ℤ) = -e) ↔
        ((y : Fin τ.rank → ℤ) = e ∨ (y : Fin τ.rank → ℤ) = -e)) := by
    intro x y hxy
    induction hxy with
    | rel x y hrel =>
      rw [dotProduct_mulVec_eq_iform] at hrel
      constructor
      · rintro (h1 | h1)
        · by_contra hy
          push Not at hy
          exact hrel (by rw [h1]; exact hS.iso y y.2 hy.1 hy.2)
        · by_contra hy
          push Not at hy
          have := hS.iso y y.2 hy.1 hy.2
          exact hrel (by
            rw [h1, ← neg_one_smul ℤ e, iform_smul_left, this, mul_zero])
      · rintro (h1 | h1)
        · by_contra hx
          push Not at hx
          have := hS.iso x x.2 hx.1 hx.2
          exact hrel (by rw [h1, iform_comm]; exact this)
        · by_contra hx
          push Not at hx
          have := hS.iso x x.2 hx.1 hx.2
          exact hrel (by
            rw [h1, iform_comm, ← neg_one_smul ℤ e, iform_smul_left, this, mul_zero])
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  have := hQ _ _ (Quotient.exact h)
  have h2 : ((⟨e, hS.mem_e⟩ : kernelRoots χ) : Fin τ.rank → ℤ) = e ∨
      ((⟨e, hS.mem_e⟩ : kernelRoots χ) : Fin τ.rank → ℤ) = -e := Or.inl rfl
  rcases this.mp h2 with h3 | h3
  · exact hS.ne₂ h3
  · exact hS.ne₂' h3

theorem LayerShape.mk_eq_e_iff (hS : LayerShape χ e δ₂ δ₃) (γ : Fin τ.rank → ℤ)
    (h : γ ∈ kernelRoots χ) :
    (Quotient.mk (kernelRootSetoid χ) ⟨γ, h⟩ : KernelComponent χ) =
      Quotient.mk (kernelRootSetoid χ) ⟨e, hS.mem_e⟩ ↔ γ = e ∨ γ = -e := by
  constructor
  · intro h1
    by_contra hγ
    push Not at hγ
    exact hS.mk_e_ne (h1.symm.trans (hS.conn γ h hγ.1 hγ.2))
  · rintro (rfl | rfl)
    · rfl
    · refine mk_eq_of_iform_ne_zero (α := ⟨-e, h⟩) (β := ⟨e, hS.mem_e⟩) ?_
      change iform (-e) e ≠ 0
      rw [← neg_one_smul ℤ e, iform_smul_left]
      have := iform_self_pos hS.mem_e.1.ne_zero
      omega

theorem LayerShape.exists_eq (hS : LayerShape χ e δ₂ δ₃) (i : KernelComponent χ) :
    i = Quotient.mk (kernelRootSetoid χ) ⟨e, hS.mem_e⟩ ∨
      i = Quotient.mk (kernelRootSetoid χ) ⟨δ₂, hS.mem₂⟩ := by
  induction i using Quotient.inductionOn with
  | h a =>
    obtain ⟨γ, hγ⟩ := a
    by_cases h1 : γ = e ∨ γ = -e
    · exact Or.inl ((hS.mk_eq_e_iff γ hγ).2 h1)
    · push Not at h1
      exact Or.inr (hS.conn γ hγ h1.1 h1.2)

end Classes

section Certificate

variable {τ : Tag}

abbrev ChainOK (C : RootCertificate τ) (ch par : List ℕ) : Prop :=
  ∀ i < ch.length, 0 < i → par.getD i 0 < i ∧
    iform (C.root (ch.getD i 0)) (C.root (ch.getD (par.getD i 0) 0)) ≠ 0

theorem ChainOK.class_eq {C : RootCertificate τ} {ch par : List ℕ} (hch : ChainOK C ch par)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    (hker : ∀ i < ch.length, C.root (ch.getD i 0) ∈ kernelRoots χ) (h0 : 0 < ch.length) :
    ∀ (i : ℕ) (hi : i < ch.length),
      (Quotient.mk (kernelRootSetoid χ) ⟨C.root (ch.getD i 0), hker i hi⟩ : KernelComponent χ) =
        Quotient.mk (kernelRootSetoid χ) ⟨C.root (ch.getD 0 0), hker 0 h0⟩ := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rfl
    · obtain ⟨hlt, hform⟩ := hch i hi hpos
      have hpar : par.getD i 0 < ch.length := hlt.trans hi
      have h1 := ih _ hlt hpar
      have h2 : (Quotient.mk (kernelRootSetoid χ) ⟨C.root (ch.getD i 0), hker i hi⟩ :
          KernelComponent χ) =
          Quotient.mk (kernelRootSetoid χ) ⟨C.root (ch.getD (par.getD i 0) 0), hker _ hpar⟩ :=
        mk_eq_of_iform_ne_zero (α := ⟨_, hker i hi⟩) (β := ⟨_, hker _ hpar⟩) hform
      exact h2.trans h1

abbrev ShapeOK (C : RootCertificate τ) (b : Fin τ.rank → Bool) (k : Fin τ.rank) (ch par : List ℕ)
    (h₃ : ℕ) : Prop :=
  Even (maskPairing b (Pi.single k 1 : Fin τ.rank → ℤ)) ∧
  (∀ p < C.roots.length, Even (maskPairing b (C.root p)) →
    List.ofFn (C.root p) = List.ofFn (Pi.single k 1 : Fin τ.rank → ℤ) ∨
    List.ofFn (C.root p) = List.ofFn (-(Pi.single k 1) : Fin τ.rank → ℤ) ∨
    ∃ i < ch.length, ch.getD i 0 = p) ∧
  (∀ p < C.roots.length, Even (maskPairing b (C.root p)) →
    List.ofFn (C.root p) ≠ List.ofFn (Pi.single k 1 : Fin τ.rank → ℤ) →
    List.ofFn (C.root p) ≠ List.ofFn (-(Pi.single k 1) : Fin τ.rank → ℤ) →
    iform (Pi.single k 1 : Fin τ.rank → ℤ) (C.root p) = 0) ∧
  0 < ch.length ∧
  (∀ i < ch.length, ch.getD i 0 < C.roots.length ∧ Even (maskPairing b (C.root (ch.getD i 0))) ∧
    List.ofFn (C.root (ch.getD i 0)) ≠ List.ofFn (Pi.single k 1 : Fin τ.rank → ℤ) ∧
    List.ofFn (C.root (ch.getD i 0)) ≠ List.ofFn (-(Pi.single k 1) : Fin τ.rank → ℤ)) ∧
  ChainOK C ch par ∧
  (h₃ < C.roots.length ∧ Even (maskPairing b (C.root h₃)) ∧
    List.ofFn (C.root h₃) ≠ List.ofFn (Pi.single k 1 : Fin τ.rank → ℤ) ∧
    List.ofFn (C.root h₃) ≠ List.ofFn (-(Pi.single k 1) : Fin τ.rank → ℤ) ∧
    List.ofFn (C.root h₃) ≠ List.ofFn (C.root (ch.getD 0 0)) ∧
    List.ofFn (C.root h₃) ≠ List.ofFn (-(C.root (ch.getD 0 0))))

theorem LayerShape.of_shapeOK {C : RootCertificate τ} (hC : C.check = true)
    {b : Fin τ.rank → Bool} {k : Fin τ.rank} {ch par : List ℕ} {h₃ : ℕ}
    (h : ShapeOK C b k ch par h₃) :
    LayerShape (maskChar b) (Pi.single k 1) (C.root (ch.getD 0 0)) (C.root h₃) := by
  obtain ⟨he, hcover, hiso, h0, hchain, hch, h3⟩ := h
  have hmem : ∀ p < C.roots.length, Even (maskPairing b (C.root p)) →
      C.root p ∈ kernelRoots (maskChar b) := fun p hp hev =>
    mem_kernelRoots_maskChar.2 ⟨(RootCertificate.isRoot_iff hC).2 ⟨p, hp, rfl⟩, hev⟩
  have hker : ∀ i < ch.length, C.root (ch.getD i 0) ∈ kernelRoots (maskChar b) := fun i hi =>
    hmem _ (hchain i hi).1 (hchain i hi).2.1
  have hne : ∀ {u v : Fin τ.rank → ℤ}, List.ofFn u ≠ List.ofFn v → u ≠ v := fun h e =>
    h (by rw [e])
  have hmemE : (Pi.single k 1 : Fin τ.rank → ℤ) ∈ kernelRoots (maskChar b) :=
    mem_kernelRoots_maskChar.2 ⟨IsRoot.basis k, he⟩
  have hrootcases : ∀ γ ∈ kernelRoots (maskChar b), γ = Pi.single k 1 ∨ γ = -(Pi.single k 1) ∨
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

section Instances

theorem shapeOK_F4 :
    ShapeOK f4Certificate (zMask .F4 ⟨0, by decide⟩) ⟨0, by decide⟩
    [21, 3, 10, 11, 19, 28, 36, 40, 41, 45, 2, 9, 30, 34, 44, 47, 35, 38]
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
    3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem shapeOK_E6 :
    ShapeOK e6Certificate (zMask .E6 ⟨0, by decide⟩) ⟨0, by decide⟩
    [1, 3, 8, 9, 12, 13, 19, 21, 24, 25, 31, 33, 36, 42, 68, 69, 70, 71, 4, 14, 15, 26,
       66, 67, 5, 16, 61, 64, 55, 59]
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 5, 5, 5, 5,
       9, 9]
    3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem shapeOK_E7 :
    ShapeOK e7Certificate (zMask .E7 ⟨0, by decide⟩) ⟨0, by decide⟩
    [1, 3, 9, 10, 13, 14, 22, 24, 27, 28, 36, 38, 41, 42, 49, 52, 55, 63, 97, 101, 104,
       105, 107, 108, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 4, 15, 16, 29,
       30, 43, 89, 94, 98, 102, 106, 109, 120, 121, 5, 17, 18, 31, 80, 86, 90, 95, 6, 19,
       70, 77]
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5, 5, 5, 5, 5,
       5, 9, 9, 9, 9]
    3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem shapeOK_E8 :
    ShapeOK e8Certificate (zMask .E8 ⟨0, by decide⟩) ⟨0, by decide⟩
    [1, 3, 10, 11, 14, 15, 25, 27, 30, 31, 41, 43, 46, 47, 56, 59, 62, 63, 72, 75, 78,
       88, 122, 130, 135, 136, 142, 143, 147, 148, 149, 153, 154, 155, 158, 159, 160,
       161, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 177, 178, 179,
       181, 182, 183, 186, 187, 190, 191, 195, 199, 225, 227, 228, 229, 4, 16, 17, 32,
       33, 48, 49, 64, 110, 118, 123, 131, 137, 138, 144, 145, 150, 156, 162, 167, 176,
       180, 185, 189, 194, 198, 202, 205, 230, 231, 5, 18, 19, 34, 35, 50, 97, 106, 111,
       119, 124, 132, 208, 211, 232, 233, 6, 20, 21, 36, 82, 93, 234, 235, 7, 22, 236,
       237, 238, 239]
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
       1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
       5, 5, 5, 9, 9, 9, 9, 9, 9, 9, 9, 13, 13, 13, 13, 17, 17]
    3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem layerShape_F4 :
    ∃ δ₂ δ₃ : Fin Tag.F4.rank → ℤ,
      LayerShape (zChar .F4 ⟨0, by decide⟩) (Pi.single ⟨0, by decide⟩ 1) δ₂ δ₃ ∧
        iform δ₂ δ₂ = 4 :=
  ⟨_, _, LayerShape.of_shapeOK f4Certificate_check shapeOK_F4, by decide +kernel⟩

theorem layerShape_E6 :
    ∃ δ₂ δ₃ : Fin Tag.E6.rank → ℤ,
      LayerShape (zChar .E6 ⟨0, by decide⟩) (Pi.single ⟨0, by decide⟩ 1) δ₂ δ₃ :=
  ⟨_, _, LayerShape.of_shapeOK e6Certificate_check shapeOK_E6⟩

theorem layerShape_E7 :
    ∃ δ₂ δ₃ : Fin Tag.E7.rank → ℤ,
      LayerShape (zChar .E7 ⟨0, by decide⟩) (Pi.single ⟨0, by decide⟩ 1) δ₂ δ₃ :=
  ⟨_, _, LayerShape.of_shapeOK e7Certificate_check shapeOK_E7⟩

theorem layerShape_E8 :
    ∃ δ₂ δ₃ : Fin Tag.E8.rank → ℤ,
      LayerShape (zChar .E8 ⟨0, by decide⟩) (Pi.single ⟨0, by decide⟩ 1) δ₂ δ₃ :=
  ⟨_, _, LayerShape.of_shapeOK e8Certificate_check shapeOK_E8⟩

end Instances

end CFSG.ClassicalInvolution.RouteD.Exotic
