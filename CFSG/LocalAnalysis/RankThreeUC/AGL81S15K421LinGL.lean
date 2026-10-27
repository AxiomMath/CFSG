module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinDef

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421MonoProof

open K421MonoProof

@[expose] def Mono81.map {G G' : Type} [Group G] [Group G'] (D : Mono81 G) (φ : G →* G')
    (hφ : Function.Injective φ) : Mono81 G' where
  a := φ.comp D.a
  s := φ D.s
  a_inj := hφ.comp D.a_inj
  s_pow := by rw [← map_pow, D.s_pow, map_one]
  s_conj := fun x => by
    have h := D.s_conj x
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, h]
  s_ne_a := fun x => ⟨fun h => (D.s_ne_a x).1 (hφ h), fun h =>
    (D.s_ne_a x).2 (hφ (by rw [map_pow]; exact h))⟩
  f := φ D.f
  f_s := by
    obtain ⟨x, hx⟩ := D.f_s
    refine ⟨x, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, hx]
  f_diag := fun c => by
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, D.f_diag c]

theorem Mono81.map_av {G G' : Type} [Group G] [Group G'] (D : Mono81 G) (φ : G →* G')
    (hφ : Function.Injective φ) (x : V3) : (D.map φ hφ).av x = φ (D.av x) := rfl

end K421MonoProof

namespace K421LinProof

open K421MonoProof K421OrbProof Matrix

theorem V3_add_neg (x : V3) : x + -x = 0 := by
  funext b
  have h : ∀ z : ZMod 3, z + -z = 0 := by decide
  exact h (x b)

theorem V3_neg_add (x : V3) : -x + x = 0 := by
  funext b
  have h : ∀ z : ZMod 3, -z + z = 0 := by decide
  exact h (x b)

@[expose] def aGL (x : V3) : GL Idx F2 :=
  ⟨aMat x, aMat (-x), by rw [← aMat_add, V3_add_neg, aMat_zero],
    by rw [← aMat_add, V3_neg_add, aMat_zero]⟩

@[expose] def aHom : Multiplicative V3 →* GL Idx F2 where
  toFun x := aGL (Multiplicative.toAdd x)
  map_one' := Units.ext aMat_zero
  map_mul' _ _ := Units.ext (aMat_add _ _)

@[expose] def sGL : GL Idx F2 := ⟨sMat, sMat * sMat, sMat_cube, sMat_cube'⟩

@[expose] def fGL : GL Idx F2 := ⟨fMat, fInv, fMat_mul_fInv, fInv_mul_fMat⟩

@[expose] def nGL (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : GL Idx F2 :=
  ⟨pMat π * jMat ε, jMat ε * pMat π.symm, nMat_mul_inv π ε, nMat_inv_mul π ε⟩

@[expose] def mono0 : Mono81 (GL Idx F2) where
  a := aHom
  s := sGL
  a_inj := fun x y h => by
    have h1 : aMat (Multiplicative.toAdd x) = aMat (Multiplicative.toAdd y) := congrArg Units.val h
    exact Multiplicative.toAdd.injective (aMat_inj _ _ h1)
  s_pow := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    show sMat ^ 3 = 1
    rw [pow_succ, pow_two]
    exact sMat_cube')
  s_conj := fun x => by
    rw [mul_inv_eq_iff_eq_mul]
    exact Units.ext (sMat_aMat x)
  s_ne_a := fun x => ⟨fun h => sMat_ne_aMat x (congrArg Units.val h), fun h =>
    sMat_sq_ne_aMat x (by
      have h1 := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, pow_two] at h1
      exact h1)⟩
  f := fGL
  f_s := ⟨![0, 2, 1], Units.ext fInv_sMat_fMat⟩
  f_diag := fun c => Units.ext (fInv_aMat_fMat c)

section Embedding

variable (ι₀ : Type) [Fintype ι₀] [DecidableEq ι₀]

@[expose] def blockHom : Matrix Idx Idx F2 →* Matrix (ι₀ ⊕ Idx) (ι₀ ⊕ Idx) F2 where
  toFun M := Matrix.fromBlocks 1 0 0 M
  map_one' := Matrix.fromBlocks_one
  map_mul' M N := by
    rw [Matrix.fromBlocks_multiply]
    simp

theorem blockHom_injective : Function.Injective (blockHom ι₀) := by
  intro M N h
  have := congrArg Matrix.toBlocks₂₂ h
  simpa [blockHom] using this

@[expose] def embGL : GL Idx F2 →* GL (ι₀ ⊕ Idx) F2 := Units.map (blockHom ι₀)

theorem embGL_injective : Function.Injective (embGL ι₀) :=
  Units.map_injective (blockHom_injective ι₀)

@[expose] def monoE : Mono81 (GL (ι₀ ⊕ Idx) F2) := mono0.map (embGL ι₀) (embGL_injective ι₀)

end Embedding

@[expose] def SignedPerms {G : Type} [Group G] (D : Mono81 G) : Prop :=
  ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool), ∃ n : G, ∀ x : V3,
    n * D.av x * n⁻¹ = D.av (act π ε x)

theorem signedPerms_mono0 : SignedPerms mono0 := fun π ε => ⟨nGL π ε, fun x => by
  rw [mul_inv_eq_iff_eq_mul]
  exact Units.ext (nMat_aMat π ε x)⟩

theorem SignedPerms.map {G G' : Type} [Group G] [Group G'] {D : Mono81 G} (h : SignedPerms D)
    (φ : G →* G') (hφ : Function.Injective φ) : SignedPerms (D.map φ hφ) := fun π ε => by
  obtain ⟨n, hn⟩ := h π ε
  refine ⟨φ n, fun x => ?_⟩
  show φ n * φ (D.av x) * (φ n)⁻¹ = φ (D.av (act π ε x))
  rw [← map_inv, ← map_mul, ← map_mul, hn x]

theorem signedPerms_monoE (ι₀ : Type) [Fintype ι₀] [DecidableEq ι₀] : SignedPerms (monoE ι₀) :=
  signedPerms_mono0.map _ _

end K421LinProof

end CFSG.LocalAnalysis.RankThreeUC.S15
