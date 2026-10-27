module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso

public section

namespace CFSG.HardMathSupport.U4FF

namespace ClassFinal

open CFSG.QuasithinUnique.Setup.X7 (matRep MatIso matIso_of_reindex)

section Conj

variable {G : Type} [Group G] {E : Type} [Field E] {κ : Type} [Fintype κ] [DecidableEq κ] {m : ℕ}

theorem exists_conj_of_single (R₁ : G →* Matrix κ κ E) (R₂ : G →* Matrix (Fin m) (Fin m) E)
    (A : G → Matrix (Fin m) (Fin m) E) (Φ : (matRep R₁).Equiv (matRep R₂)) (e : κ ≃ Fin m)
    (P' : GL (Fin m) E)
    (hP' : ∀ g, (P' : Matrix (Fin m) (Fin m) E) * Matrix.reindex e e (R₁ g) =
      A g * (P' : Matrix (Fin m) (Fin m) E)) :
    ∃ P : GL (Fin m) E, ∀ g, (P : Matrix (Fin m) (Fin m) E) * R₂ g =
      A g * (P : Matrix (Fin m) (Fin m) E) := by
  classical
  obtain ⟨P₁, Q₁, h₁⟩ := MatIso.exists_of_equiv Φ
  let φ := Matrix.reindexAlgEquiv E E e
  let R₁' : G →* Matrix (Fin m) (Fin m) E :=
    { toFun := fun g => φ (R₁ g)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun g h => by rw [map_mul, map_mul] }
  have hperm : MatIso R₁ R₁' (CFSG.QuasithinUnique.Setup.X7.permMat E e)
      (CFSG.QuasithinUnique.Setup.X7.permMat E e.symm) :=
    matIso_of_reindex e (fun g x' x => by
      simp [R₁', φ, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply])
  have t1 := h₁.symm.trans hperm
  have hPinv : (P' : Matrix (Fin m) (Fin m) E) * ((P'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)
      = 1 := Units.mul_inv P'
  have hPinv' : ((P'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) * (P' : Matrix (Fin m) (Fin m) E)
      = 1 := Units.inv_mul P'
  refine ⟨⟨(P' : Matrix (Fin m) (Fin m) E) * (CFSG.QuasithinUnique.Setup.X7.permMat E e * Q₁),
    (P₁ * CFSG.QuasithinUnique.Setup.X7.permMat E e.symm) *
      ((P'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E), ?_, ?_⟩, fun g => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFSG.QuasithinUnique.Setup.X7.permMat E e * Q₁),
      t1.mul_inv, Matrix.one_mul, hPinv]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((P'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E),
      hPinv', Matrix.one_mul, t1.inv_mul]
  · show (P' : Matrix (Fin m) (Fin m) E) * (CFSG.QuasithinUnique.Setup.X7.permMat E e * Q₁) * R₂ g =
      A g * ((P' : Matrix (Fin m) (Fin m) E) * (CFSG.QuasithinUnique.Setup.X7.permMat E e * Q₁))
    have h2 := t1.comm g
    have h3 : (P' : Matrix (Fin m) (Fin m) E) * R₁' g = A g * (P' : Matrix (Fin m) (Fin m) E) :=
      hP' g
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h3, Matrix.mul_assoc]

end Conj

theorem exists_ringHom_of_dvd {F D : Type} [Field F] [Field D] [Finite F] [Finite D] [CharP F 2]
    [CharP D 2] {f d : ℕ} (hF : Nat.card F = 2 ^ f) (hD : Nat.card D = 2 ^ d) (hfd : f ∣ d) :
    Nonempty (F →+* D) := by
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let _ : Algebra (ZMod 2) D := ZMod.algebra D 2
  have : Fintype F := Fintype.ofFinite F
  have : Fintype D := Fintype.ofFinite D
  have hfF : Module.finrank (ZMod 2) F = f := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [ZMod.card, Fintype.card_eq_nat_card, hF] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hfD : Module.finrank (ZMod 2) D = d := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [ZMod.card, Fintype.card_eq_nat_card, hD] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  obtain ⟨ι⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := F) (L := D)
    (by rw [hfF, hfD]; exact hfd)
  exact ⟨ι.toRingHom⟩

end ClassFinal

end CFSG.HardMathSupport.U4FF
