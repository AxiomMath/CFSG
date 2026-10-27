module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDKap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDOmDef

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

variable {G : Type} [Group G] {V : Subgroup G}

private theorem s8d_sl_map_symm_map (A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
    Matrix.SpecialLinearGroup.map (sec12GF4Equiv.symm : Sec12F4 →+* GaloisField 2 2)
      (Matrix.SpecialLinearGroup.map (sec12GF4Equiv : GaloisField 2 2 →+* Sec12F4) A) = A := by
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

private theorem s8d_sl_map_map_symm (A : Sec12SL) :
    Matrix.SpecialLinearGroup.map (sec12GF4Equiv : GaloisField 2 2 →+* Sec12F4)
      (Matrix.SpecialLinearGroup.map (sec12GF4Equiv.symm : Sec12F4 →+* GaloisField 2 2) A) =
        A := by
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem s8d_natOmega4_of_model {Y : Subgroup (MulAut ↥V)} (e : ↥V ≃* Multiplicative Sec12M)
    (φ : Sec12SL × Sec12SL →* MulAut ↥V) (hinj : Function.Injective φ) (hrange : φ.range = Y)
    (hact : ∀ (A B : Sec12SL) (v : ↥V), Multiplicative.toAdd (e (φ (A, B) v)) =
      (A : Sec12M) * Multiplicative.toAdd (e v) * (B : Sec12M)ᵀ) :
    IsNatOmega4Plus V Y := by
  let f : GaloisField 2 2 ≃+* Sec12F4 := sec12GF4Equiv
  let g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) →* Sec12SL :=
    Matrix.SpecialLinearGroup.map (f : GaloisField 2 2 →+* Sec12F4)
  let g' : Sec12SL →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    Matrix.SpecialLinearGroup.map (f.symm : Sec12F4 →+* GaloisField 2 2)
  have hgc : ∀ A, (g A : Sec12M) = (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).map f :=
    fun A => rfl
  have hg'g : ∀ A, g' (g A) = A := s8d_sl_map_symm_map
  have hgg' : ∀ A, g (g' A) = A := s8d_sl_map_map_symm
  have hginj : Function.Injective g := fun A A' h => by rw [← hg'g A, ← hg'g A', h]
  refine ⟨e.trans (AddEquiv.toMultiplicative f.symm.mapMatrix.toAddEquiv),
    φ.comp (g.prodMap g), ?_, ?_, ?_⟩
  · intro p p' hpp'
    have h1 := hinj hpp'
    exact Prod.ext (hginj (Prod.ext_iff.mp h1).1) (hginj (Prod.ext_iff.mp h1).2)
  · rw [← hrange]
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact ⟨g.prodMap g p, rfl⟩
    · rintro _ ⟨p, rfl⟩
      refine ⟨(g' p.1, g' p.2), ?_⟩
      show φ (g (g' p.1), g (g' p.2)) = φ p
      rw [hgg', hgg']
  · intro A B v
    have h1 := hact (g A) (g B) v
    have h2 : Multiplicative.toAdd
        ((e.trans (AddEquiv.toMultiplicative f.symm.mapMatrix.toAddEquiv))
          ((φ.comp (g.prodMap g)) (A, B) v)) =
          f.symm.mapMatrix (Multiplicative.toAdd (e (φ (g A, g B) v))) := rfl
    have h3 : Multiplicative.toAdd
        ((e.trans (AddEquiv.toMultiplicative f.symm.mapMatrix.toAddEquiv)) v) =
          f.symm.mapMatrix (Multiplicative.toAdd (e v)) := rfl
    have hA : f.symm.mapMatrix (g A : Sec12M) = (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) := by
      rw [hgc]
      ext i j
      simp [RingEquiv.mapMatrix_apply]
    have hBt : f.symm.mapMatrix ((g B : Sec12M)ᵀ) =
        (B : Matrix (Fin 2) (Fin 2) (GaloisField 2 2))ᵀ := by
      rw [hgc]
      ext i j
      simp [RingEquiv.mapMatrix_apply]
    rw [h2, h3, h1, map_mul, map_mul, hA, hBt]

theorem s8d_concl_Om (K : AddCoord V) {Z : Subgroup (MulAut ↥V)}
    (ψ : Sec12SL × Sec12SL ≃* ↥Z) (hψ : ∀ (A B : Sec12SL) (p : EvW × EvW),
      s8dPom (s8dAp (K.s8dKap (ψ (A, B))) p) = (A : Sec12M) * s8dPom p * (B : Sec12M)ᵀ) :
    IsNatOmega4Plus V Z := by
  refine s8d_natOmega4_of_model (K.s8dPsiM.symm.trans (AddEquiv.toMultiplicative s8dPom))
    (Z.subtype.comp ψ.toMonoidHom) (Subtype.val_injective.comp ψ.injective) ?_ ?_
  · ext c
    constructor
    · rintro ⟨p, rfl⟩
      exact (ψ p).2
    · intro hc
      refine ⟨ψ.symm ⟨c, hc⟩, ?_⟩
      show ((ψ (ψ.symm ⟨c, hc⟩) : ↥Z) : MulAut ↥V) = c
      rw [MulEquiv.apply_symm_apply]
  · intro A B v
    obtain ⟨p, rfl⟩ := K.Ψ.surjective v
    have hv : ∀ q : EvW × EvW, Multiplicative.toAdd
        ((K.s8dPsiM.symm.trans (AddEquiv.toMultiplicative s8dPom)) (K.Ψ q)) = s8dPom q := by
      intro q
      show s8dPom (K.Ψ.symm (K.Ψ q)) = s8dPom q
      rw [K.Ψ.symm_apply_apply]
    have hc : ((Z.subtype.comp ψ.toMonoidHom) (A, B)) (K.Ψ p) =
        K.Ψ (s8dAp (K.s8dKap (ψ (A, B))) p) := (K.s8dKap_spec _ p).symm
    rw [hc, hv, hv, hψ]

end CFSG.OddStandard.SmallF3.Omega
