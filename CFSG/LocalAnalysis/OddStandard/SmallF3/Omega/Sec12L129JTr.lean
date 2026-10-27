module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JF4a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Matrix

variable {G : Type} [Group G]

private theorem sec12_map_surj (A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
    ∃ A' : Sec12SL, Matrix.SpecialLinearGroup.map (sec12GF4Equiv.symm : Sec12F4 →+* _) A' = A := by
  refine ⟨Matrix.SpecialLinearGroup.map (sec12GF4Equiv : GaloisField 2 2 →+* Sec12F4) A, ?_⟩
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem sec12_natOmega4_model {V : Subgroup G} {Y : Subgroup (MulAut ↥V)}
    (h : IsNatOmega4Plus V Y) :
    ∃ (e : ↥V ≃* Multiplicative Sec12M) (φ : Sec12SL × Sec12SL →* MulAut ↥V),
      Function.Injective φ ∧ φ.range = Y ∧
        ∀ (A B : Sec12SL) (v : ↥V), Multiplicative.toAdd (e (φ (A, B) v)) =
          (A : Sec12M) * Multiplicative.toAdd (e v) * (B : Sec12M)ᵀ := by
  obtain ⟨e, φ, hinj, hrange, hact⟩ := h
  let f : GaloisField 2 2 ≃+* Sec12F4 := sec12GF4Equiv
  let g : Sec12SL →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    Matrix.SpecialLinearGroup.map (f.symm : Sec12F4 →+* GaloisField 2 2)
  have hgc : ∀ A : Sec12SL, (g A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
      (A : Sec12M).map f.symm := fun A => rfl
  have hginj : Function.Injective g := by
    intro A A' hAA'
    apply Subtype.ext
    have h1 : (A : Sec12M).map f.symm = (A' : Sec12M).map f.symm := by
      rw [← hgc, ← hgc, hAA']
    exact Matrix.map_injective f.symm.injective h1
  have hgsurj : Function.Surjective g := fun A => sec12_map_surj A
  refine ⟨e.trans (AddEquiv.toMultiplicative f.mapMatrix.toAddEquiv),
    φ.comp (g.prodMap g), ?_, ?_, ?_⟩
  · intro p p' hpp'
    have h1 := hinj hpp'
    have h2 : g p.1 = g p'.1 := (Prod.ext_iff.mp h1).1
    have h3 : g p.2 = g p'.2 := (Prod.ext_iff.mp h1).2
    exact Prod.ext (hginj h2) (hginj h3)
  · apply le_antisymm
    · rw [← hrange]
      rintro _ ⟨p, rfl⟩
      exact ⟨g.prodMap g p, rfl⟩
    · rw [← hrange]
      rintro _ ⟨p, rfl⟩
      obtain ⟨a, ha⟩ := hgsurj p.1
      obtain ⟨b, hb⟩ := hgsurj p.2
      exact ⟨(a, b), by simp [ha, hb]⟩
  · intro A B v
    have h1 := hact (g A) (g B) v
    have h2 : (e.trans (AddEquiv.toMultiplicative f.mapMatrix.toAddEquiv))
        ((φ.comp (g.prodMap g)) (A, B) v) = Multiplicative.ofAdd (f.mapMatrix
          (Multiplicative.toAdd (e (φ (g A, g B) v)))) := rfl
    have h3 : Multiplicative.toAdd ((e.trans (AddEquiv.toMultiplicative f.mapMatrix.toAddEquiv)) v)
        = f.mapMatrix (Multiplicative.toAdd (e v)) := rfl
    have hA : f.mapMatrix (g A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) = (A : Sec12M) := by
      rw [hgc]; ext i j; simp
    have hB : f.mapMatrix (g B : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) = (B : Sec12M) := by
      rw [hgc]; ext i j; simp
    have hBt : f.mapMatrix ((g B : Matrix (Fin 2) (Fin 2) (GaloisField 2 2))ᵀ) = (B : Sec12M)ᵀ := by
      rw [← hB]
      ext i j
      simp [RingEquiv.mapMatrix_apply]
    rw [h2, h3, toAdd_ofAdd, h1, map_mul, map_mul, hA, hBt]

end CFSG.OddStandard.SmallF3.Omega
