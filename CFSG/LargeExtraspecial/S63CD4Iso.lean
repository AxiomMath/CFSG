module

public import CFSG.Quasithin.Recognition.CertD4Bridge
public import CFSG.Quasithin.Recognition.CertTrialityModel

public section

namespace CFSG.LargeExtraspecial.S63

open CFSG.Blueprint CFSG.Quasithin
open CFSG.Open (quasithinRootElt quasithinD4Root quasithinTrialityD4Two quasithinTrialityGens)

theorem map_quasithinRootElt' {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (pos : List (Fin 8 × Fin 8)) (t : K) :
    (quasithinRootElt pos t).map f = quasithinRootElt pos (f t) := by
  ext r c
  simp only [quasithinRootElt, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_rootProd' {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (a : K) (s : Bool) :
    (quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) (a ^ 2) *
      quasithinRootElt (quasithinD4Root 3 s) (a ^ 4)).map f =
    quasithinRootElt (quasithinD4Root 0 s) (f a) *
      quasithinRootElt (quasithinD4Root 2 s) (f a ^ 2) *
      quasithinRootElt (quasithinD4Root 3 s) (f a ^ 4) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_quasithinRootElt', map_quasithinRootElt',
    map_quasithinRootElt', map_pow, map_pow]

theorem coe_map_gl' {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (A : GL (Fin 8) K) :
    ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) =
      (A : Matrix (Fin 8) (Fin 8) K).map f := by
  simp [Matrix.GeneralLinearGroup.map]

theorem nonempty_quasithinTrialityD4Two_equiv :
    Nonempty (quasithinTrialityD4Two ≃* trialityGroup8) := by
  let e := gf8EquivGaloisField
  let f : GaloisField 2 3 →+* GF8 := e.symm.toRingHom
  let g : GF8 →+* GaloisField 2 3 := e.toRingHom
  let ψ : GL (Fin 8) (GaloisField 2 3) →* GL (Fin 8) GF8 := Matrix.GeneralLinearGroup.map f
  have hinj : Function.Injective ψ := by
    refine Units.map_injective (f := (f.mapMatrix : Matrix (Fin 8) (Fin 8) (GaloisField 2 3) →+*
      Matrix (Fin 8) (Fin 8) GF8).toMonoidHom) ?_
    intro M N h
    exact Matrix.map_injective e.symm.injective h
  have hset : ψ '' {A : GL (Fin 8) (GaloisField 2 3) |
      (A : Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) ∈ quasithinTrialityGens} =
      {A : GL (Fin 8) GF8 | (A : Matrix (Fin 8) (Fin 8) GF8) ∈ trialityGens8} := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      rcases hA with ⟨a, s, hs⟩ | ⟨s, hs⟩
      · refine Or.inl ⟨f a, s, ?_⟩
        show ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) GF8) :
          Matrix (Fin 8) (Fin 8) GF8) = _
        rw [coe_map_gl', hs, map_rootProd']
        rfl
      · refine Or.inr ⟨s, ?_⟩
        show ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) GF8) :
          Matrix (Fin 8) (Fin 8) GF8) = _
        rw [coe_map_gl', hs, map_quasithinRootElt', map_one]
        rfl
    · intro hB
      let A : GL (Fin 8) (GaloisField 2 3) := Matrix.GeneralLinearGroup.map g B
      have hA : (A : Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) =
          (B : Matrix (Fin 8) (Fin 8) GF8).map g := coe_map_gl' g B
      have hψA : ψ A = B := by
        apply Units.ext
        show ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) GF8) :
          Matrix (Fin 8) (Fin 8) GF8) = _
        rw [coe_map_gl', hA, Matrix.map_map]
        ext i j
        simp [f, g]
      refine ⟨A, ?_, hψA⟩
      rcases hB with ⟨a, s, hs⟩ | ⟨s, hs⟩
      · refine Or.inl ⟨g a, s, ?_⟩
        rw [hA, hs]
        exact map_rootProd' g a s
      · refine Or.inr ⟨s, ?_⟩
        rw [hA, hs]
        show (quasithinRootElt (quasithinD4Root 1 s) (1 : GF8)).map g = _
        rw [map_quasithinRootElt', map_one]
  have hmap : quasithinTrialityD4Two.map ψ = trialityGroup8 := by
    rw [quasithinTrialityD4Two, trialityGroup8, MonoidHom.map_closure, hset]
  exact ⟨(Subgroup.equivMapOfInjective _ ψ hinj).trans (MulEquiv.subgroupCongr hmap)⟩

theorem nonempty_equiv_trialityGroup8
    (X : Type) [Group X] (h : LieModel X .trialityD4 0 2 1) :
    Nonempty (X ≃* trialityGroup8) := by
  obtain ⟨e1⟩ := trialityD4ModelBridge_of_lieModel X h
  obtain ⟨e2⟩ := nonempty_quasithinTrialityD4Two_equiv
  exact ⟨e1.trans e2⟩

end CFSG.LargeExtraspecial.S63
