module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Gold

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

open Subgroup CFSG.Open CFSG.Goldschmidt

variable {X : Type} [Group X] [Finite X]

theorem map_conjNormal_oddCore (A : Subgroup X) (g : X) :
    (goldschmidtOddCore ↥(nc A)).map (MulAut.conjNormal g : MulAut ↥(nc A)).toMonoidHom =
      goldschmidtOddCore ↥(nc A) := by
  rw [goldschmidtOddCore_eq_pPrimeCore]
  exact CFSG.pPrimeCore_map_iso 2 _

@[expose] noncomputable def rhoAut (A : Subgroup X) (g : X) : MulAut (Mbar A) :=
  QuotientGroup.congr (goldschmidtOddCore ↥(nc A)) (goldschmidtOddCore ↥(nc A))
    (MulAut.conjNormal g) (map_conjNormal_oddCore A g)

theorem rhoAut_proj (A : Subgroup X) (g : X) (m : ↥(nc A)) :
    rhoAut A g (proj A m) = proj A (MulAut.conjNormal g m) := rfl

theorem rhoAut_one (A : Subgroup X) : rhoAut A 1 = 1 := by
  ext q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥(nc A)) q
  rw [rhoAut_proj]
  simp

theorem rhoAut_mul (A : Subgroup X) (g h : X) : rhoAut A (g * h) = rhoAut A g * rhoAut A h := by
  ext q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥(nc A)) q
  rw [MulAut.mul_apply, rhoAut_proj, rhoAut_proj, rhoAut_proj]
  simp

@[expose] noncomputable def rhoHom (A : Subgroup X) : X →* MulAut (Mbar A) where
  toFun := rhoAut A
  map_one' := rhoAut_one A
  map_mul' := rhoAut_mul A

theorem map_rhoHom_pCore (A : Subgroup X) (g : X) :
    (pCore 2 (Mbar A)).map (rhoHom A g).toMonoidHom = pCore 2 (Mbar A) :=
  CFSG.pCore_map_iso 2 (rhoHom A g)

theorem rhoHom_mem_pCore (A : Subgroup X) (g : X) {q : Mbar A} (hq : q ∈ pCore 2 (Mbar A)) :
    rhoHom A g q ∈ pCore 2 (Mbar A) := by
  rw [← map_rhoHom_pCore A g]
  exact ⟨q, hq, rfl⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold
