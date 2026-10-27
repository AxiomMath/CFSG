module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDBase
public import CFSG.HardMathSupport.RichardWeiss.Proving.AltFiveGeneration

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.HardMathSupport.RichardWeiss.Proving

theorem s8d_cond {Z : Subgroup S8A}
    (θ' : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) ≃* ↥Z)
    (hθ : ∀ a : ↥(alternatingGroup (Fin 5)), (θ' (a, a) : S8A) = s8dDiag a) {f : S8A}
    (hf : (θ' (s8dG, 1) : S8A) = f) :
    f * s8dDiag (finRotate 5) = s8dDiag (finRotate 5) * f ∧ f ^ 5 = 1 ∧ f ≠ 1 ∧
      f ≠ s8dDiag (finRotate 5) ∧
      s8dDiag altFiveVPerm * f * (s8dDiag altFiveVPerm)⁻¹ * (f⁻¹ * s8dDiag (finRotate 5)) =
        f⁻¹ * s8dDiag (finRotate 5) * (s8dDiag altFiveVPerm * f * (s8dDiag altFiveVPerm)⁻¹) := by
  set ι : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) →* S8A :=
    Z.subtype.comp θ'.toMonoidHom with hι
  have hιv : ∀ x, ι x = (θ' x : S8A) := fun _ => rfl
  have hιinj : Function.Injective ι := Subtype.val_injective.comp θ'.injective
  have hf' : ι (s8dG, 1) = f := hf
  have hc0 : ι (s8dG, s8dG) = s8dDiag (finRotate 5) := hθ s8dG
  have hb : ι (altFiveV, altFiveV) = s8dDiag altFiveVPerm := hθ altFiveV
  have hg1 : s8dG ≠ 1 := by
    intro h
    have h1 := congrArg Subtype.val h
    exact absurd h1 (by decide)
  have hg5 : s8dG ^ 5 = 1 := Subtype.ext (by decide)
  rw [← hf', ← hc0, ← hb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    congr 1
  · rw [← map_pow, Prod.pow_mk, hg5, one_pow, Prod.mk_one_one, map_one]
  · intro h
    rw [← map_one ι] at h
    have h2 := congrArg Prod.fst (hιinj h)
    exact hg1 h2
  · intro h
    have h2 := congrArg Prod.snd (hιinj h)
    exact hg1 h2.symm
  · have key : ((altFiveV, altFiveV) * (s8dG, 1) * (altFiveV, altFiveV)⁻¹ *
        ((s8dG, 1)⁻¹ * (s8dG, s8dG)) :
          ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) =
        (s8dG, 1)⁻¹ * (s8dG, s8dG) *
          ((altFiveV, altFiveV) * (s8dG, 1) * (altFiveV, altFiveV)⁻¹) := by
      ext <;> simp [mul_assoc]
    have h := congrArg ι key
    simpa only [map_mul, map_inv] using h

end CFSG.OddStandard.SmallF3.Omega
