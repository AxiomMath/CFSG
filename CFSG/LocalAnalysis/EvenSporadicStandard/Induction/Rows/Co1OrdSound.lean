module

public import Certificates.Certificate27217
public import CFSG.RankThree.PartOne.KS.Co1ScalCheck

public section

namespace CFSG.EvenSporadicStandard.Induction.Co1Ord

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Sporadic.GLQ
  CFSG.Blueprint CFSG.RankThree.PartOne.KS
open scoped Matrix

theorem exists_orderOf_sixteen :
    ∃ g : NativeSporadic.Co1, orderOf g = 16 := by
  have h : co1OrdCheck () = true := Certificates.certificate27217
  unfold co1OrdCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hprog, hpow⟩, hne⟩ := h
  have hR := regsRep_runProg co1OrdProg hprog
    (regsRep_initRegs (n := 11) Co1Scal.rep_gA Co1Scal.rep_gB)
  let g : NativeSporadic.Co1 := runProg (initRegs Co1Scal.gA Co1Scal.gB) co1OrdProg co1OrdOut
  have hX : CFSG.Sporadic.GLQ.Rep (spec2 24) (valHom Co1Scal.SM) g (co1OrdRegs ())[co1OrdOut]! :=
    hR.2 co1OrdOut (by decide)
  have hW := hX.1
  have hM : (spec2 24).toMat (co1OrdRegs ())[co1OrdOut]!.1 = valHom Co1Scal.SM g := hX.2.2.1
  have h16 : valHom Co1Scal.SM g ^ 16 = 1 := by
    rw [← hM]
    exact (spec2 24).pow_eq_one_of_check hW hpow
  have hg16 : g ^ 16 = 1 :=
    valHom_injective Co1Scal.SM (by rw [map_pow, map_one]; exact h16)
  have hg8 : ¬ g ^ 8 = 1 := by
    intro hg8
    have h8 : valHom Co1Scal.SM g ^ 8 = 1 := by rw [← map_pow, hg8, map_one]
    apply (spec2 24).toVec_ne hne
    rw [(spec2 24).toVec_vmul ((spec2 24).unit_wf 0) ((spec2 24).pow_spec hW 8).1,
      ((spec2 24).pow_spec hW 8).2, hM, h8, Matrix.vecMul_one]
  refine ⟨g, ?_⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 3) hg8 hg16

end CFSG.EvenSporadicStandard.Induction.Co1Ord
