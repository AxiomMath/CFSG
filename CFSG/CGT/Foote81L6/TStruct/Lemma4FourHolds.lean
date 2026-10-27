module

public import CFSG.CGT.Foote81L6.TStruct.Lemma4Four
public import CFSG.CGT.Foote81L6.Fusion.FourthPower
public import CFSG.CGT.Foote81L6.MainL6Inputs

public section

namespace CFSG.CGT.Foote81L6

theorem footeLemma4OneFour_holds (h3 : FooteLemma3One) : FooteLemma4OneFour := by
  intro G _ _ T n D g hgT hg1
  have hTC : (T : Subgroup G) ≤ Subgroup.centralizer ({D.a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (D.a_comm_T hx)
  exact D.lemma4_one_four rfl (footeNotConjAB_of_one h3 G T 2 n D)
    (fun g' hg'T hg'0 => D.isConj_mul_b_of_not_mem_T₀
      (D.eq_b_of_isConj_b_of_lemma3 (h3 G T 2 n D)) le_rfl (T.subtype hTC)
      (Sylow.coe_subtype T hTC) D.a_mul_a hg'T hg'0) hgT hg1

end CFSG.CGT.Foote81L6
