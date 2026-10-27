module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem y7c_mulAut_equiv_GL6 {M : Type} [Group M] [Finite M] (hM : IsE 6 M) :
    Nonempty (MulAut M ≃* Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsE] at hM
  have hcomm : ∀ a b : M, a * b = b * a := fun a b =>
    congrArg Subtype.val
      (isMulCommutative_iff.mp hM.1.1 ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := M) (p := 2) (n := 6)
    hcomm (fun a => hM.1.2 a (Subgroup.mem_top a)) hM.2
  exact ⟨CFSG.SectionRank.Ccomm.elemAutEquivGL e⟩

theorem y7c_card_mulAut_E6 {M : Type} [Group M] [Finite M] (hM : IsE 6 M) :
    Nat.card (MulAut M) = 20158709760 := by
  obtain ⟨e⟩ := y7c_mulAut_equiv_GL6 hM
  rw [Nat.card_congr e.toEquiv]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Matrix.card_GL_field, ZMod.card]
  norm_num [Fin.prod_univ_succ]

theorem y7c_not_dvd_seven_cube {M : Type} [Group M] [Finite M] (hM : IsE 6 M) :
    ¬ 7 ^ 3 ∣ Nat.card (MulAut M) := by
  rw [y7c_card_mulAut_E6 hM]
  norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
