module

public import CFSG.CGT.PushingUpLit.BHS.HomTransfer
public import CFSG.Quasithin.Background.A1a

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_noncomm_of_nonabelian {P T M Y A : Subgroup (MulAut V)} (hmin : MinPar P T M)
    (ho2 : pCoreOf 2 P = ⊥) (hYn : P ≤ Subgroup.normalizer (Y : Set (MulAut V)))
    (hYO : Y ≤ opResidual 2 P) (hYab : ∃ a ∈ Y, ∃ b ∈ Y, a * b ≠ b * a)
    (hAT : A ≤ T) (hA : A ≠ ⊥) : ∃ a ∈ A, ∃ y ∈ Y, a * y ≠ y * a := by
  by_contra hcon
  push Not at hcon
  set D : Subgroup (MulAut V) := P ⊓ Subgroup.centralizer (Y : Set (MulAut V)) with hD
  have hDP : D ≤ P := inf_le_left
  have hDn : P ≤ Subgroup.normalizer (D : Set (MulAut V)) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, A1a.le_normalizer_centralizer hYn hg⟩
  by_cases hDM : D ≤ M
  · have h33 := three_three_a hmin.syl hmin.lt_P hmin.max hDP hDn hDM
    have hDT : D ⊓ T ≤ pCoreOf 2 P := le_pCoreOf_of_le_normalizer 2
      (inf_le_right.trans hmin.T_le) h33 (hmin.syl.2.1.to_le inf_le_right)
    rw [ho2] at hDT
    apply hA
    rw [eq_bot_iff]
    intro a ha
    exact hDT ⟨⟨hmin.T_le (hAT ha),
      Subgroup.mem_centralizer_iff.2 fun y hy => (hcon a ha y hy).symm⟩, hAT ha⟩
  · have hOD := three_three_b hmin.syl hmin.max hDP hDn hDM
    obtain ⟨a, ha, b, hb, hab⟩ := hYab
    exact hab (Subgroup.mem_centralizer_iff.1 (hOD (hYO hb)).2 a ha)

end CFSG.CGT.PushingUpLit.BHS5
