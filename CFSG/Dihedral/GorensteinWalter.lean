module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.Dihedral.GorensteinWalter.ExternalSimpleAdapter

public section

namespace CFSG

open scoped MatrixGroups

namespace GorensteinWalter

theorem gorenstein_walter (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (_hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k)) := by
  exact ExternalSimpleAdapter.conclusion_of_isDGroup G hnonab P _hdih
    (GorensteinWalter.gorensteinWalter G
      (ExternalSimpleAdapter.hasDihedralSylowTwo G hnonab P _hdih))

end GorensteinWalter

end CFSG
