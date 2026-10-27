module

public import CFSG.Dihedral.GorensteinWalter
public import CFSG.Dihedral.OriginalProjectiveExclusion

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem aSeven_model_of_pure [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hp : d.PureProjectiveNormalizer) (hR : d.R ≠ ⊥) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨i, _, _, hi, _⟩ := hp.2.2.2.2
  rcases gorenstein_walter G hnonab d.S
      ⟨2 ^ (d.n - 1), d.sylow_mulEquiv_dihedral⟩ with hA | hP
  · exact hA
  · obtain ⟨p, k, hprime, hpodd, hsize, ⟨e⟩⟩ := hP
    let : Fact p.Prime := hprime
    have hk : k ≠ 0 := by
      intro hk
      simp [hk] at hsize
    have hfield : IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hprime.out, hpodd, by omega, GaloisField.card p k hk⟩
    exact False.elim (hR (d.R_eq_bot_of_psl2_model i hi (GaloisField p k) hfield e))

end CFSG.DihedralBlueprint.OriginalData
