module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.false_of_escape (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoData3 p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤) (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hVL : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥)
    (hV : pCorePreimage p M ⊓ R ≠ ⊥) : False := by
  obtain ⟨e, heR, -, hep, -, -, hcen, heL⟩ := hd.toAt.exists_escape_elt
    (kFactCycAut_of_kFactOutCyclic hOut) hS hKL h84 hD2 hL hLX₀ hVL hV
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({(e : G)} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcen x hx)
  have hRe : R ≤ Subgroup.centralizer ({(e : G)} : Set G) := fun x hx => hPC (hd.cfg.ext.le_P hx)
  have hP1 : (P : Subgroup G).map (MulAut.conj (1 : G)).toMonoidHom = P := by
    ext x
    simp
  exact hd.noCentral e ⟨L, hL, hLX₀, heR, hep, hRe, heL⟩ ⟨1, M.one_mem, by rw [hP1]; exact hPC⟩

end Data

end CFSG.LocalAnalysis.RankThreeTheoremC
