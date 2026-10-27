module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Setting

variable {G : Type*} [Group G]

theorem sigmaStar_le {p : ℕ} {M D : Subgroup G} (h : Prop95Hyp p M D) : sigmaStar D ≤ M :=
  iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => h.clause_a d hd hd1

theorem sigmaOf_le {p : ℕ} {M D : Subgroup G} (h : Prop95Hyp p M D) : sigmaOf D ≤ M :=
  (sigmaOf_le_sigmaStar D).trans (sigmaStar_le h)

theorem gammaD_le {p : ℕ} {M D : Subgroup G} (h : Prop95Hyp p M D) : gammaD D ≤ M :=
  (gammaD_le_sigmaStar D).trans (sigmaStar_le h)

theorem normalizer_le_normalizer_sigmaStar (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (sigmaStar D : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_gLBConj_eq] at hn ⊢
  rw [← sigmaStar_gLBConj, hn]

theorem normalizer_le_normalizer_sigmaOf (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (sigmaOf D : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_gLBConj_eq] at hn ⊢
  rw [← sigmaOf_gLBConj, hn]

end Setting

section Standing

variable {G : Type} [Group G] [Finite G]

theorem prime_of_standing {m p : ℕ} (hS : GLStanding G m p) : p.Prime :=
  hS.beta.1

theorem ne_two_of_standing {m p : ℕ} (hS : GLStanding G m p) : p ≠ 2 :=
  hS.beta.2.1

theorem charTwo_of_isTwoLocal {m p : ℕ} (hS : GLStanding G m p) {M : Subgroup G}
    (hM : IsTwoLocal M) : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
  hS.charTwo M hM

end Standing

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
