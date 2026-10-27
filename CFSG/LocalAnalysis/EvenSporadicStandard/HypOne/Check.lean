module

public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.EvenSporadicStandard.HypOne

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Open

@[expose] def e8Check (n : ℕ) (a b c : Table) : Bool :=
  commT n a b && commT n a c && commT n b c && ordTest n 2 a && ordTest n 2 b && ordTest n 2 c &&
    ordTest n 2 (compT n a b) && ordTest n 2 (compT n a c) && ordTest n 2 (compT n b c) &&
    ordTest n 2 (compT n (compT n a b) c)

theorem hasElemAbelianEight_of_e8Check {n : ℕ} (hn : n < 2 ^ 32) {a b c : Equiv.Perm (Fin n)}
    (h : e8Check n (toTable a) (toTable b) (toTable c) = true)
    {K : Subgroup (Equiv.Perm (Fin n))} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    HasElemAbelianEight K := by
  simp only [e8Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hac⟩, hbc⟩, ha2⟩, hb2⟩, hc2⟩, hab2⟩, hac2⟩, hbc2⟩, habc2⟩ := h
  have rA := rep_toTable hn a
  have rB := rep_toTable hn b
  have rC := rep_toTable hn c
  have order2 : ∀ {T : Table} {g : Equiv.Perm (Fin n)}, Rep n T g → ordTest n 2 T = true →
      orderOf g = 2 := fun hT hT2 => (ordTest_iff perm_faithful hT (by norm_num)).1 hT2
  obtain ⟨E, hE, hEe, hEc⟩ := exists_elemAbelian_eight a b c
    ((commT_iff rA rB).1 hab) ((commT_iff rA rC).1 hac) ((commT_iff rB rC).1 hbc)
    (order2 rA ha2) (order2 rB hb2) (order2 rC hc2)
    (order2 (Rep.compT rA rB) hab2) (order2 (Rep.compT rA rC) hac2)
    (order2 (Rep.compT rB rC) hbc2) (order2 (Rep.compT (Rep.compT rA rB) rC) habc2)
  refine HasElemAbelianEight.of_le (hE.trans ?_) hEe hEc
  exact sup_le (sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb))
    (Subgroup.zpowers_le.mpr hc)

end CFSG.EvenSporadicStandard.HypOne
