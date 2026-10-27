module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourKer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveKer
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.NineSettingOfHypC
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpPrimeCoreLe

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M Q H : Subgroup G} {p : ℕ}

theorem TwelveCtx.nineTwelveKerConclusion (h912 : NineTwelveKerGen) (h : TwelveCtx G M p Q H) :
    NineTwelveKerConclusion G M Q H Q p := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hC := h.hypCGen hEQ hE hEc hΓ
  exact h912 G M E H E p hC.toNineSettingGen hC.mem_H2Fam hC.not_mem_sigmaM

private theorem relPPrimeCore_kSub_le_kerIn (h : TwelveCtx G M p Q H) (hL : pLayerIn p H ≤ M) :
    relPPrimeCore p (kSub p M H) ≤
      CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn M (kSub p M H) := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hOH : relPPrimeCore p H ≤ M :=
    relPPrimeCore_le_of_gamma (Q := Q) h.p_prime (hEQ.trans h.Q_le_H) hE hEc hΓ
  have hOK : relPPrimeCore p (kSub p M H) ≤ M :=
    (relPPrimeCore_le_of_le_normal h.p_prime (kSub_le p M H) (kSub_normal_of_le hL)).trans hOH
  have hle := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
    (p := p) (kSub p M H)
  have hnormN := (Subgroup.normal_subgroupOf_iff hle).mp
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      h.p_prime (kSub p M H))
  exact fun x hx => CFSG.LocalAnalysis.RankThreeUC.WeakClosure.mem_kerIn.mpr
    ⟨hle hx, fun k hk => hOK (hnormN x k hx hk)⟩

theorem kSub_eq_centralizer_sup_kerIn_of_nineTwelveKer
    (h : TwelveCtx G M p Q H) (h912 : NineTwelveKerConclusion G M Q H Q p)
    (hL : pLayerIn p H ≤ M) {R W : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R (relPPrimeCore p H)) (hWR : W ≤ R)
    (hno5 : ¬ (p = 5 ∧ CFSG.IsExtraspecialPGroup 3 ↥(omegaOnePSub 3 R) ∧
      Nat.card ↥(omegaOnePSub 3 R) = 3 ^ 5 ∧ Monoid.exponent ↥(omegaOnePSub 3 R) = 3)) :
    kSub p M H = (kSub p M H ⊓ Subgroup.centralizer (W : Set G)) ⊔
      CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn M (kSub p M H) := by
  have hsup : kSub p M H ⊓ Subgroup.centralizer (R : Set G) ≤
      kSub p M H ⊓ Subgroup.centralizer (W : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hWR)
  refine le_antisymm ?_
    (sup_le inf_le_left (CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_left M _))
  rcases h912.2 hL R hR with h1 | h13 | h5
  · exact h1.le.trans (sup_le_sup hsup (relPPrimeCore_kSub_le_kerIn h hL))
  · rw [← kerIn_eq M (kSub p M H)]
    exact h13.2.le.trans (sup_le_sup hsup le_rfl)
  · exact absurd h5 hno5

theorem kSub_le_M_of_nineTwelveKer
    (h : TwelveCtx G M p Q H) (h912 : NineTwelveKerConclusion G M Q H Q p)
    (hL : pLayerIn p H ≤ M) {R W : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R (relPPrimeCore p H)) (hWR : W ≤ R)
    (hCW : Subgroup.centralizer (W : Set G) ≤ M)
    (hno5 : ¬ (p = 5 ∧ CFSG.IsExtraspecialPGroup 3 ↥(omegaOnePSub 3 R) ∧
      Nat.card ↥(omegaOnePSub 3 R) = 3 ^ 5 ∧ Monoid.exponent ↥(omegaOnePSub 3 R) = 3)) :
    kSub p M H ≤ M := by
  rw [kSub_eq_centralizer_sup_kerIn_of_nineTwelveKer h h912 hL hR hWR hno5]
  exact sup_le (inf_le_right.trans hCW)
    (CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_right M _)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
