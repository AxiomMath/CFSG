module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Block
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin Equiv
open scoped commutatorElement

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L : Subgroup G} {n : ℕ}

theorem normalizer_le_of_le_F4 (h : Hyp5_0_1 G T M L n) (h432 : Stmt4_3_2_F4) {C : Subgroup G}
    (hC : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hLC : L ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ M := by
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨C, hC, hC2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C : Set G)))
  have h1 := (h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le h.maximal
    h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩).1 M' hM' (hLC.trans hle)
  rw [← h1]
  exact hle

end Hyp5_0_1

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L : Subgroup G} {n : ℕ}

theorem isA5Block_F4 (he234 : E2.E23FourStatement) (h432 : Stmt4_3_2_F4) (hR : L2RankOneSylowFact)
    (h : Hyp5_0_1 G T M L n) {V W : Subgroup G} (hV : IsCh5Module T L V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hNS : ¬ Subgroup.normalizer (baum T : Set G) ≤ M) (F : S5Frame (L ⊔ T) W)
    (hWQ : W ≤ pCoreOf 2 L) (hO2W : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) :
    IsShort2 L ∧ IsAltType L 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ∀ C : Subgroup G, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ L ⊔ T ≤ Subgroup.normalizer (C : Set G) := by
    intro C hCS hC hch hLN
    exact hNS ((normalizer_le_normalizer_of_characteristic hCS hch).trans
      (h.normalizer_le_of_le_F4 h432 hC (h.sylow.1.to_le (hCS.trans inf_le_left))
        (le_sup_left.trans hLN)))
  have hct : CharTwo (L ⊔ T) :=
    charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, h.maximal.1.2.2.2⟩
  obtain ⟨K, hKb, hKT, hKC⟩ := he234 G (L ⊔ T) T (borelL T L ⊔ T) V (h.minParabolic_sup hR)
    h.sqtkGroup_sup hct hV.isTwoReducedIn hJ hchar
  have hLc : L ∈ cComp (L ⊔ T) := h.maximal.1.2.1
  have hn3 : ¬ IsAltType K 3 := fun h3 =>
    false_of_isSolvable_subnormal_sup h.sylow.1 le_sup_right hLc hKb.1.2.1 hKb.1.2.2
      (isSolvable_of_isAltType_three' h3) hKT
  have hKc : K ∈ cComp (L ⊔ T) := hKC hn3
  have hKL : K ≤ L := h.le_of_isShort2 hKb.1.1 hKb.1.2.1
  have hKeq : K = L := by
    by_contra hne
    exact hLc.2.2.2 K (lt_of_le_of_ne hKL hne) hKc.1 hKc.2.1 hKc.2.2.1
  rw [hKeq] at hKb
  obtain ⟨⟨hsh, -, -⟩, hty⟩ := hKb
  refine ⟨hsh, ?_⟩
  rcases hty with ⟨m, -, hlin⟩ | h3 | h5
  · exact (false_of_isLin2Type F (F.exists_mem_of_sign h.sylow.1 h.T_le_normalizer) hWQ hO2W
      hlin).elim
  · exact (not_isSolvable_of_mem_cComp hLc (isSolvable_of_isAltType_three' h3)).elim
  · exact h5

end Hyp5_0_1

end CFSG.Quasithin.H13
