module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Induct
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

theorem sol78JunctionAt_of_cor23SSec {H : Type} [Group H] [Finite H] (hcor : Sol78Cor23SSec H) :
    Sol78JunctionAt H := by
  intro hkp _ _ K M _ _ hlt hne hA hP
  obtain ⟨S, T, -, hT, hS2, hT2, hST, hKS, hMT, hKM⟩ := hlt
  have hSN : S ≤ normalizer (T : Set H) := le_normalizer_of_commutator_le hST
  have hKT : K ≤ centralizer (T : Set H) :=
    hKM.trans (conjClosure_le_of_le_normalizer hMT.1 fun g hg =>
      mem_normalizer_centralizer_of_mem_normalizer (hSN hg))
  have hKST : IsCompIn K (centralizer ((S ⊔ T : Subgroup H) : Set H)) :=
    isCompIn_of_le hKS (le_centralizer_sup hKS.1 hKT)
      (Subgroup.centralizer_le (by exact_mod_cast (le_sup_left : S ≤ S ⊔ T)))
  obtain ⟨m, L, T', s, hl, hL0, hLm, hT'ne, hLM, hinj⟩ :=
    (junction_conn (fun G _ _ hG _ => hcor G hG) hkp (Nat.card S) rfl hT hT2 hS2 hSN hMT hKST hKM
      ⟨hA, hP⟩).exists_inj
  refine ⟨m, L, T', s, ?_, hl.toChain hLm hinj, hL0, hT'ne, hLM⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact absurd (hL0.symm.trans hLm) hne
  · exact hm

end CFSG.EvenSporadicStandard.Induction.Junction
