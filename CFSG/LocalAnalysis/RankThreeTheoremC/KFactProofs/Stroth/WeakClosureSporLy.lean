module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
public import CFSG.Sporadic.Recognition.LyonsAS44Conj
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThreeAux
import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
import CFSG.Sporadic.Recognition.LyonsAS44Cert

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.Sporadic.Recognition.LyonsSims

theorem wcOn_three_of_lemma45 {G : Type} [Group G] [Finite G] {x : G} (T : Sylow 3 G)
    (h : Lemma45 x (T : Subgroup G)) : WCOn 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine WCOn.of_sylow T fun hc => ?_
  exfalso
  obtain ⟨R, E, hRT, -, hR, -, hE, hcent, -⟩ := h
  have hRc : R ≤ Subgroup.centralizer (R : Set G) := by
    intro r hr s hs
    exact congrArg Subtype.val (hc.is_comm.comm ⟨s, hRT hs⟩ ⟨r, hRT hr⟩)
  rw [inf_of_le_left hRc] at hcent
  rw [hcent, hE] at hR
  norm_num at hR

theorem wcOn_Ly_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.Ly] : WCOn 3 CFSG.Blueprint.NativeSporadic.Ly := by
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult.oneClassDoubleCover_of_ly
      (T := CFSG.Blueprint.NativeSporadic.Ly) ⟨MulEquiv.refl _⟩)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  obtain ⟨T⟩ : Nonempty (Sylow 3 CFSG.Blueprint.NativeSporadic.Ly) := inferInstance
  exact wcOn_three_of_lemma45 T (lemma45_of_certificate D St T)

theorem wcOn_Ly_three
    [Finite (Carrier .Ly)] : WCOn 3 (Carrier .Ly) :=
  wcOn_Ly_three_aux

theorem wcSporadicAt_Ly
    [Finite (Carrier .Ly)] : WCSporadicAt .Ly := by
  refine wcSporadicAt_of_card .Ly (N := 51765179004000000) CFSG.Sporadic.Ly.card_Ly ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 51765179004000000 = {2, 3, 5, 7, 11, 31, 37, 67} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_Ly_three
  · haveI : Fact (Nat.Prime 5) := ⟨hq⟩
    exact WCOn.of_hasNoncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_Ly
  all_goals (exfalso; norm_num at hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
