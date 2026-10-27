module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMFlag
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMBlocks

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem leviAt_orthMinus {r f s : ℕ} {d : Fin (s + 1) → ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2 ^ f) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hd : OrthCuts r d)
    (p : ℕ) : LeviAt (orthParab r (minusTailForm K b c) d) p := by
  intro hB hp h5 hrank hpar hne hsyl
  have hp2 : p ≠ 2 := by omega
  have hpq : ¬ p ∣ Nat.card K ^ 2 - 1 := fun h => by
    have := orthMinus_two_le_pRank hr hK hirr hp hp2 h
    omega
  have hpQ : p ∣ Nat.card ↥(orthParab r (minusTailForm K b c) d) :=
    dvd_card_of_sylow_hyp hp hsyl
  exact leviAt_of_blocks (orthParab r (minusTailForm K b c) d).subtype
    (by rw [Subgroup.range_subtype]) hp h5 hpQ (orthLeviHom b c hd) (isPGroup_ker_orthLeviHom hd)
    (orthLeviBlock K r d b c)
    (pi_orthLeviBlock_le_range hd hr (commutator_orthogonalGroup_quadTail_minus hr hirr))
    (fun g hg hg1 => orthMinus_orthParab_hblk hd hK hirr hp h5 hpq g hg hg1)
    (fun y hy j => by
      have : y = 1 := Subtype.ext hy
      rw [this, map_one, Pi.one_apply]
      exact Subgroup.one_mem _)
    (orthMinus_two_le_pRank_three hr hK hirr)

theorem leviSubAt_orthMinus {r f : ℕ} (hr : 3 ≤ r) (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    LeviSubAt ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
  orthMinus_leviSubAt_of_orthParab hr hirr fun _ _ hd p => leviAt_orthMinus hr hK hirr hd p

theorem leviSubAt_of_pomegaMinus {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .POmegaMinus n 2 f) : LeviSubAt S := by
  obtain ⟨⟨-, -, hn⟩, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hcard
  exact LeviSubAt.of_mulEquiv (e.trans ((orthMinusStatedProjEquiv (by omega)).trans
    (tailOmegaEquiv (minusTailIsometry n K b c) (coe_quadMinus n K b c)
      (commutator_orthogonalGroup_quadMinus hn hirr))))
    (leviSubAt_orthMinus (by omega) hcard hirr)

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
