module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Stabilizer

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime
  CFSG.Sporadic.Recognition.PresentedWords CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem isSimpleGroup_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSimpleGroup X) : IsSimpleGroup Y :=
  have := h
  e.symm.isSimpleGroup

theorem isSimpleGroup_G :
    IsSimpleGroup (PG m0 X0) := by
  obtain ⟨e⟩ := nonempty_native_equiv
  exact isSimpleGroup_of_equiv (X := CFSG.Blueprint.NativeSporadic.Fi24prime) (Y := PG m0 X0) e
    CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime

theorem ker_rho_le_ker_toG :
    rho.ker ≤ toGQ.ker := by
  have hker_le_Zp : rho.ker ≤ Zp := by
    intro k hk
    rw [Zp_eq_stabilizer]
    refine MulAction.mem_stabilizer_iff.2 ?_
    rw [smul_def, MonoidHom.mem_ker.1 hk]
    rfl
  haveI : IsSimpleGroup (PG m0 X0) := isSimpleGroup_G
  haveI : (rho.ker.map toGQ).Normal :=
    Subgroup.Normal.map (inferInstance : rho.ker.Normal) toGQ (toG_surjective m0_eq)
  rcases Subgroup.Normal.eq_bot_or_eq_top (rho.ker.map toGQ) with hbot | htop
  · rwa [Subgroup.map_eq_bot_iff] at hbot
  · exfalso
    have hsurj : Function.Surjective (fun k : Zp => toGQ (k : Q3)) := by
      intro g
      have hg : g ∈ rho.ker.map toGQ := by rw [htop]; trivial
      rcases Subgroup.mem_map.1 hg with ⟨k, hk, rfl⟩
      exact ⟨⟨k, hker_le_Zp hk⟩, rfl⟩
    haveI : Finite Zp := Nat.finite_of_card_ne_zero (by rw [card_Zp]; norm_num)
    have hcard := Nat.card_le_card_of_surjective (fun k : Zp => toGQ (k : Q3)) hsurj
    rw [card_G, card_Zp] at hcard
    norm_num at hcard

theorem rho_injective :
    Function.Injective rho := by
  refine (MonoidHom.ker_eq_bot_iff rho).mp ?_
  have hle : rho.ker ≤ toGQ.ker := ker_rho_le_ker_toG
  have hdvd : Nat.card rho.ker ∣ 3 := by
    rw [← card_ker_toG]
    exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    haveI : Finite Q3 := Nat.finite_of_card_ne_zero (by rw [card_Q3]; norm_num)
    have hcard23 : Nat.card toGQ.ker ≤ Nat.card rho.ker :=
      le_of_eq (card_ker_toG.trans h3.symm)
    have hEq : rho.ker = toGQ.ker := Subgroup.eq_of_le_of_card_ge hle hcard23
    have hz : (PresentedGroup.of (zeta 10) : Q3) ∈ rho.ker := by
      rw [hEq]
      exact MonoidHom.mem_ker.2 (toG_zeta m0_eq (k := 10) (by norm_num))
    have hzne : rho (PresentedGroup.of (zeta 10) : Q3) ≠ 1 := by
      intro h
      apply zeta_smul_x0_ne
      rw [smul_def, h]
      rfl
    exact hzne (MonoidHom.mem_ker.1 hz)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
