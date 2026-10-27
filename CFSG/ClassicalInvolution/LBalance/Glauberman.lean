module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.ClassicalInvolution.LBalance.Glauberman.PartB

public section

namespace CFSG.ClassicalInvolution

theorem pPrimeCore_two_eq_oddCore (G : Type*) [Group G] : CFSG.pPrimeCore 2 G = CFSG.oddCore G := by
  unfold CFSG.pPrimeCore CFSG.oddCore
  congr 1
  ext N
  exact and_congr_right fun _ => Nat.coprime_two_left

theorem eq_bot_of_pPrimeCore_eq_bot {G : Type*} [Group G] (hG : CFSG.pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) : N = ⊥ := by
  rw [← le_bot_iff, ← hG]
  exact le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hN⟩

variable {G : Type} [Group G] [Finite G]

theorem glauberman_sylowFixingAut_sylow_comm (hG : CFSG.pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (P : Sylow 2 (sylowFixingAut (S : Subgroup G))) : ∀ x y : P, x * y = y * x :=
  GlaubermanAut.sylow_comm (fun N hN hodd => @eq_bot_of_pPrimeCore_eq_bot G _ hG N hN hodd)
    S.isPGroup' (Sylow.not_dvd_index S) P

theorem glauberman_sylowFixingAut_normal_complement (hG : CFSG.pPrimeCore 2 G = ⊥) (S : Sylow 2 G) :
    ∃ N : Subgroup (sylowFixingAut (S : Subgroup G)), ∃ _ : N.Normal, Odd (Nat.card N) ∧
      IsPGroup 2 (sylowFixingAut (S : Subgroup G) ⧸ N) :=
  GlaubermanAut.exists_normal_two_complement
    (fun N hN hodd => @eq_bot_of_pPrimeCore_eq_bot G _ hG N hN hodd) S.isPGroup'
    (Sylow.not_dvd_index S)

theorem glauberman_sylowFixingAut_normal_complement_index (hG : CFSG.pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) :
    ∃ N : Subgroup (sylowFixingAut (S : Subgroup G)), N.Normal ∧ Odd (Nat.card N) ∧
      ∃ k : ℕ, N.index = 2 ^ k := by
  obtain ⟨N, hN, hodd, hq⟩ := glauberman_sylowFixingAut_normal_complement hG S
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hq
  exact ⟨N, hN, hodd, k, by rw [Subgroup.index_eq_card]; exact hk⟩

theorem glauberman_sylowFixingAut_isSolvable (hG : CFSG.pPrimeCore 2 G = ⊥) (S : Sylow 2 G) :
    Group.IsSolvable (sylowFixingAut (S : Subgroup G)) :=
  GlaubermanAut.isSolvable_sylowFixingAut
    (fun N hN hodd => @eq_bot_of_pPrimeCore_eq_bot G _ hG N hN hodd) S.isPGroup'
    (Sylow.not_dvd_index S)

theorem glaubermanSylowFixingSolvable : GlaubermanSylowFixingSolvable :=
  fun G _ _ hG S => @glauberman_sylowFixingAut_isSolvable G _ _ hG S

end CFSG.ClassicalInvolution
