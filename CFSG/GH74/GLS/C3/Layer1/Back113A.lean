module

public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.GH74.GLS.C3.Layer1.BackStmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem nonempty_alt5_of_hasL2Model5
    {K : Type} [Group K] (h : HasL2Model K (fun r => r = 5)) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨p, f, hp, hf, hP, hL⟩ := h
  obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).1 hP
  exact CFSG.QuasithinUnique.Setup.Family.alternating_five_of_model_five
    (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL)

theorem nonempty_alt6_of_hasL2Model9 {K : Type} [Group K] (h : HasL2Model K (fun r => r = 9)) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨p, f, hp, hf, hP, hL⟩ := h
  have hp3 : p = 3 := by
    have h1 : p ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hP]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h1)
  subst hp3
  have hf2 : f = 2 := by
    have : (3 : ℕ) ^ f = 3 ^ 2 := by rw [hP]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
  subst hf2
  exact CFSG.QuasithinUnique.Setup.Family.alternating_six_of_model_nine
    (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL)

variable {x : G} {K L M T Q : Subgroup G}

theorem kbar_alt (p91 : Prop91Concl K M T Q)
    (hK7 : ¬ HasL2Model (kBar K) (fun r => r = 7)) :
    ∃ n ∈ ({5, 6, 7} : Finset ℕ), Nonempty (kBar K ≃* alternatingGroup (Fin n)) := by
  obtain ⟨-, -, hc, hd⟩ := p91
  by_cases hex : ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K'
  · rcases hd hex with h | h
    · exact ⟨5, by simp, nonempty_alt5_of_hasL2Model5 h⟩
    · exact ⟨7, by simp, h⟩
  · obtain ⟨q, hq, hqm⟩ := hc hex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨5, by simp, nonempty_alt5_of_hasL2Model5 hqm⟩
    · exact absurd hqm hK7
    · exact ⟨6, by simp, nonempty_alt6_of_hasL2Model9 hqm⟩

theorem terminal_of
    (hh : Hyp9 x K L M T Q) (p91 : Prop91Concl K M T Q) (hnot : ¬ IsSylowOf 2 T ⊤) :
    IsTerminalPair 2 x K := by
  rcases hh.b with hB1 | hB2
  · by_contra hnt
    obtain ⟨y, hy⟩ := hB1.v2star
    have hex : ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K' := ⟨x, y, K, hy.1.1.1.1⟩
    have hA : Nonempty (kBar K ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := by
      rcases p91.2.2.2 hex with h | h
      · exact Or.inl (nonempty_alt5_of_hasL2Model5 h)
      · exact Or.inr h
    exact hnot (hB1.nonTerminal hnt p91.1.2 hA)
  · exact hB2.terminal

end CFSG.GH74.GLS.C3.Layer1.Back
