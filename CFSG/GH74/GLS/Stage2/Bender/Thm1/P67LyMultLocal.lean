module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultCover
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultArith
public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.Sporadic.Ly
public import CFSG.GH74.Generic.GKFCover
public import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.LySchreier

theorem coverBound_alt11 : CoverBound (alternatingGroup (Fin 11)) 2 2 := by
  intro E _ _ hE q hq hker _
  have h := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hE q hq hker
  rwa [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (by norm_num)] at h

theorem card_alternatingGroup_eleven : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem exists_noncomm_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnp : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup G := { ‹Group G› with mul_comm := fun a b => h a b }
  exact hnp IsSimpleGroup.prime_card

theorem lyMult_two
    {J T : Type} [Group J] [Finite J] [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.Ly)) (π : J →* T) (hπ : Function.Surjective π)
    (hJ : Group.IsPerfect J) (hz : π.ker ≤ center J) (hp : IsPGroup 2 π.ker) : π.ker = ⊥ := by
  obtain ⟨eT⟩ := hT
  have hcard : Nat.card T = 51765179004000000 := by
    rw [Nat.card_congr eT.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  have hfin : Finite T := Finite.of_surjective π hπ
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 (by rw [hcard]; norm_num)
  obtain ⟨hq, hc, ⟨e⟩⟩ := involution_centralizers_quasisimple ⟨eT⟩ t ht
  have hKp : IsPGroup 2 (center ↥(centralizer ({t} : Set T))) :=
    IsPGroup.of_card (n := 1) (by rw [hc, pow_one])
  have hKc : Nat.card (centralizer ({t} : Set T)) = 39916800 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center ↥(centralizer ({t} : Set T)))
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_eleven, hc] at h1
    omega
  have hA := eq_one_of_mem_commutator_comap π hπ hz hp (centralizer ({t} : Set T)) hq.1 e hKp
    (by rw [hc]; exact coverBound_alt11)
  refine ker_eq_bot_of_local π hπ hJ hz hp (centralizer ({t} : Set T)) ?_ hA
  rw [hKc, hcard, factorization_two_cover_alt11, factorization_two_lyOrder]

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult
