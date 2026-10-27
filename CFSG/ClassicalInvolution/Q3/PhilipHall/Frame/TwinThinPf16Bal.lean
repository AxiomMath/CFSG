module

public import CFSG.ClassicalInvolution.Q3.TL3C1

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin

open CFSG CFSG.Open CFSG.ClassicalInvolution

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_bot_of_balance {t s : G}
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) (hPt : P ≤ Subgroup.centralizer ({t} : Set G))
    (hPn : ∀ c ∈ Subgroup.centralizer ({t} : Set G), ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hs : s ∈ P)
    {O : Subgroup G} (hOodd : Odd (Nat.card ↥O)) (hOs : O ≤ Subgroup.centralizer ({s} : Set G))
    (hOn : ∀ c ∈ Subgroup.centralizer ({s} : Set G), ∀ o ∈ O, c * o * c⁻¹ ∈ O) :
    O ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCdef
  set s' : ↥C := ⟨s, hPt hs⟩ with hs'
  set P' : Subgroup ↥C := P.subgroupOf C with hP'def
  have hP'n : P'.Normal := by
    refine ⟨fun p hp c => ?_⟩
    rw [hP'def, Subgroup.mem_subgroupOf] at hp ⊢
    exact hPn c c.2 p hp
  have hP'2 : IsPGroup 2 ↥P' := hP2.comap_of_injective C.subtype Subtype.val_injective
  have hsP' : s' ∈ P' := by
    rw [hP'def, Subgroup.mem_subgroupOf]
    exact hs
  have key := CFSG.ClassicalInvolution.Q3.TC.oddCoreImg_centralizer_eq_bot hO hP'n hP'2 hsP'
  set X : Subgroup ↥C := (O ⊓ C).subgroupOf C with hXdef
  have hXC : X ≤ Subgroup.centralizer ({s'} : Set ↥C) := by
    intro x hx
    rw [hXdef, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hOs hx.1)
    simpa [hs'] using h
  have hXodd : Odd (Nat.card ↥X) := by
    have hle : (O ⊓ C) ≤ O := inf_le_left
    have hcard : Nat.card ↥X = Nat.card ↥(O ⊓ C) := by
      rw [hXdef]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hcard]
    exact Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hle)
  have hXn : ∀ e ∈ Subgroup.centralizer ({s'} : Set ↥C), ∀ n ∈ X, e * n * e⁻¹ ∈ X := by
    intro e he n hn
    rw [hXdef, Subgroup.mem_subgroupOf] at hn ⊢
    have he' : (e : G) ∈ Subgroup.centralizer ({s} : Set G) := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp he
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg Subtype.val h
      simpa [hs'] using this
    refine ⟨?_, ?_⟩
    · show (e : G) * (n : G) * (e : G)⁻¹ ∈ O
      exact hOn e he' n hn.1
    · exact (e * n * e⁻¹).2
  have hXle := CFSG.ClassicalInvolution.Q3.TC.le_oddCoreImg_of_normalizes hXC hXn hXodd
  rw [key] at hXle
  rw [eq_bot_iff]
  intro x hx
  have hxX : (⟨x, hx.2⟩ : ↥C) ∈ X := by
    rw [hXdef, Subgroup.mem_subgroupOf]
    exact hx
  have h1 := hXle hxX
  rw [Subgroup.mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin
