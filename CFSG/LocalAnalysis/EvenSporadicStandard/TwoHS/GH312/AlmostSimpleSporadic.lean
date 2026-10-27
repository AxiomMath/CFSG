module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleIndexFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleLocal
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Card
public import CFSG.Sporadic.J2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore

public section

open Subgroup CFSG.Blueprint

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

theorem AlmostSimpleLocal.card_centralizer_eq_of_isSporadic_M12
    {T : Type} [Group T] {u : T}
    (h : AlmostSimpleLocal T u) (hT : NativeSporadic.IsSporadic T .M12) :
    Nat.card ↥(centralizer ({u} : Set T)) = 240 := by
  obtain ⟨e⟩ := hT
  rcases CFSG.Sporadic.Schreier.card_centralizer_involution_of_mulEquiv_M12 e h.orderOf_eq with
    h1 | h1
  · have := h.sixty_dvd
    rw [h1] at this
    omega
  · exact h1

theorem two_pow_six_dvd_card_of_isSporadic_M12 {T : Type}
    [Group T] (hT : NativeSporadic.IsSporadic T .M12) : 2 ^ 6 ∣ Nat.card T := by
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv]
  have h : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Schreier.m12_card
  rw [h]
  norm_num

theorem false_of_isSporadic_M12
    {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : T.Normal) {u : X} (huT : u ∈ T) (hloc : AlmostSimpleLocal ↥T ⟨u, huT⟩)
    (hM : NativeSporadic.IsSporadic ↥T .M12)
    (hC : Nat.card ↥(centralizer ({u} : Set X)) = 960) (P : Sylow 2 X)
    (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7) : False := by
  have h240 := hloc.card_centralizer_eq_of_isSporadic_M12 hM
  rw [card_centralizer_subtype_eq_card_inf huT] at h240
  exact false_of_card_centralizer_eq_four_mul hT (two_pow_six_dvd_card_of_isSporadic_M12 hM) P hP
    (by rw [hC, h240])

open CFSG.ComponentClassification.J2Cover in
theorem card_centralizer_involution_of_isSporadic_J2
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .J2)
    {u : Y} (hu : orderOf u = 2) :
    Nat.card ↥(centralizer ({u} : Set Y)) = 240 ∨
      Nat.card ↥(centralizer ({u} : Set Y)) = 1920 := by
  obtain ⟨e⟩ := hY
  let e' : Y ≃* P := e.trans nativeEquivP
  rw [← card_centralizer_singleton_mulEquiv e' u]
  have hz : orderOf ((e' u : P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hu
  obtain ⟨hcov, -, h2B, -, h2A⟩ := inner_classes
  obtain ⟨r, hr, c, hcP, hrc⟩ := hcov _ (e' u).2 hz
  have hrP : r ∈ P := by
    have : r = c⁻¹ * (e' u : Equiv.Perm (Fin 315)) * c := by rw [hrc]; group
    rw [this]
    exact P.mul_mem (P.mul_mem (P.inv_mem hcP) (e' u).2) hcP
  have hic : IsConj (⟨r, hrP⟩ : P) (e' u) :=
    isConj_iff.2 ⟨(⟨c, hcP⟩ : P), Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hrc.symm)⟩
  rw [← card_centralizer_singleton_eq_of_isConj hic, card_centralizer_subtype_eq_card_inf hrP]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    rw [show (P ⊓ centralizer ({permA} : Set (Equiv.Perm (Fin 315))) : Subgroup _) =
      CFSG.Sporadic.Schreier.centralizerIn P permA from rfl, h2B, (cent2B_facts).2.1]
  · right
    rw [show (P ⊓ centralizer ({permTwoA} : Set (Equiv.Perm (Fin 315))) : Subgroup _) =
      CFSG.Sporadic.Schreier.centralizerIn P permTwoA from rfl, h2A, (cent2A_facts).2.1]

theorem AlmostSimpleLocal.card_centralizer_eq_of_isSporadic_J2
    {T : Type} [Group T] {u : T} (h : AlmostSimpleLocal T u)
    (hT : NativeSporadic.IsSporadic T .J2) : Nat.card ↥(centralizer ({u} : Set T)) = 240 := by
  rcases card_centralizer_involution_of_isSporadic_J2 hT h.orderOf_eq with h1 | h1
  · exact h1
  · have := h.card_dvd
    rw [h1] at this
    omega

theorem two_pow_six_dvd_card_of_isSporadic_J2 {T : Type}
    [Group T] (hT : NativeSporadic.IsSporadic T .J2) : 2 ^ 6 ∣ Nat.card T := by
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv]
  have h : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  rw [h]
  norm_num

theorem false_of_isSporadic_J2
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hT : T.Normal) {u : X} (huT : u ∈ T)
    (hloc : AlmostSimpleLocal ↥T ⟨u, huT⟩) (hJ : NativeSporadic.IsSporadic ↥T .J2)
    (hC : Nat.card ↥(centralizer ({u} : Set X)) = 960) (P : Sylow 2 X)
    (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7) : False := by
  have h240 := hloc.card_centralizer_eq_of_isSporadic_J2 hJ
  rw [card_centralizer_subtype_eq_card_inf huT] at h240
  exact false_of_card_centralizer_eq_four_mul hT (two_pow_six_dvd_card_of_isSporadic_J2 hJ) P hP
    (by rw [hC, h240])

end CFSG.EvenSporadicStandard.TwoHS.GH312
