module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBasic
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.J1
import CFSG.Adapters.StatedClassicalOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem examExcludes_alt : ExamExcludes FamAlt := by
  intro G _ _ K B B' P R m h ⟨n, hn5, hn8, ⟨e⟩⟩
  have h7 := h.pow_seven_dvd_card_quotient
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin] at h7
  interval_cases n <;> norm_num [Nat.factorial] at h7

theorem examExcludes_sporadic_small
    (s : TauCeti.SporadicName)
    (hs : s = .M11 ∨ s = .M12 ∨ s = .J1) : ExamExcludes (FamSporadic s) := by
  intro G _ _ K B B' P R m h ⟨e⟩
  have h7 := h.pow_seven_dvd_card_quotient
  rw [Nat.card_congr e.toEquiv] at h7
  rcases hs with rfl | rfl | rfl
  · rw [show Nat.card (NativeSporadic.Carrier .M11) = 7920 from
      CFSG.Sporadic.Mathieu.card_M11] at h7
    norm_num at h7
  · rw [show Nat.card (NativeSporadic.Carrier .M12) = 95040 from
      CFSG.Sporadic.Mathieu.card_M12] at h7
    norm_num at h7
  · rw [show Nat.card (NativeSporadic.Carrier .J1) = 175560 from
      CFSG.Sporadic.J1.card_J1] at h7
    norm_num at h7

theorem card_of_statedPSL {X : Type} [Group X] {n p f : ℕ} (hn : 2 ≤ n)
    (h : StatedClassicalModel X .PSL n p f) :
    Nat.card X = ((p ^ f) ^ (n * (n - 1) / 2) * ∏ index ∈ Finset.Icc 2 n, ((p ^ f) ^ index - 1)) /
      Nat.gcd n (p ^ f - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by omega) h

theorem examExcludes_l4 : ExamExcludes FamL4 := by
  intro G _ _ K B B' P R m h hmodel
  have h7 := h.pow_seven_dvd_card_quotient
  have hcard : Nat.card (↥K ⧸ Subgroup.center ↥K) = 20160 := by
    rw [card_of_statedPSL (by norm_num) hmodel]
    decide
  rw [hcard] at h7
  norm_num at h7

theorem examExcludes_evenL3_small :
    ∀ (G : Type) [Group G] [Finite G] (K B B' P R : Subgroup G) (m : ℕ),
      ExamConfig K B B' P R m → ∀ f : ℕ, f ≤ 2 → 1 ≤ f →
        ¬ StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL 3 2 f := by
  intro G _ _ K B B' P R m h f hf2 hf1 hmodel
  have h7 := h.pow_seven_dvd_card_quotient
  interval_cases f
  · have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 168 := by
      rw [card_of_statedPSL (by norm_num) hmodel]
      decide
    rw [hc] at h7
    norm_num at h7
  · have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 20160 := by
      rw [card_of_statedPSL (by norm_num) hmodel]
      decide
    rw [hc] at h7
    norm_num at h7

end CFSG.QuasithinUnique.Lin2
