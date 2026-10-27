module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1OddA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure Y7AOdd (s : Setting3 G L) (N₃ : Subgroup G) : Prop where
  A_le : s.fr.A ≤ N₃
  le : N₃ ≤ normIn L s.fr.A
  pow9 : ∀ x ∈ N₃, x ^ 9 ∈ s.fr.A
  char : ∀ x ∈ normIn L s.fr.A, ∀ j : ℕ, x ^ (3 ^ j) ∈ s.fr.A → x ∈ N₃

theorem y7a_exists_N3 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ N₃ : Subgroup G, Y7AOdd s N₃ := by
  have h18 : SecProp (normIn L s.fr.A) (zL L ⊔ s.fr.A)
      (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y) := hH.hLF.fact18.1.2.1
  rw [f3_zL_eq_bot hH, bot_sup_eq] at h18
  obtain ⟨hn, hfrob⟩ := h18
  have hcard : Nat.card
      (↥(normIn L s.fr.A) ⧸ s.fr.A.subgroupOf (normIn L s.fr.A)) = 18 := hfrob.1
  have hAN : s.fr.A ≤ normIn L s.fr.A := fun a ha =>
    Subgroup.mem_inf.mpr ⟨s3_A_le_L s ha, Subgroup.le_normalizer ha⟩
  obtain ⟨N₃, hA, hle, hpow9, hchar⟩ :=
    y7a_odd_sub (A := s.fr.A) (N := normIn L s.fr.A) hAN (hn := hn) hcard
  exact ⟨N₃, hA, hle, hpow9, hchar⟩

end CFSG.OddStandard.HigherRank.YamadaG23
