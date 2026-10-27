module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXElem
public import CFSG.RankThree.PartOne.KS.HeKit
public import CFSG.Sporadic.HeldB.InnerClass
public import Certificates.Certificate22615

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Sporadic.HeldB SporX

theorem he_elem_t0 :
    ∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {heGenPerm 0} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ 4 ≤ Nat.card E :=
  Certificates.certificate22615.1

theorem he_elem_t1 :
    ∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {heT1P} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ 4 ≤ Nat.card E :=
  Certificates.certificate22615.2.1

theorem he_elem_u :
    ∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {heAutU} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ 3 ≤ Nat.card E :=
  Certificates.certificate22615.2.2

theorem hinFor_spor_He :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .He := by
  intro Y _ _ _ ⟨e₀⟩ _ p m _ _ _ _ _ τ hτ _
  refine hinConcl_of_autModel CFSG.RankThree.PartOne.heAutModel
    (Rp := fun ρ => ρ = heGenPerm 0 ∨ ρ = heT1P ∨ ρ = heAutU) ?_ ?_ (e₀.trans heEquivP) p m τ hτ
  · intro t ht ht2
    by_cases htP : t ∈ heP
    · rcases involution_conj_cases htP ht2 with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
      · exact ⟨_, Or.inl rfl, g, heP_le_heAutGroup hg, rfl⟩
      · exact ⟨_, Or.inr (Or.inl rfl), g, heP_le_heAutGroup hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := exists_conj_heAutU ht htP ht2
      exact ⟨_, Or.inr (Or.inr rfl), g, heP_le_heAutGroup hg, rfl⟩
  · rintro _ (rfl | rfl | rfl)
    · obtain ⟨E, hE, hc, hs, hcard⟩ := he_elem_t0
      exact ⟨E, hE, hc, hs, fun _ => lt_of_lt_of_le (by norm_num) hcard,
        fun _ => lt_of_lt_of_le (by norm_num) hcard⟩
    · obtain ⟨E, hE, hc, hs, hcard⟩ := he_elem_t1
      exact ⟨E, hE, hc, hs, fun _ => lt_of_lt_of_le (by norm_num) hcard,
        fun _ => lt_of_lt_of_le (by norm_num) hcard⟩
    · obtain ⟨E, hE, hc, hs, hcard⟩ := he_elem_u
      exact ⟨E, hE, hc, hs, fun h => absurd h heAutU_not_mem,
        fun _ => lt_of_lt_of_le (by norm_num) hcard⟩

end CFSG.ComponentClassification.HarrisLit.Hin
