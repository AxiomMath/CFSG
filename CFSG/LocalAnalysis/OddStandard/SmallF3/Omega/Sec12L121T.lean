module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121V0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

theorem sec121_t_not_mem_V (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) :
    t ∉ secV t S L E := by
  obtain ⟨V0, -, hB, hinv, hdec, ht⟩ := sec121_exists_V0 F hE
  exact fun h => ht (sec121_V_le_V0 F hE hB hinv hdec h)

theorem sec121_V_inf_zpowers (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) :
    secV t S L E ⊓ zpowers t = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxV, hxt⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxt
  have hmod : t ^ (k % ((orderOf t : ℕ) : ℤ)) = t ^ k := zpow_mod_orderOf t k
  rw [F.ht2] at hmod
  have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk with hk | hk
  · rw [← hmod, hk, zpow_zero]
  · rw [hk, zpow_one] at hmod
    rw [← hmod] at hxV
    exact absurd hxV (sec121_t_not_mem_V F hE)

theorem sec121_V_sup_zpowers (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) :
    secV t S L E ⊔ zpowers t = E := by
  have htA : t ∈ secA t S L := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hBV : secB S L ≤ secV t S L E ⊔ zpowers t := (sec121_B_le_V F hE).trans le_sup_left
  have hAV : secA t S L ≤ secV t S L E ⊔ zpowers t := sup_le hBV le_sup_right
  apply le_antisymm
  · exact sup_le (sec121_V_le_E F hE) ((Subgroup.zpowers_le.2 (sec120_A_le_E F hE htA)))
  · intro e he
    obtain ⟨v, hv, hfv⟩ := sec121_f_surj_V F hE (sec12E_f_mem F (hE.1 he))
    have hvE : v ∈ E := sec121_V_le_E F hE hv
    have ha : v⁻¹ * e ∈ secA t S L := sec120_inv_mul_mem_A F hE hvE he hfv
    have hmem : v * (v⁻¹ * e) ∈ secV t S L E ⊔ zpowers t :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (hAV ha)
    simpa using hmem

theorem sec121_f_eq_one_iff_V (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) {v : G}
    (hv : v ∈ secV t S L E) : sec12f t v = 1 ↔ v ∈ secB S L := by
  have hvE : v ∈ E := sec121_V_le_E F hE hv
  rw [sec120_f_eq_one_iff F hE hvE]
  constructor
  · intro hA
    rcases (sec12E_mem_A F).mp hA with hB | ⟨b, hb, rfl⟩
    · exact hB
    · exfalso
      refine sec121_t_not_mem_V F hE ?_
      have hbV : b ∈ secV t S L E := sec121_B_le_V F hE hb
      have hmem : (t * b) * b⁻¹ ∈ secV t S L E :=
        Subgroup.mul_mem _ hv (Subgroup.inv_mem _ hbV)
      simpa using hmem
  · intro hB
    exact Subgroup.mem_sup_left hB

end CFSG.OddStandard.SmallF3.Omega
