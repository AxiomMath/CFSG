module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHarada
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.Fin76b

theorem cent_sigma_eq {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t σ : G} {T : Subgroup G}
    (h : OuterConfig G L z t T) (hσz : σ * z = z * σ) (hσL : σ ∉ L ⊔ Subgroup.zpowers z)
    (hσ2 : σ * σ = 1) :
    Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({σ} : Set G) =
      (L ⊓ Subgroup.centralizer ({σ} : Set G)) ⊔ (Subgroup.zpowers z ⊔ Subgroup.zpowers σ) := by
  have hσK : σ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hσz
  have hLK : L ≤ Subgroup.centralizer ({z} : Set G) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.2 (h.z_comm_of_mem_A ha)
  have hzK : Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hzσ : Subgroup.zpowers z ≤ Subgroup.centralizer ({σ} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hσz.symm)
  have hσσ : Subgroup.zpowers σ ≤ Subgroup.centralizer ({σ} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hσK' : Subgroup.zpowers σ ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.2 hσK
  have hzL : Subgroup.zpowers z ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.2 h.z_cent
  apply le_antisymm
  · intro y hy
    obtain ⟨hyz, hyσ⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨a, _haK, _haM, hall⟩ :=
      Subgroup.relIndex_eq_two_iff_exists_notMem_and.1 h.index_two
    have hσa : σ * a ∈ L ⊔ Subgroup.zpowers z := by
      rcases hall σ hσK with h1 | h1
      · exact h1
      · exact absurd h1 hσL
    obtain ⟨m, hmM, c, hcσ, hmy⟩ : ∃ m ∈ L ⊔ Subgroup.zpowers z, ∃ c ∈ Subgroup.zpowers σ,
        y = m * c := by
      by_cases hyM : y ∈ L ⊔ Subgroup.zpowers z
      · exact ⟨y, hyM, 1, one_mem _, (mul_one y).symm⟩
      · have hya : y * a ∈ L ⊔ Subgroup.zpowers z := by
          rcases hall y hyz with h1 | h1
          · exact h1
          · exact absurd h1 hyM
        refine ⟨y * σ⁻¹, ?_, σ, Subgroup.mem_zpowers σ, by group⟩
        have e : y * σ⁻¹ = y * a * (σ * a)⁻¹ := by group
        rw [e]
        exact mul_mem hya (inv_mem hσa)
    have hmC : m ∈ Subgroup.centralizer ({σ} : Set G) := by
      have e : y * c⁻¹ = m := by
        rw [hmy]
        group
      rw [← e]
      exact mul_mem hyσ (inv_mem (hσσ hcσ))
    obtain ⟨a', ha', b, hb, hm_ab⟩ := exists_mul_of_mem_sup_comm' hzL hmM
    have ha'C : a' ∈ Subgroup.centralizer ({σ} : Set G) := by
      have e : m * b⁻¹ = a' := by
        rw [hm_ab]
        group
      rw [← e]
      exact mul_mem hmC (inv_mem (hzσ hb))
    have hbc : b * c ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers σ :=
      mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hcσ)
    have hx : a' ∈ L ⊓ Subgroup.centralizer ({σ} : Set G) := ⟨ha', ha'C⟩
    have ey : y = a' * (b * c) := by
      rw [hmy, hm_ab]
      group
    rw [ey]
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hbc)
  · apply sup_le
    · intro a ha
      exact ⟨hLK ha.1, ha.2⟩
    · apply sup_le
      · exact le_inf hzK hzσ
      · exact le_inf hσK' hσσ

end CFSG.EvenSporadicStandard.Fin76b
