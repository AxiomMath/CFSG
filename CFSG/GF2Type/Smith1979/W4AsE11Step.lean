module

public import CFSG.LargeExtraspecial.S111BO2
public import CFSG.LargeExtraspecial.S111TEightB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {A : Subgroup G} {g : G} {h k : G}
  {m : S.M}

theorem false_of_commute_w4 (P : S11.Pair111 S g A h k ((m : G) * k)) (hw : S.width = 4)
    {σ τ : S.O} (hσ : σ ∈ S.Lbar k) (hσ1 : σ ≠ 1) (hτ : τ ∈ S.Lbar ((m : G) * k))
    (hτ1 : τ ≠ 1) (hc : σ * τ = τ * σ) : False := by
  have hE : S11.Ebar S k ((m : G) * k) ≠ ⊥ := fun h0 => hσ1 (by
    have hmem := (P.mem_Ebar_of_commute hσ hσ1 hτ hτ1 hc).1
    rw [h0] at hmem
    exact Subgroup.mem_bot.mp hmem)
  have h2 := P.card_Lbar_le_mul hE
  have h8 : Nat.card (S.Lbar k) = 8 := by
    rw [P.hy.cons.card_Lbar, hw]
    norm_num
  obtain ⟨x, hx, hxE⟩ := P.exists_not_mem_Ebar
  have hdvd : Nat.card (S11.Ebar S k ((m : G) * k)) ∣ 8 := by
    rw [← h8]
    exact Subgroup.card_dvd_of_le (inf_le_left : S11.Ebar S k ((m : G) * k) ≤ S.Lbar k)
  have hlt : Nat.card (S11.Ebar S k ((m : G) * k)) < 8 := by
    rw [← h8]
    refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (h8 ▸ hdvd)) fun heq => hxE ?_
    have := Subgroup.eq_of_le_of_card_ge (inf_le_left : S11.Ebar S k ((m : G) * k) ≤ S.Lbar k)
      (le_of_eq heq.symm)
    exact (SetLike.ext_iff.mp this x).mpr hx
  have h4 : Nat.card (S11.Ebar S k ((m : G) * k)) = 4 := by
    have hpos : 0 < Nat.card (S11.Ebar S k ((m : G) * k)) := Nat.card_pos
    rw [h8] at h2
    interval_cases hc' : Nat.card (S11.Ebar S k ((m : G) * k)) <;> simp_all
  exact P.false_of_index_two hE (by rw [h8, h4])

theorem noCommuting111_w4 :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (A : Subgroup G),
      S11.Cfg111 S g A → S.width = 4 → ∀ h : G, h ∈ S.M →
        A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z →
        ∀ k j : G, k * S.z * k⁻¹ ∈ A → k * S.z * k⁻¹ ≠ S.z →
        j * S.z * j⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom → j * S.z * j⁻¹ ≠ S.z →
        ∀ σ ∈ S.Lbar k, ∀ τ ∈ S.Lbar j, σ ≠ 1 → τ ≠ 1 → σ * τ ≠ τ * σ := by
  intro G _ _ _ S g A C hw h hh hA k j hk hkz hj hjz σ hσ τ hτ hσ1 hτ1 hc
  have P : S11.Pair111 S g A h k j := ⟨C, hh, hA, hk, hkz, hj, hjz⟩
  obtain ⟨m, hm⟩ := P.exists_conj
  have P' : S11.Pair111 S g A h k ((m : G) * k) :=
    ⟨C, hh, hA, hk, hkz, hm ▸ hj, hm ▸ hjz⟩
  have hτ' : τ ∈ S.Lbar ((m : G) * k) := by rwa [Lbar_eq_of_conj_eq S hm]
  exact false_of_commute_w4 P' hw hσ hσ1 hτ' hτ1 hc

end CFSG.GF2Type.Smith1979.W4As
