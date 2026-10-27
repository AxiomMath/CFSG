module

public import CFSG.ClassicalInvolution.RouteD.TypeUModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Steinberg Module Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem blockEmb_four_comp_blockEmb2 {N : ℕ} (hN : 4 ≤ N) (a : Fin 3) :
    (blockEmb K p f N 4 0 (by omega)).comp (blockEmb2 K p f 3 a) =
      blockEmb K p f N 2 a (by omega) := by
  have h := blockEmb_comp (K := K) (p := p) (f := f) (by omega : 0 + 4 ≤ N)
    (by omega : (a : ℕ) + 2 ≤ 4)
  simp only [Nat.zero_add] at h
  exact h

theorem exists_blocks_of_chain3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {N : ℕ} (hN : 4 ≤ N)
    {R₀ R₁ R₂ : Subgroup (Su K p f N)} {i₀ i₁ i₂ : Su K p f N}
    (h₀ : IsLongRootSU2 K p f (by omega : 2 ≤ N) R₀ i₀)
    (h₁ : IsLongRootSU2 K p f (by omega : 2 ≤ N) R₁ i₁)
    (h₂ : IsLongRootSU2 K p f (by omega : 2 ≤ N) R₂ i₂)
    (c₀₁ : Commute i₀ i₁) (c₁₂ : Commute i₁ i₂) (c₀₂ : Commute i₀ i₂)
    (n₀₁ : i₀ ≠ i₁) (n₁₂ : i₁ ≠ i₂) (n₀₂ : i₀ ≠ i₂)
    (r₀₂ : Commutes R₀ R₂) (a₀₁ : ¬ Commutes R₀ R₁) (a₁₂ : ¬ Commutes R₁ R₂) :
    ∃ ι : Su K p f 4 →* Su K p f N, Function.Injective ι ∧
      (blockEmb2 K p f 3 0).range.map ι = R₀ ∧ (blockEmb2 K p f 3 1).range.map ι = R₁ ∧
      (blockEmb2 K p f 3 2).range.map ι = R₂ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hn3 : 3 ≤ N := by omega
  let u : ℕ → Su K p f N := fun a => if a = 0 then i₀ else if a = 1 then i₁ else i₂
  have hu0 : u 0 = i₀ := by simp [u]
  have hu1 : u 1 = i₁ := by simp [u]
  have hu2 : u 2 = i₂ := by simp [u]
  have hc : ∀ a < 3, ∀ b < 3, Commute (u a) (u b) := by
    intro a ha b hb
    interval_cases a <;> interval_cases b <;> simp only [hu0, hu1, hu2] <;>
      first | exact Commute.refl _ | exact c₀₁ | exact c₀₁.symm | exact c₁₂ | exact c₁₂.symm |
        exact c₀₂ | exact c₀₂.symm
  have hchain : IsInvChain (fun a => suMat (u a)) 3 :=
    { sq := fun a ha => by
        interval_cases a
        · simp only [hu0]; exact h₀.coe_mul_self
        · simp only [hu1]; exact h₁.coe_mul_self
        · simp only [hu2]; exact h₂.coe_mul_self
      comm := fun a ha b hb => typeU_suMat_commute (hc a ha b hb)
      dim := fun a ha => by
        interval_cases a
        · show finrank K (eigSpace (suMat (u 0)) (-1)) = 2
          rw [hu0]; exact h₀.finrank_minusSpaceSU h2
        · show finrank K (eigSpace (suMat (u 1)) (-1)) = 2
          rw [hu1]; exact h₁.finrank_minusSpaceSU h2
        · show finrank K (eigSpace (suMat (u 2)) (-1)) = 2
          rw [hu2]; exact h₂.finrank_minusSpaceSU h2
      far := fun a ha b hb hab => by
        obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 2 := by omega
        simp only [hu0, hu2]
        exact (spaces_of_commutes_su hK hp hn3 h₀ h₂ n₀₂ r₀₂).2.2
      adj := fun a ha => by
        have ha' : a < 2 := by omega
        interval_cases a
        · simp only [hu0, hu1]
          exact inf_ne_bot_of_not_commutes_su h2 h₀ h₁ c₀₁ a₀₁
        · simp only [hu1, hu2]
          exact inf_ne_bot_of_not_commutes_su h2 h₁ h₂ c₁₂ a₁₂
      ne := fun a ha h => by
        have ha' : a < 2 := by omega
        interval_cases a
        · simp only [hu0, hu1] at h
          exact n₀₁ (suMat_injective h)
        · simp only [hu1, hu2] at h
          exact n₁₂ (suMat_injective h) }
  obtain ⟨-, P, hPI, -⟩ := hchain.exists_su_frame hσ h2 (by norm_num : 2 ≤ 3)
  have hR : ∀ {R : Subgroup (Su K p f N)} {i : Su K p f N},
      IsLongRootSU2 K p f (by omega : 2 ≤ N) R i → ∀ (a : ℕ) (ha : a + 2 ≤ N),
        suMat i * suMat P = suMat P * negBlock K N a →
        R = (blockEmb K p f N 2 a ha).range.map (MulAut.conj P).toMonoidHom := by
    intro R i hRi a ha h
    rw [hRi.eq_longRootGroupSU h2, longRootGroupSU_eq_map_conj_of_mul_eq P h,
      range_blockEmb_eq_longRootGroupSU h2 ha]
  have e₀ := hR h₀ 0 (by omega) (by simpa only [hu0] using hPI 0 (by norm_num))
  have e₁ := hR h₁ 1 (by omega) (by simpa only [hu1] using hPI 1 (by norm_num))
  have e₂ := hR h₂ 2 (by omega) (by simpa only [hu2] using hPI 2 (by norm_num))
  have hblk : ∀ a : Fin 3, (blockEmb2 K p f 3 a).range.map
      ((MulAut.conj P).toMonoidHom.comp (blockEmb K p f N 4 0 (by omega))) =
      (blockEmb K p f N 2 a (by omega)).range.map (MulAut.conj P).toMonoidHom := by
    intro a
    rw [← Subgroup.map_map, ← MonoidHom.range_comp, blockEmb_four_comp_blockEmb2 hN a]
  refine ⟨(MulAut.conj P).toMonoidHom.comp (blockEmb K p f N 4 0 (by omega)),
    (MulAut.conj P).injective.comp (blockEmb_injective (by omega)), ?_, ?_, ?_⟩
  · rw [e₀]
    exact hblk 0
  · rw [e₁]
    exact hblk 1
  · rw [e₂]
    exact hblk 2

end CFSG.ClassicalInvolution.Q3.Q3W
