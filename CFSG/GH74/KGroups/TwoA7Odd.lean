module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG Equiv Equiv.Perm Subgroup

section Odd

theorem pPrimeCore_eq_bot_of_rho {G : Type*} [Group G] [Finite G] {n : ℕ} (ρ : G →* Perm (Fin n))
    {z : G} (hz : orderOf z = 2) (hker : ∀ x, ρ x = 1 → x = 1 ∨ x = z)
    (B : Subgroup (Perm (Fin n))) [B.Normal] (hB : B ≤ ρ.range)
    (hBodd : ∀ N : Subgroup (Perm (Fin n)), (∀ b ∈ B, ∀ x ∈ N, b * x * b⁻¹ ∈ N) →
      ¬ 2 ∣ Nat.card N → N ⊓ B = ⊥)
    (hC : ∀ g : Perm (Fin n), (∀ b ∈ B, g * b = b * g) → g ∈ B) :
    pPrimeCore 2 G = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro M hM hcop
  have hModd : ¬ 2 ∣ Nat.card M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop
  have hinjM : ∀ x ∈ M, ρ x = 1 → x = 1 := by
    intro x hx hx1
    rcases hker x hx1 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hx
      apply hModd
      have := Subgroup.orderOf_dvd_natCard M hx
      rw [hz] at this
      exact this
  set N : Subgroup (Perm (Fin n)) := M.map ρ with hN
  have hNcard : Nat.card N = Nat.card M := by
    have hinj : Function.Injective (ρ.comp M.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : ρ (x : G) = 1 := hx
      exact Subtype.ext (hinjM x x.2 h1)
    have : N = (ρ.comp M.subtype).range := by
      ext y
      simp only [hN, Subgroup.mem_map, MonoidHom.mem_range]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, rfl⟩
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hNodd : ¬ 2 ∣ Nat.card N := by rw [hNcard]; exact hModd
  have hnorm : ∀ b ∈ B, ∀ x ∈ N, b * x * b⁻¹ ∈ N := by
    intro b hb x hx
    obtain ⟨g, hg⟩ := hB hb
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨g * m * g⁻¹, hM.conj_mem m hm g, ?_⟩
    rw [map_mul, map_mul, map_inv, hg]
  have hNB : N ⊓ B = ⊥ := hBodd N hnorm hNodd
  have hcomm : ∀ x ∈ N, ∀ b ∈ B, x * b = b * x := by
    intro x hx b hb
    have h1 : x * b * x⁻¹ * b⁻¹ ∈ N ⊓ B := by
      refine ⟨?_, ?_⟩
      · have := hnorm b hb x⁻¹ (N.inv_mem hx)
        have h2 := N.mul_mem hx this
        have h3 : x * (b * x⁻¹ * b⁻¹) = x * b * x⁻¹ * b⁻¹ := by group
        rwa [h3] at h2
      · exact B.mul_mem (Subgroup.Normal.conj_mem ‹B.Normal› b hb x) (B.inv_mem hb)
    rw [hNB, Subgroup.mem_bot] at h1
    calc x * b = x * b * x⁻¹ * b⁻¹ * b * x := by group
      _ = b * x := by rw [h1]; group
  have hNbot : N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxB : x ∈ B := hC x (fun b hb => hcomm x hx b hb)
    have : x ∈ N ⊓ B := ⟨hx, hxB⟩
    rw [hNB] at this
    exact this
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply hinjM x hx
  have : ρ x ∈ N := ⟨x, hx, rfl⟩
  rw [hNbot, Subgroup.mem_bot] at this
  exact this

end Odd

end CFSG.GH74.KGroups.TwoA7
