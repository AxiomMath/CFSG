module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Reg

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup

variable {K : Type*} [Group K] {Ω : Type*} [MulAction K Ω]

theorem exists_regular_normal_two_of_action [Finite K] [Finite Ω] [MulAction.IsPretransitive K Ω]
    (hΩ : Nat.card Ω = 16) (ω : Ω) {N : Subgroup K} (hN : ∀ k : K, k ∈ N ↔ ∀ α : Ω, k • α = α)
    (hN2 : IsPGroup 2 N) (hS : Nat.card (MulAction.stabilizer K ω) = 20 * Nat.card N)
    {x : K} (hx5 : x ^ 5 = 1) (hxω : x • ω = ω) (hfix : ∀ α : Ω, x • α = α → α = ω)
    (hnorm : ∀ g ∈ MulAction.stabilizer K ω, g * x * g⁻¹ ∈ zpowers x ⊔ N)
    (hcent : ∀ g ∈ MulAction.stabilizer K ω, g * x * g⁻¹ * x⁻¹ ∈ N → g ∈ zpowers x ⊔ N) :
    ∃ W : Subgroup K, W.Normal ∧ IsPGroup 2 W ∧ N ≤ W ∧ Nat.card W = 16 * Nat.card N ∧
      (∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ N) ∧ (∀ a ∈ W, a * a ∈ N) ∧
      (∀ α β : Ω, ∃ w ∈ W, w • α = β) ∧ (∀ w ∈ W, w • ω = ω → w ∈ N) ∧
      (∀ M : Subgroup K, M.Normal → IsPGroup 2 M → M ≤ W) := by
  classical
  let π : K →* Equiv.Perm Ω := MulAction.toPermHom K Ω
  have hπ : ∀ (k : K) (α : Ω), π k α = k • α := fun k α => rfl
  have hker : π.ker = N := by
    ext k
    rw [MonoidHom.mem_ker, hN, Equiv.ext_iff]
    exact forall_congr' fun α => by simp [hπ]
  haveI hNn : N.Normal := hker ▸ π.normal_ker
  let G : Subgroup (Equiv.Perm Ω) := π.range
  haveI : MulAction.IsPretransitive G Ω := ⟨fun α β => by
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K α β
    exact ⟨⟨π k, k, rfl⟩, hk⟩⟩
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hKcard : Nat.card N * Nat.card G = Nat.card K := by
    have := Subgroup.card_ker_mul_card_range π
    rwa [hker] at this
  have hKos : Nat.card (MulAction.stabilizer K ω) * Nat.card Ω = Nat.card K := by
    rw [← MulAction.index_stabilizer_of_transitive K ω]
    exact Subgroup.card_mul_index _
  have hGcard : Nat.card G = 320 := by
    rw [hΩ, hS] at hKos
    have h2 : Nat.card N * Nat.card G = Nat.card N * 320 := by
      rw [hKcard, ← hKos]; ring
    exact Nat.eq_of_mul_eq_mul_left hNpos h2
  have hSG : Nat.card (MulAction.stabilizer G ω) = 20 := by
    have h1 : Nat.card (MulAction.stabilizer G ω) * Nat.card Ω = Nat.card G := by
      rw [← MulAction.index_stabilizer_of_transitive G ω]
      exact Subgroup.card_mul_index _
    rw [hΩ, hGcard] at h1
    omega
  let xG : G := ⟨π x, x, rfl⟩
  have hxG5 : xG ^ 5 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    show (π x) ^ 5 = 1
    rw [← map_pow, hx5, map_one])
  have hxGω : xG • ω = ω := hxω
  have hfixG : ∀ α : Ω, xG • α = α → α = ω := fun α h => hfix α h
  have hmem_stab : ∀ (g : G) (k : K), π k = (g : Equiv.Perm Ω) → g ∈ MulAction.stabilizer G ω →
      k ∈ MulAction.stabilizer K ω := by
    intro g k hk hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    have h1 : (g : Equiv.Perm Ω) ω = ω := hg
    rw [← hk] at h1
    exact h1
  have hzp : ∀ k : K, π k ∈ zpowers (π x) → (⟨π k, k, rfl⟩ : G) ∈ zpowers xG := by
    intro k hk
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact Subgroup.mem_zpowers_iff.2 ⟨i, Subtype.ext (by
      rw [Subgroup.coe_zpow]
      exact hi)⟩
  have hmapN : N.map π = ⊥ := (Subgroup.map_eq_bot_iff _).2 hker.ge
  have hnormG : ∀ g ∈ MulAction.stabilizer G ω, g * xG * g⁻¹ ∈ zpowers xG := by
    intro g hg
    obtain ⟨k, hk⟩ := g.2
    have h1 := hnorm k (hmem_stab g k hk hg)
    have h2 : π (k * x * k⁻¹) ∈ zpowers (π x) := by
      have := Subgroup.mem_map_of_mem π h1
      rwa [Subgroup.map_sup, MonoidHom.map_zpowers, hmapN, sup_bot_eq] at this
    have h3 : g * xG * g⁻¹ = ⟨π (k * x * k⁻¹), _, rfl⟩ := by
      apply Subtype.ext
      show (g : Equiv.Perm Ω) * π x * (g : Equiv.Perm Ω)⁻¹ = π (k * x * k⁻¹)
      rw [← hk, map_mul, map_mul, map_inv]
    rw [h3]
    exact hzp _ h2
  have hcentG : ∀ g ∈ MulAction.stabilizer G ω, g * xG = xG * g → g ∈ zpowers xG := by
    intro g hg hc
    obtain ⟨k, hk⟩ := g.2
    have hc' : π k * π x = π x * π k := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [← hk] at this
      exact this
    have hcomm : k * x * k⁻¹ * x⁻¹ ∈ N := by
      rw [← hker, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hc']
      group
    have h1 := hcent k (hmem_stab g k hk hg) hcomm
    have h2 : π k ∈ zpowers (π x) := by
      have := Subgroup.mem_map_of_mem π h1
      rwa [Subgroup.map_sup, MonoidHom.map_zpowers, hmapN, sup_bot_eq] at this
    have h3 : g = ⟨π k, k, rfl⟩ := Subtype.ext hk.symm
    rw [h3]
    exact hzp k h2
  obtain ⟨R, hRn, hR2, hRc, hRcomm, hRsq, hRtr, hRreg, hRmax⟩ :=
    exists_regular_normal_two (G := G) (Ω := Ω) hΩ ω hSG hxG5 hxGω hfixG hnormG hcentG
  let ρ : K →* G := π.rangeRestrict
  have hρ : ∀ k : K, ((ρ k : G) : Equiv.Perm Ω) = π k := fun k => rfl
  have hρsurj : Function.Surjective ρ := MonoidHom.rangeRestrict_surjective π
  have hρker : ρ.ker = N := by rw [MonoidHom.ker_rangeRestrict, hker]
  have hρN : ∀ n ∈ N, ρ n = 1 := fun n hn => MonoidHom.mem_ker.1 (hρker ▸ hn)
  have hρNiff : ∀ k : K, ρ k = 1 ↔ k ∈ N := fun k => by
    rw [← hρker, MonoidHom.mem_ker]
  refine ⟨R.comap ρ, hRn.comap ρ, hR2.comap_of_ker_isPGroup ρ (hρker ▸ hN2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [Subgroup.mem_comap, hρN n hn]
    exact one_mem R
  · have h1 := Subgroup.index_comap_of_surjective R hρsurj
    have h2 := Subgroup.card_mul_index (R.comap ρ)
    have h3 := Subgroup.card_mul_index R
    rw [h1] at h2
    rw [hRc, hGcard] at h3
    have h4 : Nat.card N * Nat.card G = Nat.card K := hKcard
    rw [hGcard] at h4
    have h5 : R.index = 20 := by omega
    rw [h5] at h2
    omega
  · intro a ha b hb
    have hc := hRcomm _ ha _ hb
    rw [← hρNiff]
    simp only [map_mul, map_inv]
    rw [hc]
    group
  · intro a ha
    have hc := hRsq _ ha
    rw [← hρNiff]
    simp only [map_mul]
    exact hc
  · intro α β
    obtain ⟨r, hrR, hr⟩ := hRtr α β
    obtain ⟨w, rfl⟩ := hρsurj r
    exact ⟨w, hrR, hr⟩
  · intro w hw hwω
    rw [← hρNiff]
    exact hRreg _ hw hwω
  · intro M hM hM2
    have hMn : (M.map ρ).Normal := hM.map ρ hρsurj
    have := hRmax (M.map ρ) hMn (hM2.map ρ)
    exact Subgroup.map_le_iff_le_comap.1 this

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
