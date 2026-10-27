module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119H
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119D
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119E

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G} {α σ : G}

theorem lemma119_gen (h : OuterS8Hyp G L z t T E Q x B β S) (c : OI13Ctx L z t T E B β S α σ)
    (hZQ : ∀ q : G, q ∈ c.Qs → q * q = 1 → ¬ ∃ g : G, q = g * z * g⁻¹)
    (hEA : ∀ A : Subgroup (MulAut ↥E), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 16)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    {y : G} (hy : y ∈ c.Nc) (hyN : y ∉ c.N1) (hy2 : y * y = 1) :
    (∃ g : G, g * z * g⁻¹ = y) → ∃ g ∈ c.Nc, g * z * g⁻¹ = y := by
  classical
  rintro ⟨g, hg⟩
  have hoy : OYFacts c y := by
    rcases c.Nc_perm hy with ⟨h1, -, -⟩ | ⟨h1, h2, h3⟩
    · exact absurd (c.mem_N1.2 ⟨hy, h1⟩) hyN
    · exact
        { sq := hy2
          conjT := c.Nc_t hy
          conjA := h1
          conjW1 := fun w hw => h2 w hw
          conjW2 := fun w hw => h3 w hw
          notQ := fun hq => hyN (c.Qs_le_N1 hq) }
  obtain ⟨g₁, hg₁, hE₁⟩ := exists_g1 h c hZQ hoy hg
  obtain ⟨g₂, hg₂, hEq, hSeq, hZeq⟩ := exists_g2 h c hZQ hoy hg₁ hE₁
  have hmap : conjSubMap g₂ (S ⊔ E) = conjSubMap g₂ S ⊔ conjSubMap g₂ E := Subgroup.map_sup S E _
  rw [hSeq, hEq] at hmap
  have hSE : ∀ n : G, n ∈ S ⊔ E ↔ g₂ * n * g₂⁻¹ ∈ Y0 y α ⊔ c.E0 hoy := by
    intro n
    have h1 : g₂ * n * g₂⁻¹ ∈ conjSubMap g₂ (S ⊔ E) ↔ n ∈ S ⊔ E := by
      rw [mem_conjSubMap]
      have e : g₂⁻¹ * (g₂ * n * g₂⁻¹) * g₂ = n := by group
      rw [e]
    rw [← h1, hmap]
  have hQ₁mem : ∀ v : G, v ∈ conjSubMap g₂⁻¹ c.Qs ↔ g₂ * v * g₂⁻¹ ∈ c.Qs := fun v => by
    rw [mem_conjSubMap, inv_inv]
  have hQ₁M : conjSubMap g₂⁻¹ c.Qs ≤ normalizer ((S ⊔ E : Subgroup G) : Set G) := by
    intro v hv
    have hq := (hQ₁mem v).1 hv
    rw [mem_normalizer_iff]
    intro n
    rw [hSE n, hSE (v * n * v⁻¹)]
    have hnorm := Qs_normalizes_U_iff c hoy hq (g₂ * n * g₂⁻¹)
    have e : g₂ * v * g₂⁻¹ * (g₂ * n * g₂⁻¹) * (g₂ * v * g₂⁻¹)⁻¹ =
        g₂ * (v * n * v⁻¹) * g₂⁻¹ := by group
    rw [e] at hnorm
    exact hnorm
  have hZiff : ∀ v : G, g₂ * v * g₂⁻¹ ∈ c.Zs ↔ v ∈ c.Zs := by
    intro v
    have h2 : g₂ * v * g₂⁻¹ ∈ conjSubMap g₂ c.Zs ↔ g₂ * v * g₂⁻¹ ∈ c.Zs := by rw [hZeq]
    rw [← h2, mem_conjSubMap]
    have e : g₂⁻¹ * (g₂ * v * g₂⁻¹) * g₂ = v := by group
    rw [e]
  have hcentQs : ∀ a ∈ c.Qs, (∀ q' ∈ c.Qs, a * q' = q' * a) → a ∈ c.Zs := fun a ha hc =>
    c.h.mem_Zg_of_cmt_t c.hα c.hF c.hM c.hp ha
      (fun q' hq' => Or.inl (by rw [hc q' hq']; group))
  have hZQ₁ : ∀ v : G, (v ∈ conjSubMap g₂⁻¹ c.Qs ∧ ∀ q ∈ conjSubMap g₂⁻¹ c.Qs, v * q = q * v) ↔
      v ∈ c.Zs := by
    intro v
    constructor
    · rintro ⟨hv, hc⟩
      have hvQ := (hQ₁mem v).1 hv
      have hcen : ∀ q' ∈ c.Qs, (g₂ * v * g₂⁻¹) * q' = q' * (g₂ * v * g₂⁻¹) := by
        intro q' hq'
        have hq1 : g₂⁻¹ * q' * g₂ ∈ conjSubMap g₂⁻¹ c.Qs := (hQ₁mem _).2 (by
          have e : g₂ * (g₂⁻¹ * q' * g₂) * g₂⁻¹ = q' := by group
          rw [e]
          exact hq')
        have hcv := hc _ hq1
        calc g₂ * v * g₂⁻¹ * q' = g₂ * (v * (g₂⁻¹ * q' * g₂)) * g₂⁻¹ := by group
          _ = g₂ * ((g₂⁻¹ * q' * g₂) * v) * g₂⁻¹ := by rw [hcv]
          _ = q' * (g₂ * v * g₂⁻¹) := by group
      exact (hZiff v).1 (hcentQs _ hvQ hcen)
    · intro hv
      have hvZ : g₂ * v * g₂⁻¹ ∈ c.Zs := (hZiff v).2 hv
      have hvQ : g₂ * v * g₂⁻¹ ∈ c.Qs := c.Zs_le_Qs hvZ
      refine ⟨(hQ₁mem v).2 hvQ, fun q hq => ?_⟩
      have hqQ := (hQ₁mem q).1 hq
      have hcomm := c.Zs_comm_Qs hvZ hqQ
      calc v * q = g₂⁻¹ * ((g₂ * v * g₂⁻¹) * (g₂ * q * g₂⁻¹)) * g₂ := by group
        _ = g₂⁻¹ * ((g₂ * q * g₂⁻¹) * (g₂ * v * g₂⁻¹)) * g₂ := by rw [hcomm]
        _ = q * v := by group
  have hQ₁eq : conjSubMap g₂⁻¹ c.Qs = c.Qs :=
    rigid c hEA hπ (conjSubMap g₂⁻¹ c.Qs) hQ₁M (conjIso g₂⁻¹ c.Qs).symm hZQ₁
  have hNc : g₂ ∈ c.Nc := by
    rw [mem_Nc]
    intro q
    have h1 : q ∈ conjSubMap g₂⁻¹ c.Qs ↔ q ∈ c.Qs := by rw [hQ₁eq]
    exact h1.symm.trans (hQ₁mem q)
  exact ⟨g₂, hNc, hg₂⟩

theorem lemma119_of (h : OuterS8Hyp G L z t T E Q x B β S) (c : OI13Ctx L z t T E B β S α σ)
    (hZQ : ∀ q : G, q ∈ c.Qs → q * q = 1 → ¬ ∃ g : G, q = g * z * g⁻¹)
    (hEA : ∀ A : Subgroup (MulAut ↥E), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 16)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π) :
    (∃ g : G, g * z * g⁻¹ = z * σ) → ∃ g ∈ c.Nc, g * z * g⁻¹ = z * σ := by
  have hzσ : z * σ ∈ c.Nc := mul_mem c.z_mem_Nc (c.N1_le_Nc c.sigma_mem_N1)
  have hgz : z * σ * z ∈ c.N1 := by
    have e : z * σ * z = σ := by
      calc z * σ * z = z * (σ * z) := by group
        _ = z * (z * σ) := by rw [c.hσ.comm_z]
        _ = (z * z) * σ := by group
        _ = σ := by rw [c.h.z_sq, one_mul]
    rw [e]
    exact c.sigma_mem_N1
  have hyN : z * σ ∉ c.N1 := by
    intro hN
    rcases c.Nc_xor hzσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 hN
    · exact h2 hgz
  have hy2 : z * σ * (z * σ) = 1 := by
    calc z * σ * (z * σ) = z * (σ * z) * σ := by group
      _ = z * (z * σ) * σ := by rw [c.hσ.comm_z]
      _ = (z * z) * (σ * σ) := by group
      _ = 1 := by rw [c.h.z_sq, c.hσ.sq, mul_one]
  exact lemma119_gen h c hZQ hEA hπ hzσ hyN hy2

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
