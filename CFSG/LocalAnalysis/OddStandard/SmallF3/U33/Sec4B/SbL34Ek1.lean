module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Eh
public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

theorem card_eq_six_mul_card_centralizer {G : Type} [Group G] [Finite G] (H V : Subgroup G)
    (hVH : ∀ g ∈ H, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hV4 : Nat.card V = 4)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVs : ∀ a ∈ V, a * a = 1)
    {ρ σ : G} (hρ : ρ ∈ H) (hσ : σ ∈ H) (hρ3 : ρ * ρ * ρ = 1) (hσ2 : σ * σ = 1)
    (hρV : ∀ v ∈ V, ρ * v * ρ⁻¹ = v → v = 1) (hσV : ∃ v ∈ V, σ * v * σ⁻¹ ≠ v) :
    Nat.card H = 6 * Nat.card ↥(H ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  obtain ⟨E, hEadd, hEmod, hEfin, ψ, hfin, hkerψ⟩ :=
    exists_rep H V ⊥ (k := 2) hVH bot_le
      (by
        intro g _ v hv
        rw [Subgroup.mem_bot] at hv ⊢
        rw [hv]
        group)
      (by
        intro a ha b hb
        rw [Subgroup.mem_bot]
        rw [hVc a ha b hb]
        group)
      (by
        intro a ha
        rw [Subgroup.mem_bot]
        exact hVs a ha)
      (by
        rw [Subgroup.card_bot, hV4]
        norm_num)
  letI := hEadd
  letI := hEmod
  letI := hEfin
  have hGL : Nat.card (E ≃ₗ[ZMod 2] E) = 6 := by
    rw [CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod hfin,
      Fin.prod_univ_two]
    norm_num
  have hker_eq : ψ.ker = (H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, hkerψ g]
    constructor
    · intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨g.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
      intro a ha
      have h' := h a ha
      rw [Subgroup.mem_bot] at h'
      exact h'
    · intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h
      intro a ha
      rw [Subgroup.mem_bot]
      exact Subgroup.mem_centralizer_iff_commutator_eq_one'.1 h.2 a ha
  have hker_card : Nat.card ψ.ker = Nat.card ↥(H ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show H ⊓ Subgroup.centralizer (V : Set G) ≤ H from inf_le_left)).toEquiv
  let ρH : ↥H := ⟨ρ, hρ⟩
  let σH : ↥H := ⟨σ, hσ⟩
  obtain ⟨v, hvV, hvne⟩ := hσV
  have hv1 : v ≠ 1 := by
    intro hv
    rw [hv] at hvne
    simp at hvne
  have hne_ρ : ψ ρH ≠ 1 := by
    intro h1
    have hmem : ρ * v * ρ⁻¹ * v⁻¹ = 1 := by
      have h := (hkerψ ρH).1 h1 v hvV
      rw [Subgroup.mem_bot] at h
      simpa using h
    rw [mul_inv_eq_iff_eq_mul] at hmem
    exact hv1 (hρV v hvV (by simpa using hmem))
  have hne_σ : ψ σH ≠ 1 := by
    intro h1
    have hmem : σ * v * σ⁻¹ * v⁻¹ = 1 := by
      have h := (hkerψ σH).1 h1 v hvV
      rw [Subgroup.mem_bot] at h
      simpa using h
    rw [mul_inv_eq_iff_eq_mul] at hmem
    exact hvne (by simpa using hmem)
  have hρH3 : ρH ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change ρ ^ 3 = (1 : G)
    rw [pow_succ, pow_succ, pow_one, hρ3]
  have hσH2 : σH ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change σ ^ 2 = (1 : G)
    rw [pow_two, hσ2]
  have hordρ : orderOf (ψ ρH) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact orderOf_eq_prime (by rw [← map_pow, hρH3, map_one]) hne_ρ
  have hordσ : orderOf (ψ σH) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    exact orderOf_eq_prime (by rw [← map_pow, hσH2, map_one]) hne_σ
  have hdvd3 : 3 ∣ Nat.card ψ.range := by
    have h := Subgroup.orderOf_dvd_natCard ψ.range
      (MonoidHom.mem_range.2 ⟨ρH, rfl⟩ : ψ ρH ∈ ψ.range)
    rwa [hordρ] at h
  have hdvd2 : 2 ∣ Nat.card ψ.range := by
    have h := Subgroup.orderOf_dvd_natCard ψ.range
      (MonoidHom.mem_range.2 ⟨σH, rfl⟩ : ψ σH ∈ ψ.range)
    rwa [hordσ] at h
  have hdvd6 : 6 ∣ Nat.card ψ.range := by
    have hcop : Nat.Coprime 2 3 := by decide
    have h := hcop.mul_dvd_of_dvd_of_dvd hdvd2 hdvd3
    simpa using h
  have hdvd_range : Nat.card ψ.range ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [hGL] at h
  have hrange : Nat.card ψ.range = 6 :=
    (Nat.dvd_antisymm hdvd6 hdvd_range).symm
  have hmain := Subgroup.card_ker_mul_card_range ψ
  rw [hker_card, hrange] at hmain
  rw [← hmain]
  exact Nat.mul_comm _ _

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
