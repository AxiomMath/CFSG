module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5NRankAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {Ψ : SL2F3 × SL2F3 →* G}

@[expose] def nrQC (Ψ : SL2F3 × SL2F3 →* G) : Subgroup G where
  carrier := {g | ∃ a ∈ nrQ Ψ, ∃ c : G, (∀ x ∈ nrQ Ψ, x * c = c * x) ∧ g = a * c}
  one_mem' := ⟨1, one_mem _, 1, fun x _ => by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨a', ha', c', hc', rfl⟩
    refine ⟨a * a', mul_mem ha ha', c * c', fun x hx => ?_, ?_⟩
    · calc x * (c * c') = (x * c) * c' := by group
        _ = (c * x) * c' := by rw [hc x hx]
        _ = c * (x * c') := by group
        _ = c * (c' * x) := by rw [hc' x hx]
        _ = c * c' * x := by group
    · calc a * c * (a' * c') = a * (c * a') * c' := by group
        _ = a * (a' * c) * c' := by rw [← hc a' ha']
        _ = a * a' * (c * c') := by group
  inv_mem' := by
    rintro _ ⟨a, ha, c, hc, rfl⟩
    have hc' : ∀ x ∈ nrQ Ψ, x * c⁻¹ = c⁻¹ * x := fun x hx => by
      calc x * c⁻¹ = c⁻¹ * (c * x) * c⁻¹ := by group
        _ = c⁻¹ * (x * c) * c⁻¹ := by rw [hc x hx]
        _ = c⁻¹ * x := by group
    refine ⟨a⁻¹, inv_mem ha, c⁻¹, hc', ?_⟩
    calc (a * c)⁻¹ = c⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * c⁻¹ := (hc' a⁻¹ (inv_mem ha)).symm

theorem nrQ_le_nrQC : nrQ Ψ ≤ nrQC Ψ := fun a ha =>
  ⟨a, ha, 1, fun x _ => by simp, by simp⟩

theorem mem_nrQC_of_comm {c : G} (hc : ∀ x ∈ nrQ Ψ, x * c = c * x) : c ∈ nrQC Ψ :=
  ⟨1, one_mem _, c, hc, by simp⟩

variable {E : Subgroup G} (S : NrSetting Ψ E)

include S

theorem NrSetting.rel_self_of_mem {e : G} (he : e ∈ nrQC Ψ) (s : Bool × Fin 3) :
    NrRel Ψ e s s := by
  obtain ⟨a, ha, c, hc, rfl⟩ := he
  obtain ⟨p, hp, rfl⟩ := (mem_nrQ Ψ).mp ha
  have hcq : c * nrqG Ψ s * c⁻¹ = nrqG Ψ s := by
    calc c * nrqG Ψ s * c⁻¹ = (nrqG Ψ s * c) * c⁻¹ := by rw [← hc _ (nrqG_mem s)]
      _ = nrqG Ψ s := by group
  have hconj : Ψ p * c * nrqG Ψ s * (Ψ p * c)⁻¹ = Ψ p * nrqG Ψ s * (Ψ p)⁻¹ := by
    calc Ψ p * c * nrqG Ψ s * (Ψ p * c)⁻¹ = Ψ p * (c * nrqG Ψ s * c⁻¹) * (Ψ p)⁻¹ := by group
      _ = Ψ p * nrqG Ψ s * (Ψ p)⁻¹ := by rw [hcq]
  unfold NrRel
  rw [hconj]
  have hmap : Ψ (p * nrCls s * p⁻¹) = Ψ p * nrqG Ψ s * (Ψ p)⁻¹ := by
    simp only [map_mul, map_inv]
    rfl
  rcases sec5nr_inner p hp s with h | h
  · left
    rw [← hmap, S.ker.map_eq h]
    rfl
  · right
    rw [← hmap, S.ker.map_eq h, map_mul]
    rfl

theorem NrSetting.rho_eq_one_of_mem (e : ↥E) (he : (e : G) ∈ nrQC Ψ) : nrRho S e = 1 :=
  Equiv.ext fun s => S.act_eq_of_rel (S.rel_self_of_mem he s)

theorem NrSetting.mem_nrQC_of_rho_eq_one (e : ↥E) (h : nrRho S e = 1) : (e : G) ∈ nrQC Ψ := by
  classical
  have hrel : ∀ g : Fin 4, NrRel Ψ (e : G) (nrGen g) (nrGen g) := fun g => by
    have h1 : nrAct S e (nrGen g) = nrGen g := by
      rw [← nrRho_apply, h]
      rfl
    have h2 := S.rel_act e (nrGen g)
    rwa [h1] at h2
  let ε : Fin 4 → Bool := fun g =>
    decide (¬ ((e : G) * nrqG Ψ (nrGen g) * (e : G)⁻¹ = nrqG Ψ (nrGen g)))
  obtain ⟨p, hp, hpε⟩ := sec5nr_realize ε
  have hconj : ∀ g : Fin 4, (e : G) * nrqG Ψ (nrGen g) * (e : G)⁻¹ =
      Ψ p * nrqG Ψ (nrGen g) * (Ψ p)⁻¹ := fun g => by
    have h1 : Ψ p * nrqG Ψ (nrGen g) * (Ψ p)⁻¹ =
        nrqG Ψ (nrGen g) * (if ε g then nrzG Ψ else 1) := by
      have h2 := S.ker.map_eq (hpε g)
      rw [nrMap_cls_mul] at h2
      simp only [map_mul, map_inv] at h2
      exact h2
    rw [h1]
    by_cases hc : (e : G) * nrqG Ψ (nrGen g) * (e : G)⁻¹ = nrqG Ψ (nrGen g)
    · have h3 : ε g = false := by simp [ε, hc]
      rw [h3, if_neg (by simp), mul_one, hc]
    · have h3 : ε g = true := by simp [ε, hc]
      rw [h3, if_pos rfl]
      rcases hrel g with h2 | h2
      · exact absurd h2 hc
      · exact h2
  have hcg : ∀ g : Fin 4, Commute (nrqG Ψ (nrGen g)) ((Ψ p)⁻¹ * (e : G)) := fun g => by
    have h1 := hconj g
    show nrqG Ψ (nrGen g) * ((Ψ p)⁻¹ * (e : G)) = (Ψ p)⁻¹ * (e : G) * nrqG Ψ (nrGen g)
    calc nrqG Ψ (nrGen g) * ((Ψ p)⁻¹ * (e : G))
        = (Ψ p)⁻¹ * (Ψ p * nrqG Ψ (nrGen g) * (Ψ p)⁻¹) * (e : G) := by group
      _ = (Ψ p)⁻¹ * ((e : G) * nrqG Ψ (nrGen g) * (e : G)⁻¹) * (e : G) := by rw [h1]
      _ = (Ψ p)⁻¹ * (e : G) * nrqG Ψ (nrGen g) := by group
  refine ⟨Ψ p, map_mem_nrQ Ψ hp, (Ψ p)⁻¹ * (e : G), fun x hx => ?_, by group⟩
  obtain ⟨p', hp', rfl⟩ := (mem_nrQ Ψ).mp hx
  obtain ⟨a, b, c, d, hw⟩ := sec5nr_gen_word p' hp'
  have hcomm : Commute (Ψ p') ((Ψ p)⁻¹ * (e : G)) := by
    rw [hw]
    simp only [map_mul, map_pow]
    exact ((((hcg 0).pow_left _).mul_left ((hcg 1).pow_left _)).mul_left
      ((hcg 2).pow_left _)).mul_left ((hcg 3).pow_left _)
  exact hcomm

theorem NrSetting.ker_nrRho : (nrRho S).ker = (nrQC Ψ).subgroupOf E := by
  ext e
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨S.mem_nrQC_of_rho_eq_one e, S.rho_eq_one_of_mem e⟩

theorem sec5nr_ex
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ nrQC Ψ ∧ a * a ∈ nrQC Ψ) {n : ℕ}
    (hn : (nrQC Ψ).relIndex E = 2 ^ n) : n ≤ 2 := by
  have h1 : Nat.card (nrRho S).range = 2 ^ n := by
    rw [← Subgroup.index_ker, S.ker_nrRho]
    exact hn
  have hsq : ∀ y ∈ (nrRho S).range, y * y = 1 ∧ NrPres y := by
    rintro _ ⟨e, rfl⟩
    refine ⟨?_, S.pres e⟩
    rw [← map_mul]
    exact S.rho_eq_one_of_mem (e * e) (hab e e.2 e e.2).2
  have hcomm : ∀ x ∈ (nrRho S).range, ∀ y ∈ (nrRho S).range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have h2 : nrRho S (a * b * a⁻¹ * b⁻¹) = 1 :=
      S.rho_eq_one_of_mem (a * b * a⁻¹ * b⁻¹) (hab a a.2 b b.2).1
    simp only [map_mul, map_inv] at h2
    exact (commutatorElement_eq_one_iff_mul_comm (g₁ := nrRho S a) (g₂ := nrRho S b)).mp h2
  have h3 : 2 ^ n ≤ 4 := h1 ▸ sec5nr_card_le_four _ hsq hcomm
  by_contra hlt
  have h4 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.OddStandard.SmallF3.Omega
