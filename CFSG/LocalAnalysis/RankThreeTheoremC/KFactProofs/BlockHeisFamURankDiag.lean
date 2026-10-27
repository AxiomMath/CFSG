module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamURankBasic
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

theorem heisU_false_of_torus {L K : Type} [Group L] [Field K] [Finite K] (hrk : OddRankLeThree L)
    {n q r : ℕ} (hn : 5 ≤ n) (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ q + 1) (ρ : StatedSU n q K →* L)
    (hρ : ((6 ≤ n ∨ ¬ r ∣ n) ∧ ∀ g, ρ g = 1 → (g : GL (Fin n) K) ∈ StatedScalars (Fin n) K) ∨
      Function.Injective ρ) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hrK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    refine hrq.trans ⟨q - 1, ?_⟩
    obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [hm]
    apply Nat.sub_eq_of_eq_add
    simp only [Nat.add_sub_cancel]
    ring
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r hrK
  have hζq : ζ ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hrq)
  obtain ⟨ψ, hψ, hψZ⟩ := heisU_exists_torus hn (by omega) hr hζ hζq
  obtain ⟨hexp, hcard⟩ := heisU_torus_data (K := K) hζ
  have hinj : Function.Injective (ρ.comp ψ) := by
    rcases hρ with ⟨hnr, hker⟩ | hρi
    · rw [injective_iff_map_eq_one]
      intro c hc
      exact hψZ hnr c (hker _ hc)
    · exact hρi.comp hψ
  exact heisU_false_of_injective hrk hr hr2 (fun x y => mul_comm x y) hexp hcard.ge (ρ.comp ψ)
    hinj

theorem heisU_center_eq_bot_of_not_injective {G L : Type*} [Group G] [Group L] (D : Subgroup G)
    (hD : (Nat.card D).Prime) (ρ : G →* L) (hρ : Function.Surjective ρ)
    (hZ : ∀ g, ρ g ∈ Subgroup.center L ↔ g ∈ D) (hinj : ¬ Function.Injective ρ) :
    Subgroup.center L = ⊥ := by
  haveI : Fact (Nat.card D).Prime := ⟨hD⟩
  rw [injective_iff_map_eq_one] at hinj
  push Not at hinj
  obtain ⟨g, hg1, hg⟩ := hinj
  have hgD : g ∈ D := (hZ g).1 (by rw [hg1]; exact Subgroup.one_mem _)
  have hgen : Subgroup.zpowers (⟨g, hgD⟩ : D) = ⊤ :=
    zpowers_eq_top_of_prime_card rfl (fun h => hg (congrArg Subtype.val h))
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := hρ x
  have hhD : h ∈ D := (hZ h).1 hx
  have hmem : (⟨h, hhD⟩ : D) ∈ Subgroup.zpowers (⟨g, hgD⟩ : D) := hgen ▸ Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk' : g ^ k = h := congrArg Subtype.val hk
  rw [Subgroup.mem_bot, ← hk', map_zpow, hg1, one_zpow]

theorem heisU_exception {L K : Type} [Group L] [Field K] [Finite K] (hrk : OddRankLeThree L)
    {n f p : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 3 ≤ n) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hdiv : p ∣ Nat.gcd n (2 ^ f + 1)) (ρ : StatedSU n (2 ^ f) K →* L)
    (hρ : Function.Surjective ρ)
    (hZ : ∀ g, ρ g ∈ Subgroup.center L ↔ (g : GL (Fin n) K) ∈ StatedScalars (Fin n) K) :
    p = 5 ∧ n = 5 ∧ f = 2 ∧ Subgroup.center L = ⊥ := by
  have hpn : p ∣ n := hdiv.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ 2 ^ f + 1 := hdiv.trans (Nat.gcd_dvd_right _ _)
  have hnp : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hker : ∀ g, ρ g = 1 → (g : GL (Fin n) K) ∈ StatedScalars (Fin n) K := fun g hg =>
    (hZ g).1 (by rw [hg]; exact Subgroup.one_mem _)
  by_cases hn6 : 6 ≤ n
  · exact (heisU_false_of_torus hrk (by omega) hq2 hK hp (by omega) hpq ρ
      (Or.inl ⟨Or.inl hn6, hker⟩)).elim
  have hn5 : n = 5 := by omega
  subst hn5
  have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpn
  subst hp5'
  by_cases hf2 : f = 2
  · subst hf2
    refine ⟨rfl, rfl, rfl, ?_⟩
    have hDcard : Nat.card ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K)) = 5 := by
      rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num)).2.2]
      norm_num
    refine heisU_center_eq_bot_of_not_injective _ (by rw [hDcard]; exact Nat.prime_five) ρ hρ
      (fun g => (hZ g).trans Subgroup.mem_subgroupOf.symm) ?_
    intro hinj
    exact heisU_false_of_torus hrk (le_refl 5) hq2 hK Nat.prime_five (by norm_num) hpq ρ
      (Or.inr hinj)
  · obtain ⟨r, hr, hr2, hr5, hrq⟩ := heisU_exists_prime_dvd hpq hf2
    exact (heisU_false_of_torus hrk (le_refl 5) hq2 hK hr hr2 hrq ρ
      (Or.inl ⟨Or.inr (fun h => hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 h)),
        hker⟩)).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
