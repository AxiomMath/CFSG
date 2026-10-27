module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FChiConst
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FKone
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Wreath

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private lemma sec4F_chi0_of_eq_pt (h : Sec4FSetup t L S z A B φ)
    (χ₀ : ↥(normalizer (A : Set G)) →* ℤˣ)
    (ht : ∀ ht' : t ∈ normalizer (A : Set G), χ₀ ⟨t, ht'⟩ = -1)
    {y : G} (hyN : y ∈ normalizer (A : Set G)) {p : Option (Fin 7)}
    (hp : y = sec4MPt t φ p) : χ₀ ⟨y, hyN⟩ = -1 := by
  have hpN : sec4MPt t φ p ∈ normalizer (A : Set G) := hp ▸ hyN
  have hsub : (⟨y, hyN⟩ : ↥(normalizer (A : Set G))) = ⟨sec4MPt t φ p, hpN⟩ := by
    apply Subtype.ext
    exact hp
  rw [hsub]
  exact h.chi0_pt χ₀ ht p hpN

private lemma sec4F_actHom_of_eq_pt (h : Sec4FSetup t L S z A B φ)
    {y : G} (hyN : y ∈ normalizer (A : Set G)) {p : Option (Fin 7)}
    (hp : y = sec4MPt t φ p) : h.actHom ⟨y, hyN⟩ = 1 := by
  have hreal : Sec4MRealizes t φ y 1 := by
    rw [hp]
    exact h.realizes_of_mem_A (sec4MPt_mem_A h.data p)
  exact (h.eq_actHom hyN hreal).symm

theorem Sec4FSetup.chi_exists (h : Sec4FSetup t L S z A B φ) (hsplit : Asc82Split47) :
    ∃ χ : ↥(normalizer (A : Set G)) →* ℤˣ,
      ∀ (y : G) (hy : y ∈ normalizer (A : Set G)), (∃ g : G, y = g⁻¹ * t * g) →
        χ ⟨y, hy⟩ = -1 := by
  classical
  obtain ⟨M₀, hM₀le, hidx, htM₀⟩ :=
    hsplit G t L S z h.ctx h.not_tz A h.data.isMax
  have hidx2 : (M₀.subgroupOf (normalizer (A : Set G))).index = 2 := hidx
  obtain ⟨χ₀, hχ₀⟩ :=
    CFSG.EvenSporadicStandard.exists_hom_of_index_two (M₀.subgroupOf (normalizer (A : Set G)))
      hidx2
  have ht : ∀ ht' : t ∈ normalizer (A : Set G), χ₀ ⟨t, ht'⟩ = -1 := by
    intro ht'
    have hnotK : (⟨t, ht'⟩ : ↥(normalizer (A : Set G))) ∉
        M₀.subgroupOf (normalizer (A : Set G)) := by
      rw [Subgroup.mem_subgroupOf]
      exact htM₀
    have hne : χ₀ ⟨t, ht'⟩ ≠ 1 := fun h1 => hnotK ((hχ₀ _).mp h1)
    rcases Int.units_eq_one_or (χ₀ ⟨t, ht'⟩) with h1 | h1
    · exact absurd h1 hne
    · exact h1
  by_cases hB : ∃ y₀ : G, y₀ ∈ normalizer (A : Set G) ∧
      (∃ g : G, y₀ = g⁻¹ * t * g) ∧
        ∃ a b : Option (Fin 7), a ≠ b ∧ Sec4MRealizes t φ y₀ (Equiv.swap a b)
  · obtain ⟨y₀, hy₀N, hy₀, a₀, b₀, hab₀, hσ₀⟩ := hB
    by_cases hε1 : χ₀ ⟨y₀, hy₀N⟩ = 1
    · let sgn : ↥(normalizer (A : Set G)) →* ℤˣ :=
        (Equiv.Perm.sign : Equiv.Perm (Option (Fin 7)) →* ℤˣ).comp h.actHom
      refine ⟨χ₀ * sgn, ?_⟩
      intro y hyN hy
      rcases h.kcases hy hyN with hpt | hsw
      · obtain ⟨p, hp⟩ := hpt
        have hchi0 : χ₀ ⟨y, hyN⟩ = -1 := sec4F_chi0_of_eq_pt h χ₀ ht hyN hp
        have hact : h.actHom ⟨y, hyN⟩ = 1 := sec4F_actHom_of_eq_pt h hyN hp
        have hsign : sgn ⟨y, hyN⟩ = 1 := by
          simp only [sgn, MonoidHom.comp_apply]
          rw [hact, Equiv.Perm.sign_one]
        rw [MonoidHom.mul_apply, hchi0, hsign, mul_one]
      · obtain ⟨a, b, hab, hσ⟩ := hsw
        have hχ0eq : χ₀ ⟨y, hyN⟩ = χ₀ ⟨y₀, hy₀N⟩ :=
          h.chi0_swap χ₀ ht hy hy₀ hyN hy₀N hab hab₀ hσ hσ₀
        have hsign : sgn ⟨y, hyN⟩ = -1 := by
          simp only [sgn, MonoidHom.comp_apply]
          rw [← h.eq_actHom hyN hσ, Equiv.Perm.sign_swap hab]
        rw [MonoidHom.mul_apply, hχ0eq, hε1, hsign, one_mul]
    · refine ⟨χ₀, ?_⟩
      intro y hyN hy
      rcases h.kcases hy hyN with hpt | hsw
      · obtain ⟨p, hp⟩ := hpt
        exact sec4F_chi0_of_eq_pt h χ₀ ht hyN hp
      · obtain ⟨a, b, hab, hσ⟩ := hsw
        have hχ0eq : χ₀ ⟨y, hyN⟩ = χ₀ ⟨y₀, hy₀N⟩ :=
          h.chi0_swap χ₀ ht hy hy₀ hyN hy₀N hab hab₀ hσ hσ₀
        rcases Int.units_eq_one_or (χ₀ ⟨y₀, hy₀N⟩) with h1 | h1
        · exact absurd h1 hε1
        · rw [hχ0eq, h1]
  · refine ⟨χ₀, ?_⟩
    intro y hyN hy
    rcases h.kcases hy hyN with hpt | hsw
    · obtain ⟨p, hp⟩ := hpt
      exact sec4F_chi0_of_eq_pt h χ₀ ht hyN hp
    · exfalso
      obtain ⟨a, b, hab, hσ⟩ := hsw
      exact hB ⟨y, hyN, hy, a, b, hab, hσ⟩

end CFSG.OddStandard.SmallF3.Omega
