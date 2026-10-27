module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.NormalC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Fix2
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem pCore_two_le_kleinV [Finite G] (cfg : H2Cfg G t v J) : pCore 2 G ≤ kleinV t v := by
  by_cases hW : pCore 2 G = ⊥
  · rw [hW]; exact bot_le
  · haveI : (pCore 2 G).Normal := pCore_normal
    have hWp : IsPGroup 2 ↥(pCore 2 G) := pCore_isPGroup
    have hZne : pCore 2 G ⊓ centralizer (pCore 2 G : Set G) ≠ ⊥ :=
      inf_centralizer_ne_bot hWp hW
    have hZn : (pCore 2 G ⊓ centralizer (pCore 2 G : Set G)).Normal := inferInstance
    have hZp : IsPGroup 2 ↥(pCore 2 G ⊓ centralizer (pCore 2 G : Set G)) := hWp.to_inf_left
    obtain ⟨z, hzZ, hz1, hzt⟩ := exists_commute_of_normal_two_group cfg.t_sq hZn hZp hZne
    have hNC :
        (pCore 2 G ⊓ centralizer (pCore 2 G : Set G)) ⊓ centralizer ({t} : Set G)
          ≤ centralizer ({t} : Set G) := inf_le_right
    have hNnorm : ∀ c ∈ centralizer ({t} : Set G),
        ∀ x ∈ (pCore 2 G ⊓ centralizer (pCore 2 G : Set G)) ⊓ centralizer ({t} : Set G),
          c * x * c⁻¹ ∈
            (pCore 2 G ⊓ centralizer (pCore 2 G : Set G)) ⊓ centralizer ({t} : Set G) := by
      intro c hc x hx
      exact ⟨hZn.conj_mem x hx.1 c,
        (centralizer ({t} : Set G)).mul_mem
          ((centralizer ({t} : Set G)).mul_mem hc hx.2)
          ((centralizer ({t} : Set G)).inv_mem hc)⟩
    have hNp : IsPGroup 2
        ↥((pCore 2 G ⊓ centralizer (pCore 2 G : Set G)) ⊓ centralizer ({t} : Set G)) :=
      hZp.to_le inf_le_left
    have hNV :
        (pCore 2 G ⊓ centralizer (pCore 2 G : Set G)) ⊓ centralizer ({t} : Set G)
          ≤ kleinV t v :=
      le_kleinV_of_isPGroup cfg hNC hNnorm hNp
    have hzC : z ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hzt
    have hzN : z ∈ (pCore 2 G ⊓ centralizer (pCore 2 G : Set G)) ⊓ centralizer ({t} : Set G) :=
      ⟨hzZ, hzC⟩
    have hzV : z ∈ kleinV t v := hNV hzN
    have hcent_eq : centralizer ({z} : Set G) = centralizer ({t} : Set G) :=
      centralizer_eq_of_mem cfg hzV hz1
    have hW_le_cz : pCore 2 G ≤ centralizer ({z} : Set G) := by
      intro w hw
      exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hzZ.2) w hw)
    have hW_le_C : pCore 2 G ≤ centralizer ({t} : Set G) := hcent_eq ▸ hW_le_cz
    have hWnormC : ∀ c ∈ centralizer ({t} : Set G), ∀ x ∈ pCore 2 G, c * x * c⁻¹ ∈ pCore 2 G :=
      fun c _ x hx => (inferInstance : (pCore 2 G).Normal).conj_mem x hx c
    exact le_kleinV_of_isPGroup cfg hW_le_C hWnormC hWp

theorem normal_or_fitting_eq_bot [Finite G] (cfg : H2Cfg G t v J) :
    (kleinV t v).Normal ∨ fittingSubgroup G = ⊥ := by
  by_cases hW : pCore 2 G = ⊥
  · right
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_eq_bot.2 fun p => ?_
    have hp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
    have : Fact (Nat.Prime (p : ℕ)) := ⟨hp⟩
    by_cases h2 : (p : ℕ) = 2
    · rw [h2]; exact hW
    · apply cfg.odd _ CFSG.pCore_normal
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := (p : ℕ)) (G := G)).exists_card_eq
      rw [hn]
      exact (hp.odd_of_ne_two h2).pow
  · left
    have hWV : pCore 2 G ≤ kleinV t v := pCore_two_le_kleinV cfg
    by_cases hWVeq : pCore 2 G = kleinV t v
    · rw [← hWVeq]; exact CFSG.pCore_normal
    · exfalso
      have hWn : (pCore 2 G).Normal := pCore_normal
      have hWp : IsPGroup 2 ↥(pCore 2 G) := pCore_isPGroup
      have hcardV : Nat.card ↥(kleinV t v) = 4 := card_kleinV cfg
      have hcardW : Nat.card ↥(pCore 2 G) = 2 := by
        have hdvd : Nat.card ↥(pCore 2 G) ∣ 4 := by
          have h := Subgroup.card_dvd_of_le hWV
          rwa [hcardV] at h
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at hdvd
        obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        interval_cases k
        · have h1 : pCore 2 G = ⊥ := Subgroup.card_eq_one.mp (by simpa using hk)
          exact absurd h1 hW
        · simpa using hk
        · have h4 : Nat.card ↥(pCore 2 G) = 4 := by simpa using hk
          have hV : pCore 2 G = kleinV t v :=
            Subgroup.eq_of_le_of_card_ge hWV (by simp [hcardV, h4])
          exact absurd hV hWVeq
      obtain ⟨y, hy1, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(pCore 2 G))).1 hcardW
      have hy1G : (y : G) ≠ 1 := fun hc => hy1 (Subtype.ext hc)
      have hcentral : ∀ g : G, g * (y : G) = (y : G) * g := by
        intro g
        have hmem : g * (y : G) * g⁻¹ ∈ pCore 2 G := hWn.conj_mem (y : G) y.2 g
        let y' : ↥(pCore 2 G) := ⟨g * (y : G) * g⁻¹, hmem⟩
        have hy'1 : y' ≠ 1 := by
          intro hc
          apply hy1G
          have h1 : g * (y : G) * g⁻¹ = 1 := by simpa [y'] using congrArg Subtype.val hc
          calc (y : G) = g⁻¹ * (g * (y : G) * g⁻¹) * g := by group
            _ = 1 := by rw [h1]; group
        have hy'eq : y' = y := hyuniq y' hy'1
        have hval : g * (y : G) * g⁻¹ = (y : G) := congrArg Subtype.val hy'eq
        calc g * (y : G) = (g * (y : G) * g⁻¹) * g := by group
          _ = (y : G) * g := by rw [hval]
      exact hy1G (cfg.center (y : G) hcentral)

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
