module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UAutFix
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapReps
public import CFSG.LocalAnalysis.OddStandard.AltStdSmallSylowSym

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

private lemma u_comm_of_swap {q₁ q₂ : Perm (Fin 8)} {a b : Fin 8} (hab : a ≠ b)
    (h1 : q₁ * swap a b = swap a b * q₁) (h2 : q₂ * swap a b = swap a b * q₂)
    {p : Fin 8} (hp : p = a ∨ p = b) : q₁ (q₂ p) = q₂ (q₁ p) := by
  have h1p : q₁ (swap a b p) = swap a b (q₁ p) := by
    simpa only [Equiv.Perm.mul_apply] using DFunLike.congr_fun h1 p
  have h2p : q₂ (swap a b p) = swap a b (q₂ p) := by
    simpa only [Equiv.Perm.mul_apply] using DFunLike.congr_fun h2 p
  have hsp : swap a b p ≠ p := by
    rcases hp with rfl | rfl
    · rw [Equiv.swap_apply_left]; exact hab.symm
    · rw [Equiv.swap_apply_right]; exact hab
  have h1ab : q₁ p = a ∨ q₁ p = b := by
    by_contra h
    simp only [not_or] at h
    have hfix : swap a b (q₁ p) = q₁ p := Equiv.swap_apply_of_ne_of_ne h.1 h.2
    exact hsp (q₁.injective (by rw [h1p, hfix]))
  have h2ab : q₂ p = a ∨ q₂ p = b := by
    by_contra h
    simp only [not_or] at h
    have hfix : swap a b (q₂ p) = q₂ p := Equiv.swap_apply_of_ne_of_ne h.1 h.2
    exact hsp (q₂.injective (by rw [h2p, hfix]))
  have h1mem : q₁ p = p ∨ q₁ p = swap a b p := by
    rcases h1ab with h | h <;> rcases hp with hp | hp
    · left; rw [h, hp]
    · right; rw [h, hp, Equiv.swap_apply_right]
    · right; rw [h, hp, Equiv.swap_apply_left]
    · left; rw [h, hp]
  have h2mem : q₂ p = p ∨ q₂ p = swap a b p := by
    rcases h2ab with h | h <;> rcases hp with hp | hp
    · left; rw [h, hp]
    · right; rw [h, hp, Equiv.swap_apply_right]
    · right; rw [h, hp, Equiv.swap_apply_left]
    · left; rw [h, hp]
  have hswap2 : swap a b (swap a b p) = p := by
    rw [← Equiv.Perm.mul_apply, Equiv.swap_mul_self, Equiv.Perm.one_apply]
  rcases h1mem with h1' | h1' <;> rcases h2mem with h2' | h2'
  · rw [h2', h1', h2']
  · rw [h2', h1p, h1', h2']
  · rw [h2', h1', h2p, h2']
  · rw [h2', h1p, h1', hswap2, h2p, h2', hswap2]

private lemma u_comm_swap_of_central {P : Subgroup (Perm (Fin 8))} {ρ : Perm (Fin 8)}
    (hZ : ∀ q ∈ P, (∀ p ∈ P, q * p = p * q) → q = 1 ∨ q = ρ)
    (hρsupp : ρ.support.card = 8)
    {q : Perm (Fin 8)} {a b : Fin 8} (hab : a ≠ b)
    (hc : IsCentralIn P ⁅q, swap a b⁆) : q * swap a b = swap a b * q := by
  have hmem : ⁅q, swap a b⁆ ∈ P := hc.1
  have hcen : ∀ p ∈ P, ⁅q, swap a b⁆ * p = p * ⁅q, swap a b⁆ := hc.2
  rcases hZ _ hmem hcen with h1 | hρ
  · exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · exfalso
    have hle : (⁅q, swap a b⁆).support.card ≤ 4 := by
      rw [commutatorElement_def, Equiv.swap_inv, ← Equiv.swap_apply_apply]
      calc (swap (q a) (q b) * swap a b).support.card
          ≤ ((swap (q a) (q b)).support ∪ (swap a b).support).card :=
            Finset.card_le_card (Equiv.Perm.support_mul_le _ _)
        _ ≤ (swap (q a) (q b)).support.card + (swap a b).support.card :=
            Finset.card_union_le _ _
        _ = 4 := by
            rw [Equiv.Perm.card_support_swap (show q a ≠ q b from fun h => hab (q.injective h)),
              Equiv.Perm.card_support_swap hab]
    rw [hρ, hρsupp] at hle
    omega

theorem exists_sylow_eight_swaps :
    ∃ P : Subgroup (Perm (Fin 8)), IsPGroup 2 P ∧ Nat.card P = 2 ^ 7 ∧
      swap 0 1 ∈ P ∧ swap 2 3 ∈ P ∧ swap 4 5 ∈ P ∧ swap 6 7 ∈ P ∧
      (∀ q ∈ P, (∀ p ∈ P, q * p = p * q) → q = 1 ∨ q = ρ₄') := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup (Perm (Fin 8)) := centralizer ({ρ₄'} : Set (Perm (Fin 8)))
  have hcardC : Nat.card C = 2 ^ 7 * 3 := by
    dsimp only [C]
    rw [CFSG.OddStandard.AltStdSec.nat_card_centralizer_of_mul_self ρ₄'_mul_self,
      card_cycleType_ρ₄']
    norm_num [Nat.factorial]
  let k : Set (Perm (Fin 8)) := {swap 0 1, swap 2 3, swap 4 5, swap 6 7}
  let B : Subgroup (Perm (Fin 8)) := Subgroup.closure k
  have hBC : B ≤ C := by
    change Subgroup.closure k ≤ C
    rw [Subgroup.closure_le]
    intro x hx
    change x ∈ centralizer ({ρ₄'} : Set (Perm (Fin 8)))
    rw [mem_centralizer_singleton_iff]
    simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide
  have hBpg : IsPGroup 2 B := by
    have hcomm : k.Pairwise Commute := by
      intro x hx y hy _
      simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        exact (commute_iff_eq _ _).2 (by decide)
    haveI : IsMulCommutative B := Subgroup.isMulCommutative_closure hcomm
    have hsq : ∀ x ∈ B, x ^ 2 = 1 := by
      intro x hx
      change x ∈ Subgroup.closure k at hx
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
      · intro y hy
        simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> decide
      · simp
      · intro y z hy hz ihy ihz
        have hyz : y * z = z * y := by
          have h := mul_comm' (⟨y, hy⟩ : B) ⟨z, hz⟩
          exact Subtype.ext_iff.mp h
        calc (y * z) ^ 2 = y * (z * y) * z := by simp only [pow_two, mul_assoc]
          _ = y * (y * z) * z := by rw [← hyz]
          _ = (y * y) * (z * z) := by simp only [mul_assoc]
          _ = 1 := by rw [← pow_two, ← pow_two, ihy, ihz, one_mul]
      · intro y hy ihy
        calc (y⁻¹) ^ 2 = (y ^ 2)⁻¹ := by rw [pow_two, pow_two, mul_inv_rev]
          _ = 1 := by rw [ihy, inv_one]
    exact IsPGroup.of_exponent_dvd_pow (n := 1) (by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro g
      apply Subtype.ext
      simpa using hsq (g : Perm (Fin 8)) g.2)
  have hρ'B : ρ₄' ∈ B := by
    change ρ₄' ∈ Subgroup.closure k
    rw [show ρ₄' = swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 from rfl]
    exact B.mul_mem (B.mul_mem (B.mul_mem (subset_closure (by simp [k]))
      (subset_closure (by simp [k]))) (subset_closure (by simp [k])))
      (subset_closure (by simp [k]))
  have hρC : ρ₄' ∈ C := hBC hρ'B
  obtain ⟨S, hBS⟩ : ∃ S : Sylow 2 ↥C, B.subgroupOf C ≤ S :=
    hBpg.comap_subtype.exists_le_sylow
  let P : Subgroup (Perm (Fin 8)) := (S : Subgroup ↥C).map C.subtype
  have hcardS : Nat.card S = 2 ^ 7 := by
    rw [Sylow.card_eq_multiplicity]
    congr 1
    rw [show Nat.card (↥C) = Nat.card C from rfl, hcardC]
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
  have hPpg : IsPGroup 2 P := by
    dsimp only [P]
    exact S.isPGroup'.map C.subtype
  have hcardP : Nat.card P = 2 ^ 7 := by
    dsimp only [P]
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hcardS
  have hPC : P ≤ C := by
    intro p hp
    dsimp only [P] at hp
    obtain ⟨s, -, rfl⟩ := hp
    exact s.2
  have hρP : ρ₄' ∈ P := by
    dsimp only [P]
    refine ⟨⟨ρ₄', hρC⟩, hBS ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 hρ'B
  have hρcommP : ∀ p ∈ P, ρ₄' * p = p * ρ₄' := by
    intro p hp
    exact (mem_centralizer_singleton_iff.1 (hPC hp)).symm
  have hcenterP : ∀ q ∈ P, (∀ p ∈ P, q * p = p * q) → q = 1 ∨ q = ρ₄' := by
    intro q hq hqcomm
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · right
      have hρ1 : ρ₄' ≠ 1 := by
        intro h
        have hc := card_cycleType_ρ₄'
        rw [h] at hc
        simpa using hc
      exact (CFSG.OddStandard.AltStdSmall.eq_of_mem_center_sylow_sym (n := 8)
        (by norm_num) (by norm_num) hPpg (hcardP ▸ dvd_refl _) hρP hq hρcommP hqcomm
        hρ1 hq1).symm
  have h01 : swap 0 1 ∈ P := by
    dsimp only [P]
    refine ⟨⟨swap 0 1, hBC (subset_closure (by simp [k]))⟩, hBS ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (subset_closure (by simp [k]))
  have h23 : swap 2 3 ∈ P := by
    dsimp only [P]
    refine ⟨⟨swap 2 3, hBC (subset_closure (by simp [k]))⟩, hBS ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (subset_closure (by simp [k]))
  have h45 : swap 4 5 ∈ P := by
    dsimp only [P]
    refine ⟨⟨swap 4 5, hBC (subset_closure (by simp [k]))⟩, hBS ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (subset_closure (by simp [k]))
  have h67 : swap 6 7 ∈ P := by
    dsimp only [P]
    refine ⟨⟨swap 6 7, hBC (subset_closure (by simp [k]))⟩, hBS ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (subset_closure (by simp [k]))
  exact ⟨P, hPpg, hcardP, h01, h23, h45, h67, hcenterP⟩

theorem comm_of_comm_swaps {q₁ q₂ : Perm (Fin 8)}
    (h₁ : q₁ * swap 0 1 = swap 0 1 * q₁ ∧ q₁ * swap 2 3 = swap 2 3 * q₁ ∧
      q₁ * swap 4 5 = swap 4 5 * q₁ ∧ q₁ * swap 6 7 = swap 6 7 * q₁)
    (h₂ : q₂ * swap 0 1 = swap 0 1 * q₂ ∧ q₂ * swap 2 3 = swap 2 3 * q₂ ∧
      q₂ * swap 4 5 = swap 4 5 * q₂ ∧ q₂ * swap 6 7 = swap 6 7 * q₂) :
    q₁ * q₂ = q₂ * q₁ := by
  refine Equiv.ext fun p => ?_
  fin_cases p
  · exact u_comm_of_swap (a := 0) (b := 1) (by decide) h₁.1 h₂.1 (Or.inl rfl)
  · exact u_comm_of_swap (a := 0) (b := 1) (by decide) h₁.1 h₂.1 (Or.inr rfl)
  · exact u_comm_of_swap (a := 2) (b := 3) (by decide) h₁.2.1 h₂.2.1 (Or.inl rfl)
  · exact u_comm_of_swap (a := 2) (b := 3) (by decide) h₁.2.1 h₂.2.1 (Or.inr rfl)
  · exact u_comm_of_swap (a := 4) (b := 5) (by decide) h₁.2.2.1 h₂.2.2.1 (Or.inl rfl)
  · exact u_comm_of_swap (a := 4) (b := 5) (by decide) h₁.2.2.1 h₂.2.2.1 (Or.inr rfl)
  · exact u_comm_of_swap (a := 6) (b := 7) (by decide) h₁.2.2.2 h₂.2.2.2 (Or.inl rfl)
  · exact u_comm_of_swap (a := 6) (b := 7) (by decide) h₁.2.2.2 h₂.2.2.2 (Or.inr rfl)

theorem z2_comm {P : Subgroup (Perm (Fin 8))} (h01 : swap 0 1 ∈ P) (h23 : swap 2 3 ∈ P)
    (h45 : swap 4 5 ∈ P) (h67 : swap 6 7 ∈ P)
    (hZ : ∀ q ∈ P, (∀ p ∈ P, q * p = p * q) → q = 1 ∨ q = ρ₄')
    {q₁ q₂ : Perm (Fin 8)} (hq₁ : q₁ ∈ P) (hq₂ : q₂ ∈ P)
    (hc₁ : ∀ q ∈ P, IsCentralIn P ⁅q₁, q⁆) (hc₂ : ∀ q ∈ P, IsCentralIn P ⁅q₂, q⁆) :
    q₁ * q₂ = q₂ * q₁ := by
  have hρsupp : ρ₄'.support.card = 8 := by decide
  have h₁ : q₁ * swap 0 1 = swap 0 1 * q₁ ∧ q₁ * swap 2 3 = swap 2 3 * q₁ ∧
      q₁ * swap 4 5 = swap 4 5 * q₁ ∧ q₁ * swap 6 7 = swap 6 7 * q₁ :=
    ⟨u_comm_swap_of_central hZ hρsupp (by decide) (hc₁ _ h01),
     u_comm_swap_of_central hZ hρsupp (by decide) (hc₁ _ h23),
     u_comm_swap_of_central hZ hρsupp (by decide) (hc₁ _ h45),
     u_comm_swap_of_central hZ hρsupp (by decide) (hc₁ _ h67)⟩
  have h₂ : q₂ * swap 0 1 = swap 0 1 * q₂ ∧ q₂ * swap 2 3 = swap 2 3 * q₂ ∧
      q₂ * swap 4 5 = swap 4 5 * q₂ ∧ q₂ * swap 6 7 = swap 6 7 * q₂ :=
    ⟨u_comm_swap_of_central hZ hρsupp (by decide) (hc₂ _ h01),
     u_comm_swap_of_central hZ hρsupp (by decide) (hc₂ _ h23),
     u_comm_swap_of_central hZ hρsupp (by decide) (hc₂ _ h45),
     u_comm_swap_of_central hZ hρsupp (by decide) (hc₂ _ h67)⟩
  exact comm_of_comm_swaps h₁ h₂

theorem hQ_of_sylow {G : Type*} [Group G] {P : Subgroup (Perm (Fin 8))}
    (h01 : swap 0 1 ∈ P) (h23 : swap 2 3 ∈ P) (h45 : swap 4 5 ∈ P) (h67 : swap 6 7 ∈ P)
    (hZ : ∀ q ∈ P, (∀ p ∈ P, q * p = p * q) → q = 1 ∨ q = ρ₄')
    (φ : Perm (Fin 8) →* G) (hφ : Function.Injective φ) :
    ∀ q₁ ∈ P.map φ, ∀ q₂ ∈ P.map φ, (∀ q ∈ P.map φ, IsCentralIn (P.map φ) ⁅q₁, q⁆) →
      (∀ q ∈ P.map φ, IsCentralIn (P.map φ) ⁅q₂, q⁆) → q₁ * q₂ = q₂ * q₁ := by
  intro q₁ hq₁ q₂ hq₂ hc₁ hc₂
  obtain ⟨p₁, hp₁, rfl⟩ := Subgroup.mem_map.1 hq₁
  obtain ⟨p₂, hp₂, rfl⟩ := Subgroup.mem_map.1 hq₂
  have hc₁' : ∀ q ∈ P, IsCentralIn P ⁅p₁, q⁆ := by
    intro q hq
    have h := hc₁ (φ q) (Subgroup.mem_map.2 ⟨q, hq, rfl⟩)
    rw [← map_commutatorElement] at h
    refine ⟨(Subgroup.mem_map_iff_mem hφ).1 h.1, ?_⟩
    intro p' hp'
    apply hφ
    rw [map_mul, map_mul]
    exact h.2 (φ p') (Subgroup.mem_map.2 ⟨p', hp', rfl⟩)
  have hc₂' : ∀ q ∈ P, IsCentralIn P ⁅p₂, q⁆ := by
    intro q hq
    have h := hc₂ (φ q) (Subgroup.mem_map.2 ⟨q, hq, rfl⟩)
    rw [← map_commutatorElement] at h
    refine ⟨(Subgroup.mem_map_iff_mem hφ).1 h.1, ?_⟩
    intro p' hp'
    apply hφ
    rw [map_mul, map_mul]
    exact h.2 (φ p') (Subgroup.mem_map.2 ⟨p', hp', rfl⟩)
  have hcomm : p₁ * p₂ = p₂ * p₁ := z2_comm h01 h23 h45 h67 hZ hp₁ hp₂ hc₁' hc₂'
  rw [← map_mul, ← map_mul, hcomm]

end CFSG.OddStandard.AltStdSec.SwapPartner
