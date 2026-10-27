module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] def Sec8T84Y (H : Subgroup G) : Subgroup G :=
  closure {x | x ∈ H ∧ Odd (orderOf x)}

private theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (x := x) (y := g * x * g⁻¹) (by
    show g * x = (g * x * g⁻¹) * g
    group)).symm

theorem sec8t84y_le (H : Subgroup G) : Sec8T84Y H ≤ H := by
  rw [Sec8T84Y, Subgroup.closure_le]
  rintro x ⟨hx, _⟩
  exact hx

theorem sec8t84y_mem_of_odd {H : Subgroup G} {x : G} (hx : x ∈ H) (ho : Odd (orderOf x)) :
    x ∈ Sec8T84Y H := by
  exact Subgroup.subset_closure ⟨hx, ho⟩

theorem sec8t84y_conj {H H' : Subgroup G} {g : G} (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H') {y : G}
    (hy : y ∈ Sec8T84Y H) : g * y * g⁻¹ ∈ Sec8T84Y H' := by
  refine Subgroup.closure_induction (p := fun y _ => g * y * g⁻¹ ∈ Sec8T84Y H')
    ?_ ?_ ?_ ?_ hy
  · rintro x ⟨hxH, hxodd⟩
    exact sec8t84y_mem_of_odd (hg x hxH) (by rw [orderOf_conj']; exact hxodd)
  · simpa using (Sec8T84Y H').one_mem
  · intro x y _ _ ihx ihy
    have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [hxy]
    exact (Sec8T84Y H').mul_mem ihx ihy
  · intro x _ ihx
    have hxinv : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [hxinv]
    exact (Sec8T84Y H').inv_mem ihx

theorem sec8t84y_odd_five [Finite G] {X C : Subgroup G} {x : G} (hx : x ∈ X) (h5 : x ^ 5 ∈ C)
    (hC : x ∉ C) : ∃ y ∈ X, Odd (orderOf y) ∧ y ^ 5 ∈ C ∧ y ∉ C := by
  obtain ⟨s, m, hm_odd, hn_eq⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨x ^ (2 ^ s), X.pow_mem hx _, ?_, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero s two_ne_zero) (by
      rw [hn_eq]; exact dvd_mul_right _ _), hn_eq,
      Nat.mul_div_cancel_left m (pow_pos (by norm_num) s)]
    exact hm_odd
  · rw [← pow_mul, mul_comm (2 ^ s) 5, pow_mul]
    exact C.pow_mem h5 (2 ^ s)
  · intro hyC
    have hcop_nat : Nat.Coprime 5 (2 ^ s) := (by norm_num : Nat.Coprime 5 2).pow_right s
    have hg : Nat.gcd 5 (2 ^ s) = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop_nat
    have hbez : (1 : ℤ) = (5 : ℤ) * Nat.gcdA 5 (2 ^ s) +
        (((2 ^ s : ℕ) : ℤ)) * Nat.gcdB 5 (2 ^ s) := by
      have := Nat.gcd_eq_gcd_ab 5 (2 ^ s)
      rw [hg] at this
      simpa using this
    have hkC : x ^ (((2 ^ s : ℕ) : ℤ)) ∈ C := by
      rw [zpow_natCast]
      exact hyC
    have h5z : x ^ (5 : ℤ) ∈ C := by simpa using h5
    have hx_eq : x = (x ^ (5 : ℤ)) ^ Nat.gcdA 5 (2 ^ s) *
        (x ^ (((2 ^ s : ℕ) : ℤ))) ^ Nat.gcdB 5 (2 ^ s) := by
      calc
        x = x ^ (1 : ℤ) := by simp
        _ = x ^ ((5 : ℤ) * Nat.gcdA 5 (2 ^ s) +
              (((2 ^ s : ℕ) : ℤ)) * Nat.gcdB 5 (2 ^ s)) := by rw [← hbez]
        _ = x ^ ((5 : ℤ) * Nat.gcdA 5 (2 ^ s)) *
              x ^ ((((2 ^ s : ℕ) : ℤ)) * Nat.gcdB 5 (2 ^ s)) := zpow_add x _ _
        _ = (x ^ (5 : ℤ)) ^ Nat.gcdA 5 (2 ^ s) *
              (x ^ (((2 ^ s : ℕ) : ℤ))) ^ Nat.gcdB 5 (2 ^ s) := by
          rw [zpow_mul, zpow_mul]
    have hxC : x ∈ C := by
      rw [hx_eq]
      exact C.mul_mem (C.zpow_mem h5z _) (C.zpow_mem hkC _)
    exact hC hxC

theorem sec8t84y_exists_mul [Finite G] {H K : Subgroup G}
    (hq : QuotEquivTo H K (alternatingGroup (Fin 6))) {x : G} (hx : x ∈ H) :
    ∃ k ∈ K, ∃ y ∈ Sec8T84Y H, x = k * y := by
  obtain ⟨φ, hφsurj, hφker⟩ := hq
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (α := Fin 6) (by rw [Nat.card_fin]; norm_num)
  let N : Subgroup (alternatingGroup (Fin 6)) := ((Sec8T84Y H).subgroupOf H).map φ
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    change n ∈ ((Sec8T84Y H).subgroupOf H).map φ at hn
    change g * n * g⁻¹ ∈ ((Sec8T84Y H).subgroupOf H).map φ
    rw [Subgroup.mem_map] at hn ⊢
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨h, rfl⟩ := hφsurj g
    refine Subgroup.mem_map.mpr ⟨h * y * h⁻¹, ?_, ?_⟩
    · have hmem : (((h * y * h⁻¹ : ↥H) : G)) ∈ Sec8T84Y H := by
        have hconj := sec8t84y_conj (H := H) (H' := H) (g := (h : G))
          (fun z hz => H.mul_mem (H.mul_mem h.2 hz) (H.inv_mem h.2)) hy
        simpa using hconj
      exact hmem
    · simp only [map_mul, map_inv]
  have hNne : N ≠ ⊥ := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card (G := alternatingGroup (Fin 6)) 5 (by
      rw [← Nat.card_eq_fintype_card, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial])
    obtain ⟨h, hh⟩ := hφsurj c
    have hc5 : c ^ 5 = 1 := by simpa [hc] using pow_orderOf_eq_one c
    have hpow : (h : G) ^ 5 ∈ K := by
      have hp : φ (h ^ 5) = 1 := by rw [map_pow, hh, hc5]
      have hker' : h ^ 5 ∈ φ.ker := MonoidHom.mem_ker.mpr hp
      rw [hφker] at hker'
      have hmemK : ((h ^ 5 : ↥H) : G) ∈ K := hker'
      simpa only [Subgroup.coe_pow] using hmemK
    have hK : (h : G) ∉ K := by
      intro hmem
      have hker' : h ∈ φ.ker := by
        rw [hφker]
        exact hmem
      have h1 : φ h = 1 := MonoidHom.mem_ker.mp hker'
      rw [hh] at h1
      have hc1 : c = 1 := h1
      rw [hc1, orderOf_one] at hc
      omega
    obtain ⟨y, hyX, hyodd, _hy5, hyK⟩ :=
      sec8t84y_odd_five (X := H) (C := K) h.2 hpow hK
    have hyY : y ∈ Sec8T84Y H := sec8t84y_mem_of_odd hyX hyodd
    have hφy : φ ⟨y, hyX⟩ ≠ 1 := by
      intro h1
      have hker' : (⟨y, hyX⟩ : ↥H) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
      rw [hφker] at hker'
      exact hyK hker'
    have hmemN : φ ⟨y, hyX⟩ ∈ N := by
      change φ ⟨y, hyX⟩ ∈ ((Sec8T84Y H).subgroupOf H).map φ
      exact Subgroup.mem_map.mpr ⟨⟨y, hyX⟩, hyY, rfl⟩
    intro hbot
    rw [hbot] at hmemN
    exact hφy (by simpa using hmemN)
  have hNtop : N = ⊤ := by
    haveI : N.Normal := hNnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top N with hbot | htop
    · exact absurd hbot hNne
    · exact htop
  have hxN : φ ⟨x, hx⟩ ∈ N := by
    rw [hNtop]
    exact Subgroup.mem_top _
  change φ ⟨x, hx⟩ ∈ ((Sec8T84Y H).subgroupOf H).map φ at hxN
  rw [Subgroup.mem_map] at hxN
  obtain ⟨y, hy, hyφ⟩ := hxN
  refine ⟨x * (y : G)⁻¹, ?_, (y : G), hy, ?_⟩
  · have hkker : (⟨x, hx⟩ * y⁻¹ : ↥H) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyφ]
      simp
    rw [hφker] at hkker
    have hmemK : (((⟨x, hx⟩ * y⁻¹ : ↥H) : G)) ∈ K := hkker
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmemK
  · group

end CFSG.OddStandard.SmallF3.Omega
