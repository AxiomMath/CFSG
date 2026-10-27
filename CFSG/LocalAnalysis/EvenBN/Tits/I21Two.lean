module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Red

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u x : G}

variable (h : SecTwoHyp G t u)

include h

theorem mem_centralizer_iff_conj {x : G} : x ∈ centralizer ({t} : Set G) ↔ x * t * x⁻¹ = t := by
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem conj_z_of_normalizer {g : G} (hg : g ∈ normalizer (secTwoR t u : Set G)) :
    g * u ^ 2 * g⁻¹ = u ^ 2 := by
  have hu : g * u * g⁻¹ ∈ secTwoR t u := (mem_normalizer_iff.mp hg u).mp SecTwoHyp.u_mem_R
  have hsq : (g * u * g⁻¹) ^ 2 = g * u ^ 2 * g⁻¹ := by rw [conj_pow]
  rcases h.sq_of_mem_R hu with h1 | h1
  · exfalso
    apply h.z_ne_one
    have : g * u ^ 2 * g⁻¹ = 1 := by rw [← hsq, h1]
    calc u ^ 2 = g⁻¹ * (g * u ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  · rw [← hsq, h1]

theorem conj_t_of_normalizer {g : G} (hg : g ∈ normalizer (secTwoR t u : Set G)) :
    g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * u ^ 2 := by
  have hmem : g * t * g⁻¹ ∈ secTwoR t u := (mem_normalizer_iff.mp hg t).mp SecTwoHyp.t_mem_R
  have hsq : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, h.t_sq]; group
  rcases h.eq_of_mem_R_of_sq_eq_one hmem hsq with h1 | h1 | h1 | h1
  · exfalso; apply h.t_ne_one
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · exact Or.inl h1
  · exfalso
    apply h.conj_z_ne_t g⁻¹
    rw [← h1]; group
  · exact Or.inr h1

theorem orbit_cases {N : Subgroup G} (hN : N ≤ normalizer (secTwoR t u : Set G)) :
    N ≤ centralizer ({t} : Set G) ∨
      ((N ⊓ centralizer ({t} : Set G)).relIndex N = 2 ∧ ∃ g ∈ N, g * t * g⁻¹ = t * u ^ 2) := by
  by_cases hall : ∀ g ∈ N, g * t * g⁻¹ = t
  · left
    intro g hg
    exact h.mem_centralizer_iff_conj.mpr (hall g hg)
  · right
    push Not at hall
    obtain ⟨g, hgN, hgt⟩ := hall
    have hgt' : g * t * g⁻¹ = t * u ^ 2 := (h.conj_t_of_normalizer (hN hgN)).resolve_left hgt
    refine ⟨?_, g, hgN, hgt'⟩
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨g, hgN⟩, fun b => ?_⟩
    have hbz : (b : G) * u ^ 2 * (b : G)⁻¹ = u ^ 2 := h.conj_z_of_normalizer (hN b.2)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf, SetLike.coe_mem,
      true_and, h.mem_centralizer_iff_conj]
    have hbN : (b : G) ∈ N := b.2
    have hbgN : (b : G) * g ∈ N := mul_mem hbN hgN
    simp only [hbgN, true_and]
    have hbg : (b : G) * g * t * ((b : G) * g)⁻¹ = ((b : G) * t * (b : G)⁻¹) * u ^ 2 := by
      calc (b : G) * g * t * ((b : G) * g)⁻¹ = (b : G) * (g * t * g⁻¹) * (b : G)⁻¹ := by group
        _ = (b : G) * (t * u ^ 2) * (b : G)⁻¹ := by rw [hgt']
        _ = ((b : G) * t * (b : G)⁻¹) * ((b : G) * u ^ 2 * (b : G)⁻¹) := by group
        _ = _ := by rw [hbz]
    have hzz : u ^ 2 * u ^ 2 = 1 := by rw [← pow_add, show 2 + 2 = 4 from rfl, h.u_pow_four]
    rcases h.conj_t_of_normalizer (hN hbN) with hc | hc
    · rw [hbg, hc]
      refine Or.inr ⟨rfl, ?_⟩
      intro htz
      exact h.z_ne_one (mul_left_cancel (htz.trans (mul_one t).symm))
    · rw [hbg, hc]
      refine Or.inl ⟨by rw [mul_assoc, hzz, mul_one], ?_⟩
      intro htz
      exact h.z_ne_one (mul_left_cancel (htz.trans (mul_one t).symm))

end CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits

theorem two_pow_mul_mod_five (j : ℕ) : (2 ^ (3 * j) * 2 ^ (j + 1)) % 5 = 2 := by
  rw [← pow_add, show 3 * j + (j + 1) = 4 * j + 1 by ring, pow_succ, pow_mul, Nat.mul_mod,
    Nat.pow_mod]
  norm_num

end CFSG.LocalAnalysis.EvenBN.Tits.I21

namespace CFSG.LocalAnalysis.EvenBN.Tits.Sec622Bar

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits I21

variable {G : Type} [Group G] [Finite G] {t u x : G}

variable (h : Sec622Bar G t u x)

include h

theorem eq_one_of_mem_R_of_pow_five {g : G} (hg : g ∈ secTwoR t u) (h5 : g ^ 5 = 1) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.secTwo.isPGroup_R) ⟨g, hg⟩
  have hk' : orderOf g = 2 ^ k := by rw [← Subgroup.orderOf_mk g hg]; exact hk
  have hd : 2 ^ k ∣ 5 := hk' ▸ orderOf_dvd_of_pow_eq_one h5
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ 5 := (dvd_pow_self 2 hne).trans hd
    omega
  rw [hk0, pow_zero] at hk'
  exact orderOf_eq_one_iff.mp hk'

theorem mem_R_of_mem_centralizer_normalizer {g : G} (hgC : g ∈ centralizer ({t} : Set G))
    (hgN : g ∈ normalizer (secTwoR t u : Set G)) : g ∈ secTwoR t u := by
  have hc := h.crel
  rw [h.cent] at hgC
  obtain ⟨a, i, j, rfl⟩ := hc.mem_closure_iff.mp hgC
  have hu : u ∈ secTwoR t u := SecTwoHyp.u_mem_R
  have hmem : (t ^ a * x ^ i * u ^ j) * u * (t ^ a * x ^ i * u ^ j)⁻¹ ∈ secTwoR t u :=
    (mem_normalizer_iff.mp hgN u).mp hu
  have e1 : (t ^ a * x ^ i * u ^ j) * u = t ^ a * x ^ i * u ^ (j + 1) := by
    rw [pow_succ]; group
  rw [e1, hc.nf_inv, hc.nf_mul] at hmem
  have ht2 : t ^ (a + a) = 1 := by
    rw [← two_mul, pow_mul, h.secTwo.t_sq, one_pow]
  have hu1 : u ^ (j + 1 + 3 * j) = u := by
    rw [show j + 1 + 3 * j = 4 * j + 1 by ring, pow_succ, pow_mul, h.secTwo.u_pow_four, one_pow,
      one_mul]
  rw [ht2, hu1, one_mul] at hmem
  have hx : x ^ (i + 4 * i * 2 ^ (3 * j) * 2 ^ (j + 1)) ∈ secTwoR t u := by
    have := mul_mem hmem (inv_mem hu)
    simpa using this
  have h5 : (x ^ (i + 4 * i * 2 ^ (3 * j) * 2 ^ (j + 1))) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h.x_five, one_pow]
  have hx1 := h.eq_one_of_mem_R_of_pow_five hx h5
  have hexp : (i + 4 * i * 2 ^ (3 * j) * 2 ^ (j + 1)) % 5 = (4 * i) % 5 := by
    have := two_pow_mul_mod_five j
    have h4 : 4 * i * 2 ^ (3 * j) * 2 ^ (j + 1) = 4 * i * (2 ^ (3 * j) * 2 ^ (j + 1)) := by ring
    rw [h4, Nat.add_mod, Nat.mul_mod (4 * i), this]
    omega
  rw [pow_mod_of_pow_eq_one h.x_five, hexp, ← pow_mod_of_pow_eq_one h.x_five] at hx1
  have hxi : x ^ i = 1 := by
    have : x ^ i * x ^ (4 * i) = 1 := by
      rw [← pow_add, show i + 4 * i = 5 * i by ring, pow_mul, h.x_five, one_pow]
    rw [hx1, mul_one] at this
    exact this
  rw [hxi, mul_one]
  exact mul_mem (pow_mem SecTwoHyp.t_mem_R a) (pow_mem hu j)

theorem isPGroup_of_sylow_eq (S : Sylow 2 G) (hS : secTwoR t u = S) : IsPGroup 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (secTwoR t u) := h.secTwo.isPGroup_R
  have hNC : normalizer (secTwoR t u : Set G) ≤ centralizer ({t} : Set G) := by
    rcases h.secTwo.orbit_cases (N := normalizer (secTwoR t u : Set G)) le_rfl with hle | ⟨hidx, -⟩
    · exact hle
    · exfalso
      set N := normalizer (secTwoR t u : Set G) with hN
      have hRN : secTwoR t u ≤ N := le_normalizer
      have hRC : secTwoR t u ≤ N ⊓ centralizer ({t} : Set G) := le_inf hRN h.secTwo.R_le_centralizer
      have h1 : (N ⊓ centralizer ({t} : Set G)).relIndex N ∣ (secTwoR t u).relIndex N :=
        ⟨(secTwoR t u).relIndex (N ⊓ centralizer ({t} : Set G)), by
          rw [mul_comm, Subgroup.relIndex_mul_relIndex _ _ _ hRC inf_le_left]⟩
      have h2 : (secTwoR t u).relIndex N ∣ (secTwoR t u).index :=
        Subgroup.relIndex_dvd_index_of_le hRN
      have h3 : ¬ 2 ∣ (secTwoR t u).index := by
        rw [hS]; exact S.not_dvd_index
      rw [hidx] at h1
      exact h3 (h1.trans h2)
  have hNR : normalizer (secTwoR t u : Set G) ≤ secTwoR t u := fun g hg =>
    h.mem_R_of_mem_centralizer_normalizer (hNC hg) hg
  have hcomm : normalizer (S : Set G) ≤ centralizer (S : Set G) := by
    intro g hg
    have hg' : g ∈ secTwoR t u := by
      have : normalizer (secTwoR t u : Set G) = normalizer (S : Set G) := by rw [hS]; rfl
      rw [← this] at hg
      exact hNR hg
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ secTwoR t u := by rw [hS]; exact hy
    exact h.secTwo.mul_comm_of_mem_R hy' hg'
  have hcompl := MonoidHom.ker_transferSylow_isComplement' S hcomm
  set K := (MonoidHom.transferSylow S hcomm).ker with hK
  have hKodd : Odd (Nat.card K) := by
    have := MonoidHom.not_dvd_card_ker_transferSylow S hcomm
    rcases Nat.even_or_odd (Nat.card K) with he | ho
    · exact absurd (even_iff_two_dvd.mp he) this
    · exact ho
  have hKO : K ≤ standardComponentOddCore G := le_sSup ⟨inferInstance, hKodd⟩
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff, ← h.oddCore]; exact hKO
  have hcard : Nat.card K * Nat.card (S : Subgroup G) = Nat.card G := hcompl.card_mul
  rw [hKbot, Subgroup.card_bot, one_mul] at hcard
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  exact IsPGroup.of_card (n := n) (hcard ▸ hn)

end CFSG.LocalAnalysis.EvenBN.Tits.Sec622Bar
