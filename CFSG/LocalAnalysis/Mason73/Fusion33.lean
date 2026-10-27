module

public import CFSG.LocalAnalysis.Mason73.Fusion35
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

@[expose] def aT (n : ℕ) : L4Model n :=
  el ![ss n, -ss n, ss n, -ss n] 1 (by rw [detSum_one_iff, Fin.sum_univ_four]; simp)

theorem aT_mul_aT (hn : 3 ≤ n) : aT n * aT n = x1T (by omega) := by
  rw [aT, el_mul, x1T_eq, el_eq_el_iff (by omega)]
  refine ⟨rfl, ?_⟩
  have h4 := four_mul_ss hn
  have key : ∀ i, (hv n χx1 - (![ss n, -ss n, ss n, -ss n] +
      pv ((1 : Fin81.R0) : Perm (Fin 4)) ![ss n, -ss n, ss n, -ss n])) i = 2 * ss n := by
    intro i
    fin_cases i
    · change hh n * ((1 : ℕ) : ZMod (2 ^ n)) - (ss n + ss n) = 2 * ss n
      rw [Nat.cast_one, mul_one]
      linear_combination -h4
    · change hh n * ((0 : ℕ) : ZMod (2 ^ n)) - (-ss n + -ss n) = 2 * ss n
      rw [Nat.cast_zero, mul_zero]
      ring
    · change hh n * ((1 : ℕ) : ZMod (2 ^ n)) - (ss n + ss n) = 2 * ss n
      rw [Nat.cast_one, mul_one]
      linear_combination -h4
    · change hh n * ((0 : ℕ) : ZMod (2 ^ n)) - (-ss n + -ss n) = 2 * ss n
      rw [Nat.cast_zero, mul_zero]
      ring
  intro i j
  rw [key i, key j]

theorem aT_mem_centralizer_tT (hn : 2 ≤ n) : aT n ∈ centralizer {tT (n := n) (by omega)} := by
  rw [Subgroup.mem_centralizer_singleton_iff, aT, tT, eq_comm, el_comm_diag_iff hn]
  have : pv ((tP : Fin81.R0) : Perm (Fin 4)) ![ss n, -ss n, ss n, -ss n] =
      ![ss n, -ss n, ss n, -ss n] := by
    funext i
    fin_cases i <;> rfl
  rw [this, sub_self]
  intro i j
  rfl

theorem mul_self_mem_A_of_mem_centralizer_x1T (hn : 3 ≤ n) {b : L4Model n}
    (hb : b ∈ centralizer {x1T (n := n) (by omega)}) : b * b ∈ A n := by
  rw [centralizer_x1T hn, Subgroup.mem_comap] at hb
  rw [mem_A_iff, map_mul]
  have key : ∀ π : Perm (Fin 4), π ∈ Fin81.R0 → PatFix π (pat (1, 0, 1)) → π * π = 1 := by
    decide
  exact Subtype.ext (key _ (piT b).2 hb)

theorem tT_not_mem_A (hn : 1 ≤ n) : tT (n := n) hn ∉ A n := by
  rw [tT, el_mem_A]
  decide

theorem x1T_ne_zT (hn : 2 ≤ n) : x1T (n := n) (by omega) ≠ zT (by omega) := by
  rw [x1T_eq, zT_eq, Ne, el_hv_eq_el_hv_iff' hn]
  decide

theorem mem_of_conj_x1T_mem_A (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) {e : L4Model n} (he : e ∈ A n) (he2 : e * e = 1) {k : G}
    (hk : k * ι e * k⁻¹ = ι (x1T (by omega))) :
    e = 1 ∨ e = zT (by omega) ∨ e = x1T (by omega) ∨ e = y1T (by omega) := by
  obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn he he2
  rcases Nat.mod_two_eq_zero_or_one (pat p 0 + pat p 1 + pat p 2 + pat p 3) with hp | hp
  · have key : ∀ q : Fin 2 × Fin 2 × Fin 2, (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 0 →
        q = (0, 0, 0) ∨ q = (0, 1, 1) ∨ q = (1, 0, 1) ∨ q = (1, 1, 0) := by
      decide
    rcases key p hp with rfl | rfl | rfl | rfl
    · exact Or.inl (omegaEl_zero hn)
    · exact Or.inr (Or.inl (zT_eq_omegaEl hn).symm)
    · exact Or.inr (Or.inr (Or.inl (x1T_eq_omegaEl hn).symm))
    · exact Or.inr (Or.inr (Or.inr (y1T_eq_omegaEl hn).symm))
  · obtain ⟨c, hc⟩ := exists_conj_w1T_eq hn p hp
    exfalso
    apply not_conj_w1T_x1T hn hι hS (k * ι c)
    rw [← hk, ← hc, map_mul, map_mul, map_inv]
    group

theorem not_conj_tT_x1T_of_central (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hz : ∀ g : G, g * ι (zT (by omega)) = ι (zT (by omega)) * g) (g : G) :
    g * ι (tT (by omega)) * g⁻¹ ≠ ι (x1T (by omega)) := by
  intro hg
  have hzconj : ∀ k : G, k⁻¹ * ι (zT (n := n) (by omega)) * k = ι (zT (by omega)) := fun k => by
    rw [mul_assoc, ← hz k, ← mul_assoc, inv_mul_cancel, one_mul]
  have hxz : ∀ g : G, g * ι (x1T (by omega)) * g⁻¹ ≠ ι (zT (by omega)) := by
    intro g' h'
    have h2 : ι (x1T (n := n) (by omega)) = ι (zT (by omega)) := by
      rw [show ι (x1T (n := n) (by omega)) = g'⁻¹ * (g' * ι (x1T (by omega)) * g'⁻¹) * g' by
        group, h', hzconj]
    exact x1T_ne_zT (by omega) (hι h2)
  obtain ⟨k, hkt, hk⟩ := GHarris.exists_conj_extremal (S := ι.range) hS.isPGroup
    (isSylowOf_x1T hn hι hS hxz) (u := ι (tT (by omega))) (h := g) (by rw [← hg]; group)
  have hca : ι (aT n) ∈ (ι.range ⊓ centralizer {ι (tT (by omega))} : Subgroup G) := by
    refine Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 (aT_mem_centralizer_tT (by omega))]
  obtain ⟨⟨b, hb⟩, hbc⟩ := Subgroup.mem_inf.1 (hk _ hca)
  have hbx : b ∈ centralizer {x1T (n := n) (by omega)} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hι
    rw [map_mul, map_mul, hb]
    exact Subgroup.mem_centralizer_singleton_iff.1 hbc
  have he : k⁻¹ * ι (x1T (by omega)) * k = ι (b * b) := by
    rw [map_mul, hb, ← aT_mul_aT hn, map_mul]
    group
  have hx2 : x1T (n := n) (by omega) * x1T (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_x1T (by omega)]
  have he2 : b * b * (b * b) = 1 := by
    apply hι
    rw [map_mul, ← he, map_one]
    calc k⁻¹ * ι (x1T (by omega)) * k * (k⁻¹ * ι (x1T (by omega)) * k)
        = k⁻¹ * ι (x1T (by omega) * x1T (by omega)) * k := by rw [map_mul]; group
      _ = 1 := by rw [hx2, map_one]; group
  rcases mem_of_conj_x1T_mem_A hn hι hS (mul_self_mem_A_of_mem_centralizer_x1T hn hbx) he2
    (k := k) (by rw [← he]; group) with h | h | h | h <;> rw [h] at he
  ·
    have h1 := orderOf_x1T (n := n) (by omega)
    rw [← orderOf_injective ι hι, show ι (x1T (n := n) (by omega)) = 1 by
      rw [show ι (x1T (n := n) (by omega)) = k * (k⁻¹ * ι (x1T (by omega)) * k) * k⁻¹ by group,
        he, map_one]
      group, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  ·
    apply x1T_ne_zT (n := n) (by omega)
    apply hι
    rw [show ι (x1T (n := n) (by omega)) = k * (k⁻¹ * ι (x1T (by omega)) * k) * k⁻¹ by group,
      he, show k * ι (zT (n := n) (by omega)) * k⁻¹ = (k⁻¹)⁻¹ * ι (zT (by omega)) * k⁻¹ by
        group, hzconj]
  ·
    apply tT_not_mem_A (n := n) (by omega)
    have : ι (tT (n := n) (by omega)) = ι (x1T (by omega)) := by
      have h1 : k⁻¹ * ι (tT (by omega)) * k = k⁻¹ * ι (x1T (by omega)) * k := by rw [hkt, he]
      simpa using h1
    rw [hι this]
    exact x1T_mem_A _
  ·
    apply tT_not_mem_A (n := n) (by omega)
    have h1 : k⁻¹ * ι (tT (by omega) * x1T (by omega)) * k = ι (zT (by omega)) := by
      rw [map_mul, show k⁻¹ * (ι (tT (by omega)) * ι (x1T (by omega))) * k =
        (k⁻¹ * ι (tT (by omega)) * k) * (k⁻¹ * ι (x1T (by omega)) * k) by group, hkt, he,
        ← map_mul, x1T_mul_y1T (by omega)]
    have h2 : tT (n := n) (by omega) * x1T (by omega) = zT (by omega) := by
      apply hι
      rw [show ι (tT (n := n) (by omega) * x1T (by omega)) =
        k * (k⁻¹ * ι (tT (by omega) * x1T (by omega)) * k) * k⁻¹ by group, h1,
        show k * ι (zT (n := n) (by omega)) * k⁻¹ = (k⁻¹)⁻¹ * ι (zT (by omega)) * k⁻¹ by
          group, hzconj]
    have : tT (n := n) (by omega) = zT (by omega) * (x1T (by omega))⁻¹ := by
      rw [← h2]
      group
    rw [this]
    exact mul_mem (zT_mem_A _) (inv_mem (x1T_mem_A _))

@[expose] def restrictCentralizer (ι : L4Model n →* G) (hn : 2 ≤ n) :
    L4Model n →* centralizer {ι (zT (n := n) (by omega))} :=
  ι.codRestrict _ fun t => Subgroup.mem_centralizer_singleton_iff.2 (by
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (zT_mem_center hn) t])

theorem restrictCentralizer_injective {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hn : 2 ≤ n) : Function.Injective (restrictCentralizer ι hn) := fun a b h =>
  hι (congrArg Subtype.val h)

theorem isSylowOf_restrictCentralizer (hn : 2 ≤ n) {ι : L4Model n →* G}
    (hS : IsSylowOf 2 ι.range ⊤) : IsSylowOf 2 (restrictCentralizer ι hn).range ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer {ι (zT (n := n) (by omega))}
  have hle : ι.range ≤ K := by
    rintro _ ⟨t, rfl⟩
    exact (restrictCentralizer ι hn t).2
  have h := GHarris.isSylowOf_inf_centralizer_of_le hS hle
  rw [inf_of_le_left hle] at h
  rw [← isSylowOf_map_subtype_iff K]
  convert h using 1
  · ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_range, Subgroup.coe_subtype]
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨t, rfl⟩, rfl⟩
  · ext x
    simp [K]

end CFSG.LocalAnalysis.Mason73
