module

public import CFSG.LocalAnalysis.Mason73.Fusion36

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem exists_conj_zT_x1T_of_pow_four (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤) {l : L4Model n}
    (hlz : l ≠ zT (by omega)) {c : L4Model n} (hc : c ∈ centralizer {l})
    (hc4 : c ^ 4 = zT (by omega)) {g : G} (hg : g * ι l * g⁻¹ = ι (zT (by omega))) :
    ∃ k : G, k⁻¹ * ι l * k = ι (zT (by omega)) ∧
      (∀ c ∈ centralizer {l}, ∃ d : L4Model n, ι d = k⁻¹ * ι c * k) ∧
      k⁻¹ * ι (zT (by omega)) * k = ι (x1T (by omega)) := by
  obtain ⟨k, hkl, hk⟩ := exists_conj_zT_of_conj hn hS hg
  obtain ⟨e, he⟩ := hk _ (zT_mem_centralizer (by omega) l)
  obtain ⟨d, hd⟩ := hk c hc
  have hed : e = d ^ 4 :=
    hι (by rw [map_pow, hd, he, ← hc4, map_pow, GHarris.conj_pow_inv])
  have heA : e ∈ A n := hed ▸ pow_four_mem_A d
  have hz2 : zT (n := n) (by omega) * zT (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zT (by omega)]
  have he' : k⁻¹ * ι (zT (n := n) (by omega)) * k⁻¹⁻¹ = ι e := by rw [inv_inv, he]
  have he2 := mul_self_of_conj_eq hι hz2 he'
  have hz1 : zT (n := n) (by omega) ≠ 1 := fun h => by
    have := orderOf_zT (n := n) (by omega)
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have he1 := ne_one_of_conj_eq hι hz1 he'
  have hzc : ∀ a : L4Model n, a⁻¹ * zT (by omega) * a = zT (by omega) := fun a => by
    rw [mul_assoc, ← Subgroup.mem_center_iff.1 (zT_mem_center (n := n) (by omega)) a,
      ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn heA he2
  rcases Nat.mod_two_eq_zero_or_one (pat p 0 + pat p 1 + pat p 2 + pat p 3) with hp | hp
  · have key : ∀ q : Fin 2 × Fin 2 × Fin 2, (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 0 →
        q = (0, 0, 0) ∨ q = (0, 1, 1) ∨ q = (1, 0, 1) ∨ q = (1, 1, 0) := by
      decide
    rcases key p hp with rfl | rfl | rfl | rfl
    · exact absurd (omegaEl_zero hn) he1
    ·
      exfalso
      apply hlz
      rw [← zT_eq_omegaEl hn] at he
      have h2 : k * ι (zT (n := n) (by omega)) * k⁻¹ = ι (zT (by omega)) := by
        calc k * ι (zT (n := n) (by omega)) * k⁻¹ =
            k * (k⁻¹ * ι (zT (by omega)) * k) * k⁻¹ := by rw [← he]
          _ = ι (zT (by omega)) := by group
      apply hι
      rw [← h2, ← hkl]
      group
    · exact ⟨k, hkl, hk, by rw [← he, x1T_eq_omegaEl hn]⟩
    ·
      refine ⟨k * ι (uT (by omega)), ?_, fun c hc => ?_, ?_⟩
      · calc (k * ι (uT (n := n) (by omega)))⁻¹ * ι l * (k * ι (uT (by omega))) =
            (ι (uT (by omega)))⁻¹ * (k⁻¹ * ι l * k) * ι (uT (by omega)) := by group
          _ = (ι (uT (by omega)))⁻¹ * ι (zT (by omega)) * ι (uT (by omega)) := by rw [hkl]
          _ = ι ((uT (by omega))⁻¹ * zT (by omega) * uT (by omega)) := by
            rw [map_mul, map_mul, map_inv]
          _ = ι (zT (by omega)) := by rw [hzc]
      · obtain ⟨d', hd'⟩ := hk c hc
        refine ⟨(uT (by omega))⁻¹ * d' * uT (by omega), ?_⟩
        rw [map_mul, map_mul, map_inv, hd']
        group
      · calc (k * ι (uT (n := n) (by omega)))⁻¹ * ι (zT (by omega)) * (k * ι (uT (by omega))) =
            (ι (uT (by omega)))⁻¹ * (k⁻¹ * ι (zT (by omega)) * k) * ι (uT (by omega)) := by
              group
          _ = (ι (uT (by omega)))⁻¹ * ι (y1T (by omega)) * ι (uT (by omega)) := by
            rw [← he, ← y1T_eq_omegaEl hn]
          _ = ι ((uT (by omega))⁻¹ * y1T (by omega) * uT (by omega)) := by
            rw [map_mul, map_mul, map_inv]
          _ = ι (x1T (by omega)) := by
            rw [← uT_conj_x1T (by omega)]
            group
  ·
    exfalso
    obtain ⟨c', hc'⟩ := exists_conj_w1T_eq hn p hp
    apply not_conj_w1T_zT hn hι hS (k * ι c')
    rw [show k * ι c' * ι (w1T hn) * (k * ι c')⁻¹ = k * ι (c' * w1T hn * c'⁻¹) * k⁻¹ by
      rw [map_mul, map_mul, map_inv]; group, hc', he]
    group

theorem exists_pow_four_eq_zT_of_x1T (hn : 3 ≤ n) :
    ∃ c ∈ centralizer {x1T (n := n) (by omega)}, c ^ 4 = zT (by omega) := by
  refine ⟨r1T n ^ 2 ^ (n - 3), mem_centralizer_singleton_iff.2
    (A_comm (pow_mem r1T_mem_A _) (x1T_mem_A _)), ?_⟩
  rw [← pow_mul, show 2 ^ (n - 3) * 4 = 2 ^ (n - 1) by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega, r1T_pow (by omega)]

theorem lemma41 (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤)
    (hzx : ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega))) {l : L4Model n}
    (hlz : l ≠ zT (by omega)) {c : L4Model n} (hc : c ∈ centralizer {l})
    (hc4 : c ^ 4 = zT (by omega)) {g : G} (hg : g * ι l * g⁻¹ = ι (zT (by omega))) :
    ∃ h ∈ centralizer {ι (zT (n := n) (by omega))}, h * ι l * h⁻¹ = ι (x1T (by omega)) := by
  obtain ⟨k, hkl, -, hkz⟩ := exists_conj_zT_x1T_of_pow_four hn hι hS hlz hc hc4 hg
  obtain ⟨g₁, hg₁⟩ := hzx
  obtain ⟨c', hc', hc'4⟩ := exists_pow_four_eq_zT_of_x1T (n := n) hn
  obtain ⟨k', hk'x, -, hk'z⟩ := exists_conj_zT_x1T_of_pow_four hn hι hS
    (x1T_ne_zT (by omega)) hc' hc'4 hg₁
  have h1 : ι (x1T (n := n) (by omega)) = k' * ι (zT (by omega)) * k'⁻¹ := by
    rw [← hk'x]
    group
  have h2 : ι (zT (n := n) (by omega)) = k' * ι (x1T (by omega)) * k'⁻¹ := by
    rw [← hk'z]
    group
  refine ⟨k' * k⁻¹, Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
  ·
    have : k' * k⁻¹ * ι (zT (n := n) (by omega)) * (k' * k⁻¹)⁻¹ = ι (zT (by omega)) := by
      calc k' * k⁻¹ * ι (zT (n := n) (by omega)) * (k' * k⁻¹)⁻¹ =
          k' * (k⁻¹ * ι (zT (by omega)) * k) * k'⁻¹ := by group
        _ = ι (zT (by omega)) := by rw [hkz, ← h2]
    calc k' * k⁻¹ * ι (zT (n := n) (by omega)) =
        k' * k⁻¹ * ι (zT (by omega)) * (k' * k⁻¹)⁻¹ * (k' * k⁻¹) := by group
      _ = ι (zT (by omega)) * (k' * k⁻¹) := by rw [this]
  · calc k' * k⁻¹ * ι l * (k' * k⁻¹)⁻¹ = k' * (k⁻¹ * ι l * k) * k'⁻¹ := by group
      _ = ι (x1T (by omega)) := by rw [hkl, ← h1]

theorem lemma41_uT (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤)
    (hzx : ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega))) {g : G}
    (hg : g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) :
    ∃ h ∈ centralizer {ι (zT (n := n) (by omega))},
      h * ι (uT (by omega)) * h⁻¹ = ι (x1T (by omega)) := by
  obtain ⟨c, hc, hc4⟩ := exists_pow_four_eq_zT_of_piT_s23 hn (μ := uT (n := n) (by omega))
    (Or.inl (piT_uT _))
  refine lemma41 hn hι hS hzx ?_ hc hc4 hg
  intro h
  have := piT_uT (n := n) (by omega)
  rw [h, mem_A_iff.1 (zT_mem_A _)] at this
  exact absurd this (by decide)

end CFSG.LocalAnalysis.Mason73
