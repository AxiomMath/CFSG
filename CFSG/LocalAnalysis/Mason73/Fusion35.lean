module

public import CFSG.LocalAnalysis.Mason73.Fusion32

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem pow_four_mem_A (d : L4Model n) : d ^ 4 ∈ A n := by
  rw [mem_A_iff, map_pow]
  have key : ∀ π : Perm (Fin 4), π ∈ Fin81.R0 → π ^ 4 = 1 := by decide
  exact Subtype.ext (key _ (piT d).2)

theorem uT_conj_x1T (hn : 2 ≤ n) :
    uT (n := n) (by omega) * x1T (by omega) * (uT (by omega))⁻¹ = y1T (by omega) := by
  rw [uT, x1T_eq, el_conj hn, y1T_eq, el_eq_el_iff hn, pv_hv,
    hv_sub_hv_isConst_iff (by omega)]
  exact ⟨rfl, by decide⟩

theorem exists_conj_w1T_eq (hn : 3 ≤ n) (p : Fin 2 × Fin 2 × Fin 2)
    (hp : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 1) :
    ∃ c : L4Model n, c * w1T hn * c⁻¹ = omegaEl hn p := by
  have key : ∀ q : Fin 2 × Fin 2 × Fin 2, (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 1 →
      ∃ π ∈ ({1, s01, tP, tP * s01} : Finset Fin81.R0), ∀ i j : Fin 4,
        (pat q i + ![1, 0, 0, 0] ((π : Perm (Fin 4))⁻¹ j)) % 2 =
          (pat q j + ![1, 0, 0, 0] ((π : Perm (Fin 4))⁻¹ i)) % 2 := by
    decide
  obtain ⟨π, -, hπ⟩ := key p hp
  obtain ⟨d, hd⟩ := exists_detSum (n := n) π
  refine ⟨el d π hd, ?_⟩
  rw [w1T, el_conj (by omega), omegaEl, dif_neg (by omega), el_eq_el_iff (by omega)]
  refine ⟨rfl, ?_⟩
  have : wv n (pat p) - pv (π : Perm (Fin 4)) (wv n ![1, 0, 0, 0]) =
      hv n (pat p) - hv n (fun i => ![1, 0, 0, 0] ((π : Perm (Fin 4))⁻¹ i)) := by
    funext i
    simp only [Pi.sub_apply, pv, wv, hv]
    ring
  rw [this, hv_sub_hv_isConst_iff (by omega)]
  exact hπ

theorem conj_x1T_of_conj_mem_A (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) {e : L4Model n} (he : e ∈ A n) (he2 : e * e = 1)
    (he1 : e ≠ 1) (hez : e ≠ zT (by omega)) {k : G} (hk : k * ι e * k⁻¹ = ι (zT (by omega))) :
    ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega)) := by
  obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn he he2
  rcases Nat.mod_two_eq_zero_or_one (pat p 0 + pat p 1 + pat p 2 + pat p 3) with hp | hp
  · have key : ∀ q : Fin 2 × Fin 2 × Fin 2, (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 0 →
        q = (0, 0, 0) ∨ q = (0, 1, 1) ∨ q = (1, 0, 1) ∨ q = (1, 1, 0) := by
      decide
    rcases key p hp with rfl | rfl | rfl | rfl
    · exact absurd (omegaEl_zero hn) he1
    · exact absurd (zT_eq_omegaEl hn).symm hez
    · exact ⟨k, by rw [x1T_eq_omegaEl hn]; exact hk⟩
    · refine ⟨k * ι (uT (by omega)), ?_⟩
      rw [← hk, ← y1T_eq_omegaEl hn, ← uT_conj_x1T (by omega), map_mul, map_mul, map_inv]
      group
  · obtain ⟨c, hc⟩ := exists_conj_w1T_eq hn p hp
    exfalso
    apply not_conj_w1T_zT hn hι hS (k * ι c)
    rw [← hk, ← hc, map_mul, map_mul, map_inv]
    group

theorem conj_x1T_of_fourth_power (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) {l : L4Model n} (hl : l ∉ A n) {c : L4Model n}
    (hc : c ∈ centralizer {l}) (hc4 : c ^ 4 = zT (by omega)) {g : G}
    (hg : g * ι l * g⁻¹ = ι (zT (by omega))) :
    ∃ g' : G, g' * ι (x1T (by omega)) * g'⁻¹ = ι (zT (by omega)) := by
  obtain ⟨k, hkl, hk⟩ := GHarris.exists_conj_extremal (S := ι.range) hS.isPGroup
    (isSylowOf_zT hn hS) (u := ι l) (h := g) (by rw [← hg]; group)
  have hcl : ι c ∈ (ι.range ⊓ centralizer {ι l} : Subgroup G) := by
    refine Subgroup.mem_inf.2 ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hc]
  obtain ⟨⟨d, hd⟩, -⟩ := Subgroup.mem_inf.1 (hk _ hcl)
  have hzk : k⁻¹ * ι (zT (by omega)) * k = ι (d ^ 4) := by
    rw [map_pow, hd, ← hc4, map_pow, GHarris.conj_pow_inv]
  have hz2 : zT (n := n) (by omega) * zT (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zT (by omega)]
  have he2 : d ^ 4 * d ^ 4 = 1 := by
    apply hι
    rw [map_mul, ← hzk, map_one]
    calc k⁻¹ * ι (zT (by omega)) * k * (k⁻¹ * ι (zT (by omega)) * k)
        = k⁻¹ * ι (zT (by omega) * zT (by omega)) * k := by rw [map_mul]; group
      _ = 1 := by rw [hz2, map_one]; group
  have he1 : d ^ 4 ≠ 1 := by
    intro h
    rw [h, map_one] at hzk
    have : ι (zT (n := n) (by omega)) = 1 := by
      have h' := congrArg (fun w => k * w * k⁻¹) hzk
      simp only [mul_one, mul_inv_cancel] at h'
      rw [show k * (k⁻¹ * ι (zT (by omega)) * k) * k⁻¹ = ι (zT (by omega)) by group] at h'
      exact h'
    have h1 := orderOf_zT (n := n) (by omega)
    rw [← orderOf_injective ι hι, this, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hez : d ^ 4 ≠ zT (by omega) := by
    intro h
    apply hl
    have : ι l = ι (zT (n := n) (by omega)) := by
      have h1 : k⁻¹ * ι l * k = k⁻¹ * ι (zT (by omega)) * k := by rw [hkl, hzk, h]
      simpa using h1
    rw [hι this]
    exact zT_mem_A _
  exact conj_x1T_of_conj_mem_A hn hι hS (pow_four_mem_A d) he2 he1 hez
    (k := k) (by rw [← hzk]; group)

end CFSG.LocalAnalysis.Mason73
