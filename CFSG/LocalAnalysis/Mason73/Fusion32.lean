module

public import CFSG.LocalAnalysis.Mason73.Complement
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.ABGLocalTools CFSG.ComponentClassification Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem card_range_inf_centralizer {ι : L4Model n →* G} (hι : Function.Injective ι)
    (t : L4Model n) :
    Nat.card (ι.range ⊓ centralizer {ι t} : Subgroup G) = Nat.card (centralizer {t}) := by
  have h : (ι.range ⊓ centralizer {ι t} : Subgroup G) = (centralizer {t}).map ι := by
    ext x
    simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, hι (by rw [map_mul, map_mul, hy]), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩
  rw [h, Subgroup.card_map_of_injective hι]

theorem exists_pow_of_conj_extremal (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤) {a b : L4Model n} (ha : a ∈ A n)
    (hb : IsSylowOf 2 (ι.range ⊓ centralizer {ι b}) (centralizer {ι b})) {g : G}
    (hg : g * ι a * g⁻¹ = ι b) {r : L4Model n} (hr : r ∈ A n) (hbr : b = r ^ 2 ^ (n - 1)) :
    ∃ s ∈ A n, a = s ^ 2 ^ (n - 1) := by
  obtain ⟨k, hka, hk⟩ := GHarris.exists_conj_extremal (S := ι.range) hS.isPGroup hb
    (u := ι a) (h := g) (by rw [← hg]; group)
  have hAk : ∀ x ∈ A n, ∃ y : L4Model n, ι y = k⁻¹ * ι x * k := by
    intro x hx
    have hmem : ι x ∈ (ι.range ⊓ centralizer {ι a} : Subgroup G) := by
      refine Subgroup.mem_inf.2 ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← map_mul, ← map_mul, A_comm hx ha]
    obtain ⟨⟨y, hy⟩, -⟩ := Subgroup.mem_inf.1 (hk _ hmem)
    exact ⟨y, hy⟩
  set M : Subgroup G := ((A n).map ι).map (MulAut.conj k⁻¹).toMonoidHom with hM
  have hmemM : ∀ w : G, w ∈ M ↔ ∃ x ∈ A n, k⁻¹ * ι x * k = w := by
    intro w
    simp only [hM, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ι x, ⟨x, hx, rfl⟩, rfl⟩
  have hMle : M ≤ ι.range := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := (hmemM w).1 hw
    obtain ⟨y, hy⟩ := hAk x hx
    exact ⟨y, hy⟩
  set A' : Subgroup (L4Model n) := M.comap ι with hA'
  have hcardM : Nat.card M = Nat.card (A n) := by
    rw [hM, Subgroup.card_map_of_injective (MulEquiv.injective _),
      Subgroup.card_map_of_injective hι]
  have hcard : Nat.card A' = Nat.card (A n) := by
    rw [← hcardM, ← Subgroup.card_map_of_injective hι, hA', Subgroup.map_comap_eq_self hMle]
  have hcomm : ∀ p ∈ A', ∀ q ∈ A', p * q = q * p := by
    intro p hp q hq
    obtain ⟨x, hx, hpx⟩ := (hmemM _).1 (Subgroup.mem_comap.1 hp)
    obtain ⟨y, hy, hqy⟩ := (hmemM _).1 (Subgroup.mem_comap.1 hq)
    apply hι
    rw [map_mul, map_mul, ← hpx, ← hqy]
    calc k⁻¹ * ι x * k * (k⁻¹ * ι y * k) = k⁻¹ * ι (x * y) * k := by rw [map_mul]; group
      _ = k⁻¹ * ι (y * x) * k := by rw [A_comm hx hy]
      _ = k⁻¹ * ι y * k * (k⁻¹ * ι x * k) := by rw [map_mul]; group
  have hA'eq : A' = A n := eq_A_of_comm hn hcomm (by rw [hcard, card_A (by omega)])
  have hrA' : r ∈ A' := hA'eq ▸ hr
  obtain ⟨x, hx, hxr⟩ := (hmemM _).1 (Subgroup.mem_comap.1 hrA')
  refine ⟨x, hx, hι ?_⟩
  have h1 : k⁻¹ * ι a * k = k⁻¹ * ι x ^ 2 ^ (n - 1) * k := by
    rw [hka, hbr, map_pow, ← hxr, GHarris.conj_pow_inv]
  rw [map_pow]
  simpa using h1

theorem isSylowOf_zT (hn : 3 ≤ n) {ι : L4Model n →* G} (hS : IsSylowOf 2 ι.range ⊤) :
    IsSylowOf 2 (ι.range ⊓ centralizer {ι (zT (by omega))})
      (centralizer {ι (zT (by omega))}) := by
  refine GHarris.isSylowOf_inf_centralizer_of_le hS ?_
  rintro _ ⟨y, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    (Subgroup.mem_center_iff.1 (zT_mem_center (n := n) (by omega)) y)]

theorem r1T_mem_A : r1T n ∈ A n := mem_A_of_one _

theorem not_conj_w1T_zT (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) (g : G) : g * ι (w1T hn) * g⁻¹ ≠ ι (zT (by omega)) := by
  intro hg
  obtain ⟨s, hs, hws⟩ := exists_pow_of_conj_extremal hn hι hS (w1T_mem_A hn) (isSylowOf_zT hn hS)
    hg r1T_mem_A (zT_eq_pow (by omega))
  exact pow_ne_w1T hn hs hws.symm

theorem card_centralizer_y1T (hn : 3 ≤ n) :
    Nat.card (centralizer {y1T (n := n) (by omega)}) = 2 ^ (3 * n) := by
  rw [y1T_eq_omegaEl hn, card_centralizer_omegaEl hn,
    show Nat.card (stabP (1, 1, 0)) = 4 by rw [Nat.card_eq_fintype_card]; decide,
    show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  congr 1
  omega

theorem isSylowOf_x1T (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) (hxz : ∀ g : G, g * ι (x1T (by omega)) * g⁻¹ ≠ ι (zT (by omega))) :
    IsSylowOf 2 (ι.range ⊓ centralizer {ι (x1T (by omega))})
      (centralizer {ι (x1T (by omega))}) := by
  refine GHarris.isSylowOf_of_card_le hS ⟨_, rfl⟩ fun g hg => ?_
  obtain ⟨l, hl⟩ := hg
  rw [← hl, card_range_inf_centralizer hι, card_range_inf_centralizer hι,
    card_centralizer_x1T hn]
  have hx2 : x1T (n := n) (by omega) * x1T (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_x1T (by omega)]
  have hl2 : l * l = 1 := by
    apply hι
    rw [map_mul, hl, map_one]
    calc g⁻¹ * ι (x1T (by omega)) * g * (g⁻¹ * ι (x1T (by omega)) * g)
        = g⁻¹ * ι (x1T (by omega) * x1T (by omega)) * g := by rw [map_mul]; group
      _ = 1 := by rw [hx2, map_one]; group
  have hl1 : l ≠ 1 := by
    rintro rfl
    have : ι (x1T (n := n) (by omega)) = 1 := by
      have h := congrArg (fun w => g * w * g⁻¹) hl
      simp only [map_one, mul_one, mul_inv_cancel] at h
      rw [show g * (g⁻¹ * ι (x1T (by omega)) * g) * g⁻¹ = ι (x1T (by omega)) by group] at h
      exact h.symm
    have h1 := orderOf_x1T (n := n) (by omega)
    rw [← orderOf_injective ι hι, this, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hlz : l ≠ zT (by omega) := by
    rintro rfl
    apply hxz g⁻¹
    rw [hl, inv_inv]
  by_cases hlx : l = x1T (by omega)
  · rw [hlx, card_centralizer_x1T hn]
  by_cases hly : l = y1T (by omega)
  · rw [hly, card_centralizer_y1T hn]
  exact (card_centralizer_le hn hl1 hl2 hlz hlx hly).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem not_conj_w1T_x1T (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) (g : G) : g * ι (w1T hn) * g⁻¹ ≠ ι (x1T (by omega)) := by
  intro hg
  by_cases hxz : ∃ g' : G, g' * ι (x1T (by omega)) * g'⁻¹ = ι (zT (by omega))
  · obtain ⟨g', hg'⟩ := hxz
    apply not_conj_w1T_zT hn hι hS (g' * g)
    rw [← hg', ← hg]
    group
  · push_neg at hxz
    obtain ⟨s, hs, hws⟩ := exists_pow_of_conj_extremal hn hι hS (w1T_mem_A hn)
      (isSylowOf_x1T hn hι hS hxz) hg xT_mem_A (x1T_eq_pow (by omega))
    exact pow_ne_w1T hn hs hws.symm

end CFSG.LocalAnalysis.Mason73
