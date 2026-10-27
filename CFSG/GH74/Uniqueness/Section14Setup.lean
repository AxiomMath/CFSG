module

public import CFSG.GH74.Uniqueness.Section14P
public import CFSG.GH74.Uniqueness.Bender.SuzukiAut
public import CFSG.GH74.Uniqueness.Section14Card
public import CFSG.GH74.Uniqueness.Section14Lem42

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Fact2

theorem fact2_mul_odd {a b : ℕ} (ha : a ≠ 0) (hb : Odd b) :
    (a * b).factorization 2 = a.factorization 2 := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  rw [Nat.factorization_mul ha hb0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hb)
      (even_iff_two_dvd.mpr h2)), add_zero]

theorem fact2_two_pow (k : ℕ) : (2 ^ k).factorization 2 = k := by
  rw [Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem fact2_two_pow_mul (k : ℕ) {a : ℕ} (ha : a ≠ 0) :
    (2 ^ k * a).factorization 2 = k + a.factorization 2 := by
  rw [Nat.factorization_mul (by positivity) ha, Finsupp.add_apply, fact2_two_pow]

end Fact2

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

variable {c : Ctx12 Z M} {n : ℕ} {Q : Sylow 2 ↥c.L} {U : Subgroup X}

theorem L_inf_J (h : LData c n 2) : c.L ⊓ centralizer (c.L : Set X) = ⊥ :=
  inf_centralizer_eq_bot_of_center c.L h.center_eq_bot

theorem D_le_N (h : LData c n 2) : c.D ≤ normalizer (c.L : Set X) := by
  intro d hd
  have : d ∈ ((normalizer (c.L : Set X) : Subgroup X) : Set X) := by
    rw [h.normalizer_eq]
    exact ⟨1, c.L.one_mem, d, hd, one_mul d⟩
  exact this

theorem NL_eq (h : LData c n 2) :
    ∀ g ∈ normalizer (c.L : Set X), ∃ l ∈ c.L, ∃ d ∈ c.D, g = l * d := by
  intro g hg
  have : g ∈ ((normalizer (c.L : Set X) : Subgroup X) : Set X) := hg
  rw [h.normalizer_eq] at this
  obtain ⟨l, hl, d, hd, rfl⟩ := this
  exact ⟨l, hl, d, hd, rfl⟩

theorem not_mem_Z_of_mem_J (S : ZDSetup X Z M) (h : LData c n 2) {v : X}
    (hv : v ∈ centralizer (c.L : Set X)) : v ∉ Z := by
  intro hvZ
  have hvM : v ∈ M := S.prodDisc.centralizer_le_of_mem c.hz c.hzM
    (mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hv) c.z c.z_mem_L).symm)
  have hvMo : v ∈ (zHull Z M : Set X) \ {1} := by
    rw [← h.zM_eq]
    exact ⟨hvZ, hvM⟩
  have hvL : v ∈ c.L := h.m_le hvMo.1
  have h1 : v ∈ c.L ⊓ centralizer (c.L : Set X) := mem_inf.mpr ⟨hvL, hv⟩
  rw [L_inf_J h, mem_bot] at h1
  exact hvMo.2 h1

theorem P_inf_U (h : LData c n 2) (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    pGrp c Q ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [← L_inf_J h]
  exact mem_inf.mpr ⟨P_le_L (mem_inf.mp hx).1, hU.le (mem_inf.mp hx).2⟩

theorem P_comm_U (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    ∀ x ∈ pGrp c Q, ∀ u ∈ U, x * u = u * x := fun x hx _ hu =>
  (mem_centralizer_iff.mp (hU.le hu)) x (P_le_L hx)

theorem U_le_normalizer_P (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    U ≤ normalizer (pGrp c Q : Set X) := by
  intro u hu
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro x hx
  exact P_comm_U hU x hx u hu

theorem mem_T_iff (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) {x : X} :
    x ∈ pGrp c Q ⊔ U ↔ ∃ p ∈ pGrp c Q, ∃ u ∈ U, x = p * u := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ (U_le_normalizer_P hU)]
  constructor
  · rintro ⟨p, hp, u, hu, rfl⟩
    exact ⟨p, hp, u, hu, rfl⟩
  · rintro ⟨p, hp, u, hu, rfl⟩
    exact ⟨p, hp, u, hu, rfl⟩

theorem card_T (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    Nat.card ↥(pGrp c Q ⊔ U) = 2 ^ (2 * n) * Nat.card U := by
  rw [Bender.card_sup_eq_mul_of_le_normalizer (U_le_normalizer_P hU) (P_inf_U h hU),
    card_P S h hQ]

theorem isPGroup_T (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    IsPGroup 2 ↥(pGrp c Q ⊔ U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hU.isPGroup.exists_card_eq
  apply IsPGroup.of_card (n := 2 * n + k)
  rw [card_T S h hQ hU, hk, pow_add]

theorem T_le_NL (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    pGrp c Q ⊔ U ≤ normalizer (c.L : Set X) :=
  sup_le (P_le_L.trans le_normalizer) (hU.le.trans (centralizer_le_normalizer _))

theorem card_U_eq (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    Nat.card U = 2 ^ (Nat.card (centralizer (c.L : Set X))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hU.card_eq

theorem T_sylow (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    ABGLocalTools.IsSylowOf 2 (pGrp c Q ⊔ U) (normalizer (c.L : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply ABGLocalTools.isSylowOf_of_card (T_le_NL hU)
  obtain ⟨d, hd, -, hdodd⟩ := card_normalizer_L h
  have hJ0 : Nat.card (centralizer (c.L : Set X)) ≠ 0 := Nat.card_pos.ne'
  have hL : Nat.card c.L = 2 ^ (2 * n) * ((2 ^ (2 * n) + 1) * (2 ^ n - 1)) := by
    rw [h.bender.card_eq, ← pow_mul, mul_comm n 2]
    ring
  have hq1 : Odd (2 ^ n - 1) := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : Even (2 ^ n) := (Nat.even_pow' (by have := (n_odd h).2; omega)).mpr even_two
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  have hq2 : Odd (2 ^ (2 * n) + 1) := by
    have h2 : Even (2 ^ (2 * n)) := (Nat.even_pow' (by have := (n_odd h).2; omega)).mpr even_two
    exact h2.add_one
  have hfac : (Nat.card (normalizer (c.L : Set X))).factorization 2 =
      2 * n + (Nat.card (centralizer (c.L : Set X))).factorization 2 := by
    have hodd := (hq2.mul hq1).mul hdodd
    rw [hd, hL, show Nat.card (centralizer (c.L : Set X)) * (2 ^ (2 * n) * ((2 ^ (2 * n) + 1) *
        (2 ^ n - 1))) * d = 2 ^ (2 * n) * (Nat.card (centralizer (c.L : Set X)) *
        ((2 ^ (2 * n) + 1) * (2 ^ n - 1) * d)) by ring]
    rw [fact2_two_pow_mul _ (Nat.mul_ne_zero hJ0 hodd.pos.ne'), fact2_mul_odd hJ0 hodd]
  rw [card_T S h hQ hU, hfac, pow_add, card_U_eq hU]

theorem U_sylow_D (h : LData c n 2)
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    ABGLocalTools.IsSylowOf 2 U c.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply ABGLocalTools.isSylowOf_of_card (hU.le.trans h.centralizer_le)
  obtain ⟨d, hd, -, hdodd⟩ := card_D h
  have hq1 : Odd (2 ^ n - 1) := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : Even (2 ^ n) := (Nat.even_pow' (by have := (n_odd h).2; omega)).mpr even_two
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  have hJ0 : Nat.card (centralizer (c.L : Set X)) ≠ 0 := Nat.card_pos.ne'
  rw [hd, card_U_eq hU, show (2 ^ n - 1) * Nat.card (centralizer (c.L : Set X)) * d =
    Nat.card (centralizer (c.L : Set X)) * ((2 ^ n - 1) * d) by ring,
    fact2_mul_odd hJ0 (hq1.mul hdodd)]

theorem two_part
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    2 ^ (Nat.card X).factorization 2 = 2 ^ n * Nat.card ↥(pGrp c Q ⊔ U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : (Nat.card X).factorization 2 = 3 * n + (Nat.card c.D).factorization 2 := by
    rcases h12.l1210 c n 2 h with ⟨h1, -⟩ | ⟨-, -, -, h2⟩ | ⟨h1, -⟩
    · omega
    · exact h2
    · omega
  have hUD := (U_sylow_D h hU).card_eq
  rw [card_T S h hQ hU, hX, hUD, pow_add, ← mul_assoc, ← pow_add]
  ring_nf

theorem cent_Mo_NL (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    centralizer (zHull Z M : Set X) ⊓ normalizer (c.L : Set X) =
      pGrp c Q ⊔ centralizer (c.L : Set X) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgC, hgN⟩ := mem_inf.mp hg
    set σ := conjAut c.L ⟨g, hgN⟩
    have hσ : ∀ z ∈ Bender.rootCenter (Q : Subgroup ↥c.L), σ z = z := by
      intro z hz
      apply Subtype.ext
      have hzMo : (z : X) ∈ zHull Z M := by
        rw [Mo_eq S h hQ]
        exact mem_map_of_mem _ hz
      have := (mem_centralizer_iff.mp hgC) z hzMo
      change g * z * g⁻¹ = z
      rw [← this, mul_inv_cancel_right]
    obtain ⟨r, hr, hσr⟩ := h.bender.exists_eq_conj_of_centralizes_center_suzuki Q σ hσ
    have hj := mul_inv_mem_centralizer_of_conjAut_eq c.L ⟨g, hgN⟩ r hσr
    have : g = (g * (r : X)⁻¹) * r := by group
    rw [this]
    exact mul_mem (mem_sup_right hj) (mem_sup_left (mem_map_of_mem _ hr))
  · refine sup_le (fun x hx => mem_inf.mpr ⟨?_, P_le_L.trans le_normalizer hx⟩)
      (fun x hx => mem_inf.mpr ⟨?_, centralizer_le_normalizer _ hx⟩)
    · rw [mem_centralizer_iff]
      intro m hm
      exact (Mo_central S h hQ x hx m hm).symm
    · rw [mem_centralizer_iff]
      intro m hm
      exact (mem_centralizer_iff.mp hx) m (h.m_le hm)

end Sec14

end CFSG.GH74.Uniqueness
