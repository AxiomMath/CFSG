module

public import CFSG.CGT.Stroth77.ExtensionOver
public import CFSG.CGT.Stroth77.Extension23

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {τ : StrothTypeIndex}

structure CubicBasisEquiv218 (D : StrothTypeData B τ) (hBC : B ≤ C) (d : S) (hdC : d ∈ C)
    (k : Fin 3 → ℕ) where
  e : Additive C ≃+ Torus k
  e_d : e (Additive.ofMul ⟨d, hdC⟩) = gen k 0
  e_a : e (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen k 1
  e_b : e (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen k 2

noncomputable def cubicBasisEquiv218 (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (k : Fin 3 → ℕ) (hk0 : k 0 = τ.m + 1) (hk1 : k 1 = τ.n) (hk2 : k 2 = τ.n) :
    CubicBasisEquiv218 D hBC d hdC k := by
  letI : CommGroup C := { mul_comm := comm_of_le_centralizer_of_type D hBC hC hrel }
  let dC : C := ⟨d, hdC⟩
  let aC : C := ⟨D.a, hBC D.a.2⟩
  let bC : C := ⟨D.b, hBC D.b.2⟩
  let x : (i : Fin 3) → Additive C := ![Additive.ofMul dC, Additive.ofMul aC, Additive.ofMul bC]
  have hd2C : dC ^ 2 = ⟨D.c, hBC D.c.2⟩ := by
    apply Subtype.ext
    simp [dC, pow_two, hd2]
  have hcOrder : orderOf (⟨D.c, hBC D.c.2⟩ : C) = 2 ^ τ.m := by
    rw [show (⟨D.c, hBC D.c.2⟩ : C) = Subgroup.inclusion hBC D.c from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.c,
      D.orderOf_c]
  have hcC : (⟨D.c, hBC D.c.2⟩ : C) ^ (2 ^ τ.m) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hcOrder]
  have hdN : dC ^ (2 ^ (τ.m + 1)) = 1 := by
    rw [show 2 ^ (τ.m + 1) = 2 * 2 ^ τ.m by rw [pow_succ'], pow_mul, hd2C, hcC]
  have haOrder : orderOf aC = 2 ^ (k 1) := by
    rw [show aC = Subgroup.inclusion hBC D.a from rfl]
    rw [orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.a]
    rw [D.orderOf_a, hk1]
  have hbOrder : orderOf bC = 2 ^ (k 2) := by
    rw [show bC = Subgroup.inclusion hBC D.b from rfl]
    rw [orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.b]
    rw [D.orderOf_b, hk2]
  have haN : aC ^ (2 ^ k 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, haOrder]
  have hbN : bC ^ (2 ^ k 2) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hbOrder]
  have hx : ∀ i, (2 ^ k i) • x i = 0 := by
    intro i
    fin_cases i
    · change (2 ^ k 0) • Additive.ofMul dC = 0
      rw [hk0, ← ofMul_pow, hdN]
      simp
    · change (2 ^ k 1) • Additive.ofMul aC = 0
      rw [← ofMul_pow, haN]
      simp
    · change (2 ^ k 2) • Additive.ofMul bC = 0
      rw [← ofMul_pow, hbN]
      simp
  let f : Torus k →+ Additive C := torusHomOfGens k x hx
  have hfgen : ∀ i : Fin 3, f (gen k i) = x i := fun i => torusHomOfGens_gen x hx i
  have hsurj : Function.Surjective f := by
    have hK : f.range.toSubgroup' = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro z
      have hle : Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S) ≤
          f.range.toSubgroup'.map C.subtype := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · refine Subgroup.mem_map.mpr ⟨dC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx0 : x 0 = Additive.ofMul dC := rfl
          rw [← hx0, ← hfgen 0]
          exact ⟨gen k 0, rfl⟩
        · refine Subgroup.mem_map.mpr ⟨aC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx1 : x 1 = Additive.ofMul aC := rfl
          rw [← hx1, ← hfgen 1]
          exact ⟨gen k 1, rfl⟩
        · refine Subgroup.mem_map.mpr ⟨bC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx2 : x 2 = Additive.ofMul bC := rfl
          rw [← hx2, ← hfgen 2]
          exact ⟨gen k 2, rfl⟩
      have hC' : C ≤ f.range.toSubgroup'.map C.subtype :=
        calc C = Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S) :=
              (closure_eq_of_sq_of_type D hBC hrel hdC hdB hd2).symm
          _ ≤ f.range.toSubgroup'.map C.subtype := hle
      have hz : (z : S) ∈ f.range.toSubgroup'.map C.subtype := hC' z.2
      rcases Subgroup.mem_map.mp hz with ⟨k', hk', hks⟩
      have hkz : k' = z := Subtype.ext hks
      simpa [hkz] using hk'
    have hrange : f.range = ⊤ := by
      apply AddSubgroup.toSubgroup'.injective
      simpa using hK
    exact AddMonoidHom.range_eq_top.mp hrange
  have hcardT : Nat.card (Torus k) = 2 ^ (k 0 + k 1 + k 2) := natCard_torus k
  have hcardC : Nat.card C = 2 ^ (k 0 + k 1 + k 2) := by
    rw [hrel, D.card_eq, hk0, hk1, hk2]
    rw [show τ.m + 1 + τ.n + τ.n = (τ.m + τ.n + τ.n) + 1 by ring, pow_succ]
    ring
  have heq : Nat.card (Torus k) = Nat.card (Additive C) := by
    rw [hcardT, ← Nat.card_congr Additive.ofMul, hcardC]
  have hbij : Function.Bijective f :=
    hsurj.bijective_of_nat_card_le (le_of_eq heq)
  let e : Additive C ≃+ Torus k := (AddEquiv.ofBijective f hbij).symm
  have ed : e (Additive.ofMul ⟨d, hdC⟩) = gen k 0 := by
    show (AddEquiv.ofBijective f hbij).symm (Additive.ofMul ⟨d, hdC⟩) = gen k 0
    rw [show Additive.ofMul ⟨d, hdC⟩ = x 0 from rfl, ← hfgen 0]
    exact AddEquiv.symm_apply_apply _ _
  have ea : e (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen k 1 := by
    show (AddEquiv.ofBijective f hbij).symm (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen k 1
    rw [show Additive.ofMul ⟨D.a, hBC D.a.2⟩ = x 1 from rfl, ← hfgen 1]
    exact AddEquiv.symm_apply_apply _ _
  have eb : e (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen k 2 := by
    show (AddEquiv.ofBijective f hbij).symm (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen k 2
    rw [show Additive.ofMul ⟨D.b, hBC D.b.2⟩ = x 2 from rfl, ← hfgen 2]
    exact AddEquiv.symm_apply_apply _ _
  exact ⟨e, ed, ea, eb⟩

theorem eq_c_zpow_mul_a_b218 (D : StrothTypeData B τ) {β : B} {i j l : ℤ}
    (h : D.ec β = i • gen τ.k 0 + j • gen τ.k 1 + l • gen τ.k 2) :
    β = D.c ^ i * D.a ^ j * D.b ^ l := by
  apply D.ec_injective
  rw [h, D.ec_mul, D.ec_mul, D.ec_zpow, D.ec_zpow, D.ec_zpow, D.ec_c, D.ec_a, D.ec_b]

theorem E_inclusion218 (D : StrothTypeData B τ) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) (hd2 : d * d = (D.c : S))
    {k : Fin 3 → ℕ} (E : CubicBasisEquiv218 D hBC d hdC k) (β : B) {i j l : ℤ}
    (hβ : D.ec β = i • gen τ.k 0 + j • gen τ.k 1 + l • gen τ.k 2) :
    E.e (Additive.ofMul (⟨β, hBC β.2⟩ : C)) =
      (2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  have hβ' : β = D.c ^ i * D.a ^ j * D.b ^ l := eq_c_zpow_mul_a_b218 D hβ
  have hdc : (⟨D.c, hBC D.c.2⟩ : C) = (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ :=
    (dC_sq_of_type D hBC hdC hd2).symm
  have hcimg : E.e (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = (2 : ℤ) • gen k 0 := by
    rw [hdc, ofMul_mul, map_add, E.e_d]
    rw [two_zsmul]
  have hci : ∀ n : ℤ, E.e (Additive.ofMul (⟨D.c ^ n, hBC (D.c ^ n).2⟩ : C)) =
      n • ((2 : ℤ) • gen k 0) := by
    intro n
    have hsub : (⟨D.c ^ n, hBC (D.c ^ n).2⟩ : C) = ⟨D.c, hBC D.c.2⟩ ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, hcimg]
  have hai : ∀ n : ℤ, E.e (Additive.ofMul (⟨D.a ^ n, hBC (D.a ^ n).2⟩ : C)) =
      n • gen k 1 := by
    intro n
    have hsub : (⟨D.a ^ n, hBC (D.a ^ n).2⟩ : C) = ⟨D.a, hBC D.a.2⟩ ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, E.e_a]
  have hbi : ∀ n : ℤ, E.e (Additive.ofMul (⟨D.b ^ n, hBC (D.b ^ n).2⟩ : C)) =
      n • gen k 2 := by
    intro n
    have hsub : (⟨D.b ^ n, hBC (D.b ^ n).2⟩ : C) = ⟨D.b, hBC D.b.2⟩ ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, E.e_b]
  have hprod : (⟨β, hBC β.2⟩ : C) = ⟨D.c ^ i, hBC (D.c ^ i).2⟩ *
      ⟨D.a ^ j, hBC (D.a ^ j).2⟩ * ⟨D.b ^ l, hBC (D.b ^ l).2⟩ := by
    apply Subtype.ext
    simp [hβ']
  rw [hprod]
  rw [show Additive.ofMul (⟨D.c ^ i, hBC (D.c ^ i).2⟩ * ⟨D.a ^ j, hBC (D.a ^ j).2⟩ *
      ⟨D.b ^ l, hBC (D.b ^ l).2⟩ : C) =
      Additive.ofMul ⟨D.c ^ i, hBC (D.c ^ i).2⟩ + Additive.ofMul ⟨D.a ^ j, hBC (D.a ^ j).2⟩ +
        Additive.ofMul ⟨D.b ^ l, hBC (D.b ^ l).2⟩ by rw [ofMul_mul, ofMul_mul]]
  rw [map_add, map_add, hci, hai, hbi, smul_smul]
  module

theorem E_conj_d218 (D : StrothTypeData B τ) (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) {k : Fin 3 → ℕ} (E : CubicBasisEquiv218 D hBC d hdC k) {g : S}
    (hgC : g ∈ Subgroup.normalizer C)
    {b : B} (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    {i j l : ℤ} (h : D.ec b = i • gen τ.k 0 + j • gen τ.k 1 + l • gen τ.k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨d, hdC⟩ : C))) =
      (1 + 2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  rw [hb, ofMul_mul, map_add, E.e_d]
  have hsub : Additive.ofMul ((Subgroup.inclusion hBC) b) = Additive.ofMul (⟨b, hBC b.2⟩ : C) :=
    congrArg Additive.ofMul rfl
  rw [hsub, E_inclusion218 D hBC hdC hd2 E b h]
  module

theorem E_conj_inclusion218 (D : StrothTypeData B τ) (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) {k : Fin 3 → ℕ} (E : CubicBasisEquiv218 D hBC d hdC k) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) (x : B)
    {i j l : ℤ} (h : D.ec (conjBy hgB x) = i • gen τ.k 0 + j • gen τ.k 1 + l • gen τ.k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨x, hBC x.2⟩ : C))) =
      (2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  have hsub : conjBy hgC (⟨x, hBC x.2⟩ : C) =
      (⟨conjBy hgB x, hBC (conjBy hgB x).2⟩ : C) := Subtype.ext rfl
  rw [hsub]
  exact E_inclusion218 D hBC hdC hd2 E _ h

theorem hasStrothTypeOver_of_images218 (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (τ' : StrothTypeIndex)
    (E : CubicBasisEquiv218 D hBC d hdC τ'.k)
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L)
      (![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩] j))) = τ'.action.φuv (gen τ'.k j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L)
      (![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩] j))) = τ'.action.φt (gen τ'.k j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L)
      (![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩] j))) = τ'.action.φu (gen τ'.k j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L)
      (![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩] j))) = τ'.action.φρ (gen τ'.k j)) :
    HasStrothTypeOver D C τ' := by
  refine ⟨⟨E.e, D.uv, D.t, D.u, D.ρ, D.uv_sq, D.t_sq, D.uv_comm_t, D.rho_cube, D.u_sq,
    D.u_rho, D.uv_rho, D.t_rho, D.uv_comm_u, D.t_u, hL D.uv_mem_L, hL D.t_mem_L,
    hL D.u_mem_L, hL D.ρ_mem_L,
    conj_eq_of_generator_images (hL D.uv_mem_L) E.e τ'.action.φuv E.e_d E.e_a E.e_b
      (huv 0) (huv 1) (huv 2),
    conj_eq_of_generator_images (hL D.t_mem_L) E.e τ'.action.φt E.e_d E.e_a E.e_b
      (ht 0) (ht 1) (ht 2),
    conj_eq_of_generator_images (hL D.u_mem_L) E.e τ'.action.φu E.e_d E.e_a E.e_b
      (hu 0) (hu 1) (hu 2),
    conj_eq_of_generator_images (hL D.ρ_mem_L) E.e τ'.action.φρ E.e_d E.e_a E.e_b
      (hρ 0) (hρ 1) (hρ 2)⟩, rfl, rfl, rfl, rfl⟩

theorem hasStrothType_of_images218 (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (τ' : StrothTypeIndex)
    (E : CubicBasisEquiv218 D hBC d hdC τ'.k)
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L)
      (![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩] j))) = τ'.action.φuv (gen τ'.k j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L)
      (![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩] j))) = τ'.action.φt (gen τ'.k j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L)
      (![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩] j))) = τ'.action.φu (gen τ'.k j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L)
      (![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩] j))) = τ'.action.φρ (gen τ'.k j)) :
    HasStrothType C τ' :=
  (hasStrothTypeOver_of_images218 D hBC hL hdC τ' E huv ht hu hρ).hasStrothType

end CFSG.CGT.Stroth77
