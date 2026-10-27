module

public import CFSG.CGT.PushingUpLit.LIT.A4.Cent

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly

section Struct

variable {G : Type} [Group G]

theorem zpowers_cube {a : G} (ha : a ^ 3 = 1) {z : G} (hz : z ∈ Subgroup.zpowers a) :
    z ^ 3 = 1 := by
  obtain ⟨s, rfl⟩ := hz
  calc (a ^ s) ^ 3 = (a ^ 3) ^ s := by group
    _ = 1 := by rw [ha, one_zpow]

theorem zpow_eq_pow_lt_three {g : G} (hg : g ^ 3 = 1) (t : ℤ) :
    ∃ r : ℕ, r < 3 ∧ g ^ t = g ^ r := by
  refine ⟨(t % 3).toNat, by omega, ?_⟩
  have h2 : (((t % 3).toNat : ℕ) : ℤ) = t % 3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg t (by norm_num))
  rw [← zpow_natCast, h2]
  calc g ^ t = g ^ (3 * (t / 3) + t % 3) := by rw [Int.mul_ediv_add_emod]
    _ = (g ^ 3) ^ (t / 3) * g ^ (t % 3) := by group
    _ = g ^ (t % 3) := by rw [hg, one_zpow, one_mul]

theorem centralizes_of_fixes {X : Subgroup G} {a : G} (hb : SolD3.Blk3 X a) {k : G}
    (hk : conjSub k X = X)
    (hfix : ∀ y ∈ pCoreOf 2 X, k * (y * a * y⁻¹) * k⁻¹ ∈ Subgroup.zpowers (y * a * y⁻¹)) :
    ∀ x ∈ X, k * x = x * k := by
  have hVk : conjSub k (pCoreOf 2 X) = pCoreOf 2 X := by
    have := pCoreOf_conj_eq k X
    rw [hk] at this
    exact this.symm
  have hV1 : ∀ y ∈ pCoreOf 2 X, k * y * k⁻¹ ∈ pCoreOf 2 X := fun y hy => by
    have := conj_mem_conjSub (g := k) hy
    rwa [hVk] at this
  have hV2 : ∀ y ∈ pCoreOf 2 X, k⁻¹ * y * k ∈ pCoreOf 2 X := fun y hy => by
    have : y ∈ conjSub k (pCoreOf 2 X) := by rw [hVk]; exact hy
    exact mem_conjSub_iff.1 this
  have hcX : k * a * k⁻¹ ∈ X := by
    have := conj_mem_conjSub (g := k) hb.mem
    rwa [hk] at this
  have hcA : k * a * k⁻¹ ∈ Subgroup.zpowers a := by
    have := hfix 1 (pCoreOf 2 X).one_mem
    simpa using this
  have hAfix : ∀ y ∈ pCoreOf 2 X, a * y * a⁻¹ = y → y = 1 := hb.fix
  have hA : ∀ y ∈ pCoreOf 2 X, k * y * k⁻¹ = y := by
    intro y hy
    have hy'V : k * y * k⁻¹ ∈ pCoreOf 2 X := hV1 y hy
    have huV : y⁻¹ * (k * y * k⁻¹) ∈ pCoreOf 2 X :=
      (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hy) hy'V
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 (hfix y hy)
    have e1 : k * (y * a * y⁻¹) * k⁻¹ =
        (k * y * k⁻¹) * (k * a * k⁻¹) * (k * y * k⁻¹)⁻¹ := by group
    have e2 : (y * a * y⁻¹) ^ s = y * a ^ s * y⁻¹ := conj_zpow
    have e3 : a ^ s = (y⁻¹ * (k * y * k⁻¹)) * (k * a * k⁻¹) * (y⁻¹ * (k * y * k⁻¹))⁻¹ := by
      calc a ^ s = y⁻¹ * ((y * a * y⁻¹) ^ s) * y := by rw [e2]; group
        _ = y⁻¹ * ((k * y * k⁻¹) * (k * a * k⁻¹) * (k * y * k⁻¹)⁻¹) * y := by rw [hs, e1]
        _ = _ := by group
    have hz1 : (y⁻¹ * (k * y * k⁻¹)) * (k * a * k⁻¹) * (y⁻¹ * (k * y * k⁻¹))⁻¹ *
        (k * a * k⁻¹)⁻¹ ∈ Subgroup.zpowers a := by
      rw [← e3]
      exact (Subgroup.zpowers a).mul_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) s)
        ((Subgroup.zpowers a).inv_mem hcA)
    have hz2 : (y⁻¹ * (k * y * k⁻¹)) * (k * a * k⁻¹) * (y⁻¹ * (k * y * k⁻¹))⁻¹ *
        (k * a * k⁻¹)⁻¹ ∈ pCoreOf 2 X := by
      have h1 := SolK.pCoreOf_normalized X hcX ((pCoreOf 2 X).inv_mem huV)
      have h2 := (pCoreOf 2 X).mul_mem huV h1
      simpa [mul_assoc] using h2
    have hz : (y⁻¹ * (k * y * k⁻¹)) * (k * a * k⁻¹) * (y⁻¹ * (k * y * k⁻¹))⁻¹ *
        (k * a * k⁻¹)⁻¹ = 1 := by
      generalize (y⁻¹ * (k * y * k⁻¹)) * (k * a * k⁻¹) * (y⁻¹ * (k * y * k⁻¹))⁻¹ *
        (k * a * k⁻¹)⁻¹ = z at hz1 hz2
      have h3 : z * z * z = 1 := by
        have := zpowers_cube hb.cube hz1
        simpa [pow_succ] using this
      have h2 : z * z = 1 := hb.sq z hz2
      calc z = (z * z * z) * (z * z)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; group
    have hu' : k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k ∈ pCoreOf 2 X := hV2 _ huV
    have hcomm : (k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k) * a * (k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k)⁻¹ =
        a := by
      have h1 : (y⁻¹ * (k * y * k⁻¹)) * (k * a * k⁻¹) * (y⁻¹ * (k * y * k⁻¹))⁻¹ =
          k * a * k⁻¹ := by
        have := hz
        rw [mul_inv_eq_one] at this
        exact this
      calc (k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k) * a * (k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k)⁻¹
          = k⁻¹ * ((y⁻¹ * (k * y * k⁻¹)) * (k * a * k⁻¹) * (y⁻¹ * (k * y * k⁻¹))⁻¹) * k := by
            group
        _ = a := by rw [h1]; group
    have hone : k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k = 1 := by
      apply hAfix _ hu'
      have h1 : (k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k) * a =
          a * (k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k) := mul_inv_eq_iff_eq_mul.1 hcomm
      calc a * (k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k) * a⁻¹
          = (k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k) * a * a⁻¹ := by rw [h1]
        _ = _ := by group
    have : y⁻¹ * (k * y * k⁻¹) = 1 := by
      calc y⁻¹ * (k * y * k⁻¹) = k * (k⁻¹ * (y⁻¹ * (k * y * k⁻¹)) * k) * k⁻¹ := by group
        _ = 1 := by rw [hone]; group
    calc k * y * k⁻¹ = y * (y⁻¹ * (k * y * k⁻¹)) := by group
      _ = y := by rw [this, mul_one]
  have hB : k * a * k⁻¹ = a := by
    obtain ⟨v, hv, hv1⟩ := hb.exists_ne_one
    have hd : a⁻¹ * (k * a * k⁻¹) ∈ Subgroup.zpowers a :=
      (Subgroup.zpowers a).mul_mem ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)) hcA
    have hdv : ∀ w ∈ pCoreOf 2 X, (a⁻¹ * (k * a * k⁻¹)) * w = w * (a⁻¹ * (k * a * k⁻¹)) := by
      intro w hw
      have hw2 : a * w * a⁻¹ ∈ pCoreOf 2 X := hb.conj_mem hw
      have h1 := hA _ hw2
      have h2 := hA w hw
      have e : (k * a * k⁻¹) * w * (k * a * k⁻¹)⁻¹ = k * (a * w * a⁻¹) * k⁻¹ := by
        calc (k * a * k⁻¹) * w * (k * a * k⁻¹)⁻¹
            = (k * a * k⁻¹) * (k * w * k⁻¹) * (k * a * k⁻¹)⁻¹ := by rw [h2]
          _ = k * (a * w * a⁻¹) * k⁻¹ := by group
      rw [h1] at e
      calc (a⁻¹ * (k * a * k⁻¹)) * w = a⁻¹ * ((k * a * k⁻¹) * w * (k * a * k⁻¹)⁻¹) *
            (k * a * k⁻¹) := by group
        _ = a⁻¹ * (a * w * a⁻¹) * (k * a * k⁻¹) := by rw [e]
        _ = w * (a⁻¹ * (k * a * k⁻¹)) := by group
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 hd
    obtain ⟨r, hr, hr'⟩ := zpow_eq_pow_lt_three hb.cube t
    rw [hr'] at ht
    interval_cases r
    · have h0 : a⁻¹ * (k * a * k⁻¹) = 1 := by simpa using ht.symm
      calc k * a * k⁻¹ = a * (a⁻¹ * (k * a * k⁻¹)) := by group
        _ = a := by rw [h0, mul_one]
    · exfalso
      apply hv1
      apply hAfix v hv
      have h1 := hdv v hv
      rw [← ht, pow_one] at h1
      calc a * v * a⁻¹ = v * a * a⁻¹ := by rw [h1]
        _ = v := by group
    · exfalso
      apply hv1
      apply hAfix v hv
      have h1 := hdv v hv
      rw [← ht] at h1
      have h2 : Commute (a ^ 2) v := h1
      have h3 : Commute ((a ^ 2) ^ 2) v := h2.pow_left 2
      have e : (a ^ 2) ^ 2 = a := by
        calc (a ^ 2) ^ 2 = a ^ 3 * a := by group
          _ = a := by rw [hb.cube, one_mul]
      rw [e] at h3
      calc a * v * a⁻¹ = v * a * a⁻¹ := by rw [h3.eq]
        _ = v := by group
  intro x hx
  obtain ⟨y, hy, j, rfl⟩ := hb.dec x hx
  have h1 : k * y = y * k := mul_inv_eq_iff_eq_mul.1 (hA y hy)
  have h2 : k * a = a * k := mul_inv_eq_iff_eq_mul.1 hB
  have h3 : k * a ^ j = a ^ j * k := ((show Commute k a from h2).pow_right j).eq
  calc k * (y * a ^ j) = (k * y) * a ^ j := by group
    _ = y * (k * a ^ j) := by rw [h1]; group
    _ = y * (a ^ j * k) := by rw [h3]
    _ = y * a ^ j * k := by group

end Struct

section Omega

variable {G : Type} [Group G] {M X : Subgroup G} {m : G}

@[expose] def Omega (X : Subgroup G) (m : G) : Type :=
  {Z : Subgroup G // Nat.card ↥Z = 3 ∧ (Z ≤ X ∨ Z ≤ conjSub m X)}

theorem card_order_three_le [Finite G] {Y : Subgroup G} (hY : Nat.card ↥Y = 12) :
    Nat.card {Z : Subgroup G // Nat.card ↥Z = 3 ∧ Z ≤ Y} ≤ 4 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfac : (Nat.card ↥Y).factorization 3 = 1 := by
    rw [hY]
    norm_num [Nat.factorization]
  have hsub : ∀ Z : {Z : Subgroup G // Nat.card ↥Z = 3 ∧ Z ≤ Y},
      Nat.card ↥(Z.1.subgroupOf Y) = 3 ^ (Nat.card ↥Y).factorization 3 := by
    intro Z
    rw [hfac, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Z.2.2).toEquiv]
    exact Z.2.1
  let f : {Z : Subgroup G // Nat.card ↥Z = 3 ∧ Z ≤ Y} → Sylow 3 ↥Y := fun Z =>
    Sylow.ofCard (Z.1.subgroupOf Y) (hsub Z)
  have hf : Function.Injective f := by
    intro Z Z' h
    apply Subtype.ext
    have h1 : ((f Z : Sylow 3 ↥Y) : Subgroup ↥Y) = (f Z' : Sylow 3 ↥Y) := by rw [h]
    simp only [f, Sylow.coe_ofCard] at h1
    have h2 := Subgroup.subgroupOf_inj.1 h1
    rwa [inf_eq_left.2 Z.2.2, inf_eq_left.2 Z'.2.2] at h2
  rcases isEmpty_or_nonempty {Z : Subgroup G // Nat.card ↥Z = 3 ∧ Z ≤ Y} with hE | ⟨⟨Z₀⟩⟩
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  · have hdvd := Sylow.card_dvd_index (f Z₀)
    have hcard : Nat.card ↥((f Z₀ : Sylow 3 ↥Y) : Subgroup ↥Y) = 3 := by
      simp only [f, Sylow.coe_ofCard]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Z₀.2.2).toEquiv]
      exact Z₀.2.1
    have hidx := Subgroup.card_mul_index ((f Z₀ : Sylow 3 ↥Y) : Subgroup ↥Y)
    rw [hcard, hY] at hidx
    have h4 : ((f Z₀ : Sylow 3 ↥Y) : Subgroup ↥Y).index = 4 := by omega
    rw [h4] at hdvd
    exact (Nat.card_le_card_of_injective f hf).trans (Nat.le_of_dvd (by norm_num) hdvd)

theorem card_a4 [Finite G] (c : A4Cfg G M X) : Nat.card ↥X = 12 := by
  obtain ⟨a, ha⟩ := SolD3.exists_blk3 c.short c.nat
  have h1 : Nat.card ↥(pCore 2 ↥X) = 4 := by
    have h2 := ha.card
    rw [SolK.pCoreOf_eq_map, Subgroup.card_map_of_injective X.subtype_injective] at h2
    exact h2
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥X)
  rw [c.card_top, h1] at h2
  omega

theorem card_omega_le [Finite G] (c : A4Cfg G M X) : Nat.card (Omega X m) ≤ 8 := by
  have hX := card_order_three_le (Y := X) (card_a4 c)
  have hX2 := card_order_three_le (Y := conjSub m X) ((conjSub_card m X).trans (card_a4 c))
  classical
  let g : Omega X m → {Z : Subgroup G // Nat.card ↥Z = 3 ∧ Z ≤ X} ⊕
      {Z : Subgroup G // Nat.card ↥Z = 3 ∧ Z ≤ conjSub m X} := fun Z =>
    if hZ : Z.1 ≤ X then Sum.inl ⟨Z.1, Z.2.1, hZ⟩
    else Sum.inr ⟨Z.1, Z.2.1, Z.2.2.resolve_left hZ⟩
  have hg : Function.Injective g := by
    intro Z Z' h
    apply Subtype.ext
    by_cases h1 : Z.1 ≤ X <;> by_cases h2 : Z'.1 ≤ X
    · simp only [g, h1, h2, ↓reduceDIte] at h
      exact Subtype.mk.inj (Sum.inl.inj h)
    · simp only [g, h1, h2, ↓reduceDIte] at h
      exact absurd h Sum.inl_ne_inr
    · simp only [g, h1, h2, ↓reduceDIte] at h
      exact absurd h Sum.inr_ne_inl
    · simp only [g, h1, h2, ↓reduceDIte] at h
      exact Subtype.mk.inj (Sum.inr.inj h)
  have := Nat.card_le_card_of_injective g hg
  rw [Nat.card_sum] at this
  omega

end Omega

section Action

variable {G : Type} [Group G] {M X : Subgroup G} {m : G}

theorem blk3_ne_one {X : Subgroup G} {a : G} (hb : SolD3.Blk3 X a) : a ≠ 1 := by
  intro h1
  obtain ⟨w, hw, hw1⟩ := hb.exists_ne_one
  apply hw1
  apply hb.fix w hw
  rw [h1]
  group

theorem zpowers_conj_card {X : Subgroup G} {a : G} (hb : SolD3.Blk3 X a) {y : G}
    (hy : y ∈ pCoreOf 2 X) :
    Nat.card ↥(Subgroup.zpowers (y * a * y⁻¹)) = 3 ∧ Subgroup.zpowers (y * a * y⁻¹) ≤ X := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ⟨?_, ?_⟩
  · rw [Nat.card_zpowers]
    apply orderOf_eq_prime
    · rw [conj_pow, hb.cube]
      group
    · intro h1
      apply blk3_ne_one hb
      calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
  · rw [Subgroup.zpowers_le]
    have hyX : y ∈ X := SolK.pCoreOf_le_self X hy
    exact X.mul_mem (X.mul_mem hyX hb.mem) (X.inv_mem hyX)

theorem omega_conj_mem (h : TwoConj M X m) {k : G} (hk : k ∈ M) (Z : Omega X m) :
    Nat.card ↥(conjSub k Z.1) = 3 ∧ (conjSub k Z.1 ≤ X ∨ conjSub k Z.1 ≤ conjSub m X) := by
  refine ⟨(conjSub_card k Z.1).trans Z.2.1, ?_⟩
  rcases twoConj_perm h hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases Z.2.2 with hZ | hZ
    · exact Or.inl ((conjSub_map_le k hZ).trans h1.le)
    · exact Or.inr ((conjSub_map_le k hZ).trans h2.le)
  · rcases Z.2.2 with hZ | hZ
    · exact Or.inr ((conjSub_map_le k hZ).trans h1.le)
    · exact Or.inl ((conjSub_map_le k hZ).trans h2.le)

@[expose] def omegaAct (h : TwoConj M X m) (k : ↥M) (Z : Omega X m) : Omega X m :=
  ⟨conjSub (k : G) Z.1, omega_conj_mem h k.2 Z⟩

@[expose] def omegaHom (h : TwoConj M X m) : ↥M →* Equiv.Perm (Omega X m) where
  toFun k :=
    { toFun := omegaAct h k
      invFun := omegaAct h k⁻¹
      left_inv := fun Z => Subtype.ext (by
        show conjSub ((k⁻¹ : ↥M) : G) (conjSub (k : G) Z.1) = Z.1
        rw [conjSub_conjSub, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, conjSub_one])
      right_inv := fun Z => Subtype.ext (by
        show conjSub (k : G) (conjSub ((k⁻¹ : ↥M) : G) Z.1) = Z.1
        rw [conjSub_conjSub, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, conjSub_one]) }
  map_one' := Equiv.ext fun Z => Subtype.ext (by
    show conjSub (((1 : ↥M)) : G) Z.1 = Z.1
    rw [Subgroup.coe_one, conjSub_one])
  map_mul' := fun a b => Equiv.ext fun Z => Subtype.ext (by
    show conjSub ((a * b : ↥M) : G) Z.1 = conjSub (a : G) (conjSub (b : G) Z.1)
    rw [conjSub_conjSub, Subgroup.coe_mul])

theorem omegaHom_apply (h : TwoConj M X m) (k : ↥M) (Z : Omega X m) :
    (omegaHom h k Z).1 = conjSub (k : G) Z.1 := rfl

variable [Finite G]

theorem eq_one_of_fixes (c : A4Cfg G M X) (h : TwoConj M X m) (hC : pairCent X m = ⊥)
    {k : G} (hk : k ∈ M) (hK : ∀ Z : Omega X m, conjSub k Z.1 = Z.1) : k = 1 := by
  obtain ⟨a, ha⟩ := SolD3.exists_blk3 c.short c.nat
  have hb2 := blk3_of_conj ha m
  have hfix : ∀ {Y : Subgroup G} {b : G}, SolD3.Blk3 Y b → (Y ≤ X ∨ Y ≤ conjSub m X) →
      ∀ y ∈ pCoreOf 2 Y, k * (y * b * y⁻¹) * k⁻¹ ∈ Subgroup.zpowers (y * b * y⁻¹) := by
    intro Y b hb hY y hy
    obtain ⟨hc, hle⟩ := zpowers_conj_card hb hy
    have h1 : conjSub k (Subgroup.zpowers (y * b * y⁻¹)) = Subgroup.zpowers (y * b * y⁻¹) :=
      hK ⟨Subgroup.zpowers (y * b * y⁻¹), hc, hY.imp (fun h => hle.trans h) (fun h => hle.trans h)⟩
    have h2 := conj_mem_conjSub (g := k) (Subgroup.mem_zpowers (y * b * y⁻¹))
    rwa [h1] at h2
  have hX : conjSub k X = X ∧ conjSub k (conjSub m X) = conjSub m X := by
    rcases twoConj_perm h hk with hh | ⟨h1, h2⟩
    · exact hh
    · exfalso
      obtain ⟨hc, hle⟩ := zpowers_conj_card ha (y := 1) (pCoreOf 2 X).one_mem
      have h3 : conjSub k (Subgroup.zpowers (1 * a * 1⁻¹)) = Subgroup.zpowers (1 * a * 1⁻¹) :=
        hK ⟨Subgroup.zpowers (1 * a * 1⁻¹), hc, Or.inl hle⟩
      have h4 : Subgroup.zpowers (1 * a * 1⁻¹) ≤ conjSub m X := by
        have h5 : Subgroup.zpowers (1 * a * 1⁻¹) ≤ conjSub k X :=
          calc Subgroup.zpowers (1 * a * 1⁻¹) = conjSub k (Subgroup.zpowers (1 * a * 1⁻¹)) :=
                h3.symm
            _ ≤ conjSub k X := conjSub_map_le k hle
        rwa [h1] at h5
      have h6 : Subgroup.zpowers (1 * a * 1⁻¹) ≤ ⊥ := by
        rw [← twoConj_inf_eq_bot c h]
        exact le_inf hle h4
      have h7 : Nat.card ↥(Subgroup.zpowers (1 * a * 1⁻¹)) = 1 := by
        rw [le_bot_iff.1 h6]
        exact Subgroup.card_bot
      omega
  have hcX := centralizes_of_fixes ha hX.1 (hfix ha (Or.inl le_rfl))
  have hcX2 := centralizes_of_fixes hb2 hX.2 (hfix hb2 (Or.inr le_rfl))
  have hmem : k ∈ pairCent X m :=
    mem_pairCent_iff.2 ⟨fun x hx => (hcX x hx).symm, fun y hy => (hcX2 y hy).symm⟩
  rw [hC, Subgroup.mem_bot] at hmem
  exact hmem

theorem omegaHom_injective (c : A4Cfg G M X) (h : TwoConj M X m) (hC : pairCent X m = ⊥) :
    Function.Injective (omegaHom h) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  apply Subtype.ext
  exact eq_one_of_fixes c h hC k.2 (fun Z => congrArg Subtype.val (Equiv.congr_fun hk Z))

theorem exists_injective_perm_eight (c : A4Cfg G M X) (h : TwoConj M X m)
    (hC : pairCent X m = ⊥) : ∃ ψ : ↥M →* Equiv.Perm (Fin 8), Function.Injective ψ := by
  classical
  have hcard : Nat.card (Omega X m) ≤ 8 := card_omega_le c
  have : Finite (Omega X m) := inferInstanceAs (Finite {Z : Subgroup G // _})
  have : Fintype (Omega X m) := Fintype.ofFinite _
  have hle : Fintype.card (Omega X m) ≤ Fintype.card (Fin 8) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hle
  let e : Omega X m ≃ Set.range ι := Equiv.ofInjective ι ι.injective
  exact ⟨(Equiv.Perm.extendDomainHom e).comp (omegaHom h),
    (Equiv.Perm.extendDomainHom_injective e).comp (omegaHom_injective c h hC)⟩

end Action

end CFSG.CGT.PushingUpLit.A4
