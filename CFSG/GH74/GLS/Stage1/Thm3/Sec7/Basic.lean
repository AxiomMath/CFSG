module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.B

open Subgroup

variable {G : Type*} [Group G]

theorem comm_of_forall_sq {E : Subgroup G} (hEx : ∀ a ∈ E, a * a = 1) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have h1 := hEx (a * b) (E.mul_mem ha hb)
  have h2 := hEx a ha
  have h3 := hEx b hb
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right h2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right h3
  have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, ha', hb'] at hab'
  exact hab'.symm

theorem card_le_two_of_sq_eq_one {A : Type*} [Group A] [Finite A] [IsCyclic A] (T : Subgroup A)
    (hT : ∀ x ∈ T, x * x = 1) : Nat.card T ≤ 2 := by
  classical
  have := Fintype.ofFinite A
  have h2 := IsCyclic.card_pow_eq_one_le (α := A) (n := 2) (by norm_num)
  have hinj : Function.Injective
      (fun t : T => (⟨(t : A), by simpa [pow_two] using hT t t.2⟩ : {x : A // x ^ 2 = 1})) := by
    intro a b h
    have := congrArg Subtype.val h
    exact Subtype.ext this
  have h3 := Nat.card_le_card_of_injective _ hinj
  have h4 : Nat.card {x : A // x ^ 2 = 1} = (Finset.univ.filter (fun x : A => x ^ 2 = 1)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem z_mem_zpowers_of_cyc [Finite G] {T : Subgroup G} (hT : IsCyclic T) (hT2 : IsPGroup 2 T)
    {z : G} (hz : z ∈ T) (hz2 : z * z = 1) (hz1 : z ≠ 1) {y : G} (hy : y ∈ T) (hy1 : y ≠ 1) :
    z ∈ zpowers y := by
  classical
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨y, hy⟩
  have hk' : orderOf y = 2 ^ k := by simpa using hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hy1
    have : orderOf y = 1 := by simpa using hk'
    exact orderOf_eq_one_iff.mp this
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  set w : G := y ^ (2 ^ k') with hw
  have hw2 : orderOf w = 2 := by
    rw [hw, orderOf_pow_of_dvd (by positivity) (by rw [hk', pow_succ]; exact dvd_mul_right _ _), hk',
      pow_succ]
    simp
  have hwT : w ∈ T := T.pow_mem hy _
  have hwsq : w ^ 2 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2] at this
  have hwz : w = z := by
    have := Fintype.ofFinite T
    have h := IsCyclic.card_pow_eq_one_le (α := T) (n := 2) (by norm_num)
    by_contra hne
    let a' : T := ⟨w, hwT⟩
    let b' : T := ⟨z, hz⟩
    have hsub : ({1, a', b'} : Finset T) ⊆ Finset.univ.filter (fun x : T => x ^ 2 = 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Subtype.ext (by simpa [a'] using hwsq)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Subtype.ext (by simpa [b', pow_two] using hz2)
    have hcard : ({1, a', b'} : Finset T).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · intro e
        simp only [Finset.mem_singleton] at e
        exact hne (congrArg Subtype.val e)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, ?_⟩
        · intro e
          have : w = 1 := (congrArg Subtype.val e).symm
          rw [this] at hw2; simp at hw2
        · intro e; exact hz1 (congrArg Subtype.val e).symm
    have := Finset.card_le_card hsub
    omega
  rw [← hwz, hw]
  exact Subgroup.pow_mem _ (mem_zpowers y) _

theorem cyc_comm {T : Subgroup G} (hT : IsCyclic T) {a b : G} (ha : a ∈ T) (hb : b ∈ T) :
    a * b = b * a := by
  have := (hT.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact congrArg Subtype.val this

theorem zpow_of_sq_eq_one {w : G} (hw2 : w * w = 1) (k : ℤ) : w ^ k = 1 ∨ w ^ k = w := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul]
    have : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw2
    rw [this, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul]
    have : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw2
    rw [this, one_zpow, one_mul]

theorem mem_sup_inv {T : Subgroup G} {w : G} (hw2 : w * w = 1) (hinv : ∀ a ∈ T, w * a * w⁻¹ = a⁻¹)
    {y : G} (hy : y ∈ T ⊔ zpowers w) : y ∈ T ∨ ∃ a ∈ T, y = w * a := by
  have hwn : w ∈ normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinv x hx]; exact T.inv_mem hx
    · intro hx
      have hu := hinv _ hx
      have h1 : w⁻¹ * w⁻¹ = 1 := by rw [← mul_inv_rev, hw2, inv_one]
      have : w * (w * x * w⁻¹) * w⁻¹ = x := by
        calc w * (w * x * w⁻¹) * w⁻¹ = (w * w) * x * (w⁻¹ * w⁻¹) := by group
          _ = x := by rw [hw2, h1]; group
      rw [this] at hu
      rw [hu]
      exact T.inv_mem hx
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers w) T (zpowers_le.2 hwn)
  rw [sup_comm] at hy
  have hy' : y ∈ (↑(zpowers w ⊔ T) : Set G) := hy
  rw [hset] at hy'
  obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.1 hy'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  rcases zpow_of_sq_eq_one hw2 k with h | h
  · left; rw [h, one_mul]; exact ha
  · right; exact ⟨a, ha, by rw [h]⟩

theorem dih_normal_inf [Finite G] {T N : Subgroup G} {z w : G} (hT : IsCyclic T) (hT2 : IsPGroup 2 T)
    (hz : z ∈ T) (hz2 : z * z = 1) (hz1 : z ≠ 1) (h4 : 3 ≤ Nat.card T)
    (hw2 : w * w = 1) (hinv : ∀ a ∈ T, w * a * w⁻¹ = a⁻¹)
    (hNn : ∀ d ∈ T ⊔ zpowers w, ∀ n ∈ N, d * n * d⁻¹ ∈ N) (hND : N ≤ T ⊔ zpowers w)
    (hzN : z ∉ N) : N = ⊥ := by
  have hNT : ∀ a ∈ N, a ∈ T → a = 1 := by
    intro a haN haT
    by_contra ha1
    have := z_mem_zpowers_of_cyc hT hT2 hz hz2 hz1 haT ha1
    exact hzN (zpowers_le.2 haN this)
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  rcases mem_sup_inv hw2 hinv (hND hn) with h | ⟨a, ha, rfl⟩
  · exact hNT n hn h
  · exfalso
    have hsq : ∀ b ∈ T, b * b = 1 := by
      intro b hb
      have h1 := hNn b (Subgroup.mem_sup_left hb) _ hn
      have h2 := N.mul_mem h1 (N.inv_mem hn)
      have hbT : b * b ∈ T := T.mul_mem hb hb
      have e : b * (w * a) * b⁻¹ * (w * a)⁻¹ = b * b := by
        have hab : a * b⁻¹ = b⁻¹ * a := cyc_comm hT ha (T.inv_mem hb)
        have hwb := hinv b⁻¹ (T.inv_mem hb)
        simp only [inv_inv] at hwb
        calc b * (w * a) * b⁻¹ * (w * a)⁻¹ = b * w * (a * b⁻¹) * a⁻¹ * w⁻¹ := by group
          _ = b * w * (b⁻¹ * a) * a⁻¹ * w⁻¹ := by rw [hab]
          _ = b * (w * b⁻¹ * w⁻¹) := by group
          _ = b * b := by rw [hwb]
      rw [e] at h2
      exact hNT _ h2 hbT
    have hle : Nat.card (⊤ : Subgroup T) ≤ 2 := by
      have : IsCyclic T := hT
      refine card_le_two_of_sq_eq_one (⊤ : Subgroup T) ?_
      intro x _
      apply Subtype.ext
      simpa using hsq (x : G) x.2
    rw [Subgroup.card_top] at hle
    omega

theorem card_le_relIndex_of_trivial_inf [Finite G] {S P D : Subgroup G} {g : G}
    (hP : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P)
    (hDg : ∀ x ∈ D, g⁻¹ * x * g ∈ S) (htriv : ∀ x ∈ D, g⁻¹ * x * g ∈ P → x = 1) :
    Nat.card D ≤ P.relIndex S := by
  have hnormal : (P.subgroupOf S).Normal := ⟨fun n hn s => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hP (s : G) s.2 (n : G) hn⟩
  let c : D →* S := ((MulAut.conj g⁻¹).toMonoidHom.comp D.subtype).codRestrict S
    (fun x => by simpa [MulAut.conj_apply] using hDg x.1 x.2)
  let φ : D →* S ⧸ P.subgroupOf S := (QuotientGroup.mk' (P.subgroupOf S)).comp c
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hx
    have hx' : g⁻¹ * (x : G) * g ∈ P := by simpa [c, MulAut.conj_apply] using hx
    exact Subtype.ext (htriv x x.2 hx')
  have := Nat.card_le_card_of_injective _ hinj
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact this

theorem core73D [Finite G] {S P T : Subgroup G} {z w g : G}
    (hP : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P)
    (hT : IsCyclic T) (hT2 : IsPGroup 2 T) (hz : z ∈ T) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (h4 : 3 ≤ Nat.card T) (hw2 : w * w = 1) (hinv : ∀ a ∈ T, w * a * w⁻¹ = a⁻¹)
    (hDg : ∀ x ∈ T ⊔ zpowers w, g⁻¹ * x * g ∈ S) (hzg : g⁻¹ * z * g ∉ P) :
    (∀ x ∈ T ⊔ zpowers w, g⁻¹ * x * g ∈ P → x = 1) ∧ Nat.card ↥(T ⊔ zpowers w) ≤ P.relIndex S := by
  set D := T ⊔ zpowers w with hD
  set N : Subgroup G := D ⊓ P.comap (MulAut.conj g⁻¹).toMonoidHom with hN
  have hNmem : ∀ x, x ∈ N ↔ x ∈ D ∧ g⁻¹ * x * g ∈ P := by
    intro x
    simp [hN]
  have hNn : ∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N := by
    intro d hd n hn
    rw [hNmem] at hn ⊢
    refine ⟨D.mul_mem (D.mul_mem hd hn.1) (D.inv_mem hd), ?_⟩
    have := hP (g⁻¹ * d * g) (by simpa using hDg d hd) (g⁻¹ * n * g) hn.2
    have e : g⁻¹ * (d * n * d⁻¹) * g = (g⁻¹ * d * g) * (g⁻¹ * n * g) * (g⁻¹ * d * g)⁻¹ := by group
    rw [e]; exact this
  have hzN : z ∉ N := by
    rw [hNmem]
    exact fun h => hzg h.2
  have hNbot : N = ⊥ :=
    dih_normal_inf hT hT2 hz hz2 hz1 h4 hw2 hinv hNn inf_le_left hzN
  have htriv : ∀ x ∈ D, g⁻¹ * x * g ∈ P → x = 1 := by
    intro x hx hxP
    have : x ∈ N := (hNmem x).2 ⟨hx, hxP⟩
    rw [hNbot, Subgroup.mem_bot] at this
    exact this
  exact ⟨htriv, card_le_relIndex_of_trivial_inf hP hDg htriv⟩

theorem sq_mem_of_iso_E4 {S P : Subgroup G} [(P.subgroupOf S).Normal]
    (e : (↥S ⧸ P.subgroupOf S) ≃* Multiplicative (ZMod 2 × ZMod 2)) : ∀ x ∈ S, x * x ∈ P := by
  intro x hx
  have h1 : e (QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨x, hx⟩) = 1 := by
    rw [map_mul]
    generalize e (QuotientGroup.mk ⟨x, hx⟩) = a
    show Multiplicative.ofAdd (a.toAdd + a.toAdd) = 1
    have : a.toAdd + a.toAdd = 0 := by
      rcases a.toAdd with ⟨a1, a2⟩
      ext <;> simp [← two_mul] <;> decide +revert
    rw [this]; rfl
  have h2 : (QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨x, hx⟩ : ↥S ⧸ P.subgroupOf S) = 1 :=
    e.injective (by rw [h1, map_one])
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem exists_Y [Finite G] {S P : Subgroup G} {a : G} (hPS : P ≤ S)
    (hP : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P) (hcard : P.relIndex S = 8)
    (haS : a ∈ S) (h4 : ∀ s ∈ S, s ^ 4 ∈ P) (h2 : a * a ∉ P) :
    ∃ Y : Subgroup G, Y ≤ S ∧ P ≤ Y ∧ a ∈ Y ∧ Y.relIndex S = 2 ∧
      ∀ y ∈ Y, ∃ p ∈ P, ∃ k : ℕ, k < 4 ∧ y = p * a ^ k := by
  have hnormal : (P.subgroupOf S).Normal := ⟨fun n hn s => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hP (s : G) s.2 (n : G) hn⟩
  let π : S →* S ⧸ P.subgroupOf S := QuotientGroup.mk' (P.subgroupOf S)
  let ab : S ⧸ P.subgroupOf S := π ⟨a, haS⟩
  have hab4 : ab ^ 4 = 1 := by
    have : ab ^ 4 = π (⟨a, haS⟩ ^ 4) := by rw [map_pow]
    rw [this, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using h4 a haS
  have hab2 : ab ^ 2 ≠ 1 := by
    intro h
    have : ab ^ 2 = π (⟨a, haS⟩ ^ 2) := by rw [map_pow]
    rw [this, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h2 (by simpa [pow_two] using h)
  have hord : orderOf ab = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ab) (by simpa using hab2) (by simpa using hab4)
    simpa using this
  set Yb : Subgroup (S ⧸ P.subgroupOf S) := zpowers ab with hYb
  have hYbcard : Nat.card Yb = 4 := by rw [hYb, Nat.card_zpowers, hord]
  have hSbar : Nat.card (S ⧸ P.subgroupOf S) = 8 := by
    rw [← Subgroup.index_eq_card]; exact hcard
  have hidx : Yb.index = 2 := by
    have := Subgroup.card_mul_index Yb
    rw [hYbcard, hSbar] at this
    omega
  set Y : Subgroup G := (Yb.comap π).map S.subtype with hY
  have hmemY : ∀ y : G, y ∈ Y ↔ ∃ hy : y ∈ S, π ⟨y, hy⟩ ∈ Yb := by
    intro y
    simp only [hY, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨y'.2, hy'⟩
    · rintro ⟨hy, hyb⟩
      exact ⟨⟨y, hy⟩, hyb, rfl⟩
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_⟩
  · rintro y hy
    exact ((hmemY y).1 hy).1
  · intro p hp
    refine (hmemY p).2 ⟨hPS hp, ?_⟩
    have : π ⟨p, hPS hp⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact hp
    rw [this]; exact one_mem _
  · exact (hmemY a).2 ⟨haS, mem_zpowers _⟩
  · have h1 : Y.subgroupOf S = Yb.comap π := by
      ext x
      rw [Subgroup.mem_subgroupOf, hmemY]
      constructor
      · rintro ⟨hy, hyb⟩; exact hyb
      · intro h; exact ⟨x.2, h⟩
    rw [Subgroup.relIndex, h1, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hidx
  · intro y hy
    obtain ⟨hyS, hyb⟩ := (hmemY y).1 hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyb
    have hk' : ab ^ (k % 4).toNat = π ⟨y, hyS⟩ := by
      rw [← hk]
      have h4' : (4 : ℤ) = (orderOf ab : ℤ) := by rw [hord]; rfl
      have : ab ^ k = ab ^ (k % (orderOf ab : ℤ)) := by rw [zpow_mod_orderOf]
      rw [this, hord]
      have hnn : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
      rw [← zpow_natCast]
      congr 1
      simp only [Nat.cast_ofNat] at hnn ⊢
      exact Int.toNat_of_nonneg hnn
    set m : ℕ := (k % 4).toNat
    have hm : ab ^ m = π ⟨a ^ m, S.pow_mem haS m⟩ := by
      have := map_pow π (⟨a, haS⟩ : S) m
      rw [← this]; rfl
    rw [hm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hk'
    have hp : (a ^ m)⁻¹ * y ∈ P := by simpa using hk'
    have hm4 : m < 4 := by
      have h1 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
      omega
    refine ⟨a ^ m * ((a ^ m)⁻¹ * y) * (a ^ m)⁻¹, ?_, m, hm4, ?_⟩
    · exact hP (a ^ m) (S.pow_mem haS m) _ hp
    · group

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.B
