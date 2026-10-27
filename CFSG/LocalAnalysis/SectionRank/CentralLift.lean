module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.SectionRank

open CFSG.Open
open scoped commutatorElement

variable {P : Type*} [Group P]

section ClassTwo

variable (hc : ∀ x y z : P, Commute ⁅x, y⁆ z)
include hc

theorem commutatorElement_mul_left_of_central (x y z : P) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have h1 : y * z * y⁻¹ = ⁅y, z⁆ * z := by rw [commutatorElement_def]; group
  have h2 : x * ⁅y, z⁆ = ⁅y, z⁆ * x := (hc y z x).eq.symm
  calc ⁅x * y, z⁆ = x * (y * z * y⁻¹) * x⁻¹ * z⁻¹ := by rw [commutatorElement_def]; group
    _ = (x * ⁅y, z⁆) * z * x⁻¹ * z⁻¹ := by rw [h1]; group
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [h2, commutatorElement_def]; group
    _ = ⁅x, z⁆ * ⁅y, z⁆ := (hc y z ⁅x, z⁆).eq

theorem commutatorElement_mul_right_of_central (x y z : P) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h := commutatorElement_mul_left_of_central hc y z x
  calc ⁅x, y * z⁆ = ⁅y * z, x⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = (⁅y, x⁆ * ⁅z, x⁆)⁻¹ := by rw [h]
    _ = ⁅x, z⁆ * ⁅x, y⁆ := by rw [mul_inv_rev, commutatorElement_inv, commutatorElement_inv]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := (hc x z ⁅x, y⁆).eq

theorem commutatorElement_pow_left_of_central (x z : P) (n : ℕ) : ⁅x ^ n, z⁆ = ⁅x, z⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, commutatorElement_mul_left_of_central hc, ih, pow_succ]

theorem mul_pow_of_central (x y : P) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    set c := ⁅y, x⁆
    have hcx : ∀ k : ℕ, Commute (c ^ k) x := fun k => (hc y x x).pow_left k
    have hcy : ∀ k : ℕ, Commute (c ^ k) y := fun k => (hc y x y).pow_left k
    have hsw : y ^ n * x = c ^ n * x * y ^ n := by
      rw [← commutatorElement_pow_left_of_central hc, commutatorElement_def]; group
    rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_succ, ih]
    calc x ^ n * y ^ n * c ^ n.choose 2 * (x * y)
        = x ^ n * (y ^ n * (c ^ n.choose 2 * x)) * y := by simp only [mul_assoc]
      _ = x ^ n * (y ^ n * x) * c ^ n.choose 2 * y := by
          rw [(hcx _).eq]; simp only [mul_assoc]
      _ = x ^ n * (c ^ n * x * y ^ n) * c ^ n.choose 2 * y := by rw [hsw]
      _ = x ^ n * (x * c ^ n) * y ^ n * (c ^ n.choose 2 * y) := by
          rw [(hcx n).eq]; simp only [mul_assoc]
      _ = x ^ n * x * (c ^ n * y ^ n) * (y * c ^ n.choose 2) := by
          rw [(hcy _).eq]; simp only [mul_assoc]
      _ = x ^ n * x * (y ^ n * c ^ n) * (y * c ^ n.choose 2) := by
          rw [((hcy n).pow_right n).eq]
      _ = x ^ n * x * y ^ n * (c ^ n * y) * c ^ n.choose 2 := by simp only [mul_assoc]
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + n.choose 2) := by
          rw [(hcy n).eq, pow_succ x, pow_succ y, pow_add]; simp only [mul_assoc]

theorem mul_pow_prime_of_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcp : ∀ x y : P, ⁅x, y⁆ ^ p = 1) (x y : P) : (x * y) ^ p = x ^ p * y ^ p := by
  rw [mul_pow_of_central hc, Nat.choose_two_right]
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = 2 * m := by
    have := hp.eq_two_or_odd'
    rcases this with h | ⟨m, hm⟩
    · exact absurd h hp2
    · exact ⟨m, by omega⟩
  rw [hm, show p * (2 * m) / 2 = p * m by
    rw [show p * (2 * m) = 2 * (p * m) by ring]; exact Nat.mul_div_cancel_left _ two_pos,
    pow_mul, hcp, one_pow, mul_one]

@[expose] def powHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcp : ∀ x y : P, ⁅x, y⁆ ^ p = 1) :
    P →* P where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow_prime_of_central hc hp hp2 hcp x y

@[expose] def commHom (x : P) : P →* P where
  toFun y := ⁅x, y⁆
  map_one' := by simp
  map_mul' y z := commutatorElement_mul_right_of_central hc x y z

end ClassTwo

theorem exists_extend [Finite P] {p : ℕ} [hp : Fact p.Prime] {B : Type*} [Group B]
    (hcomm : ∀ a b : B, a * b = b * a) (hpow : ∀ a : B, a ^ p = 1) {k : ℕ}
    (hB : Nat.card B = p ^ k) (F : B →* P) (hF : Function.Injective F) {y : P} (hy : y ^ p = 1)
    (hy1 : y ∉ F.range) (hyc : ∀ b, Commute (F b) y) :
    ∃ F' : B × Subgroup.zpowers y →* P, Function.Injective F' ∧
      (∀ a b : B × Subgroup.zpowers y, a * b = b * a) ∧
      (∀ a : B × Subgroup.zpowers y, a ^ p = 1) ∧ Nat.card (B × Subgroup.zpowers y) = p ^ (k + 1) ∧
      ∀ a, ∃ b n, F' a = F b * y ^ n := by
  have hcomm' : ∀ b (u : Subgroup.zpowers y), Commute (F b) ((Subgroup.zpowers y).subtype u) := by
    rintro b ⟨u, n, rfl⟩
    exact (hyc b).zpow_right n
  have hy1' : y ≠ 1 := fun h => hy1 (h ▸ one_mem _)
  have hord : orderOf y = p := orderOf_eq_prime hy hy1'
  have hdisj : ∀ u ∈ Subgroup.zpowers y, u ∈ F.range → u = 1 := by
    intro u hu hur
    set H : Subgroup P := F.range ⊓ Subgroup.zpowers y
    have hdvd : Nat.card H ∣ p := hord ▸ Nat.card_zpowers y ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out _ hdvd) with h1 | h1
    · have : (⟨u, hur, hu⟩ : H) = 1 :=
        @Subsingleton.elim _ (Nat.card_eq_one_iff_unique.1 h1).1 _ _
      exact congrArg Subtype.val this
    · exfalso
      have heq : H = Subgroup.zpowers y := Subgroup.eq_of_le_of_card_ge inf_le_right
        (by rw [Nat.card_zpowers, hord, h1])
      have : y ∈ H := heq ▸ Subgroup.mem_zpowers y
      exact hy1 this.1
  refine ⟨F.noncommCoprod (Subgroup.zpowers y).subtype hcomm', ?_, ?_, ?_, ?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨b, u⟩ h
    rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at h
    change F b * (u : P) = 1 at h
    have hu : (u : P) = (F b)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hu1 : (u : P) = 1 := hdisj u u.2 (hu ▸ inv_mem ⟨b, rfl⟩)
    have hb : F b = 1 := by rw [hu1, mul_one] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨hF (hb.trans (map_one F).symm), Subtype.ext hu1⟩
  · rintro ⟨b₁, ⟨u₁, n₁, rfl⟩⟩ ⟨b₂, ⟨u₂, n₂, rfl⟩⟩
    refine Prod.ext (hcomm _ _) (Subtype.ext ?_)
    change y ^ n₁ * y ^ n₂ = y ^ n₂ * y ^ n₁
    rw [← zpow_add, ← zpow_add, add_comm]
  · rintro ⟨b, ⟨u, n, rfl⟩⟩
    refine Prod.ext (hpow b) (Subtype.ext ?_)
    change (y ^ n) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  · rw [Nat.card_prod, hB, Nat.card_zpowers, hord, pow_succ]
  · rintro ⟨b, ⟨u, n, rfl⟩⟩
    refine ⟨b, (n % p).toNat, ?_⟩
    rw [MonoidHom.noncommCoprod_apply]
    change F b * y ^ n = F b * y ^ (n % p).toNat
    congr 1
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero)),
      ← hord, zpow_mod_orderOf]

theorem exists_mem_not_mem_range_of_card_lt [Finite P] {B : Type*} [Group B] {F : B →* P}
    (hF : Function.Injective F) {S : Subgroup P} (h : Nat.card B < Nat.card S) :
    ∃ y ∈ S, y ∉ F.range := by
  by_contra hcon
  push Not at hcon
  have := Subgroup.card_le_of_le (fun y hy => hcon y hy : S ≤ F.range)
  rw [← Nat.card_congr (MonoidHom.ofInjective hF).toEquiv] at this
  omega

theorem three_le_pRank_of_central [Finite P] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (A : Subgroup P) (hAZ : A ≤ Subgroup.center P) (hArank : pRank p A ≤ 2)
    (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A) (hpow : ∀ x : P, x ^ p ∈ A) (hindex : p ^ 4 ≤ A.index) :
    3 ≤ pRank p (⊤ : Subgroup P) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hcen : ∀ a ∈ A, ∀ g : P, Commute a g := fun a ha g =>
    (Subgroup.mem_center_iff.1 (hAZ ha) g).symm
  have hc : ∀ x y z : P, Commute ⁅x, y⁆ z := fun x y z => hcen _ (hcomm x y) z
  have hcp : ∀ x y : P, ⁅x, y⁆ ^ p = 1 := fun x y => by
    rw [← commutatorElement_pow_left_of_central hc, commutatorElement_eq_one_iff_mul_comm]
    exact (hcen _ (hpow x) y).eq
  set K : Subgroup P := (powHom hc hp.out hp2 hcp).ker
  have hmemK : ∀ {x : P}, x ∈ K ↔ x ^ p = 1 := Iff.rfl
  have hK4 : p ^ 4 ≤ Nat.card K := by
    have h1 : Nat.card P = Nat.card (powHom hc hp.out hp2 hcp).range * Nat.card K := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
    have h2 : (powHom hc hp.out hp2 hcp).range ≤ A := by
      rintro _ ⟨x, rfl⟩
      exact hpow x
    have h3 := Subgroup.card_le_of_le h2
    have h4 := A.card_mul_index
    have h5 : Nat.card A * A.index ≤ Nat.card A * Nat.card K := by
      rw [h4, h1]
      exact Nat.mul_le_mul_right _ h3
    exact hindex.trans (Nat.le_of_mul_le_mul_left h5 Nat.card_pos)
  set Ω : Subgroup P := K ⊓ A
  have hΩcomm : ∀ a b : Ω, a * b = b * a := fun a b => Subtype.ext (hcen _ a.2.2 b).eq
  have hΩpow : ∀ a : Ω, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact a.2.1)
  have hΩ : IsElemAbelian p Ω := ⟨⟨⟨hΩcomm⟩⟩, fun x hx => hx.1⟩
  obtain ⟨a, ha⟩ : ∃ a, Nat.card Ω = p ^ a :=
    IsPGroup.iff_card.1 fun g => ⟨1, by rw [pow_one]; exact hΩpow g⟩
  have ha2 : a ≤ 2 := (le_pRank hp1 inf_le_right hΩ ha).trans hArank
  have hcommΩ : ∀ x y : P, ⁅x, y⁆ ∈ Ω := fun x y => ⟨hcp x y, hcomm x y⟩
  obtain ⟨x, hxK, hxΩ⟩ := exists_mem_not_mem_range_of_card_lt (F := Ω.subtype)
    Subtype.val_injective (S := K) (by
      rw [ha]
      exact lt_of_lt_of_le (Nat.pow_lt_pow_right hp1 (by omega : a < 4)) hK4)
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := exists_extend hΩcomm hΩpow ha Ω.subtype
    Subtype.val_injective (y := x) hxK hxΩ (fun b => hcen _ b.2.2 x)
  have hF₁K : ∀ b, F₁ b ∈ K := fun b => by
    obtain ⟨b', n, hb⟩ := hr₁ b
    rw [hb]
    exact mul_mem b'.2.1 (pow_mem hxK n)
  by_cases ha2' : a = 2
  · have := le_pRank_of_injective hp1 hc₁ hp₁ hcard₁ F₁ hF₁ (le_top : F₁.range ≤ ⊤)
    omega
  set φ : K →* P := (commHom hc x).comp K.subtype
  have hφrange : φ.range ≤ Ω := by
    rintro _ ⟨y, rfl⟩
    exact hcommΩ x y
  have hφker : Nat.card K ≤ Nat.card φ.ker * p ^ a := by
    have h1 : Nat.card K = Nat.card φ.range * Nat.card φ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    have h2 : Nat.card φ.range ≤ p ^ a := ha ▸ Subgroup.card_le_of_le hφrange
    rw [h1, mul_comm]
    exact Nat.mul_le_mul_left _ h2
  have hker : p ^ (a + 1) < Nat.card φ.ker := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card φ.ker * p ^ a ≤ p ^ (a + 1) * p ^ a := Nat.mul_le_mul_right _ hcon
    rw [← pow_add] at h1
    have h2 : p ^ (a + 1 + a) < p ^ 4 := Nat.pow_lt_pow_right hp1 (by omega)
    omega
  obtain ⟨y, hyS, hyr⟩ := exists_mem_not_mem_range_of_card_lt hF₁ (S := φ.ker.map K.subtype)
    (by rw [hcard₁, Subgroup.card_map_of_injective Subtype.val_injective]; exact hker)
  obtain ⟨⟨y', hy'K⟩, hy'ker, rfl⟩ := Subgroup.mem_map.1 hyS
  have hxy : ⁅x, y'⁆ = 1 := hy'ker
  have hxyc : Commute x y' := commutatorElement_eq_one_iff_mul_comm.1 hxy
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := exists_extend hc₁ hp₁ hcard₁ F₁ hF₁ (y := y')
    hy'K hyr (fun b => by
      obtain ⟨b', n, hb⟩ := hr₁ b
      rw [hb]
      exact (hcen _ b'.2.2 y').mul_left (hxyc.pow_left n))
  by_cases ha1 : a = 1
  · have := le_pRank_of_injective hp1 hc₂ hp₂ hcard₂ F₂ hF₂ (le_top : F₂.range ≤ ⊤)
    omega
  have ha0 : a = 0 := by omega
  rw [ha0, pow_zero] at ha
  have hKcomm : ∀ u ∈ K, ∀ v ∈ K, Commute u v := by
    intro u hu v hv
    have h1 : (⟨⁅u, v⁆, hcommΩ u v⟩ : Ω) = 1 :=
      @Subsingleton.elim _ (Nat.card_eq_one_iff_unique.1 ha).1 _ _
    exact commutatorElement_eq_one_iff_mul_comm.1 (congrArg Subtype.val h1)
  have hF₂K : ∀ b, F₂ b ∈ K := fun b => by
    obtain ⟨b', n, hb⟩ := hr₂ b
    rw [hb]
    exact mul_mem (hF₁K b') (pow_mem hy'K n)
  obtain ⟨z, hzK, hzr⟩ := exists_mem_not_mem_range_of_card_lt hF₂ (S := K)
    (by rw [hcard₂]; exact lt_of_lt_of_le (Nat.pow_lt_pow_right hp1 (by omega)) hK4)
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, -⟩ := exists_extend hc₂ hp₂ hcard₂ F₂ hF₂ (y := z) hzK hzr
    (fun b => hKcomm _ (hF₂K b) _ hzK)
  have := le_pRank_of_injective hp1 hc₃ hp₃ hcard₃ F₃ hF₃ (le_top : F₃.range ≤ ⊤)
  omega

theorem pRank_quotient_le_three {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hG : pRank p (⊤ : Subgroup G) ≤ 2) (A : Subgroup G) [A.Normal]
    (hAZ : A ≤ Subgroup.center G) : pRank p (⊤ : Subgroup (G ⧸ A)) ≤ 3 := by
  have hp1 : 1 < p := hp.out.one_lt
  by_contra hcon
  push Not at hcon
  obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp1 (⊤ : Subgroup (G ⧸ A))
  set P : Subgroup G := E.comap (QuotientGroup.mk' A)
  have hAP : A ≤ P := fun a ha => by
    change (QuotientGroup.mk' A) a ∈ E
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff a).2 ha]
    exact one_mem E
  set A' : Subgroup P := A.subgroupOf P
  have hA'Z : A' ≤ Subgroup.center P := fun a ha => Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hAZ ha) g)
  have hEcomm := hE.1
  have hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A' := by
    intro x y
    rw [Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    have h1 : (⟨QuotientGroup.mk' A x, x.2⟩ : E) * ⟨QuotientGroup.mk' A y, y.2⟩ =
        ⟨QuotientGroup.mk' A y, y.2⟩ * ⟨QuotientGroup.mk' A x, x.2⟩ := mul_comm' _ _
    have h2 := congrArg Subtype.val h1
    change (QuotientGroup.mk' A) ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    change (QuotientGroup.mk' A x) * (QuotientGroup.mk' A y) =
      (QuotientGroup.mk' A y) * (QuotientGroup.mk' A x) at h2
    rw [h2]
    group
  have hpow : ∀ x : P, x ^ p ∈ A' := by
    intro x
    rw [Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' A) ((x : G) ^ p) = 1
    rw [map_pow]
    exact hE.2 _ x.2
  have hindex : p ^ 4 ≤ A'.index := by
    have h1 : Nat.card P = Nat.card A * Nat.card E :=
      QuotientGroup.card_preimage_mk A (E : Set (G ⧸ A))
    have h2 : Nat.card A' = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
    have h3 := A'.card_mul_index
    rw [h1, h2] at h3
    have h4 : A'.index = Nat.card E := Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
    rw [h4, hcard]
    exact Nat.pow_le_pow_right hp.out.pos hcon
  have hPG : pRank p (⊤ : Subgroup P) ≤ 2 :=
    (pRank_top_le_of_injective hp1 P.subtype Subtype.val_injective).trans hG
  have hA'rank : pRank p A' ≤ 2 := (pRank_mono hp1 le_top).trans hPG
  have := three_le_pRank_of_central hp2 A' hA'Z hA'rank hcomm hpow hindex
  omega

end CFSG.SectionRank
