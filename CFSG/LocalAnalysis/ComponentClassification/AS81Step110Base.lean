module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
public import CFSG.LargeExtraspecial.AS35IExtra
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure ExtraIn (X : Subgroup G) (z : G) : Prop where
  extraspecial : CFSG.IsExtraspecialPGroup 2 ↥X
  order : orderOf z = 2
  sylow : IsSylowOf 2 (zpowers z) (centralizer (X : Set G))

omit [Finite G] in
theorem centerIn_eq_map_subtype_center (X : Subgroup G) :
    centerIn X = (center ↥X).map X.subtype := by
  ext x
  constructor
  · rintro ⟨hxA, hxC⟩
    exact ⟨⟨x, hxA⟩, mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hxC y y.2),
      rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_iff.mpr fun a ha =>
      congrArg Subtype.val (mem_center_iff.mp hy ⟨a, ha⟩)⟩

namespace ExtraIn

variable {X : Subgroup G} {z : G} (hX : ExtraIn X z)
include hX

theorem centerIn_eq : centerIn X = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZC : centerIn X ≤ centralizer (X : Set G) := inf_le_right
  have hZp : IsPGroup 2 (centerIn X) := hX.extraspecial.1.to_le inf_le_left
  have hPN : zpowers z ≤ normalizer ((centerIn X : Subgroup G) : Set G) :=
    (hX.sylow.le.trans (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hle : centerIn X ≤ zpowers z := by
    have hsup := hX.sylow.isPGroup.to_sup_of_normal_right' hZp hPN
    have heq := hX.sylow.eq_of_le le_sup_left (sup_le hX.sylow.le hZC) hsup
    rw [← heq]
    exact le_sup_right
  refine eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, hX.order, centerIn_eq_map_subtype_center,
    card_map_of_injective X.subtype_injective, hX.extraspecial.2.2.2]

theorem mem : z ∈ X := ((hX.centerIn_eq ▸ mem_zpowers z : z ∈ centerIn X)).1

theorem mem_centralizer : z ∈ centralizer (X : Set G) :=
  ((hX.centerIn_eq ▸ mem_zpowers z : z ∈ centerIn X)).2

theorem commute {x : G} (hx : x ∈ X) : x * z = z * x :=
  mem_centralizer_iff.mp hX.mem_centralizer x hx

theorem commute_of_mem_zpowers {c x : G} (hc : c ∈ zpowers z) (hx : x ∈ X) : x * c = c * x := by
  have : c ∈ centerIn X := hX.centerIn_eq ▸ hc
  exact mem_centralizer_iff.mp this.2 x hx

theorem zpowers_le' : zpowers z ≤ X := Subgroup.zpowers_le.mpr hX.mem

theorem commutator_mem {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
  have h := CFSG.RankThree.Literature.FSmith.commutatorElement_mem_center hX.extraspecial
    (⟨x, hx⟩ : ↥X) ⟨y, hy⟩
  have : ((⁅(⟨x, hx⟩ : ↥X), ⟨y, hy⟩⁆ : ↥X) : G) ∈ centerIn X := by
    rw [centerIn_eq_map_subtype_center]
    exact ⟨_, h, rfl⟩
  rw [hX.centerIn_eq, commutatorElement_def] at this
  simpa using this

theorem sq_mem {x : G} (hx : x ∈ X) : x ^ 2 ∈ zpowers z := by
  have h := CFSG.RankThree.Literature.FSmith.sq_mem_center hX.extraspecial (⟨x, hx⟩ : ↥X)
  have : ((⟨x, hx⟩ ^ 2 : ↥X) : G) ∈ centerIn X := by
    rw [centerIn_eq_map_subtype_center]
    exact ⟨_, h, rfl⟩
  rw [hX.centerIn_eq] at this
  simpa using this

omit hX [Finite G] in
theorem mem_zpowers_iff_of_order {z c : G} (hz : orderOf z = 2) :
    c ∈ zpowers z ↔ c = 1 ∨ c = z := by
  constructor
  · intro hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    have h := zpow_mod_orderOf z k
    rw [hz] at h
    push_cast at h
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [← h, hk, zpow_zero]
    · right
      rw [← h, hk, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem commute_of_mem_normalizer {d : G} (hd : d ∈ normalizer (X : Set G)) :
    d * z = z * d := by
  have hdz : d * z * d⁻¹ ∈ centerIn X := by
    refine ⟨(mem_normalizer_iff.mp hd z).mp hX.mem, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : d⁻¹ * y * d ∈ X := by
      have := (mem_normalizer_iff.mp (inv_mem hd) y).mp hy
      simpa using this
    have h1 := hX.commute hy'
    calc y * (d * z * d⁻¹) = d * ((d⁻¹ * y * d) * z) * d⁻¹ := by group
      _ = d * (z * (d⁻¹ * y * d)) * d⁻¹ := by rw [h1]
      _ = d * z * d⁻¹ * y := by group
  rw [hX.centerIn_eq, mem_zpowers_iff_of_order hX.order] at hdz
  rcases hdz with h | h
  · exfalso
    have hz1 : z = 1 := by
      have h' : d⁻¹ * (d * z * d⁻¹) * d = z := by group
      rw [h, mul_one, inv_mul_cancel] at h'
      exact h'.symm
    have h2 := hX.order
    rw [hz1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [h]

theorem card_centralizer {U : Subgroup G} (hUX : U ≤ X) (hzU : z ∈ U) :
    Nat.card (X ⊓ centralizer (U : Set G) : Subgroup G) * Nat.card U = 2 * Nat.card X := by
  have hA : center ↥X ≤ U.subgroupOf X := by
    intro w hw
    have : (w : G) ∈ centerIn X := by
      rw [centerIn_eq_map_subtype_center]
      exact ⟨w, hw, rfl⟩
    rw [hX.centerIn_eq] at this
    exact Subgroup.zpowers_le.mpr hzU this
  have h := CFSG.LargeExtraspecial.Asc22.card_centralizer_mul_card hX.extraspecial hA
  have h1 : Nat.card (U.subgroupOf X) = Nat.card U :=
    Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv
  have h2 : (centralizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X)).map X.subtype =
      X ⊓ centralizer (U : Set G) := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, mem_centralizer_iff.mpr fun u hu => ?_⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hw ⟨u, hUX hu⟩ (mem_subgroupOf.mpr hu))
    · rintro ⟨hyX, hyC⟩
      refine ⟨⟨y, hyX⟩, mem_centralizer_iff.mpr fun u hu => ?_, rfl⟩
      exact Subtype.ext (mem_centralizer_iff.mp hyC u (mem_subgroupOf.mp hu))
  rw [← h2, card_map_of_injective X.subtype_injective, ← h1, h]

theorem mem_zpowers_of_mem_centralizer {y : G} (hy : y ∈ centralizer (X : Set G)) {n : ℕ}
    (hyn : y ^ 2 ^ n = 1) : y ∈ zpowers z := by
  obtain ⟨a, haC, hay⟩ := AS76b.exists_conj_mem_of_isSylowOf hX.sylow hy hyn
  have ha : a * z = z * a := (mem_centralizer_iff.mp haC z hX.mem).symm
  have hza : ∀ k : ℤ, a⁻¹ * z ^ k * a = z ^ k := fun k => by
    have : a⁻¹ * z * a = z := by
      calc a⁻¹ * z * a = a⁻¹ * (z * a) := by group
        _ = a⁻¹ * (a * z) := by rw [ha]
        _ = z := by group
    rw [show a⁻¹ * z ^ k * a = (a⁻¹ * z * a) ^ k by
      rw [← MulAut.conj_inv_apply]; simp [map_zpow], this]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hay
  refine mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← hza k, hk]
  group

theorem mem_of_commutator_mem {d : G} {n : ℕ} (hdn : d ^ 2 ^ n = 1)
    (hdN : d ∈ normalizer (X : Set G))
    (hdX : ∀ x ∈ X, x * d * x⁻¹ * d⁻¹ ∈ zpowers z) : d ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc1 : ∀ x : G, x ∈ centralizer ({d} : Set G) ↔ x * d * x⁻¹ * d⁻¹ = 1 := fun x => by
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc x * d = x * d * x⁻¹ * d⁻¹ * (d * x) := by group
        _ = d * x := by rw [h, one_mul]
  have hd2 : IsPGroup 2 (zpowers d) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hdn)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hXd : IsPGroup 2 ↥(X ⊔ zpowers d) :=
    hX.extraspecial.1.to_sup_of_normal_left' hd2 (Subgroup.zpowers_le.mpr hdN)
  have hzd : z * d = d * z := (hX.commute_of_mem_normalizer hdN).symm
  by_cases hU : ∀ x ∈ X, x * d = d * x
  · exact hX.zpowers_le' (hX.mem_zpowers_of_mem_centralizer
      (mem_centralizer_iff.mpr fun x hx => hU x hx) hdn)
  push Not at hU
  obtain ⟨x₀, hx₀X, hx₀d⟩ := hU
  have hx₀C : x₀ ∉ centralizer ({d} : Set G) := fun h =>
    hx₀d (mem_centralizer_singleton_iff.mp h)
  have hcz : ∀ x ∈ X, x ∉ centralizer ({d} : Set G) → x * d * x⁻¹ * d⁻¹ = z := by
    intro x hx hxd
    rcases (mem_zpowers_iff_of_order hX.order).mp (hdX x hx) with h | h
    · exact absurd ((hc1 x).mpr h) hxd
    · exact h
  have hcmul : ∀ a ∈ X, ∀ b ∈ X, a * b * d * (a * b)⁻¹ * d⁻¹ =
      (b * d * b⁻¹ * d⁻¹) * (a * d * a⁻¹ * d⁻¹) := by
    intro a ha b hb
    have hcom := hX.commute_of_mem_zpowers (hdX b hb) ha
    calc a * b * d * (a * b)⁻¹ * d⁻¹ = a * (b * d * b⁻¹ * d⁻¹) * (d * a⁻¹ * d⁻¹) := by group
      _ = (b * d * b⁻¹ * d⁻¹) * a * (d * a⁻¹ * d⁻¹) := by rw [hcom]
      _ = (b * d * b⁻¹ * d⁻¹) * (a * d * a⁻¹ * d⁻¹) := by group
  have hz2 : z * z = 1 := by rw [← sq, ← hX.order, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by
    have h2 := hX.order
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hiff : ∀ a ∈ X, ∀ b ∈ X, a * b ∈ centralizer ({d} : Set G) ↔
      (a ∈ centralizer ({d} : Set G) ↔ b ∈ centralizer ({d} : Set G)) := by
    intro a ha b hb
    rw [hc1, hc1, hc1, hcmul a ha b hb]
    rcases (mem_zpowers_iff_of_order hX.order).mp (hdX a ha) with h1 | h1 <;>
    rcases (mem_zpowers_iff_of_order hX.order).mp (hdX b hb) with h2 | h2 <;>
    simp [h1, h2, hz2, hz1]
  set U := X ⊓ centralizer ({d} : Set G) with hUdef
  have hzU : z ∈ U := ⟨hX.mem, mem_centralizer_singleton_iff.mpr hzd⟩
  have hUidx : U.relIndex X = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨x₀, hx₀X, fun b hb => ?_⟩
    have h := hiff b hb x₀ hx₀X
    by_cases hbd : b ∈ centralizer ({d} : Set G)
    · exact Or.inr ⟨⟨hb, hbd⟩, fun h' => hx₀C ((h.mp h'.2).mp hbd)⟩
    · exact Or.inl ⟨⟨X.mul_mem hb hx₀X, h.mpr ⟨fun h' => absurd h' hbd,
        fun h' => absurd h' hx₀C⟩⟩, fun h' => hbd h'.2⟩
  have hUcard : 2 * Nat.card U = Nat.card X := by
    have h := relIndex_mul_card U X
    rwa [hUidx, inf_eq_left.mpr inf_le_left] at h
  have hCcard : Nat.card (X ⊓ centralizer (U : Set G) : Subgroup G) = 4 := by
    have h := hX.card_centralizer (U := U) inf_le_left hzU
    have hpos : 0 < Nat.card U := Nat.card_pos
    nlinarith
  obtain ⟨u, ⟨huX, huC⟩, huz⟩ : ∃ u ∈ X ⊓ centralizer (U : Set G), u ∉ zpowers z := by
    by_contra hcon
    push Not at hcon
    have h := card_le_of_le (show X ⊓ centralizer (U : Set G) ≤ zpowers z from hcon)
    rw [hCcard, Nat.card_zpowers, hX.order] at h
    omega
  have hxu : ∀ x ∈ X, x * u = u * x → x ∈ centralizer ({d} : Set G) := by
    intro x hx hxu
    by_contra hxd
    apply huz
    rw [← hX.centerIn_eq]
    refine ⟨huX, mem_centralizer_iff.mpr fun y hy => ?_⟩
    by_cases hyd : y ∈ centralizer ({d} : Set G)
    · exact (mem_centralizer_iff.mp huC y ⟨hy, hyd⟩)
    · have hx' : x⁻¹ ∉ centralizer ({d} : Set G) := fun h => hxd (by simpa using inv_mem h)
      have hyx : y * x⁻¹ ∈ centralizer ({d} : Set G) :=
        (hiff y hy x⁻¹ (X.inv_mem hx)).mpr ⟨fun h => absurd h hyd, fun h => absurd h hx'⟩
      have h1 := mem_centralizer_iff.mp huC _ ⟨X.mul_mem hy (X.inv_mem hx), hyx⟩
      calc y * u = y * x⁻¹ * (x * u) := by group
        _ = y * x⁻¹ * (u * x) := by rw [hxu]
        _ = (y * x⁻¹ * u) * x := by group
        _ = (u * (y * x⁻¹)) * x := by rw [h1]
        _ = u * y := by group
  have hcu : ∀ x ∈ X, x * d * x⁻¹ * d⁻¹ = x * u * x⁻¹ * u⁻¹ := by
    intro x hx
    by_cases hxd : x ∈ centralizer ({d} : Set G)
    · rw [(hc1 x).mp hxd, mem_centralizer_iff.mp huC x ⟨hx, hxd⟩]
      group
    · rw [hcz x hx hxd]
      rcases (mem_zpowers_iff_of_order hX.order).mp (hX.commutator_mem hx huX) with h | h
      · exfalso
        apply hxd
        refine hxu x hx ?_
        calc x * u = x * u * x⁻¹ * u⁻¹ * (u * x) := by group
          _ = u * x := by rw [h, one_mul]
      · exact h.symm
  have hyC : u⁻¹ * d ∈ centralizer (X : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h := hcu x hx
    have h' : d * x⁻¹ * d⁻¹ = u * x⁻¹ * u⁻¹ := by
      have : x * (d * x⁻¹ * d⁻¹) = x * (u * x⁻¹ * u⁻¹) := by
        simpa [mul_assoc] using h
      exact mul_left_cancel this
    calc x * (u⁻¹ * d) = u⁻¹ * (u * x * u⁻¹) * d := by group
      _ = u⁻¹ * (d * x * d⁻¹) * d := by
          rw [show u * x * u⁻¹ = (u * x⁻¹ * u⁻¹)⁻¹ by group,
            show d * x * d⁻¹ = (d * x⁻¹ * d⁻¹)⁻¹ by group, h']
      _ = u⁻¹ * d * x := by group
  obtain ⟨k, hk⟩ := hXd ⟨u⁻¹ * d, mul_mem (mem_sup_left (inv_mem huX))
    (mem_sup_right (mem_zpowers d))⟩
  have hk' : (u⁻¹ * d) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hy := hX.zpowers_le' (hX.mem_zpowers_of_mem_centralizer hyC hk')
  rw [show d = u * (u⁻¹ * d) by group]
  exact X.mul_mem huX hy


end ExtraIn

section Transvection

omit [Finite G] in
theorem commutator_mul_left_of_commute {a b e : G} (ha : Commute e a) (hb : Commute e b) :
    a * (e * b) * a⁻¹ * (e * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hc : Commute e (a * b * a⁻¹ * b⁻¹) :=
    ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right
  calc a * (e * b) * a⁻¹ * (e * b)⁻¹ = (a * e) * b * a⁻¹ * b⁻¹ * e⁻¹ := by group
    _ = (e * a) * b * a⁻¹ * b⁻¹ * e⁻¹ := by rw [← ha.eq]
    _ = e * (a * b * a⁻¹ * b⁻¹) * e⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * e * e⁻¹ := by rw [hc.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem mul_mem_iff_of_card_le_two_mul {W Z₀ : Subgroup G} (hZW : Z₀ ≤ W)
    (hW : Nat.card W ≤ 2 * Nat.card Z₀) {w w' : G} (hw : w ∈ W) (hw' : w' ∈ W) :
    w * w' ∈ Z₀ ↔ (w ∈ Z₀ ↔ w' ∈ Z₀) := by
  have h := relIndex_mul_card Z₀ W
  rw [inf_eq_left.mpr hZW] at h
  have hpos : Z₀.relIndex W ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := W)).ne h
  have hZpos : 0 < Nat.card Z₀ := Nat.card_pos
  have hle : Z₀.relIndex W ≤ 2 := by
    by_contra hc
    push Not at hc
    have : 3 * Nat.card Z₀ ≤ Z₀.relIndex W * Nat.card Z₀ := Nat.mul_le_mul_right _ hc
    omega
  rcases (show Z₀.relIndex W = 1 ∨ Z₀.relIndex W = 2 by omega) with h1 | h2
  · have hle := relIndex_eq_one.mp h1
    simp [hle hw, hle hw', hle (W.mul_mem hw hw')]
  · have := mul_mem_iff_of_index_two (H := Z₀.subgroupOf W) h2 (a := ⟨w, hw⟩) (b := ⟨w', hw'⟩)
    simpa [mem_subgroupOf] using this

theorem exists_hom_of_transvection {Y U Z₀ D' : Subgroup G} (hUY : U ≤ Y) (hZU : Z₀ ≤ U)
    (hidx : U.relIndex Y = 2) (hZY : ∀ c ∈ Z₀, ∀ y ∈ Y, y * c = c * y)
    (hYY : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Z₀)
    (hC4 : Nat.card (Y ⊓ centralizer (U : Set G) : Subgroup G) ≤ 2 * Nat.card Z₀)
    (hDZ : ∀ d ∈ D', ∀ c ∈ Z₀, d * c * d⁻¹ = c)
    (hYd : ∀ d ∈ D', ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ U)
    (hUd : ∀ d ∈ D', ∀ u ∈ U, u * d * u⁻¹ * d⁻¹ ∈ Z₀) :
    ∃ χ : ↥D' →* Multiplicative (ZMod 2), ∀ d : ↥D',
      χ d = 1 ↔ ∀ y ∈ Y, y * (d : G) * y⁻¹ * (d : G)⁻¹ ∈ Z₀ := by
  classical
  obtain ⟨x₀, hx₀Y, hx₀U⟩ : ∃ x₀ ∈ Y, x₀ ∉ U := by
    by_contra hcon
    push Not at hcon
    rw [relIndex_eq_one.mpr hcon] at hidx
    exact absurd hidx (by norm_num)
  have hidx' : (U.subgroupOf Y).index = 2 := hidx
  have hmemY : ∀ {a b : G}, a ∈ Y → b ∈ Y → (a * b ∈ U ↔ (a ∈ U ↔ b ∈ U)) := fun ha hb => by
    have := mul_mem_iff_of_index_two hidx' (a := ⟨_, ha⟩) (b := ⟨_, hb⟩)
    simpa [mem_subgroupOf] using this
  set w : G → G := fun d => x₀⁻¹ * (d * x₀ * d⁻¹) with hw
  have hdx : ∀ d : G, d * x₀ * d⁻¹ = x₀ * w d := fun d => by simp only [hw]; group
  have hwU : ∀ d ∈ D', w d ∈ U := by
    intro d hd
    have := hYd d hd x₀⁻¹ (Y.inv_mem hx₀Y)
    rw [inv_inv] at this
    simpa [hw, mul_assoc] using this
  have hconjU : ∀ d ∈ D', ∀ u ∈ U, ∃ e ∈ Z₀, d * u * d⁻¹ = e * u := by
    intro d hd u hu
    refine ⟨(u * d * u⁻¹ * d⁻¹)⁻¹, inv_mem (hUd d hd u hu), ?_⟩
    group
  have hwC : ∀ d ∈ D', w d ∈ centralizer (U : Set G) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro u hu
    have huY := hUY hu
    have hwY := hUY (hwU d hd)
    obtain ⟨e, he, hdu⟩ := hconjU d hd u hu
    have hc := hYY x₀ hx₀Y u huY
    have h1 := hDZ d hd _ hc
    have h2 : d * (x₀ * u * x₀⁻¹ * u⁻¹) * d⁻¹ =
        (d * x₀ * d⁻¹) * (d * u * d⁻¹) * (d * x₀ * d⁻¹)⁻¹ * (d * u * d⁻¹)⁻¹ := by group
    rw [hdx, hdu, h1, commutator_mul_left_of_commute
      (Commute.symm (hZY e he _ (Y.mul_mem hx₀Y hwY))) (Commute.symm (hZY e he u huY))] at h2
    have h3 : w d * u * (w d)⁻¹ = u := by
      calc w d * u * (w d)⁻¹ = x₀⁻¹ * (x₀ * w d * u * (x₀ * w d)⁻¹ * u⁻¹) * (u * x₀) := by group
        _ = x₀⁻¹ * (x₀ * u * x₀⁻¹ * u⁻¹) * (u * x₀) := by rw [← h2]
        _ = u := by group
    calc u * w d = w d * u * (w d)⁻¹ * w d := by rw [h3]
      _ = w d * u := by group
  have hwmul : ∀ d d' : G, w (d * d') = w d * (d * w d' * d⁻¹) := fun d d' => by
    simp only [hw]
    group
  set W := Y ⊓ centralizer (U : Set G) with hWdef
  have hZW : Z₀ ≤ W := fun c hc =>
    ⟨hUY (hZU hc), mem_centralizer_iff.mpr fun u hu => hZY c hc u (hUY hu)⟩
  have hwW : ∀ d ∈ D', w d ∈ W := fun d hd => ⟨hUY (hwU d hd), hwC d hd⟩
  have hpar := fun {a b : G} (ha : a ∈ W) (hb : b ∈ W) =>
    mul_mem_iff_of_card_le_two_mul hZW hC4 ha hb
  let χ : ↥D' →* Multiplicative (ZMod 2) :=
    { toFun := fun d => Multiplicative.ofAdd (if w d ∈ Z₀ then 0 else 1)
      map_one' := by
        have : w 1 = 1 := by simp only [hw]; group
        simp [this]
      map_mul' := fun d d' => by
        obtain ⟨e, he, hed⟩ := hconjU d d.2 _ (hwU d' d'.2)
        have hmul : w ((d : G) * d') = e * (w d * w d') := by
          rw [hwmul, hed, ← mul_assoc, (hZY e he _ (hUY (hwU d d.2))), mul_assoc]
        have key : w ((d : G) * d') ∈ Z₀ ↔ (w d ∈ Z₀ ↔ w d' ∈ Z₀) := by
          rw [hmul, ← hpar (hwW d d.2) (hwW d' d'.2)]
          constructor
          · intro h
            have := mul_mem (inv_mem he) h
            simpa using this
          · exact fun h => mul_mem he h
        show Multiplicative.ofAdd (if w ((d : G) * d') ∈ Z₀ then (0 : ZMod 2) else 1) =
          Multiplicative.ofAdd (if w d ∈ Z₀ then (0 : ZMod 2) else 1) *
            Multiplicative.ofAdd (if w d' ∈ Z₀ then (0 : ZMod 2) else 1)
        by_cases h1 : w d ∈ Z₀ <;> by_cases h2 : w d' ∈ Z₀
        · have h3 : w ((d : G) * d') ∈ Z₀ := key.mpr (iff_of_true h1 h2)
          simp only [h1, h2, h3, ↓reduceIte]
          rfl
        · have h3 : w ((d : G) * d') ∉ Z₀ := fun h => h2 ((key.mp h).mp h1)
          simp only [h1, h2, h3, ↓reduceIte]
          rfl
        · have h3 : w ((d : G) * d') ∉ Z₀ := fun h => h1 ((key.mp h).mpr h2)
          simp only [h1, h2, h3, ↓reduceIte]
          rfl
        · have h3 : w ((d : G) * d') ∈ Z₀ := key.mpr (iff_of_false h1 h2)
          simp only [h1, h2, h3, ↓reduceIte]
          rfl }
  refine ⟨χ, fun d => ?_⟩
  change Multiplicative.ofAdd (if w d ∈ Z₀ then (0 : ZMod 2) else 1) = 1 ↔ _
  constructor
  · intro h1 y hy
    have hwz : w d ∈ Z₀ := by
      by_contra hc
      simp only [hc, ↓reduceIte] at h1
      exact absurd (congrArg Multiplicative.toAdd h1) (by decide)
    by_cases hyU : y ∈ U
    · exact hUd d d.2 y hyU
    · have hu : x₀⁻¹ * y ∈ U := (hmemY (Y.inv_mem hx₀Y) hy).mpr
        ⟨fun h => absurd (by simpa using U.inv_mem h) hx₀U, fun h => absurd h hyU⟩
      obtain ⟨e, he, hdu⟩ := hconjU d d.2 _ hu
      have h2 : y * (d : G) * y⁻¹ * (d : G)⁻¹ = x₀ * (w d * e)⁻¹ * x₀⁻¹ := by
        calc y * (d : G) * y⁻¹ * (d : G)⁻¹
            = x₀ * (x₀⁻¹ * y) * ((d : G) * (x₀⁻¹ * y) * (d : G)⁻¹)⁻¹ *
                ((d : G) * x₀ * (d : G)⁻¹)⁻¹ := by group
          _ = x₀ * (x₀⁻¹ * y) * (e * (x₀⁻¹ * y))⁻¹ * (x₀ * w d)⁻¹ := by rw [hdu, hdx]
          _ = x₀ * (w d * e)⁻¹ * x₀⁻¹ := by group
      have hm : (w d * e)⁻¹ ∈ Z₀ := inv_mem (mul_mem hwz he)
      rw [h2, hZY _ hm x₀ hx₀Y, mul_assoc, mul_inv_cancel, mul_one]
      exact hm
  · intro h
    have := h x₀⁻¹ (Y.inv_mem hx₀Y)
    rw [inv_inv] at this
    have hwz : w d ∈ Z₀ := by simpa [hw, mul_assoc] using this
    simp only [hwz, ↓reduceIte]
    rfl

theorem card_le_two_mul_of_transvection {Y U Z₀ D' : Subgroup G} (hUY : U ≤ Y) (hZU : Z₀ ≤ U)
    (hidx : U.relIndex Y = 2) (hZY : ∀ c ∈ Z₀, ∀ y ∈ Y, y * c = c * y)
    (hYY : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Z₀)
    (hC4 : Nat.card (Y ⊓ centralizer (U : Set G) : Subgroup G) ≤ 2 * Nat.card Z₀)
    (hDZ : ∀ d ∈ D', ∀ c ∈ Z₀, d * c * d⁻¹ = c)
    (hYd : ∀ d ∈ D', ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ U)
    (hUd : ∀ d ∈ D', ∀ u ∈ U, u * d * u⁻¹ * d⁻¹ ∈ Z₀) (D'' : Subgroup G)
    (hD'' : ∀ d ∈ D', (∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ Z₀) → d ∈ D'') :
    Nat.card D' ≤ 2 * Nat.card (D' ⊓ D'' : Subgroup G) := by
  obtain ⟨χ, hχ⟩ := exists_hom_of_transvection hUY hZU hidx hZY hYY hC4 hDZ hYd hUd
  have h1 := card_eq_card_quotient_mul_card_subgroup χ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv] at h1
  have h2 : Nat.card χ.range ≤ 2 := by
    have := card_le_card_group χ.range
    rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)), Fintype.card_multiplicative,
      ZMod.card] at this
  have h3 : Nat.card χ.ker ≤ Nat.card (D' ⊓ D'' : Subgroup G) := by
    have hle : χ.ker.map D'.subtype ≤ D' ⊓ D'' := by
      rintro _ ⟨d, hd, rfl⟩
      exact ⟨d.2, hD'' d d.2 ((hχ d).mp hd)⟩
    rw [← card_map_of_injective D'.subtype_injective]
    exact card_le_of_le hle
  calc Nat.card D' = Nat.card χ.range * Nat.card χ.ker := h1
    _ ≤ 2 * Nat.card (D' ⊓ D'' : Subgroup G) := Nat.mul_le_mul h2 h3

end Transvection

end CFSG.ComponentClassification.AS81
