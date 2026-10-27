module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step110Lag

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Cosets

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_mul_mem_of_inj_mod {B D I : Subgroup G} (hIB : I ≤ B) (hID : I ≤ D)
    (f : G → G) (hf : ∀ d ∈ D, f d ∈ B)
    (hmul : ∀ d ∈ D, ∀ e ∈ D, (f d)⁻¹ * f (d * e) * (f e)⁻¹ ∈ I)
    (hfI : ∀ i ∈ I, f i ∈ I) (hker : ∀ d ∈ D, f d ∈ I → d ∈ I)
    (hcard : Nat.card B ≤ Nat.card D) : ∀ b ∈ B, ∃ d ∈ D, (f d)⁻¹ * b ∈ I := by
  have hrel : ∀ d ∈ D, ∀ e ∈ D, (f d)⁻¹ * f (d * e) ∈ I ↔ e ∈ I := by
    intro d hd e he
    have h1 := hmul d hd e he
    constructor
    · intro h2
      apply hker e he
      have : f e = ((f d)⁻¹ * f (d * e) * (f e)⁻¹)⁻¹ * ((f d)⁻¹ * f (d * e)) := by group
      rw [this]
      exact mul_mem (inv_mem h1) h2
    · intro h2
      have : (f d)⁻¹ * f (d * e) = ((f d)⁻¹ * f (d * e) * (f e)⁻¹) * f e := by group
      rw [this]
      exact mul_mem h1 (hfI e h2)
  have hrel' : ∀ d d' : ↥D, (f d)⁻¹ * f d' ∈ I ↔ (d : G)⁻¹ * d' ∈ I := by
    intro d d'
    have := hrel d d.2 ((d : G)⁻¹ * d') (mul_mem (inv_mem d.2) d'.2)
    rwa [mul_inv_cancel_left] at this
  let Φ : ↥D ⧸ I.subgroupOf D → ↥B ⧸ I.subgroupOf B :=
    Quotient.map' (fun d : ↥D => (⟨f d, hf d d.2⟩ : ↥B)) (fun d d' hdd' => by
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hdd' ⊢
      simpa using (hrel' d d').2 (by simpa using hdd'))
  have hΦ : ∀ d : ↥D, Φ (d : ↥D ⧸ I.subgroupOf D) = ((⟨f d, hf d d.2⟩ : ↥B) : _) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H d => ?_
    induction y using QuotientGroup.induction_on with | H d' => ?_
    rw [hΦ, hΦ, QuotientGroup.eq, mem_subgroupOf] at hxy
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa using (hrel' d d').1 (by simpa using hxy)
  have hcD : Nat.card D = Nat.card (↥D ⧸ I.subgroupOf D) * Nat.card I := by
    rw [card_eq_card_quotient_mul_card_subgroup (I.subgroupOf D),
      Nat.card_congr (subgroupOfEquivOfLe hID).toEquiv]
  have hcB : Nat.card B = Nat.card (↥B ⧸ I.subgroupOf B) * Nat.card I := by
    rw [card_eq_card_quotient_mul_card_subgroup (I.subgroupOf B),
      Nat.card_congr (subgroupOfEquivOfLe hIB).toEquiv]
  have hI0 : 0 < Nat.card I := Nat.card_pos
  have hge : Nat.card (↥B ⧸ I.subgroupOf B) ≤ Nat.card (↥D ⧸ I.subgroupOf D) := by
    rw [hcB, hcD] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hI0
  have hbij := hinj.bijective_of_nat_card_le hge
  intro b hb
  obtain ⟨x, hx⟩ := hbij.2 ((⟨b, hb⟩ : ↥B) : ↥B ⧸ I.subgroupOf B)
  induction x using QuotientGroup.induction_on with | H d => ?_
  refine ⟨d, d.2, ?_⟩
  rw [hΦ, QuotientGroup.eq, mem_subgroupOf] at hx
  simpa using hx

end Cosets

section Extra

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {z : G}

omit [Finite G] in
theorem comm_mem_of_mem_normalizer {x d : G} (hx : x ∈ X) (hd : d ∈ normalizer (X : Set G)) :
    x * d * x⁻¹ * d⁻¹ ∈ X := by
  have h := X.mul_mem hx ((mem_normalizer_iff.mp hd _).mp (X.inv_mem hx))
  rwa [show x * (d * x⁻¹ * d⁻¹) = x * d * x⁻¹ * d⁻¹ by group] at h

omit [Finite G] in
theorem commute_of_mem_zpowers_of_commute {w c : G} (hw : w * z = z * w) (hc : c ∈ zpowers z) :
    w * c = c * w := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  exact ((Commute.zpow_right (show Commute w z from hw) k)).eq

omit [Finite G] in
theorem barMap_eq_iff [(zpowers z).Normal] {a b : G} :
    barMap z a = barMap z b ↔ a⁻¹ * b ∈ zpowers z :=
  QuotientGroup.eq

omit [Finite G] in
theorem comm_commute_of_conj {x y d e f : G} (hA : d⁻¹ * y * d = e * y)
    (hB : x⁻¹ * y * x = f * y) (hex : x * e = e * x) (hed : d * e = e * d)
    (hfx : x * f = f * x) (hfd : d * f = f * d) (hef : e * f = f * e) :
    x * d * x⁻¹ * d⁻¹ * y = y * (x * d * x⁻¹ * d⁻¹) := by
  have hA' : d⁻¹ * y = e * y * d⁻¹ := by
    calc d⁻¹ * y = d⁻¹ * y * d * d⁻¹ := by group
      _ = e * y * d⁻¹ := by rw [hA]
  have hB' : x⁻¹ * y = f * y * x⁻¹ := by
    calc x⁻¹ * y = x⁻¹ * y * x * x⁻¹ := by group
      _ = f * y * x⁻¹ := by rw [hB]
  have hC : d * y = e⁻¹ * y * d := by
    have h1 : y * d = e * (d * y) := by
      calc y * d = d * (d⁻¹ * y * d) := by group
        _ = d * (e * y) := by rw [hA]
        _ = e * (d * y) := by rw [← mul_assoc, hed, mul_assoc]
    calc d * y = e⁻¹ * (e * (d * y)) := by group
      _ = e⁻¹ * (y * d) := by rw [← h1]
      _ = e⁻¹ * y * d := by group
  have hD : x * y = f⁻¹ * y * x := by
    have h1 : y * x = f * (x * y) := by
      calc y * x = x * (x⁻¹ * y * x) := by group
        _ = x * (f * y) := by rw [hB]
        _ = f * (x * y) := by rw [← mul_assoc, hfx, mul_assoc]
    calc x * y = f⁻¹ * (f * (x * y)) := by group
      _ = f⁻¹ * (y * x) := by rw [← h1]
      _ = f⁻¹ * y * x := by group
  have hexi : x⁻¹ * e = e * x⁻¹ := by
    calc x⁻¹ * e = x⁻¹ * (e * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * e) * x⁻¹ := by rw [hex]
      _ = e * x⁻¹ := by group
  have hexi' : x * e⁻¹ = e⁻¹ * x := by
    calc x * e⁻¹ = e⁻¹ * (e * x) * e⁻¹ := by group
      _ = e⁻¹ * (x * e) * e⁻¹ := by rw [hex]
      _ = e⁻¹ * x := by group
  calc x * d * x⁻¹ * d⁻¹ * y
      = x * d * x⁻¹ * (d⁻¹ * y) := by group
    _ = x * d * x⁻¹ * (e * y * d⁻¹) := by rw [hA']
    _ = x * d * (x⁻¹ * e) * y * d⁻¹ := by group
    _ = x * d * (e * x⁻¹) * y * d⁻¹ := by rw [hexi]
    _ = x * d * e * (x⁻¹ * y) * d⁻¹ := by group
    _ = x * d * e * (f * y * x⁻¹) * d⁻¹ := by rw [hB']
    _ = x * (d * e) * f * y * x⁻¹ * d⁻¹ := by group
    _ = x * (e * d) * f * y * x⁻¹ * d⁻¹ := by rw [hed]
    _ = x * e * (d * f) * y * x⁻¹ * d⁻¹ := by group
    _ = x * e * (f * d) * y * x⁻¹ * d⁻¹ := by rw [hfd]
    _ = x * e * f * (d * y) * x⁻¹ * d⁻¹ := by group
    _ = x * e * f * (e⁻¹ * y * d) * x⁻¹ * d⁻¹ := by rw [hC]
    _ = (x * e) * f * e⁻¹ * y * d * x⁻¹ * d⁻¹ := by group
    _ = (e * x) * f * e⁻¹ * y * d * x⁻¹ * d⁻¹ := by rw [hex]
    _ = e * (x * f) * e⁻¹ * y * d * x⁻¹ * d⁻¹ := by group
    _ = e * (f * x) * e⁻¹ * y * d * x⁻¹ * d⁻¹ := by rw [hfx]
    _ = e * f * (x * e⁻¹) * y * d * x⁻¹ * d⁻¹ := by group
    _ = e * f * (e⁻¹ * x) * y * d * x⁻¹ * d⁻¹ := by rw [hexi']
    _ = e * f * e⁻¹ * (x * y) * d * x⁻¹ * d⁻¹ := by group
    _ = e * f * e⁻¹ * (f⁻¹ * y * x) * d * x⁻¹ * d⁻¹ := by rw [hD]
    _ = (e * f) * e⁻¹ * f⁻¹ * (y * x * d * x⁻¹ * d⁻¹) := by group
    _ = (f * e) * e⁻¹ * f⁻¹ * (y * x * d * x⁻¹ * d⁻¹) := by rw [hef]
    _ = y * (x * d * x⁻¹ * d⁻¹) := by group

namespace ExtraIn

variable (hX : ExtraIn X z)
include hX

theorem comm_commute_of_comm_mem {x y d : G} (hx : x ∈ X) (hy : y ∈ X)
    (hd : d ∈ normalizer (X : Set G)) (hyd : y * d * y⁻¹ * d⁻¹ ∈ zpowers z) :
    x * d * x⁻¹ * d⁻¹ * y = y * (x * d * x⁻¹ * d⁻¹) := by
  have hzd : d * z = z * d := hX.commute_of_mem_normalizer hd
  have hzx : x * z = z * x := hX.commute hx
  have hzdi : d⁻¹ * z = z * d⁻¹ := by
    calc d⁻¹ * z = d⁻¹ * (z * d) * d⁻¹ := by group
      _ = d⁻¹ * (d * z) * d⁻¹ := by rw [hzd]
      _ = z * d⁻¹ := by group
  have heZ : d⁻¹ * y * d * y⁻¹ ∈ zpowers z := by
    have h1 : d⁻¹ * y * d * y⁻¹ = d⁻¹ * (y * d * y⁻¹ * d⁻¹) * d := by group
    rw [h1, mul_assoc d⁻¹, ← commute_of_mem_zpowers_of_commute hzd hyd, inv_mul_cancel_left]
    exact hyd
  have hfZ : x⁻¹ * y * x * y⁻¹ ∈ zpowers z := by
    have h1 := hX.commutator_mem (X.inv_mem hx) hy
    rwa [inv_inv] at h1
  refine comm_commute_of_conj (e := d⁻¹ * y * d * y⁻¹) (f := x⁻¹ * y * x * y⁻¹) (by group)
    (by group) (commute_of_mem_zpowers_of_commute hzx heZ)
    (commute_of_mem_zpowers_of_commute hzd heZ) (commute_of_mem_zpowers_of_commute hzx hfZ)
    (commute_of_mem_zpowers_of_commute hzd hfZ) ?_
  obtain ⟨a, ha⟩ := mem_zpowers_iff.mp heZ
  obtain ⟨b, hb⟩ := mem_zpowers_iff.mp hfZ
  rw [← ha, ← hb]
  exact (Commute.zpow_zpow_self z a b).eq

theorem exists_comm_of_le_centralizer [(zpowers z).Normal] {d : G}
    (hd : d ∈ normalizer (X : Set G)) {w : G} (hwX : w ∈ X)
    (hw : ∀ y ∈ X, y * d * y⁻¹ * d⁻¹ ∈ zpowers z → w * y = y * w) :
    ∃ u ∈ X, (u * d * u⁻¹ * d⁻¹)⁻¹ * w ∈ zpowers z := by
  have hzd : d * z = z * d := hX.commute_of_mem_normalizer hd
  let ψ : ↥X →* G ⧸ zpowers z :=
    { toFun := fun u => barMap z ((u : G) * d * (u : G)⁻¹ * d⁻¹)
      map_one' := by simp
      map_mul' := fun u v => by
        show barMap z (((u * v : ↥X) : G) * d * ((u * v : ↥X) : G)⁻¹ * d⁻¹) =
          barMap z ((u : G) * d * (u : G)⁻¹ * d⁻¹) * barMap z ((v : G) * d * (v : G)⁻¹ * d⁻¹)
        rw [← map_mul, barMap_eq_iff, Subgroup.coe_mul]
        have haX : (u : G) * d * (u : G)⁻¹ * d⁻¹ ∈ X := comm_mem_of_mem_normalizer u.2 hd
        have hbX : (v : G) * d * (v : G)⁻¹ * d⁻¹ ∈ X := comm_mem_of_mem_normalizer v.2 hd
        have hc₁ := hX.commutator_mem u.2 (X.inv_mem hbX)
        have hc₂ := hX.commutator_mem (X.inv_mem haX) (X.inv_mem hbX)
        rw [inv_inv] at hc₁
        rw [inv_inv, inv_inv] at hc₂
        have hcomm := commute_of_mem_zpowers_of_commute (hX.commute (X.inv_mem haX)) hc₁
        set a := (u : G) * d * (u : G)⁻¹ * d⁻¹ with ha
        set b := (v : G) * d * (v : G)⁻¹ * d⁻¹ with hb
        have e1 : ((u : G) * v * d * ((u : G) * v)⁻¹ * d⁻¹)⁻¹ * (a * b) =
            a⁻¹ * ((u : G) * b⁻¹ * (u : G)⁻¹ * b) * (b⁻¹ * a * b) := by
          rw [ha, hb]
          group
        rw [e1, hcomm, mul_assoc]
        refine mul_mem hc₁ ?_
        rw [show a⁻¹ * (b⁻¹ * a * b) = a⁻¹ * b⁻¹ * a * b by group]
        exact hc₂ }
  have hψ : ∀ u : ↥X, ψ u = barMap z ((u : G) * d * (u : G)⁻¹ * d⁻¹) := fun _ => rfl
  set C₀ := ψ.ker.map X.subtype with hC₀
  have hC₀X : C₀ ≤ X := map_subtype_le _
  have hmemC₀ : ∀ y ∈ C₀, y * d * y⁻¹ * d⁻¹ ∈ zpowers z := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : barMap z ((y : G) * d * (y : G)⁻¹ * d⁻¹) = 1 := hy
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hzC₀ : z ∈ C₀ := by
    refine ⟨⟨z, hX.mem⟩, ?_, rfl⟩
    show barMap z (z * d * z⁻¹ * d⁻¹) = 1
    rw [show z * d * z⁻¹ * d⁻¹ = 1 by rw [← hzd]; group, map_one]
  set W := X ⊓ centralizer (C₀ : Set G) with hW
  have hzW : z ∈ W := ⟨hX.mem, mem_centralizer_iff.mpr fun y hy => (hX.commute (hC₀X hy))⟩
  have hrange : ψ.range ≤ W.map (barMap z) := by
    rintro _ ⟨u, rfl⟩
    refine ⟨(u : G) * d * (u : G)⁻¹ * d⁻¹, ⟨comm_mem_of_mem_normalizer u.2 hd,
      mem_centralizer_iff.mpr fun y hy => ?_⟩, rfl⟩
    exact (hX.comm_commute_of_comm_mem u.2 (hC₀X hy) hd (hmemC₀ y hy)).symm
  have hcard1 := card_ker_mul_card_range ψ
  have hker : Nat.card ψ.ker = Nat.card C₀ := (card_map_of_injective X.subtype_injective).symm
  have hcard2 := hX.card_centralizer hC₀X hzC₀
  have hcard3 : Nat.card W = 2 * Nat.card (W.map (barMap z)) := by
    have h := card_comap_barMap (W.map (barMap z))
    rw [comap_map_barMap hzW, Nat.card_zpowers, hX.order] at h
    exact h
  have hC₀pos : 0 < Nat.card C₀ := Nat.card_pos
  have heq : ψ.range = W.map (barMap z) := by
    refine eq_of_le_of_card_ge hrange ?_
    rw [hker] at hcard1
    rw [hcard3] at hcard2
    have h1 : Nat.card C₀ * Nat.card (W.map (barMap z)) = Nat.card C₀ * Nat.card ψ.range := by
      nlinarith
    exact (Nat.eq_of_mul_eq_mul_left hC₀pos h1).le
  have hwW : barMap z w ∈ W.map (barMap z) :=
    ⟨w, ⟨hwX, mem_centralizer_iff.mpr fun y hy => (hw y (hC₀X hy) (hmemC₀ y hy)).symm⟩, rfl⟩
  rw [← heq] at hwW
  obtain ⟨u, hu⟩ := hwW
  rw [hψ, barMap_eq_iff] at hu
  exact ⟨u, u.2, hu⟩

end ExtraIn

end Extra

section Conf

variable {K : Type} [Group K] [Finite K] {z : K} {X : Subgroup K} {g : K}

namespace Conf110

variable (hc : Conf110 z X g)
include hc

theorem exists_comm_mem (card_eq : Nat.card (tim77B X g) = Nat.card (tim77D X g))
    (fixD : ∀ d ∈ tim77D X g, d ∉ tim77I X g → ∀ x ∈ X,
      x * d * x⁻¹ * d⁻¹ ∈ tim77I X g → x ∈ tim77B X g)
    {x₀ : K} (hx₀ : x₀ ∈ X) (hx₀B : x₀ ∉ tim77B X g) :
    ∀ b ∈ tim77B X g, ∃ d ∈ tim77D X g, (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * b ∈ tim77I X g := by
  refine exists_inv_mul_mem_of_inj_mod tim77I_le_tim77B tim77I_le_tim77D
    (fun d => x₀ * d * x₀⁻¹ * d⁻¹) (fun d hd => hc.comm_X_D hx₀ hd) (fun d hd e he => ?_)
    (fun i hi => hc.zpowers_le_I (hc.extra.commutator_mem hx₀ hi.1))
    (fun d hd h => by_contra fun hdI => hx₀B (fixD d hd hdI x₀ hx₀ h)) card_eq.le
  have hb := hc.comm_X_D hx₀ he
  have h1 := comm_tim77B_tim77D hb hd
  have e1 : (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * (x₀ * (d * e) * x₀⁻¹ * (d * e)⁻¹) *
      (x₀ * e * x₀⁻¹ * e⁻¹)⁻¹ =
      ((x₀ * e * x₀⁻¹ * e⁻¹) * d * (x₀ * e * x₀⁻¹ * e⁻¹)⁻¹ * d⁻¹)⁻¹ := by group
  rw [e1]
  exact inv_mem h1

noncomputable def commHom {i : K} (hiI : i ∈ tim77I X g) : ↥(tim77L X g) →* ↥(zpowers z) where
  toFun l := ⟨i * l * i⁻¹ * (l : K)⁻¹, hc.config.center i hiI l l.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    have hb := hc.config.center i hiI b b.2
    have hc' : (a : K) * (i * b * i⁻¹ * (b : K)⁻¹) = (i * b * i⁻¹ * (b : K)⁻¹) * a :=
      hc.commute_of_mem_zpowers hb a
    show i * ((a : K) * b) * i⁻¹ * ((a : K) * b)⁻¹ =
      (i * a * i⁻¹ * (a : K)⁻¹) * (i * b * i⁻¹ * (b : K)⁻¹)
    calc i * ((a : K) * b) * i⁻¹ * ((a : K) * b)⁻¹
        = (i * a * i⁻¹ * (a : K)⁻¹) * ((a : K) * (i * b * i⁻¹ * (b : K)⁻¹)) * (a : K)⁻¹ := by
          group
      _ = (i * a * i⁻¹ * (a : K)⁻¹) * (i * b * i⁻¹ * (b : K)⁻¹) := by rw [hc']; group

theorem tim77B_le_centralizer_of_Z4 {i : K} (hiI : i ∈ tim77I X g)
    (hIi : tim77I X g = zpowers i) (card_eq : Nat.card (tim77B X g) = Nat.card (tim77D X g))
    (fixD : ∀ d ∈ tim77D X g, d ∉ tim77I X g → ∀ x ∈ X,
      x * d * x⁻¹ * d⁻¹ ∈ tim77I X g → x ∈ tim77B X g)
    (lt_B : tim77B X g < X) : tim77B X g ≤ centralizer ({i} : Set K) := by
  obtain ⟨x₀, hx₀X, hx₀B⟩ := IsConcreteLE.exists_of_lt lt_B
  intro b hb
  obtain ⟨d, hd, hdb⟩ := hc.exists_comm_mem card_eq fixD hx₀X hx₀B b hb
  set χ := hc.commHom hiI with hχ
  have hχv : ∀ l : ↥(tim77L X g), ((χ l : ↥(zpowers z)) : K) = i * l * i⁻¹ * (l : K)⁻¹ :=
    fun _ => rfl
  have hXL : ∀ {x : K}, x ∈ X → x ∈ tim77L X g := fun hx => (le_sup_left : X ≤ tim77L X g) hx
  have hDL : ∀ {x : K}, x ∈ tim77D X g → x ∈ tim77L X g :=
    fun hx => (le_sup_right : rightConjugate X g ≤ tim77L X g) hx.1
  have hIL : ∀ {x : K}, x ∈ tim77I X g → x ∈ tim77L X g := fun hx => hXL hx.1
  have hBL : b ∈ tim77L X g := hXL hb.1
  have hzc : ∀ a b : ↥(zpowers z), a * b = b * a := by
    intro a b
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp a.2
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn]
    exact (Commute.zpow_zpow_self z m n).eq
  have hχc : χ ⟨x₀ * d * x₀⁻¹ * d⁻¹, hXL (hc.comm_X_D hx₀X hd).1⟩ = 1 := by
    have e : (⟨x₀ * d * x₀⁻¹ * d⁻¹, hXL (hc.comm_X_D hx₀X hd).1⟩ : ↥(tim77L X g)) =
        ⟨x₀, hXL hx₀X⟩ * ⟨d, hDL hd⟩ * (⟨x₀, hXL hx₀X⟩ : ↥(tim77L X g))⁻¹ *
          (⟨d, hDL hd⟩ : ↥(tim77L X g))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hzc (χ _) (χ _)]
    group
  set j := (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * b with hjdef
  have hj : j ∈ zpowers i := hIi ▸ hdb
  have hχj : χ ⟨j, hIL hdb⟩ = 1 := by
    apply Subtype.ext
    rw [hχv]
    show i * j * i⁻¹ * j⁻¹ = 1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hj
    rw [← hk]
    group
  have e2 : (⟨b, hBL⟩ : ↥(tim77L X g)) =
      ⟨x₀ * d * x₀⁻¹ * d⁻¹, hXL (hc.comm_X_D hx₀X hd).1⟩ * ⟨j, hIL hdb⟩ := by
    apply Subtype.ext
    show b = x₀ * d * x₀⁻¹ * d⁻¹ * j
    rw [hjdef]
    group
  have hχb : χ ⟨b, hBL⟩ = 1 := by rw [e2, map_mul, hχc, hχj, one_mul]
  have h1 := congrArg Subtype.val hχb
  rw [hχv] at h1
  rw [mem_centralizer_singleton_iff]
  calc b * i = (i * b * i⁻¹ * b⁻¹)⁻¹ * (i * b) := by group
    _ = i * b := by rw [h1]; simp

theorem false_of_Z4 {i : K} (hiI : i ∈ tim77I X g) (hii : i * i = z)
    (hIi : tim77I X g = zpowers i) (card_eq : Nat.card (tim77B X g) = Nat.card (tim77D X g))
    (fixD : ∀ d ∈ tim77D X g, d ∉ tim77I X g → ∀ x ∈ X,
      x * d * x⁻¹ * d⁻¹ ∈ tim77I X g → x ∈ tim77B X g)
    (lt_B : tim77B X g < X) : False := by
  have := zpowers_normal_of_mem_center hc.center
  have hBi := hc.tim77B_le_centralizer_of_Z4 hiI hIi card_eq fixD lt_B
  obtain ⟨d, hd, hdI⟩ := hc.exists_mem_D_not_mem_I
  have hw : ∀ y ∈ X, y * d * y⁻¹ * d⁻¹ ∈ zpowers z → i * y = y * i := by
    intro y hy hyd
    have hyB := fixD d hd hdI y hy (hc.zpowers_le_I hyd)
    exact (mem_centralizer_singleton_iff.mp (hBi hyB)).symm
  obtain ⟨u, huX, hu⟩ := hc.extra.exists_comm_of_le_centralizer hd.2 hiI.1 hw
  set c := u * d * u⁻¹ * d⁻¹ with hcdef
  set e := c⁻¹ * i with hedef
  have hci : c = i * e⁻¹ := by rw [hedef]; group
  have hcI : c ∈ tim77I X g := by
    rw [hci]
    exact mul_mem hiI (inv_mem (hc.zpowers_le_I hu))
  have huB := fixD d hd hdI u huX hcI
  have hui : u * i = i * u := mem_centralizer_singleton_iff.mp (hBi huB)
  have hue : u * e⁻¹ = e⁻¹ * u := hc.commute_of_mem_zpowers (inv_mem hu) u
  have huc : u * c = c * u := by
    rw [hci]
    calc u * (i * e⁻¹) = i * (u * e⁻¹) := by rw [← mul_assoc, hui, mul_assoc]
      _ = i * e⁻¹ * u := by rw [hue, mul_assoc]
  have hu2 : u * u ∈ zpowers z := by
    rw [← sq]
    exact hc.extra.sq_mem huX
  have hcc : c * c = 1 := by
    have hwdef : u⁻¹ * c = d * u⁻¹ * d⁻¹ := by rw [hcdef]; group
    have huw : u * (u⁻¹ * c) = (u⁻¹ * c) * u := by
      calc u * (u⁻¹ * c) = c := by group
        _ = u⁻¹ * (u * c) := by group
        _ = u⁻¹ * (c * u) := by rw [huc]
        _ = (u⁻¹ * c) * u := by group
    have hdu : d * (u * u)⁻¹ * d⁻¹ = (u * u)⁻¹ := hc.conj_of_mem_zpowers (inv_mem hu2) d
    calc c * c = (u * (u⁻¹ * c)) * (u * (u⁻¹ * c)) := by group
      _ = u * ((u⁻¹ * c) * u) * (u⁻¹ * c) := by group
      _ = u * (u * (u⁻¹ * c)) * (u⁻¹ * c) := by rw [← huw]
      _ = u * u * ((u⁻¹ * c) * (u⁻¹ * c)) := by group
      _ = u * u * ((d * u⁻¹ * d⁻¹) * (d * u⁻¹ * d⁻¹)) := by rw [hwdef]
      _ = u * u * (d * (u * u)⁻¹ * d⁻¹) := by group
      _ = u * u * (u * u)⁻¹ := by rw [hdu]
      _ = 1 := mul_inv_cancel _
  have hee : e⁻¹ * e⁻¹ = 1 := by
    rw [← mul_inv_rev]
    have : e * e = 1 := mul_self_eq_one_of_mem_zpowers hc.extra.order hu
    rw [this, inv_one]
  have hcz : c * c = z := by
    have hie : e⁻¹ * i = i * e⁻¹ := (hc.commute_of_mem_zpowers (inv_mem hu) i).symm
    calc c * c = i * e⁻¹ * (i * e⁻¹) := by rw [← hci]
      _ = i * (e⁻¹ * i) * e⁻¹ := by group
      _ = i * (i * e⁻¹) * e⁻¹ := by rw [hie]
      _ = i * i * (e⁻¹ * e⁻¹) := by group
      _ = z := by rw [hii, hee, mul_one]
  exact hc.z_ne_one (hcz.symm.trans hcc)

theorem false_of_natural' (card_eq : Nat.card (tim77B X g) = Nat.card (tim77D X g))
    (fixD : ∀ d ∈ tim77D X g, d ∉ tim77I X g → ∀ x ∈ X,
      x * d * x⁻¹ * d⁻¹ ∈ tim77I X g → x ∈ tim77B X g)
    (lt_B : tim77B X g < X) (h4 : 4 * Nat.card (tim77I X g) ≤ Nat.card (tim77D X g)) :
    False := by
  have hY2 : ∀ y ∈ X, y * y ∈ zpowers z := fun y hy => by
    rw [← sq]
    exact hc.extra.sq_mem hy
  rcases hc.cases_I with hI | ⟨i, hiI, hii, hIi⟩ | h8
  ·
    have hIz : Nat.card (tim77I X g) = 2 := le_antisymm
      (hc.card_zpowers_z ▸ card_le_of_le hI) (hc.card_zpowers_z ▸ card_le_of_le hc.zpowers_le_I)
    have hBne : ¬ X ≤ tim77B X g := by
      intro hXB
      obtain ⟨d, hd, hdI⟩ := hc.exists_mem_D_not_mem_I
      exact hdI (hc.mem_I_of_comm hd fun x hx => hI (comm_tim77B_tim77D (hXB hx) hd))
    exact false_of_lagrangian (Y := X) (B₁ := tim77B X g) (D₀ := tim77D X g) hc.center
      hc.extra.order hY2 inf_le_left hc.z_mem_B hBne
      (hc.extra.card_centralizer inf_le_left hc.z_mem_B).le (by omega)
      (fun d hd y hy => hc.comm_X_D hy hd) (fun d hd b hb => hI (comm_tim77B_tim77D hb hd))
      (fun d hd hdz x hx hxd => fixD d hd (fun h => hdz (hI h)) x hx (hc.zpowers_le_I hxd))
      card_eq.le
  · exact hc.false_of_Z4 hiI hii hIi card_eq fixD lt_B
  ·
    have hBC := hc.card_eq_four_mul_of_Q8 h8 tim77I_le_tim77B
      (fun b hb j hj => hc.extra.commutator_mem hj.1 (mem_inf.mp hb).1)
    have hDC := hc.card_eq_four_mul_of_Q8 h8 tim77I_le_tim77D
      (fun d hd j hj => hc.comm_I_D hj hd)
    have hZI : ∀ c ∈ tim77I X g, c ∈ centralizer (tim77I X g : Set K) → c ∈ zpowers z :=
      fun c hcI hcC => hc.center_I_le h8 hcI fun j hj => mem_centralizer_iff.mp hcC j hj
    have hzC : z ∈ centralizer (tim77I X g : Set K) :=
      mem_centralizer_iff.mpr fun j _ => hc.commute_z j
    have hDI := card_lt_of_lt hc.config.lt_D
    have hBne : ¬ X ⊓ centralizer (tim77I X g : Set K) ≤
        tim77B X g ⊓ centralizer (tim77I X g : Set K) := by
      intro hYB
      obtain ⟨d, hd, hdz⟩ : ∃ d ∈ tim77D X g ⊓ centralizer (tim77I X g : Set K),
          d ∉ zpowers z := by
        by_contra hcon
        push Not at hcon
        have h1 := card_le_of_le (show tim77D X g ⊓ centralizer (tim77I X g : Set K) ≤
          zpowers z from fun d hd => hcon d hd)
        rw [hc.card_zpowers_z] at h1
        omega
      exact hdz (hc.mem_zpowers_of_comm_of_Q8 h8 hd fun y hy =>
        hZI _ (comm_tim77B_tim77D (mem_inf.mp (hYB hy)).1 (mem_inf.mp hd).1)
          (commutator_mem_of_mem (mem_inf.mp hy).2 (mem_inf.mp hd).2))
    exact false_of_lagrangian (Y := X ⊓ centralizer (tim77I X g : Set K))
      (B₁ := tim77B X g ⊓ centralizer (tim77I X g : Set K))
      (D₀ := tim77D X g ⊓ centralizer (tim77I X g : Set K)) hc.center hc.extra.order
      (fun y hy => hY2 y (mem_inf.mp hy).1) (inf_le_inf_right _ inf_le_left)
      ⟨hc.z_mem_B, hzC⟩ hBne (hc.card_centralizer_le_of_Q8' h8) (by omega)
      (fun d hd y hy => ⟨hc.comm_X_D (mem_inf.mp hy).1 (mem_inf.mp hd).1,
        commutator_mem_of_mem (mem_inf.mp hy).2 (mem_inf.mp hd).2⟩)
      (fun d hd b hb => hZI _ (comm_tim77B_tim77D (mem_inf.mp hb).1 (mem_inf.mp hd).1)
        (commutator_mem_of_mem (mem_inf.mp hb).2 (mem_inf.mp hd).2))
      (fun d hd hdz y hy hyd => by
        have hdI : d ∉ tim77I X g := fun h => hdz (hZI d h (mem_inf.mp hd).2)
        exact ⟨fixD d (mem_inf.mp hd).1 hdI y (mem_inf.mp hy).1 (hc.zpowers_le_I hyd),
          (mem_inf.mp hy).2⟩)
      (by omega)

theorem false_of_tim77Facts (hX : 128 ≤ Nat.card X)
    (card_eq : Nat.card (tim77B X g) = Nat.card (tim77D X g))
    (fixD : ∀ d ∈ tim77D X g, d ∉ tim77I X g → ∀ x ∈ X,
      x * d * x⁻¹ * d⁻¹ ∈ tim77I X g → x ∈ tim77B X g)
    (lt_B : tim77B X g < X)
    (cases : 2 * Nat.card (tim77B X g) = Nat.card X ∨
      4 * Nat.card (tim77I X g) ≤ Nat.card (tim77D X g)) : False := by
  rcases cases with hB | h4
  · exact hc.false_of_dihedral hX hB (card_eq ▸ hB)
  · exact hc.false_of_natural' card_eq fixD lt_B h4

end Conf110

end Conf

end CFSG.ComponentClassification.AS81
