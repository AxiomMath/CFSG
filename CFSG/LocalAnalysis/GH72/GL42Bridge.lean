module

public import CFSG.LocalAnalysis.GH72.GL42

public section

namespace CFSG.GH72

open Subgroup MulAction

variable {G : Type*} [Group G] {A : Subgroup G}

section Image

theorem mem_map_normalizerMonoidHom_iff {Q : Subgroup G} (hQ : Q ≤ normalizer (A : Set G))
    {σ : MulAut A} :
    σ ∈ (Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom ↔
      ∃ q ∈ Q, ∀ a : A, (σ a : G) = q * a * q⁻¹ := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, fun a => rfl⟩
  · rintro ⟨q, hq, hσ⟩
    refine ⟨⟨q, hQ hq⟩, hq, ?_⟩
    ext a
    exact (hσ a).symm

theorem card_map_normalizerMonoidHom {Q : Subgroup G} (hQ : Q ≤ normalizer (A : Set G)) :
    Nat.card ((Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom) =
      (centralizer (A : Set G)).relIndex Q := by
  rw [← relIndex_ker, normalizerMonoidHom_ker, relIndex_subgroupOf hQ]

theorem mem_fixedPoints_map_normalizerMonoidHom_iff {Q : Subgroup G}
    (hQ : Q ≤ normalizer (A : Set G)) (a : A) :
    a ∈ fixedPoints ((Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom) A ↔
      (a : G) ∈ centralizer (Q : Set G) := by
  rw [mem_fixedPoints, mem_centralizer_iff]
  constructor
  · intro h q hq
    have := congrArg Subtype.val
      (h ⟨A.normalizerMonoidHom ⟨q, hQ hq⟩, Subgroup.mem_map_of_mem _ hq⟩)
    change q * a * q⁻¹ = a at this
    calc q * a = q * a * q⁻¹ * q := by group
      _ = a * q := by rw [this]
  · rintro h ⟨σ, hσ⟩
    obtain ⟨q, hq, hσq⟩ := (mem_map_normalizerMonoidHom_iff hQ).mp hσ
    apply Subtype.ext
    change (σ a : G) = a
    rw [hσq, h q hq, mul_inv_cancel_right]

theorem card_fixedPoints_map_normalizerMonoidHom {Q : Subgroup G}
    (hQ : Q ≤ normalizer (A : Set G)) :
    Nat.card (fixedPoints ((Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom) A) =
      Nat.card (A ⊓ centralizer (Q : Set G) : Subgroup G) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1, x.1.2, (mem_fixedPoints_map_normalizerMonoidHom_iff hQ x.1).mp x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩,
        (mem_fixedPoints_map_normalizerMonoidHom_iff hQ ⟨y.1, y.2.1⟩).mpr y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem mem_fixedBy_normalizerMonoidHom_iff {f : G} (hfN : f ∈ normalizer (A : Set G)) (a : A) :
    a ∈ fixedBy A (A.normalizerMonoidHom ⟨f, hfN⟩) ↔ (a : G) ∈ centralizer {f} := by
  rw [mem_fixedBy, MulAut.smul_def, mem_centralizer_singleton_iff, ← Subtype.coe_inj]
  change f * a * f⁻¹ = a ↔ a * f = f * a
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem card_fixedBy_normalizerMonoidHom {f : G} (hfN : f ∈ normalizer (A : Set G)) :
    Nat.card (fixedBy A (A.normalizerMonoidHom ⟨f, hfN⟩)) =
      Nat.card (A ⊓ centralizer {f} : Subgroup G) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1, x.1.2, (mem_fixedBy_normalizerMonoidHom_iff hfN x.1).mp x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩,
        (mem_fixedBy_normalizerMonoidHom_iff hfN ⟨y.1, y.2.1⟩).mpr y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem mem_orbit_map_normalizerMonoidHom_iff {Q : Subgroup G}
    (hQ : Q ≤ normalizer (A : Set G)) (a b : A) :
    b ∈ orbit ((Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom) a ↔
      ∃ q ∈ Q, q * (a : G) * q⁻¹ = b := by
  constructor
  · rintro ⟨⟨σ, hσ⟩, rfl⟩
    obtain ⟨q, hq, hσq⟩ := (mem_map_normalizerMonoidHom_iff hQ).mp hσ
    exact ⟨q, hq, (hσq a).symm⟩
  · rintro ⟨q, hq, hqb⟩
    refine ⟨⟨A.normalizerMonoidHom ⟨q, hQ hq⟩, Subgroup.mem_map_of_mem _ hq⟩, ?_⟩
    apply Subtype.ext
    exact hqb

theorem setOf_conj_eq_image_orbit {Q : Subgroup G} (hQ : Q ≤ normalizer (A : Set G)) (a : A) :
    {b : G | ∃ q ∈ Q, q * (a : G) * q⁻¹ = b} =
      Subtype.val '' orbit ((Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom) a := by
  ext b
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hb : q * (a : G) * q⁻¹ ∈ A := (mem_normalizer_iff.mp (hQ hq) a).mp a.2
    exact ⟨⟨_, hb⟩, (mem_orbit_map_normalizerMonoidHom_iff hQ a ⟨_, hb⟩).mpr ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨b', hb', rfl⟩
    exact (mem_orbit_map_normalizerMonoidHom_iff hQ a b').mp hb'

theorem map_normalizerMonoidHom_mono {Q K : Subgroup G} (hQK : Q ≤ K) :
    (Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom ≤
      (K.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom :=
  map_mono fun _ hx => hQK hx

theorem mul_self_eq_one_of_isE16 (hA : IsE16 A) (v : A) : v * v = 1 := by
  apply Subtype.ext
  have := hA.1.2 v v.2
  rw [pow_two] at this
  exact this

theorem normalizerMonoidHom_transvection {f z : G} (hfN : f ∈ normalizer (A : Set G))
    (hz : z ∈ A) (h : ∀ a ∈ A, a⁻¹ * (f * a * f⁻¹) = 1 ∨ a⁻¹ * (f * a * f⁻¹) = z) :
    ∀ v : A, v⁻¹ * A.normalizerMonoidHom ⟨f, hfN⟩ v = 1 ∨
      v⁻¹ * A.normalizerMonoidHom ⟨f, hfN⟩ v = ⟨z, hz⟩ := by
  intro v
  rcases h v v.2 with h' | h'
  · left
    exact Subtype.ext h'
  · right
    exact Subtype.ext h'

theorem normalizerMonoidHom_eq_one_iff {f : G} (hfN : f ∈ normalizer (A : Set G)) :
    A.normalizerMonoidHom ⟨f, hfN⟩ = 1 ↔ f ∈ centralizer (A : Set G) := by
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf]

theorem normalizerMonoidHom_commute_iff {f g : G} (hfN : f ∈ normalizer (A : Set G))
    (hgN : g ∈ normalizer (A : Set G)) :
    A.normalizerMonoidHom ⟨g, hgN⟩ * A.normalizerMonoidHom ⟨f, hfN⟩ =
        A.normalizerMonoidHom ⟨f, hfN⟩ * A.normalizerMonoidHom ⟨g, hgN⟩ ↔
      ∀ a ∈ A, g * (f * a * f⁻¹) * g⁻¹ = f * (g * a * g⁻¹) * f⁻¹ := by
  constructor
  · intro h a ha
    exact congrArg (fun τ : MulAut A => ((τ ⟨a, ha⟩ : A) : G)) h
  · intro h
    ext a
    exact h a a.2

end Image

variable [Finite G]

theorem relIndex_centralizer_mem_of_odd (hA : IsE16 A) {Q : Subgroup G}
    (hQ : Q ≤ normalizer (A : Set G)) (hodd : Odd ((centralizer (A : Set G)).relIndex Q)) :
    (centralizer (A : Set G)).relIndex Q = 1 ∨ (centralizer (A : Set G)).relIndex Q = 3 ∨
      (centralizer (A : Set G)).relIndex Q = 5 ∨ (centralizer (A : Set G)).relIndex Q = 7 ∨
      (centralizer (A : Set G)).relIndex Q = 9 ∨ (centralizer (A : Set G)).relIndex Q = 15 ∨
      (centralizer (A : Set G)).relIndex Q = 21 := by
  rw [← card_map_normalizerMonoidHom hQ] at hodd ⊢
  exact card_mem_of_odd hA.2 hodd

theorem conj_orbits_of_isolated_subgroup (hA : IsE16 A) {K Q W : Subgroup G}
    (hK : K ≤ normalizer (A : Set G)) (hQK : Q ≤ K)
    (hodd : Odd ((centralizer (A : Set G)).relIndex Q))
    (hQ1 : (centralizer (A : Set G)).relIndex Q ≠ 1) (hWA : W ≤ A) (hW : Nat.card W = 8)
    (hWK : ∀ w ∈ W, ∀ k ∈ K, k * w * k⁻¹ ∈ W → k * w * k⁻¹ = w) :
    (centralizer (A : Set G)).relIndex Q = 3 ∧
      Nat.card (A ⊓ centralizer (Q : Set G) : Subgroup G) = 4 ∧
      A ⊓ centralizer (Q : Set G) ≤ W ∧
      A ⊓ centralizer (K : Set G) = A ⊓ centralizer (Q : Set G) ∧
      (∀ a ∈ A, a ∉ centralizer (Q : Set G) → {b : G | ∃ q ∈ Q, q * a * q⁻¹ = b}.ncard = 3) ∧
      ∀ a ∈ A, ∀ k ∈ K, ∃ q ∈ Q, k * a * k⁻¹ = q * a * q⁻¹ := by
  have hQN : Q ≤ normalizer (A : Set G) := hQK.trans hK
  set Q' := (Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom with hQ'
  set K' := (K.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom with hK'
  have hcard := card_map_normalizerMonoidHom hQN
  rw [← hQ'] at hcard
  have hodd' : Odd (Nat.card Q') := hcard ▸ hodd
  have hQ'1 : Q' ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcard
    exact hQ1 hcard.symm
  set W' : Subgroup A := W.subgroupOf A with hW'
  have hW'c : Nat.card W' = 8 := by
    rw [hW', ← hW]
    exact Nat.card_congr (subgroupOfEquivOfLe hWA).toEquiv
  have hsep : ∀ w ∈ W', ∀ k ∈ K', k w ∈ W' → k w = w := by
    intro w hw k hk hkw
    obtain ⟨g, hg, hkg⟩ := (mem_map_normalizerMonoidHom_iff hK).mp hk
    apply Subtype.ext
    have hkw' : g * (w : G) * g⁻¹ ∈ W := by
      have := (mem_subgroupOf.mp hkw)
      rwa [hkg] at this
    rw [hkg]
    exact hWK w (mem_subgroupOf.mp hw) g hg hkw'
  obtain ⟨h3, h4, hFW, hKF, horb, hKQ⟩ :=
    orbits_of_isolated_subgroup hA.2 (map_normalizerMonoidHom_mono hQK) hodd' hQ'1 hW'c hsep
  refine ⟨hcard ▸ h3, (card_fixedPoints_map_normalizerMonoidHom hQN) ▸ h4, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨hxA, hxQ⟩
    have : (⟨x, hxA⟩ : A) ∈ fixedPoints Q' A :=
      (mem_fixedPoints_map_normalizerMonoidHom_iff hQN ⟨x, hxA⟩).mpr hxQ
    exact mem_subgroupOf.mp (hFW this)
  · ext x
    constructor
    · rintro ⟨hxA, hxK⟩
      refine ⟨hxA, ?_⟩
      have hK'x : (⟨x, hxA⟩ : A) ∈ fixedPoints K' A :=
        (mem_fixedPoints_map_normalizerMonoidHom_iff hK ⟨x, hxA⟩).mpr hxK
      rw [hKF] at hK'x
      exact (mem_fixedPoints_map_normalizerMonoidHom_iff hQN ⟨x, hxA⟩).mp hK'x
    · rintro ⟨hxA, hxQ⟩
      refine ⟨hxA, ?_⟩
      have hQ'x : (⟨x, hxA⟩ : A) ∈ fixedPoints Q' A :=
        (mem_fixedPoints_map_normalizerMonoidHom_iff hQN ⟨x, hxA⟩).mpr hxQ
      rw [← hKF] at hQ'x
      exact (mem_fixedPoints_map_normalizerMonoidHom_iff hK ⟨x, hxA⟩).mp hQ'x
  · intro a ha haQ
    have haF : (⟨a, ha⟩ : A) ∉ fixedPoints Q' A := fun h =>
      haQ ((mem_fixedPoints_map_normalizerMonoidHom_iff hQN ⟨a, ha⟩).mp h)
    rw [show a = ((⟨a, ha⟩ : A) : G) from rfl, setOf_conj_eq_image_orbit hQN,
      Set.ncard_image_of_injective _ Subtype.val_injective]
    exact horb _ haF
  · intro a ha k hk
    obtain ⟨σ, hσ, hkσ⟩ := hKQ ⟨a, ha⟩ (A.normalizerMonoidHom ⟨k, hK hk⟩)
      (Subgroup.mem_map_of_mem _ hk)
    obtain ⟨q, hq, hσq⟩ := (mem_map_normalizerMonoidHom_iff hQN).mp hσ
    refine ⟨q, hq, ?_⟩
    have := congrArg Subtype.val hkσ
    change k * a * k⁻¹ = (σ ⟨a, ha⟩ : G) at this
    rw [this, hσq]

theorem exists_conj_eq_of_relIndex_eq_fifteen (hA : IsE16 A) {Q : Subgroup G}
    (hQ : Q ≤ normalizer (A : Set G)) (h15 : (centralizer (A : Set G)).relIndex Q = 15) :
    ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ q ∈ Q, q * a * q⁻¹ = b := by
  intro a ha b hb ha1 hb1
  have hcard := card_map_normalizerMonoidHom hQ
  rw [h15] at hcard
  obtain ⟨σ, hσ, hσa⟩ := exists_apply_eq_of_card_eq_fifteen hA.2 hcard ⟨a, ha⟩ ⟨b, hb⟩
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨q, hq, hσq⟩ := (mem_map_normalizerMonoidHom_iff hQ).mp hσ
  refine ⟨q, hq, ?_⟩
  have := congrArg Subtype.val hσa
  rw [hσq] at this
  exact this

theorem card_inf_centralizer_eq_two_of_relIndex_eq_twentyOne (hA : IsE16 A) {Q : Subgroup G}
    (hQ : Q ≤ normalizer (A : Set G)) (h21 : (centralizer (A : Set G)).relIndex Q = 21) :
    Nat.card (A ⊓ centralizer (Q : Set G) : Subgroup G) = 2 := by
  have hcard := card_map_normalizerMonoidHom hQ
  rw [h21] at hcard
  rw [← card_fixedPoints_map_normalizerMonoidHom hQ]
  exact (card_fixedPoints_eq_two_of_card_eq_twentyOne hA.2 hcard).1

theorem conj_orbit_eq_of_relIndex_eq_nine (hA : IsE16 A) {Q : Subgroup G}
    (hQ : Q ≤ normalizer (A : Set G)) (h9 : (centralizer (A : Set G)).relIndex Q = 9) {q : G}
    (hqQ : q ∈ Q) (hqA : q ∉ centralizer (A : Set G)) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hqa : q * a * q⁻¹ = a) :
    Nat.card (A ⊓ centralizer {q} : Subgroup G) = 4 ∧
      (∀ g ∈ Q, ∀ b ∈ A ⊓ centralizer {q}, g * b * g⁻¹ ∈ A ⊓ centralizer {q}) ∧
      {b : G | ∃ g ∈ Q, g * a * g⁻¹ = b} = ((A ⊓ centralizer {q} : Subgroup G) : Set G) \ {1} := by
  set Q' := (Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom with hQ'
  have hcard := card_map_normalizerMonoidHom hQ
  rw [h9, ← hQ'] at hcard
  set σ : MulAut A := A.normalizerMonoidHom ⟨q, hQ hqQ⟩ with hσ
  have hσQ : σ ∈ Q' := Subgroup.mem_map_of_mem _ hqQ
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hqA
    rw [mem_centralizer_iff]
    intro x hx
    have := congrArg (fun τ : MulAut A => ((τ ⟨x, hx⟩ : A) : G)) h
    change q * x * q⁻¹ = x at this
    calc x * q = q * x * q⁻¹ * q := by rw [this]
      _ = q * x := by group
  have hσa : σ ⟨a, haA⟩ = ⟨a, haA⟩ := Subtype.ext hqa
  have ha1' : (⟨a, haA⟩ : A) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  obtain ⟨h4, hinv, horb⟩ := orbit_eq_of_card_eq_nine hA.2 hcard hσQ hσ1 ha1' hσa
  have hfix : ∀ x : A, x ∈ fixedBy A σ ↔ (x : G) ∈ centralizer {q} := by
    intro x
    rw [mem_fixedBy, MulAut.smul_def, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg Subtype.val h
      change q * x * q⁻¹ = x at this
      calc (x : G) * q = q * x * q⁻¹ * q := by rw [this]
        _ = q * x := by group
    · intro h
      apply Subtype.ext
      change q * x * q⁻¹ = x
      rw [← h, mul_inv_cancel_right]
  have himg : ((A ⊓ centralizer {q} : Subgroup G) : Set G) = Subtype.val '' fixedBy A σ := by
    ext x
    constructor
    · rintro ⟨hxA, hxq⟩
      exact ⟨⟨x, hxA⟩, (hfix ⟨x, hxA⟩).mpr hxq, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hfix y).mp hy⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, himg,
      Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq, h4]
  · rintro g hg b ⟨hbA, hbq⟩
    have hgN := hQ hg
    have hb' : (⟨b, hbA⟩ : A) ∈ fixedBy A σ := (hfix ⟨b, hbA⟩).mpr hbq
    have := hinv (A.normalizerMonoidHom ⟨g, hgN⟩) (Subgroup.mem_map_of_mem _ hg) _ hb'
    exact ⟨(mem_normalizer_iff.mp hgN b).mp hbA, (hfix _).mp this⟩
  · rw [show a = ((⟨a, haA⟩ : A) : G) from rfl, setOf_conj_eq_image_orbit hQ, ← hQ', horb,
      Set.image_diff Subtype.val_injective, ← himg, Set.image_singleton]
    rfl

theorem exists_conj_eq_of_relIndex_eq_nine (hA : IsE16 A) {Q : Subgroup G}
    (hQ : Q ≤ normalizer (A : Set G)) (h9 : (centralizer (A : Set G)).relIndex Q = 9)
    {X Y : Subgroup G} (hXA : X ≤ A) (hYA : Y ≤ A) (hX : Nat.card X = 4) (hY : Nat.card Y = 4)
    (hXY : X ⊓ Y = ⊥) (hQX : ∀ q ∈ Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    (hQY : ∀ q ∈ Q, ∀ y ∈ Y, q * y * q⁻¹ ∈ Y) :
    ∀ a ∈ A, ∀ b ∈ A, a ∉ X → a ∉ Y → b ∉ X → b ∉ Y → ∃ q ∈ Q, q * a * q⁻¹ = b := by
  intro a ha b hb haX haY hbX hbY
  have hcard := card_map_normalizerMonoidHom hQ
  rw [h9] at hcard
  have hX' : Nat.card (X.subgroupOf A) = 4 := by
    rw [← hX]
    exact Nat.card_congr (subgroupOfEquivOfLe hXA).toEquiv
  have hY' : Nat.card (Y.subgroupOf A) = 4 := by
    rw [← hY]
    exact Nat.card_congr (subgroupOfEquivOfLe hYA).toEquiv
  have hXY' : X.subgroupOf A ⊓ Y.subgroupOf A = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxY⟩
    have : (x : G) ∈ X ⊓ Y := ⟨mem_subgroupOf.mp hxX, mem_subgroupOf.mp hxY⟩
    rw [hXY, mem_bot] at this
    exact (mem_bot).mpr (Subtype.ext this)
  have hinv : ∀ (Z : Subgroup G), (∀ q ∈ Q, ∀ z ∈ Z, q * z * q⁻¹ ∈ Z) →
      ∀ σ ∈ (Q.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom,
        ∀ z ∈ Z.subgroupOf A, σ z ∈ Z.subgroupOf A := by
    intro Z hQZ σ hσ z hz
    obtain ⟨q, hq, hσq⟩ := (mem_map_normalizerMonoidHom_iff hQ).mp hσ
    rw [mem_subgroupOf, hσq]
    exact hQZ q hq z (mem_subgroupOf.mp hz)
  obtain ⟨σ, hσ, hσa⟩ := exists_apply_eq_of_card_eq_nine hA.2 hcard hX' hY' hXY' (hinv X hQX)
    (hinv Y hQY) ⟨a, ha⟩ ⟨b, hb⟩ (fun h => haX (mem_subgroupOf.mp h))
    (fun h => haY (mem_subgroupOf.mp h)) (fun h => hbX (mem_subgroupOf.mp h))
    (fun h => hbY (mem_subgroupOf.mp h))
  obtain ⟨q, hq, hσq⟩ := (mem_map_normalizerMonoidHom_iff hQ).mp hσ
  refine ⟨q, hq, ?_⟩
  have := congrArg Subtype.val hσa
  rw [hσq] at this
  exact this

theorem conj_mem_of_commute_of_inf_centralizer (hA : IsE16 A) {u g : G}
    (hu : u ∈ normalizer (A : Set G)) (hg : g ∈ normalizer (A : Set G)) {X : Subgroup G}
    (hXA : X ≤ A) (hXu : ∀ x ∈ X, u * x * u⁻¹ ∈ X) (hfree : ∀ x ∈ X, u * x * u⁻¹ = x → x = 1)
    (hcard : Nat.card X * Nat.card (A ⊓ centralizer {u} : Subgroup G) = 16)
    (hgu : ∀ a ∈ A, g * (u * a * u⁻¹) * g⁻¹ = u * (g * a * g⁻¹) * u⁻¹) :
    ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
  set ρu : MulAut A := A.normalizerMonoidHom ⟨u, hu⟩ with hρu
  set ρg : MulAut A := A.normalizerMonoidHom ⟨g, hg⟩ with hρg
  have hc : ∀ a b : A, a * b = b * a := fun a b => hA.1.1.is_comm.comm a b
  have hXu' : ∀ x ∈ X.subgroupOf A, ρu x ∈ X.subgroupOf A := fun x hx =>
    mem_subgroupOf.mpr (hXu x (mem_subgroupOf.mp hx))
  have hfree' : ∀ x ∈ X.subgroupOf A, ρu x = x → x = 1 := fun x hx hux =>
    Subtype.ext (hfree x (mem_subgroupOf.mp hx) (congrArg Subtype.val hux))
  have hfixu : Nat.card (fixedBy A ρu) = Nat.card (A ⊓ centralizer {u} : Subgroup G) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1, Subgroup.mem_inf.mpr ⟨x.1.2, by
          rw [mem_centralizer_singleton_iff]
          have := congrArg Subtype.val (show ρu x.1 = x.1 from x.2)
          change u * x.1 * u⁻¹ = x.1 at this
          calc (x.1 : G) * u = u * x.1 * u⁻¹ * u := by rw [this]
            _ = u * x.1 := by group⟩⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
          change ρu ⟨y.1, y.2.1⟩ = ⟨y.1, y.2.1⟩
          apply Subtype.ext
          change u * y.1 * u⁻¹ = y.1
          rw [← mem_centralizer_singleton_iff.mp y.2.2, mul_inv_cancel_right]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard' : Nat.card (X.subgroupOf A) * Nat.card (fixedBy A ρu) = Nat.card A := by
    rw [hfixu, hA.2, ← hcard]
    congr 1
    exact Nat.card_congr (subgroupOfEquivOfLe hXA).toEquiv
  have hgu' : ρg * ρu = ρu * ρg := by
    ext a
    exact hgu a a.2
  intro x hx
  have := apply_mem_of_commute_of_fixedBy hc hXu' hfree' hcard' hgu' ⟨x, hXA hx⟩
    (mem_subgroupOf.mpr hx)
  exact mem_subgroupOf.mp this

omit [Finite G] in
theorem conj_eq_of_commute_of_transvection (hA : IsE16 A) {f z g : G}
    (hfN : f ∈ normalizer (A : Set G)) (hz : z ∈ A)
    (h : ∀ a ∈ A, a⁻¹ * (f * a * f⁻¹) = 1 ∨ a⁻¹ * (f * a * f⁻¹) = z)
    (hf : f ∉ centralizer (A : Set G)) (hgN : g ∈ normalizer (A : Set G))
    (hgf : ∀ a ∈ A, g * (f * a * f⁻¹) * g⁻¹ = f * (g * a * g⁻¹) * f⁻¹) : g * z * g⁻¹ = z := by
  have hf1 : A.normalizerMonoidHom ⟨f, hfN⟩ ≠ 1 := fun h' =>
    hf ((normalizerMonoidHom_eq_one_iff hfN).mp h')
  have := (apply_eq_of_commute_of_transvection (mul_self_eq_one_of_isE16 hA)
    (normalizerMonoidHom_transvection hfN hz h) hf1).2 (A.normalizerMonoidHom ⟨g, hgN⟩)
    ((normalizerMonoidHom_commute_iff hfN hgN).mpr hgf)
  exact congrArg Subtype.val this

theorem card_inf_centralizer_mul_eq_four_of_transvections (hA : IsE16 A) {f₁ f₂ z₁ z₂ c : G}
    (hf₁N : f₁ ∈ normalizer (A : Set G)) (hf₂N : f₂ ∈ normalizer (A : Set G))
    (hf : f₁ * f₂ = f₂ * f₁) (hz₁ : z₁ ∈ A) (hz₂ : z₂ ∈ A)
    (h₁ : ∀ a ∈ A, a⁻¹ * (f₁ * a * f₁⁻¹) = 1 ∨ a⁻¹ * (f₁ * a * f₁⁻¹) = z₁)
    (hf₁ : f₁ ∉ centralizer (A : Set G))
    (h₂ : ∀ a ∈ A, a⁻¹ * (f₂ * a * f₂⁻¹) = 1 ∨ a⁻¹ * (f₂ * a * f₂⁻¹) = z₂)
    (hf₂ : f₂ ∉ centralizer (A : Set G)) (hz : z₁ ≠ z₂) (hcA : c ∈ A)
    (hc₁ : f₁ * c * f₁⁻¹ = c) (hc₂ : f₂ * c * f₂⁻¹ ≠ c) :
    Nat.card (A ⊓ centralizer {f₁ * f₂} : Subgroup G) = 4 := by
  set ρ₁ := A.normalizerMonoidHom ⟨f₁, hf₁N⟩
  set ρ₂ := A.normalizerMonoidHom ⟨f₂, hf₂N⟩
  have hρ : ρ₁ * ρ₂ = ρ₂ * ρ₁ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hf
  have h4 := card_fixedBy_mul_eq_four_of_transvections (mul_self_eq_one_of_isE16 hA) hA.2 hρ
    (normalizerMonoidHom_transvection hf₁N hz₁ h₁)
    (fun h' => hf₁ ((normalizerMonoidHom_eq_one_iff hf₁N).mp h'))
    (normalizerMonoidHom_transvection hf₂N hz₂ h₂)
    (fun h' => hf₂ ((normalizerMonoidHom_eq_one_iff hf₂N).mp h'))
    (fun h' => hz (congrArg Subtype.val h')) (c := ⟨c, hcA⟩) (Subtype.ext hc₁)
    (fun h' => hc₂ (congrArg Subtype.val h'))
  have hmulN : f₁ * f₂ ∈ normalizer (A : Set G) := mul_mem hf₁N hf₂N
  have hρ12 : ρ₁ * ρ₂ = A.normalizerMonoidHom ⟨f₁ * f₂, hmulN⟩ := by
    rw [← map_mul]
    rfl
  rw [hρ12, card_fixedBy_normalizerMonoidHom hmulN] at h4
  exact h4

theorem relIndex_mem_of_transvections (hA : IsE16 A) {f₁ f₂ z₁ z₂ : G}
    (hf₁N : f₁ ∈ normalizer (A : Set G)) (hf₂N : f₂ ∈ normalizer (A : Set G))
    (hf : f₁ * f₂ = f₂ * f₁) (hz₁ : z₁ ∈ A) (hz₂ : z₂ ∈ A)
    (h₁ : ∀ a ∈ A, a⁻¹ * (f₁ * a * f₁⁻¹) = 1 ∨ a⁻¹ * (f₁ * a * f₁⁻¹) = z₁)
    (hf₁ : f₁ ∉ centralizer (A : Set G))
    (h₂ : ∀ a ∈ A, a⁻¹ * (f₂ * a * f₂⁻¹) = 1 ∨ a⁻¹ * (f₂ * a * f₂⁻¹) = z₂)
    (hf₂ : f₂ ∉ centralizer (A : Set G))
    (h₁₂ : Nat.card (A ⊓ centralizer {f₁ * f₂} : Subgroup G) = 4) {Q : Subgroup G}
    (hQ : Q ≤ normalizer (A : Set G)) (hodd : Odd ((centralizer (A : Set G)).relIndex Q))
    (hQ₁ : f₁ ∈ normalizer (Q : Set G)) (hQ₂ : f₂ ∈ normalizer (Q : Set G)) :
    ((centralizer (A : Set G)).relIndex Q = 1 ∨ (centralizer (A : Set G)).relIndex Q = 3 ∨
      (centralizer (A : Set G)).relIndex Q = 9) ∧
    ((centralizer (A : Set G)).relIndex Q = 3 →
      ∃ f ∈ ({f₁, f₂, f₁ * f₂} : Set G), ∀ q ∈ Q, ∀ a ∈ A,
        q * (f * a * f⁻¹) * q⁻¹ = f * (q * a * q⁻¹) * f⁻¹) ∧
    ((centralizer (A : Set G)).relIndex Q = 9 →
      (∀ q ∈ Q, (∀ a ∈ A, q * ((f₁ * f₂) * a * (f₁ * f₂)⁻¹) * q⁻¹ =
        (f₁ * f₂) * (q * a * q⁻¹) * (f₁ * f₂)⁻¹) → q ∈ centralizer (A : Set G)) →
      ∃ u₁ ∈ Q, ∃ u₂ ∈ Q, u₁ ∉ centralizer (A : Set G) ∧ u₂ ∉ centralizer (A : Set G) ∧
        (∀ a ∈ A, u₁ * (f₁ * a * f₁⁻¹) * u₁⁻¹ = f₁ * (u₁ * a * u₁⁻¹) * f₁⁻¹) ∧
        (∀ a ∈ A, u₂ * (f₂ * a * f₂⁻¹) * u₂⁻¹ = f₂ * (u₂ * a * u₂⁻¹) * f₂⁻¹) ∧
        ∀ q ∈ Q, ∃ i j : ℤ, ∀ a ∈ A, q * a * q⁻¹ = (u₁ ^ i * u₂ ^ j) * a * (u₁ ^ i * u₂ ^ j)⁻¹) := by
  set N := normalizer (A : Set G)
  set ρ := A.normalizerMonoidHom
  set Q' := (Q.subgroupOf N).map ρ with hQ'
  set ρ₁ := ρ ⟨f₁, hf₁N⟩ with hρ₁
  set ρ₂ := ρ ⟨f₂, hf₂N⟩ with hρ₂
  have hcard := card_map_normalizerMonoidHom hQ
  rw [← hQ'] at hcard
  have hodd' : Odd (Nat.card Q') := hcard ▸ hodd
  have hρ : ρ₁ * ρ₂ = ρ₂ * ρ₁ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hf
  have hmulN : f₁ * f₂ ∈ N := mul_mem hf₁N hf₂N
  have hρ12 : ρ₁ * ρ₂ = ρ ⟨f₁ * f₂, hmulN⟩ := by
    rw [← map_mul]
    rfl
  have h₁₂' : Nat.card (fixedBy A (ρ₁ * ρ₂)) = 4 := by
    rw [hρ12, card_fixedBy_normalizerMonoidHom hmulN, h₁₂]
  have hnorm : ∀ {f : G} (hfN : f ∈ N), f ∈ normalizer (Q : Set G) →
      ρ ⟨f, hfN⟩ ∈ normalizer (Q' : Set (MulAut A)) := fun {f} hfN hfQ =>
    le_normalizer_map ρ (Subgroup.mem_map_of_mem ρ (mem_normalizer_iff.mpr fun n =>
      mem_normalizer_iff.mp hfQ n))
  obtain ⟨-, -, -, h12bot, -, h139, h3, h9⟩ := card_dvd_three_and_card_eq_of_transvections
    (mul_self_eq_one_of_isE16 hA) hA.2 hρ (normalizerMonoidHom_transvection hf₁N hz₁ h₁)
    (fun h' => hf₁ ((normalizerMonoidHom_eq_one_iff hf₁N).mp h'))
    (normalizerMonoidHom_transvection hf₂N hz₂ h₂)
    (fun h' => hf₂ ((normalizerMonoidHom_eq_one_iff hf₂N).mp h')) h₁₂' hodd'
    (hnorm hf₁N hQ₁) (hnorm hf₂N hQ₂)
  have hcomm : ∀ {f : G} (hfN : f ∈ N) {q : G} (hq : q ∈ Q),
      ρ ⟨q, hQ hq⟩ ∈ C (ρ ⟨f, hfN⟩) ↔ ∀ a ∈ A, q * (f * a * f⁻¹) * q⁻¹ = f * (q * a * q⁻¹) * f⁻¹ :=
    fun hfN q hq => by
      rw [mem_centralizer_singleton_iff]
      exact normalizerMonoidHom_commute_iff hfN (hQ hq)
  refine ⟨hcard ▸ h139, fun hQ3 => ?_, fun hQ9 hno => ?_⟩
  · rcases h3 (hcard ▸ hQ3) with hle | hle | hle
    · refine ⟨f₁, Or.inl rfl, fun q hq => (hcomm hf₁N hq).mp (hle (Subgroup.mem_map_of_mem _ hq))⟩
    · refine ⟨f₂, Or.inr (Or.inl rfl), fun q hq =>
        (hcomm hf₂N hq).mp (hle (Subgroup.mem_map_of_mem _ hq))⟩
    · refine ⟨f₁ * f₂, Or.inr (Or.inr rfl), fun q hq => (hcomm hmulN hq).mp ?_⟩
      rw [← hρ12]
      exact hle (Subgroup.mem_map_of_mem _ hq)
  ·
    have hbot : Q' ⊓ C (ρ₁ * ρ₂) = ⊥ := by
      rw [eq_bot_iff]
      rintro σ ⟨hσ, hσc⟩
      obtain ⟨q, hq, hσq⟩ := (mem_map_normalizerMonoidHom_iff hQ).mp hσ
      have hσeq : σ = ρ ⟨q, hQ hq⟩ := by
        ext a
        exact hσq a
      rw [hσeq, hρ12] at hσc
      have hqC := hno q hq ((hcomm hmulN hq).mp hσc)
      rw [hσeq, Subgroup.mem_bot]
      exact (normalizerMonoidHom_eq_one_iff (hQ hq)).mpr hqC
    obtain ⟨hC₁, hC₂, -⟩ := h9 (hcard ▸ hQ9) hbot
    have hgen : ∀ {f : G} (hfN : f ∈ N), Nat.card (Q' ⊓ C (ρ ⟨f, hfN⟩) : Subgroup (MulAut A)) = 3 →
        ∃ u : G, ∃ hu : u ∈ Q, u ∉ centralizer (A : Set G) ∧
          (∀ a ∈ A, u * (f * a * f⁻¹) * u⁻¹ = f * (u * a * u⁻¹) * f⁻¹) ∧
          Q' ⊓ C (ρ ⟨f, hfN⟩) = zpowers (ρ ⟨u, hQ hu⟩) := by
      intro f hfN h3'
      have hne : Q' ⊓ C (ρ ⟨f, hfN⟩) ≠ ⊥ := fun h' => by
        rw [h', card_bot] at h3'
        norm_num at h3'
      obtain ⟨⟨σ, hσ⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      obtain ⟨u, hu, hσu⟩ := (mem_map_normalizerMonoidHom_iff hQ).mp hσ.1
      have hσeq : σ = ρ ⟨u, hQ hu⟩ := by
        ext a
        exact hσu a
      have hσ1' : σ ≠ 1 := fun h' => hσ1 (Subtype.ext h')
      refine ⟨u, hu, fun huC => hσ1' ?_, (hcomm hfN hu).mp (hσeq ▸ hσ.2), ?_⟩
      · rw [hσeq]
        exact (normalizerMonoidHom_eq_one_iff (hQ hu)).mpr huC
      · rw [← hσeq]
        have hord : orderOf σ = 3 := by
          rcases (Nat.dvd_prime Nat.prime_three).mp (h3' ▸ Subgroup.orderOf_dvd_natCard _ hσ)
            with h1 | h3''
          · exact absurd (orderOf_eq_one_iff.mp h1) hσ1'
          · exact h3''
        exact (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hσ)
          (by rw [Nat.card_zpowers, hord, h3'])).symm
    obtain ⟨u₁, hu₁, hu₁C, hu₁f, hz₁'⟩ := hgen hf₁N hC₁
    obtain ⟨u₂, hu₂, hu₂C, hu₂f, hz₂'⟩ := hgen hf₂N hC₂
    refine ⟨u₁, hu₁, u₂, hu₂, hu₁C, hu₂C, hu₁f, hu₂f, fun q hq => ?_⟩
    have hXY : (Q' ⊓ C ρ₁).subgroupOf Q' ⊓ (Q' ⊓ C ρ₂).subgroupOf Q' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx'
      rw [Subgroup.mem_inf, mem_subgroupOf, mem_subgroupOf] at hx'
      have hx : (x : MulAut A) ∈ Q' ⊓ C ρ₁ ⊓ C ρ₂ := ⟨⟨x.2, hx'.1.2⟩, hx'.2.2⟩
      rw [h12bot, Subgroup.mem_bot] at hx
      exact (Subgroup.mem_bot).mpr (Subtype.ext hx)
    have hcardXY : Nat.card ((Q' ⊓ C ρ₁).subgroupOf Q') * Nat.card ((Q' ⊓ C ρ₂).subgroupOf Q') =
        Nat.card Q' := by
      rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, hC₁, hC₂, hcard, hQ9]
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_eq_of_inf_eq_bot hXY hcardXY
      ⟨ρ ⟨q, hQ hq⟩, Subgroup.mem_map_of_mem ρ (show (⟨q, hQ hq⟩ : N) ∈ Q.subgroupOf N from hq)⟩
    rw [mem_subgroupOf, hz₁'] at hx
    rw [mem_subgroupOf, hρ₂, hz₂'] at hy
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hy
    refine ⟨i, j, fun a ha => ?_⟩
    have hρq : ρ ⟨q, hQ hq⟩ = ρ (⟨u₁, hQ hu₁⟩ ^ i * ⟨u₂, hQ hu₂⟩ ^ j) := by
      rw [map_mul, map_zpow, map_zpow, hi, hj]
      exact (congrArg Subtype.val hxy).symm
    exact congrArg (fun σ : MulAut A => ((σ ⟨a, ha⟩ : A) : G)) hρq

end CFSG.GH72
