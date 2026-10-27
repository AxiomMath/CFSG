module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.InductionSylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf {X Y : Subgroup G} (h : X ≤ normalizer (Y : Set G)) :
    Nat.card (X ⊔ Y : Subgroup G) * Nat.card (X ⊓ Y : Subgroup G) = Nat.card X * Nat.card Y := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X Y h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf (X ⊔ Y))
  have h3 : Nat.card (Y.subgroupOf X) = Nat.card (X ⊓ Y : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (Y.subgroupOf (X ⊔ Y)) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem exists_mul_of_mem_sup {X Y : Subgroup G} (h : X ≤ normalizer (Y : Set G)) {g : G}
    (hg : g ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, x * y = g := by
  have hg' : g ∈ ((X ⊔ Y : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y h] at hg'
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  exact ⟨x, hx, y, hy, rfl⟩

theorem le_normalizer_of_comm {A X Y : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hX : X ≤ A) (hY : Y ≤ A) : X ≤ normalizer (Y : Set G) := fun x hx =>
  Subgroup.mem_normalizer_iff.mpr fun y => by
    constructor
    · intro hy
      rwa [hA x (hX hx) y (hY hy), mul_inv_cancel_right]
    · intro hy
      have h1 : x * y * x⁻¹ * x = x * (x * y * x⁻¹) := hA _ (hY hy) x (hX hx)
      rw [inv_mul_cancel_right, mul_left_cancel_iff] at h1
      rwa [h1]

theorem mem_normalizer_of_conj_mem [Finite G] {A : Subgroup G} {g : G}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨h y, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨a, ha, hay⟩ := hy
  have hay' : g * a * g⁻¹ = g * y * g⁻¹ := hay
  rw [mul_left_inj, mul_right_inj] at hay'
  rwa [← hay']

theorem conj_mem_of_mem_normalizer {A : Subgroup G} {g a : G} (hg : g ∈ normalizer (A : Set G))
    (ha : a ∈ A) : g * a * g⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp hg a).mp ha

theorem inv_conj_mem_of_mem_normalizer {A : Subgroup G} {g a : G}
    (hg : g ∈ normalizer (A : Set G)) (ha : a ∈ A) : g⁻¹ * a * g ∈ A := by
  have h := conj_mem_of_mem_normalizer (inv_mem hg) ha
  rwa [inv_inv] at h

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ {A : Subgroup G}, g ∈ normalizer (A : Set G) →
      A.map (MulAut.conj g).toMonoidHom = A := fun {A} hA => by
    ext y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    exact ⟨fun hy => by simpa [mul_assoc] using conj_mem_of_mem_normalizer hA hy,
      fun hy => inv_conj_mem_of_mem_normalizer hA hy⟩
  have hsup : (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, key hA, key hB]
  refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
  conv_rhs => rw [← hsup]
  exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).symm

theorem mem_normalizer_centralizer {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer (centralizer (A : Set G) : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (A : Set G) → ∀ c ∈ centralizer (A : Set G),
      g * c * g⁻¹ ∈ centralizer (A : Set G) := fun {g} hg c hc =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => by
      have h := Subgroup.mem_centralizer_iff.mp hc _ (inv_conj_mem_of_mem_normalizer hg ha)
      calc a * (g * c * g⁻¹) = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
        _ = g * c * g⁻¹ * a := by group
  refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨key hg c, fun hc => ?_⟩
  have h := key (inv_mem hg) _ hc
  rwa [inv_inv, show g⁻¹ * (g * c * g⁻¹) * g = c by group] at h

theorem mem_centralizer_singleton_iff_conj {u x : G} :
    x ∈ centralizer ({u} : Set G) ↔ u * x * u⁻¹ = x := by
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

theorem mem_normalizer_centralizer_singleton {u g : G} (h : g * u = u * g) :
    g ∈ normalizer (centralizer ({u} : Set G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun c => ?_
  rw [mem_centralizer_singleton_iff_conj, mem_centralizer_singleton_iff_conj]
  have hu : u * (g * c * g⁻¹) * u⁻¹ = g * (u * c * u⁻¹) * g⁻¹ := by
    have hg' : u = g * u * g⁻¹ := by rw [h, mul_inv_cancel_right]
    conv_lhs => rw [hg']
    group
  rw [hu, mul_left_inj, mul_right_inj]

theorem mem_normalizer_oddCoreOf [Finite G] {C : Subgroup G} {g : G}
    (hg : g ∈ normalizer (C : Set G)) : g ∈ normalizer (oddCoreOf C : Set G) := by
  refine mem_normalizer_of_conj_mem fun a ha => ?_
  set Y := (oddCoreOf C).map (MulAut.conj g).toMonoidHom
  have hYC : Y ≤ C := by
    rintro _ ⟨b, hb, rfl⟩
    exact conj_mem_of_mem_normalizer hg (oddCoreOf_le C hb)
  have hCY : C ≤ normalizer (Y : Set G) := fun c hc => by
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨b, hb, rfl⟩ := hy
    have hc' : g⁻¹ * c * g ∈ C := inv_conj_mem_of_mem_normalizer hg hc
    refine ⟨(g⁻¹ * c * g) * b * (g⁻¹ * c * g)⁻¹,
      conj_mem_of_mem_normalizer (le_normalizer_oddCoreOf C hc') hb, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hodd : Odd (Nat.card Y) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact odd_card_oddCoreOf C
  exact le_oddCoreOf hYC hCY hodd ⟨a, ha, rfl⟩

theorem map_conj_inf_centralizer {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G))
    (u : G) : (A ⊓ centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom =
      A ⊓ centralizer ({g * u * g⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_inf, Subgroup.mem_inf,
    mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  refine and_congr ⟨fun h => by simpa [mul_assoc] using conj_mem_of_mem_normalizer hg h,
    fun h => inv_conj_mem_of_mem_normalizer hg h⟩ ⟨fun h => ?_, fun h => ?_⟩
  · calc y * (g * u * g⁻¹) = g * (g⁻¹ * y * g * u) * g⁻¹ := by group
      _ = g * (u * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * u * g⁻¹ * y := by group
  · calc g⁻¹ * y * g * u = g⁻¹ * (y * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * u * g⁻¹ * y) * g := by rw [h]
      _ = u * (g⁻¹ * y * g) := by group

theorem conj_mul_conj (u x y : G) : u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by
  group

theorem conj_inv_conj (u x : G) : u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by
  group

theorem exists_fixed_mul_inverted {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {u : G} (hu : u * u = 1) (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A) {a : G} (ha : a ∈ A)
    (ha3 : a ^ 3 = 1) :
    ∃ b ∈ A, ∃ c ∈ A, u * b * u⁻¹ = b ∧ u * c * u⁻¹ = c⁻¹ ∧ b * c = a := by
  have hu' : u⁻¹ = u := (eq_inv_of_mul_eq_one_left hu).symm
  have hxA : u * a * u⁻¹ ∈ A := huA a ha
  have hux : u * (u * a * u⁻¹) * u⁻¹ = a := by
    rw [hu', ← mul_assoc, ← mul_assoc, hu, one_mul, mul_assoc, hu, mul_one]
  have hcomm : a * (u * a * u⁻¹) = u * a * u⁻¹ * a := hA a ha _ hxA
  refine ⟨(a * (u * a * u⁻¹))⁻¹, inv_mem (mul_mem ha hxA), a⁻¹ * (u * a * u⁻¹),
    mul_mem (inv_mem ha) hxA, ?_, ?_, ?_⟩
  · calc u * (a * (u * a * u⁻¹))⁻¹ * u⁻¹ =
          ((u * a * u⁻¹) * (u * (u * a * u⁻¹) * u⁻¹))⁻¹ := by
          rw [conj_inv_conj u (a * (u * a * u⁻¹)), conj_mul_conj u a (u * a * u⁻¹)]
      _ = (a * (u * a * u⁻¹))⁻¹ := by rw [hux, ← hcomm]
  · calc u * (a⁻¹ * (u * a * u⁻¹)) * u⁻¹ =
          (u * a * u⁻¹)⁻¹ * (u * (u * a * u⁻¹) * u⁻¹) := by
          rw [conj_mul_conj u a⁻¹ (u * a * u⁻¹), conj_inv_conj u a]
      _ = (a⁻¹ * (u * a * u⁻¹))⁻¹ := by rw [hux, mul_inv_rev a⁻¹, inv_inv]
  · have h2 : a⁻¹ * a⁻¹ = a := by
      rw [← mul_inv_rev, inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ, ha3]
    have h3 : (u * a * u⁻¹)⁻¹ * a * (u * a * u⁻¹) = a := by
      rw [mul_assoc, hcomm, inv_mul_cancel_left]
    calc (a * (u * a * u⁻¹))⁻¹ * (a⁻¹ * (u * a * u⁻¹)) =
          (u * a * u⁻¹)⁻¹ * (a⁻¹ * a⁻¹) * (u * a * u⁻¹) := by group
      _ = a := by rw [h2, h3]

theorem conj_eq_inv_of_inf_eq_bot {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {u : G} (hu : u * u = 1) (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A)
    (hfix : A ⊓ centralizer ({u} : Set G) = ⊥) {a : G} (ha : a ∈ A) : u * a * u⁻¹ = a⁻¹ := by
  have hu' : u⁻¹ = u := (eq_inv_of_mul_eq_one_left hu).symm
  have ha'A : u * a * u⁻¹ ∈ A := huA a ha
  have hua' : u * (u * a * u⁻¹) * u⁻¹ = a := by
    rw [hu', ← mul_assoc, ← mul_assoc, hu, one_mul, mul_assoc, hu, mul_one]
  have hmem : a * (u * a * u⁻¹) ∈ A ⊓ centralizer ({u} : Set G) := by
    refine ⟨mul_mem ha ha'A, mem_centralizer_singleton_iff_conj.mpr ?_⟩
    rw [conj_mul_conj, hua', hA _ ha'A a ha]
  rw [hfix, Subgroup.mem_bot] at hmem
  exact (eq_inv_of_mul_eq_one_right hmem)

theorem eq_one_or_eq_or_eq_inv {g x : G} (hg : orderOf g = 3) (hx : x ∈ zpowers g) :
    x = 1 ∨ x = g ∨ x = g⁻¹ := by
  classical
  have hfin : IsOfFinOrder g := orderOf_pos_iff.mp (by rw [hg]; norm_num)
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hx)
  rw [hg, Finset.mem_range] at hk
  have hinv : g⁻¹ = g ^ 2 := by
    have h3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ']
    exact h3
  interval_cases k
  · exact Or.inl (pow_zero g)
  · exact Or.inr (Or.inl (pow_one g))
  · exact Or.inr (Or.inr hinv.symm)

theorem conj_eq_of_card_eq_three {W : Subgroup G} (hW : Nat.card W = 3) {s : G} (hs : s ^ 3 = 1)
    (hsW : ∀ w ∈ W, s * w * s⁻¹ ∈ W) {w : G} (hw : w ∈ W) : s * w * s⁻¹ = w := by
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  by_cases hw1 : w = 1
  · rw [hw1, mul_one, mul_inv_cancel]
  have hord : orderOf w = 3 := by
    have h := Subgroup.orderOf_dvd_natCard W hw
    rw [hW] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hzW : zpowers w = W := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hw)
    (by rw [hW, Nat.card_zpowers, hord])
  have hconj : ∀ x : G, s * x ^ 2 * s⁻¹ = (s * x * s⁻¹) ^ 2 := fun x => by
    rw [pow_two, pow_two]; group
  rcases eq_one_or_eq_or_eq_inv hord (hzW ▸ hsW w hw : s * w * s⁻¹ ∈ zpowers w) with h | h | h
  · rw [mul_inv_eq_one, mul_eq_left] at h
    exact absurd h hw1
  · exact h
  · exfalso
    have hinv : w⁻¹ = w ^ 2 := by
      have h3 : w ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one w
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ']
      exact h3
    have h2 : s ^ 2 * w * (s ^ 2)⁻¹ = w := by
      calc s ^ 2 * w * (s ^ 2)⁻¹ = s * (s * w * s⁻¹) * s⁻¹ := by rw [pow_two]; group
        _ = w := by rw [h, hinv, hconj, h, inv_pow, ← hinv, inv_inv]
    have h3 : s ^ 3 * w * (s ^ 3)⁻¹ = w⁻¹ := by
      calc s ^ 3 * w * (s ^ 3)⁻¹ = s * (s ^ 2 * w * (s ^ 2)⁻¹) * s⁻¹ := by
            rw [pow_succ' s 2]; group
        _ = w⁻¹ := by rw [h2, h]
    rw [hs, one_mul, inv_one, mul_one] at h3
    have h4 : w ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h3]; exact mul_inv_cancel w
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [hord] at h5
    norm_num at h5

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
