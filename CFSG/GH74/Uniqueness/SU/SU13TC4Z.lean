module

public import CFSG.GH74.Uniqueness.SU.SU13TC3V
public import CFSG.GH74.Uniqueness.SU.SU13TC4Orb
public import CFSG.GH74.Uniqueness.SU.SU13TC3Comm

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def Zsub (V D : Subgroup G) : Subgroup G where
  carrier := {v | v ∈ V ∧ ∀ d ∈ D, d * v * d⁻¹ = v}
  one_mem' := ⟨V.one_mem, fun d _ => by group⟩
  mul_mem' := by
    rintro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
    refine ⟨V.mul_mem ha hb, fun d hd => ?_⟩
    calc d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
      _ = a * b := by rw [hda d hd, hdb d hd]
  inv_mem' := by
    rintro a ⟨ha, hda⟩
    refine ⟨V.inv_mem ha, fun d hd => ?_⟩
    calc d * a⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ := by group
      _ = a⁻¹ := by rw [hda d hd]

@[expose] def Z2sub (V D Z : Subgroup G) (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hZV : Z ≤ V) :
    Subgroup G where
  carrier := {v | v ∈ V ∧ ∀ d ∈ D, d * v * d⁻¹ * v⁻¹ ∈ Z}
  one_mem' := ⟨V.one_mem, fun d _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
    refine ⟨V.mul_mem ha hb, fun d hd => ?_⟩
    have h1 : d * (a * b) * d⁻¹ * (a * b)⁻¹ =
        (d * a * d⁻¹ * a⁻¹) * (a * (d * b * d⁻¹ * b⁻¹) * a⁻¹) := by group
    have h2 : a * (d * b * d⁻¹ * b⁻¹) * a⁻¹ = d * b * d⁻¹ * b⁻¹ :=
      by rw [hV a ha _ (hZV (hdb d hd))]; group
    rw [h1, h2]
    exact Z.mul_mem (hda d hd) (hdb d hd)
  inv_mem' := by
    rintro a ⟨ha, hda⟩
    refine ⟨V.inv_mem ha, fun d hd => ?_⟩
    have h1 : d * a⁻¹ * d⁻¹ * a⁻¹⁻¹ = a⁻¹ * (d * a * d⁻¹ * a⁻¹)⁻¹ * a := by group
    have h2 : a⁻¹ * (d * a * d⁻¹ * a⁻¹)⁻¹ * a = (d * a * d⁻¹ * a⁻¹)⁻¹ := by
      have hc : a⁻¹ * (d * a * d⁻¹ * a⁻¹)⁻¹ = (d * a * d⁻¹ * a⁻¹)⁻¹ * a⁻¹ :=
        hV a⁻¹ (V.inv_mem ha) _ (hZV (Z.inv_mem (hda d hd)))
      rw [hc]; group
    rw [h1, h2]
    exact Z.inv_mem (hda d hd)

section ZProps

variable {e : Elts G z} {e9 : Elts9 z e} (f : FPart9 z e) (E9 : EPart9 z e e9 f.toFPart)
  (hWc : WAbel e)

theorem V_D_invariant : ∀ d ∈ E9.D, ∀ v ∈ Vsub z e.s₁ hWc, d * v * d⁻¹ ∈ Vsub z e.s₁ hWc :=
  fun d hd v hv => V_invariant f hWc d (E9.D_le_F hd) v hv

theorem r_norm_inv : ∀ d ∈ E9.D, E9.r⁻¹ * d * E9.r ∈ E9.D := by
  have h8 : E9.r ^ 8 = 1 := by rw [← E9.r_ord]; exact pow_orderOf_eq_one E9.r
  have hpow : ∀ n : ℕ, ∀ d ∈ E9.D, E9.r ^ n * d * (E9.r ^ n)⁻¹ ∈ E9.D := by
    intro n
    induction n with
    | zero => intro d hd; simpa using hd
    | succ n ih =>
      intro d hd
      have := E9.r_norm _ (ih d hd)
      have h : E9.r ^ (n + 1) * d * (E9.r ^ (n + 1))⁻¹ = E9.r * (E9.r ^ n * d * (E9.r ^ n)⁻¹) * E9.r⁻¹ := by
        rw [pow_succ']; group
      rw [h]; exact this
  intro d hd
  have h7 : E9.r ^ 7 = E9.r⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]; exact h8
  have := hpow 7 d hd
  rwa [h7, inv_inv] at this

theorem Z_le_V : Zsub (Vsub z e.s₁ hWc) E9.D ≤ Vsub z e.s₁ hWc := fun _ hx => hx.1

theorem Z_r_invariant : ∀ ζ ∈ Zsub (Vsub z e.s₁ hWc) E9.D, E9.r * ζ * E9.r⁻¹ ∈ Zsub (Vsub z e.s₁ hWc) E9.D := by
  rintro ζ ⟨hζV, hζD⟩
  refine ⟨V_invariant f hWc E9.r E9.r_mem ζ hζV, fun d hd => ?_⟩
  have h1 := hζD (E9.r⁻¹ * d * E9.r) (r_norm_inv f E9 d hd)
  calc d * (E9.r * ζ * E9.r⁻¹) * d⁻¹
      = E9.r * ((E9.r⁻¹ * d * E9.r) * ζ * (E9.r⁻¹ * d * E9.r)⁻¹) * E9.r⁻¹ := by group
    _ = E9.r * ζ * E9.r⁻¹ := by rw [h1]

theorem D_mem_normalizer_V : E9.D ≤ normalizer ((Vsub z e.s₁ hWc : Subgroup G) : Set G) := by
  intro d hd
  rw [mem_normalizer_iff]
  intro x
  refine ⟨V_D_invariant f E9 hWc d hd x, fun hx => ?_⟩
  have := V_D_invariant f E9 hWc d⁻¹ (E9.D.inv_mem hd) _ hx
  simpa [mul_assoc] using this

theorem D_isPGroup : IsPGroup 3 E9.D := IsPGroup.of_card (n := 2) (by rw [E9.D_card]; norm_num)

theorem V_inf_cent_D : Vsub z e.s₁ hWc ⊓ centralizer ((E9.D : Subgroup G) : Set G) =
    Zsub (Vsub z e.s₁ hWc) E9.D := by
  ext x
  constructor
  · rintro ⟨hxV, hxc⟩
    refine ⟨hxV, fun d hd => ?_⟩
    have := mem_centralizer_iff.mp hxc d hd
    calc d * x * d⁻¹ = x * d * d⁻¹ := by rw [this]
      _ = x := by group
  · rintro ⟨hxV, hxD⟩
    refine ⟨hxV, mem_centralizer_iff.mpr fun d hd => ?_⟩
    have := hxD d hd
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [this]

theorem three_dvd_Z (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    3 ∣ Nat.card (Zsub (Vsub z e.s₁ hWc) E9.D) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := card_modEq_card_inf_centralizer_pgroup (D_isPGroup f E9) (D_mem_normalizer_V f E9 hWc)
  rw [V_inf_cent_D f E9 hWc, V_card hz f hWc hW5] at h
  have h2 : (3 ^ 4 : ℕ) % 3 = Nat.card (Zsub (Vsub z e.s₁ hWc) E9.D) % 3 := h
  have h3 : Nat.card (Zsub (Vsub z e.s₁ hWc) E9.D) % 3 = 0 := by norm_num at h2; omega
  exact Nat.dvd_of_mod_eq_zero h3

theorem Z_ne_V (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    Zsub (Vsub z e.s₁ hWc) E9.D ≠ Vsub z e.s₁ hWc := by
  intro hZV
  have hne : E9.D ≠ ⊥ := by
    intro h
    have := E9.D_card
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨v, hv, hdv⟩ := V_faithful hz f hWc hW5 d (E9.D_le_F d.2) (fun h => hd1 (Subtype.ext h))
  have hvZ : v ∈ Zsub (Vsub z e.s₁ hWc) E9.D := by rw [hZV]; exact hv
  apply hdv
  have := hvZ.2 d d.2
  calc (d : G) * v = (d : G) * v * (d : G)⁻¹ * d := by group
    _ = v * d := by rw [this]

theorem Z_card (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    Nat.card (Zsub (Vsub z e.s₁ hWc) E9.D) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set V := Vsub z e.s₁ hWc with hV
  set Z := Zsub V E9.D with hZ
  have hVc := V_card hz f hWc hW5
  have hdvd : Nat.card Z ∣ 3 ^ 4 := hVc ▸ Subgroup.card_dvd_of_le (Z_le_V f E9 hWc)
  obtain ⟨i, hi, hiZ⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
  have hZ3 : IsPGroup 3 Z := IsPGroup.of_card hiZ
  obtain ⟨k, hk⟩ := card_pow_even_of_r8 E9.r_ord E9.r_pow hZ3 (Z_r_invariant f E9 hWc)
    (fun u hu => hu.1.2)
  have h3 := three_dvd_Z f E9 hWc hz hW5
  have hlt : Nat.card Z < 3 ^ 4 := by
    rw [← hVc]
    refine lt_of_le_of_ne (Subgroup.card_le_of_le (Z_le_V f E9 hWc)) (fun h => ?_)
    exact Z_ne_V f E9 hWc hz hW5 (Subgroup.eq_of_le_of_card_ge (Z_le_V f E9 hWc) (by rw [h]))
  rw [hk] at h3 hlt ⊢
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at h3; norm_num at h3
    · have : k = 1 := by omega
      rw [this]; norm_num
  · exfalso
    have : 9 ^ 2 ≤ 9 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

theorem V_comm_D (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    ∀ v ∈ Vsub z e.s₁ hWc, ∀ d ∈ E9.D, d * v * d⁻¹ * v⁻¹ ∈ Zsub (Vsub z e.s₁ hWc) E9.D := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set V := Vsub z e.s₁ hWc with hV
  set Z := Zsub V E9.D with hZ
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hWc a ha.1 b hb.1
  have hZV : Z ≤ V := Z_le_V f E9 hWc
  set Z2 := Z2sub V E9.D Z hVab hZV with hZ2
  have hVc := V_card hz f hWc hW5
  have hZ2V : Z2 ≤ V := fun x hx => hx.1
  have hZZ2 : Z ≤ Z2 := fun x hx => ⟨hx.1, fun d hd => by
    have := hx.2 d hd
    rw [this]; simp⟩
  have hZ2r : ∀ u ∈ Z2, E9.r * u * E9.r⁻¹ ∈ Z2 := by
    rintro u ⟨huV, hu⟩
    refine ⟨V_invariant f hWc E9.r E9.r_mem u huV, fun d hd => ?_⟩
    have h1 := hu (E9.r⁻¹ * d * E9.r) (r_norm_inv f E9 d hd)
    have h2 : d * (E9.r * u * E9.r⁻¹) * d⁻¹ * (E9.r * u * E9.r⁻¹)⁻¹ =
        E9.r * ((E9.r⁻¹ * d * E9.r) * u * (E9.r⁻¹ * d * E9.r)⁻¹ * u⁻¹) * E9.r⁻¹ := by group
    rw [h2]
    exact Z_r_invariant f E9 hWc _ h1
  have hdvd : Nat.card Z2 ∣ 3 ^ 4 := hVc ▸ Subgroup.card_dvd_of_le hZ2V
  obtain ⟨i, hi, hiZ⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
  have hZ23 : IsPGroup 3 Z2 := IsPGroup.of_card hiZ
  obtain ⟨k, hk⟩ := card_pow_even_of_r8 E9.r_ord E9.r_pow hZ23 hZ2r (fun u hu => hu.1.2)
  have hVD : ∀ d ∈ E9.D, ∀ w ∈ V, d * w * d⁻¹ ∈ V := V_D_invariant f E9 hWc
  have hVinfD : V ⊓ E9.D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ oc (centralizer ({e.s₁} : Set G)) ⊓ f.F :=
      mem_inf.mpr ⟨(mem_inf.mp hx).1.1, E9.D_le_F (mem_inf.mp hx).2⟩
    rw [W_inf_F e f.toFPart] at this
    exact this
  have hPcard : Nat.card (TT V E9.D hVD) = 3 ^ 6 := by
    rw [card_TT_eq hVD hVinfD, hVc, E9.D_card]; norm_num
  have hP3 : IsPGroup 3 (TT V E9.D hVD) := IsPGroup.of_card hPcard
  have hZlt : Z < V := lt_of_le_of_ne hZV (Z_ne_V f E9 hWc hz hW5)
  obtain ⟨v, hvV, hvZ, hvc⟩ := exists_central_mod (p := 3) (by norm_num) (P := TT V E9.D hVD) (N := V) (Z := Z)
    hP3 (le_TT hVD)
    (fun g ⟨w, hw, d, hd, hg⟩ u hu => by
      rw [hg]
      have h1 : w * d * u * (w * d)⁻¹ = w * (d * u * d⁻¹) * w⁻¹ := by group
      rw [h1]
      exact V.mul_mem (V.mul_mem hw (hVD d hd u hu)) (V.inv_mem hw))
    hZV
    (fun g ⟨w, hw, d, hd, hg⟩ u hu => by
      rw [hg]
      have h1 : w * d * u * (w * d)⁻¹ = w * (d * u * d⁻¹) * w⁻¹ := by group
      rw [h1, hu.2 d hd, hVab w hw u hu.1]
      have : u * w * w⁻¹ = u := by group
      rw [this]; exact hu)
    hZlt
  have hvZ2 : v ∈ Z2 := ⟨hvV, fun d hd => hvc d (le_TT' hVD hd)⟩
  have hZ2ne : Z ≠ Z2 := fun h => hvZ (h ▸ hvZ2)
  have hZc := Z_card f E9 hWc hz hW5
  have hlt : Nat.card Z < Nat.card Z2 := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hZZ2) (fun h => hZ2ne ?_)
    exact Subgroup.eq_of_le_of_card_ge hZZ2 (by rw [h])
  have hZ2c : Nat.card Z2 = 3 ^ 4 := by
    rw [hk] at hlt ⊢
    rw [hZc] at hlt
    have hk2 : 2 ≤ k := by
      by_contra hcon
      have : k ≤ 1 := by omega
      have : 9 ^ k ≤ 9 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have hle : Nat.card Z2 ≤ 3 ^ 4 := hVc ▸ Subgroup.card_le_of_le hZ2V
    rw [hk] at hle
    have : 9 ^ 2 ≤ 9 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have : 9 ^ k = 3 ^ 4 := by omega
    exact this
  have hZ2V' : Z2 = V := Subgroup.eq_of_le_of_card_ge hZ2V (by rw [hZ2c, hVc])
  intro w hw d hd
  have : w ∈ Z2 := by rw [hZ2V']; exact hw
  exact this.2 d hd

end ZProps

end CFSG.GH74.Uniqueness.SU.SU13
