module

public import CFSG.GH74.GLS.Stage4.RestPre

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair
open scoped Pointwise

variable {G : Type} [Group G] {D : Ch6Notation G}

namespace PreA

theorem upperSub_inf_lowerSub {F : Type} [Field F] : SL2.upperSub F ⊓ SL2.lowerSub F = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hu, hl⟩
  obtain ⟨s, rfl⟩ := (SL2.mem_upperSub_iff g).1 hu
  obtain ⟨t, ht⟩ := (SL2.mem_lowerSub_iff _).1 hl
  have h01 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) ht
  simp only [coe_sl2U, coe_sl2L] at h01
  have hs : s = 0 := by simpa using h01
  rw [Subgroup.mem_bot, hs, sl2U_zero]

theorem inf_eq_bot_of_sylow_pair {K X X' : Subgroup G} (hXK : X ≤ K) (hXK' : X' ≤ K) {F : Type}
    [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hcard : Nat.card F = p ^ f) (e : ↥K ≃* SL2 F)
    (hX : Nat.card X = Nat.card F) (hX' : Nat.card X' = Nat.card F) (hne : X ≠ X') :
    X ⊓ X' = ⊥ := by
  have hc1 : Nat.card (X.subgroupOf K) = Nat.card F := by
    rw [← hX]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
  have hc2 : Nat.card (X'.subgroupOf K) = Nat.card F := by
    rw [← hX']; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK').toEquiv
  have hne' : X.subgroupOf K ≠ X'.subgroupOf K := by
    intro h
    apply hne
    have h1 := congrArg (Subgroup.map K.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hXK, Subgroup.map_subgroupOf_eq_of_le hXK'] at h1
  obtain ⟨φ, hφ1, hφ2⟩ := SL2.exists_equiv_of_sylow_pair hp hcard e hc1 hc2 hne'
  have hinf : X.subgroupOf K ⊓ X'.subgroupOf K = ⊥ := by
    rw [← hφ1, ← hφ2, ← Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, upperSub_inf_lowerSub,
      Subgroup.map_bot]
  rw [eq_bot_iff]
  intro x hx
  have hxK : x ∈ K := hXK hx.1
  have hmem : (⟨x, hxK⟩ : ↥K) ∈ X.subgroupOf K ⊓ X'.subgroupOf K := ⟨hx.1, hx.2⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

end PreA

theorem Ch6Basics.X₁_inf_X₁' (h : Ch6Basics D) : D.X₁ ⊓ D.X₁' = ⊥ := by
  obtain ⟨F, hF, hFin, hc, ⟨e⟩⟩ := h.iso₁
  obtain ⟨m, hm⟩ := h.q₁_pow
  exact PreA.inf_eq_bot_of_sylow_pair (K := D.K₁) (by rw [h.K₁_eq]; exact le_sup_left)
    (by rw [h.K₁_eq]; exact le_sup_right) h.prime (hc.trans hm) e (h.card_X₁.trans hc.symm)
    (h.card_X₁'.trans hc.symm) h.X₁_ne

theorem Ch6Basics.X₂_inf_X₂' (h : Ch6Basics D) : D.X₂ ⊓ D.X₂' = ⊥ := by
  obtain ⟨F, hF, hFin, hc, ⟨e⟩⟩ := h.iso₂
  obtain ⟨n, hn⟩ := h.q₂_pow
  exact PreA.inf_eq_bot_of_sylow_pair (K := D.K₂) (by rw [h.K₂_eq]; exact le_sup_left)
    (by rw [h.K₂_eq]; exact le_sup_right) h.prime (hc.trans hn) e (h.card_X₂.trans hc.symm)
    (h.card_X₂'.trans hc.symm) h.X₂_ne

namespace PreA

theorem eq_bot_of_fixedPointFree_pair {R : Subgroup G} [Finite ↥R] {e f : G} (he : e * e = 1)
    (hf : f * f = 1) (heR : e ∈ normalizer (R : Set G)) (hfR : f ∈ normalizer (R : Set G))
    (hfix : ∀ a ∈ ({e, f, e * f} : Set G), ∀ r ∈ R, a * r * a⁻¹ = r → r = 1) : R = ⊥ := by
  have hinv : ∀ a ∈ ({e, f} : Set G), a * a = 1 → a ∈ normalizer (R : Set G) →
      (∀ r ∈ R, a * r * a⁻¹ = r → r = 1) → ∀ r ∈ R, a * r * a⁻¹ = r⁻¹ := by
    intro a _ ha2 haR hfa
    let φ : R →* R := ((MulAut.conj a).toMonoidHom.comp R.subtype).codRestrict R fun r =>
      (mem_normalizer_iff.1 haR r).1 r.2
    have hφ : MonoidHom.FixedPointFree φ := fun r hr =>
      Subtype.ext (hfa r r.2 (congrArg Subtype.val hr))
    have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hφ2 : Function.Involutive φ := fun r => Subtype.ext (by
      change a * (a * (r : G) * a⁻¹) * a⁻¹ = r
      rw [ha1]
      calc a * (a * (r : G) * a) * a = (a * a) * r * (a * a) := by group
        _ = r := by rw [ha2, one_mul, mul_one])
    intro r hr
    have h1 := congrFun (hφ.coe_eq_inv_of_involutive hφ2) ⟨r, hr⟩
    exact congrArg Subtype.val h1
  have he' := hinv e (by simp) he heR (hfix e (by simp))
  have hf' := hinv f (by simp) hf hfR (hfix f (by simp))
  rw [eq_bot_iff]
  intro r hr
  rw [mem_bot]
  refine hfix (e * f) (by simp) r hr ?_
  have hfr : f * r * f⁻¹ ∈ R := by rw [hf' r hr]; exact R.inv_mem hr
  calc e * f * r * (e * f)⁻¹ = e * (f * r * f⁻¹) * e⁻¹ := by group
    _ = (e * r * e⁻¹)⁻¹ := by rw [hf' r hr]; group
    _ = r := by rw [he' r hr, inv_inv]

theorem le_normalizer_of_comm {A B : Subgroup G} (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    A ≤ normalizer (B : Set G) := fun x hx => by
  rw [mem_normalizer_iff]
  intro y
  exact inv_iff_of_inv (H := A) (V := B)
    (fun s hs t ht => by rw [h s hs t ht, mul_inv_cancel_right]; exact ht) hx y

@[expose] def HInvar (H A : Subgroup G) : Prop := ∀ h ∈ H, ∀ x ∈ A, h * x * h⁻¹ ∈ A

theorem HInvar.conjBy_eq {H A : Subgroup G} (hA : HInvar H A) {h : G} (hh : h ∈ H) :
    conjBy h A = A := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    simpa [mul_assoc] using hA h⁻¹ (H.inv_mem hh) _ hx
  · intro hx
    exact hA h hh x hx

theorem HInvar.map_conjBy {H A : Subgroup G} (hA : HInvar H A) {g : G}
    (hg : g ∈ normalizer (H : Set G)) : HInvar H (conjBy g A) := by
  intro h hh x hx
  rw [mem_conjBy_iff] at hx ⊢
  have h1 : g * h * g⁻¹ ∈ H := (mem_normalizer_iff.1 hg h).1 hh
  have e : g * (h * x * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * x * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
  rw [e]
  exact hA _ h1 _ hx

theorem HInvar.conjBy_mul_of_mem {H A : Subgroup G} (hA : HInvar H A) {g h : G}
    (hg : g ∈ normalizer (H : Set G)) (hh : h ∈ H) : conjBy (g * h) A = conjBy g A := by
  rw [BNPair.conjBy_mul, (hA.map_conjBy hg).conjBy_eq hh]

theorem HInvar.sup {H A B : Subgroup G} (hA : HInvar H A) (hB : HInvar H B) : HInvar H (A ⊔ B) := by
  intro h hh x hx
  have hle : A ⊔ B ≤ conjBy h (A ⊔ B) :=
    sup_le (fun y hy => mem_conjBy_iff.2 (mem_sup_left (hA h hh y hy)))
      (fun y hy => mem_conjBy_iff.2 (mem_sup_right (hB h hh y hy)))
  exact mem_conjBy_iff.1 (hle hx)

theorem HInvar.inf {H A B : Subgroup G} (hA : HInvar H A) (hB : HInvar H B) : HInvar H (A ⊓ B) :=
  fun h hh x hx => ⟨hA h hh x hx.1, hB h hh x hx.2⟩

theorem conjBy_eq_of_swap {H A B : Subgroup G} {w : G} (hww : w * w ∈ H) (hB : HInvar H B)
    (hAB : ∀ x ∈ A, w * x * w⁻¹ ∈ B) (hBA : ∀ x ∈ B, w * x * w⁻¹ ∈ A) : conjBy w A = B := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    have h1 := hAB _ hx
    have h2 := hB (w * w)⁻¹ (H.inv_mem hww) _ h1
    have e : (w * w)⁻¹ * (w * (w * x * w⁻¹) * w⁻¹) * ((w * w)⁻¹)⁻¹ = x := by group
    rwa [e] at h2
  · intro hx
    exact hBA x hx

theorem conjBy_inf (g : G) (A B : Subgroup G) : conjBy g (A ⊓ B) = conjBy g A ⊓ conjBy g B :=
  Subgroup.map_inf A B (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

theorem conjBy_sup (g : G) (A B : Subgroup G) : conjBy g (A ⊔ B) = conjBy g A ⊔ conjBy g B :=
  Subgroup.map_sup A B (MulAut.conj g⁻¹).toMonoidHom

theorem conjBy_bot (g : G) : conjBy g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot (MulAut.conj g⁻¹).toMonoidHom

theorem fixed_le {P S : Subgroup G} {w v : G} (hwv : w * v = v * w)
    (hS : centralizer ({v} : Set G) ⊓ P = S) :
    P ⊓ conjBy w P ⊓ centralizer ({v} : Set G) ≤ S ⊓ conjBy w S := by
  rintro r ⟨⟨hrP, hrw⟩, hrv⟩
  have hrS : r ∈ S := by rw [← hS]; exact ⟨hrv, hrP⟩
  refine ⟨hrS, mem_conjBy_iff.2 ?_⟩
  have hwP : w * r * w⁻¹ ∈ P := mem_conjBy_iff.1 hrw
  have hrv' : Commute r v := mem_centralizer_singleton_iff.1 hrv
  have hc : Commute w v := hwv
  have hcomm : Commute (w * r * w⁻¹) v := (hc.mul_left hrv').mul_left hc.inv_left
  rw [← hS]
  exact ⟨mem_centralizer_singleton_iff.2 hcomm, hwP⟩

theorem A_le_K₁ (hb : Ch6Basics D) (b : Bool) : D.A b ≤ D.K₁ := by
  rw [hb.K₁_eq]
  cases b
  · exact le_sup_left
  · exact le_sup_right

theorem B_le_K₂ (hb : Ch6Basics D) (c : Bool) : D.B c ≤ D.K₂ := by
  rw [hb.K₂_eq]
  cases c
  · exact le_sup_left
  · exact le_sup_right

theorem hinvar_A (hb : Ch6Basics D) (b : Bool) : HInvar D.H (D.A b) := by
  cases b
  · exact hb.H_norm_X₁
  · exact hb.H_norm_X₁'

theorem hinvar_B (hb : Ch6Basics D) (c : Bool) : HInvar D.H (D.B c) := by
  cases c
  · exact hb.H_norm_X₂
  · exact hb.H_norm_X₂'

theorem A_exp (hb : Ch6Basics D) (b : Bool) : ∀ x ∈ D.A b, x ^ D.p = 1 := by
  cases b
  · exact hb.X₁_exp
  · exact hb.X₁'_exp

theorem A_inf (hb : Ch6Basics D) (b : Bool) : D.A b ⊓ D.A (!b) = ⊥ := by
  cases b
  · exact hb.X₁_inf_X₁'
  · rw [inf_comm]; exact hb.X₁_inf_X₁'

theorem B_inf (hb : Ch6Basics D) (c : Bool) : D.B c ⊓ D.B (!c) = ⊥ := by
  cases c
  · exact hb.X₂_inf_X₂'
  · rw [inf_comm]; exact hb.X₂_inf_X₂'

theorem z_ne_one (hb : Ch6Basics D) : D.z ≠ 1 := by
  intro h
  have := hb.z_ord
  rw [h, orderOf_one] at this
  omega

theorem z_pow_two (hb : Ch6Basics D) : D.z ^ 2 = 1 := by
  rw [← hb.z_ord]
  exact pow_orderOf_eq_one _

theorem z_pow_p (hb : Ch6Basics D) : D.z ^ D.p = D.z := by
  obtain ⟨m, hm⟩ := (hb.prime.eq_two_or_odd'.resolve_left hb.p_ne_two)
  rw [hm, pow_succ, pow_mul, z_pow_two hb, one_pow, one_mul]

theorem conjBy_w₁_A (hb : Ch6Basics D) (b : Bool) : conjBy D.w₁ (D.A b) = D.A (!b) := by
  cases b
  · exact conjBy_eq_of_swap hb.sq₁ hb.H_norm_X₁' hb.w₁_swap hb.w₁_swap'
  · exact conjBy_eq_of_swap hb.sq₁ hb.H_norm_X₁ hb.w₁_swap' hb.w₁_swap

theorem conjBy_w₂_B (hb : Ch6Basics D) (c : Bool) : conjBy D.w₂ (D.B c) = D.B (!c) := by
  cases c
  · exact conjBy_eq_of_swap (DodecA.w₂_sq_mem hb) hb.H_norm_X₂' hb.w₂_swap hb.w₂_swap'
  · exact conjBy_eq_of_swap (DodecA.w₂_sq_mem hb) hb.H_norm_X₂ hb.w₂_swap' hb.w₂_swap

theorem conjBy_w₁_B (hb : Ch6Basics D) (c : Bool) : conjBy D.w₁ (D.B c) = D.B c :=
  DodecA.conjBy_eq_self_of_comm fun x hx => hb.K_comm _ hb.w₁_mem x (B_le_K₂ hb c hx)

theorem conjBy_w₂_A (hb : Ch6Basics D) (b : Bool) : conjBy D.w₂ (D.A b) = D.A b :=
  DodecA.conjBy_eq_self_of_comm fun x hx => (hb.K_comm x (A_le_K₁ hb b hx) _ hb.w₂_mem).symm

theorem conjBy_w₀_A (hb : Ch6Basics D) (b : Bool) :
    conjBy (D.w₁ * D.w₂) (D.A b) = D.A (!b) := by
  rw [BNPair.conjBy_mul, conjBy_w₁_A hb, conjBy_w₂_A hb]

theorem conjBy_w₀_B (hb : Ch6Basics D) (c : Bool) :
    conjBy (D.w₁ * D.w₂) (D.B c) = D.B (!c) := by
  rw [BNPair.conjBy_mul, conjBy_w₁_B hb, conjBy_w₂_B hb]

theorem conjBy_w₀_pair (hb : Ch6Basics D) (b c : Bool) :
    conjBy (D.w₁ * D.w₂) (D.A b ⊔ D.B c) = D.A (!b) ⊔ D.B (!c) := by
  rw [conjBy_sup, conjBy_w₀_A hb, conjBy_w₀_B hb]

theorem w₀_a (hb : Ch6Basics D) :
    ∃ k ∈ D.H, D.w₁ * D.w₂ * D.a * (D.w₁ * D.w₂)⁻¹ = D.a * k := by
  obtain ⟨h₁, hh₁, hr₁⟩ := hb.w₁_a
  obtain ⟨h₂, hh₂, hr₂⟩ := hb.w₂_a
  have hr₁' : D.w₁ * D.a⁻¹ * D.w₁⁻¹ = h₁⁻¹ * D.a := by
    calc D.w₁ * D.a⁻¹ * D.w₁⁻¹ = (D.w₁ * D.a * D.w₁⁻¹)⁻¹ := by group
      _ = (D.a⁻¹ * h₁)⁻¹ := by rw [hr₁]
      _ = h₁⁻¹ * D.a := by group
  have hk1 : D.a⁻¹ * h₁⁻¹ * D.a ∈ D.H := by
    have := (mem_normalizer_iff.1 (inv_mem hb.a_normH) h₁⁻¹).1 (D.H.inv_mem hh₁)
    simpa using this
  have hk2 : D.w₁ * h₂ * D.w₁⁻¹ ∈ D.H := hb.conj_H₁ h₂ hh₂
  refine ⟨(D.a⁻¹ * h₁⁻¹ * D.a) * (D.w₁ * h₂ * D.w₁⁻¹), D.H.mul_mem hk1 hk2, ?_⟩
  calc D.w₁ * D.w₂ * D.a * (D.w₁ * D.w₂)⁻¹ = D.w₁ * (D.w₂ * D.a * D.w₂⁻¹) * D.w₁⁻¹ := by group
    _ = D.w₁ * (D.a⁻¹ * h₂) * D.w₁⁻¹ := by rw [hr₂]
    _ = (D.w₁ * D.a⁻¹ * D.w₁⁻¹) * (D.w₁ * h₂ * D.w₁⁻¹) := by group
    _ = (h₁⁻¹ * D.a) * (D.w₁ * h₂ * D.w₁⁻¹) := by rw [hr₁']
    _ = D.a * ((D.a⁻¹ * h₁⁻¹ * D.a) * (D.w₁ * h₂ * D.w₁⁻¹)) := by group

theorem conjBy_w₀_conjBy_a (hb : Ch6Basics D) {T : Subgroup G} (hT : HInvar D.H T) :
    conjBy (D.w₁ * D.w₂) (conjBy D.a T) = conjBy D.a (conjBy (D.w₁ * D.w₂) T) := by
  obtain ⟨k, hk, hrel⟩ := w₀_a hb
  have e : D.w₁ * D.w₂ * D.a = D.a * k * (D.w₁ * D.w₂) := by
    calc D.w₁ * D.w₂ * D.a = (D.w₁ * D.w₂ * D.a * (D.w₁ * D.w₂)⁻¹) * (D.w₁ * D.w₂) := by group
      _ = D.a * k * (D.w₁ * D.w₂) := by rw [hrel]
  have h : conjBy (D.w₁ * D.w₂ * D.a) T = conjBy (D.a * k * (D.w₁ * D.w₂)) T := by rw [e]
  rw [BNPair.conjBy_mul (D.w₁ * D.w₂) D.a T, BNPair.conjBy_mul (D.a * k) (D.w₁ * D.w₂) T,
    hT.conjBy_mul_of_mem hb.a_normH hk] at h
  exact h.symm

theorem conjBy_w₀_conjBy_a_pow (hb : Ch6Basics D) {T : Subgroup G} (hT : HInvar D.H T) (k : ℕ) :
    conjBy (D.w₁ * D.w₂) (conjBy (D.a ^ k) T) = conjBy (D.a ^ k) (conjBy (D.w₁ * D.w₂) T) := by
  induction k with
  | zero => simp [BNPair.conjBy_one]
  | succ k ih =>
    have hk : HInvar D.H (conjBy (D.a ^ k) T) := hT.map_conjBy (pow_mem hb.a_normH k)
    have e1 : conjBy (D.a ^ (k + 1)) T = conjBy D.a (conjBy (D.a ^ k) T) := by
      rw [pow_succ, BNPair.conjBy_mul]
    have e2 : conjBy (D.a ^ (k + 1)) (conjBy (D.w₁ * D.w₂) T) =
        conjBy D.a (conjBy (D.a ^ k) (conjBy (D.w₁ * D.w₂) T)) := by
      rw [pow_succ, BNPair.conjBy_mul]
    rw [e1, e2, conjBy_w₀_conjBy_a hb hk, ih]

end PreA

theorem Ch6Pre.pair_inf (h : Ch6Pre D) (b c : Bool) :
    (D.A b ⊔ D.B c) ⊓ (D.A (!b) ⊔ D.B (!c)) = ⊥ := by
  have hb := h.basics
  have hK := h.pre.K_inter
  have hmem : ∀ (b c : Bool) (y : G), y ∈ D.A b ⊔ D.B c →
      ∃ s ∈ D.A b, ∃ t ∈ D.B c, s * t = y := by
    intro b c y hy
    have hle : D.A b ≤ normalizer (D.B c : Set G) :=
      PreA.le_normalizer_of_comm fun x hx y hy =>
        hb.K_comm x (PreA.A_le_K₁ hb b hx) y (PreA.B_le_K₂ hb c hy)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hy
    exact Set.mem_mul.1 hy
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [mem_bot]
  obtain ⟨s₁, hs₁, t₁, ht₁, e₁⟩ := hmem b c x hx1
  obtain ⟨s₂, hs₂, t₂, ht₂, e₂⟩ := hmem (!b) (!c) x hx2
  have hs₁K : s₁ ∈ D.K₁ := PreA.A_le_K₁ hb b hs₁
  have hs₂K : s₂ ∈ D.K₁ := PreA.A_le_K₁ hb (!b) hs₂
  have ht₁K : t₁ ∈ D.K₂ := PreA.B_le_K₂ hb c ht₁
  have ht₂K : t₂ ∈ D.K₂ := PreA.B_le_K₂ hb (!c) ht₂
  have hy : s₂⁻¹ * s₁ = t₂ * t₁⁻¹ := by
    calc s₂⁻¹ * s₁ = s₂⁻¹ * (s₁ * t₁) * t₁⁻¹ := by group
      _ = s₂⁻¹ * (s₂ * t₂) * t₁⁻¹ := by rw [e₁, ← e₂]
      _ = t₂ * t₁⁻¹ := by group
  have hyK₁ : s₂⁻¹ * s₁ ∈ D.K₁ := D.K₁.mul_mem (D.K₁.inv_mem hs₂K) hs₁K
  have hyK₂ : s₂⁻¹ * s₁ ∈ D.K₂ := by
    rw [hy]
    exact D.K₂.mul_mem ht₂K (D.K₂.inv_mem ht₁K)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hK (Subgroup.mem_inf.2 ⟨hyK₁, hyK₂⟩))
  have hzk : D.z ^ k = 1 ∨ D.z ^ k = D.z := by
    have hmod := zpow_mod_orderOf D.z k
    rw [hb.z_ord] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← hmod]
      simp [h0]
    · right
      rw [← hmod]
      simp [h1]
  rcases hzk with h1 | h1
  · have hy1 : s₂⁻¹ * s₁ = 1 := by rw [← hk, h1]
    have hs : s₁ = s₂ := (inv_mul_eq_one.1 hy1).symm
    have hs₁1 : s₁ = 1 := by
      have hmem1 : s₁ ∈ D.A b ⊓ D.A (!b) := ⟨hs₁, by rw [hs]; exact hs₂⟩
      rw [PreA.A_inf hb b, mem_bot] at hmem1
      exact hmem1
    have ht : t₂ = t₁ := mul_inv_eq_one.1 (hy.symm.trans hy1)
    have ht₁1 : t₁ = 1 := by
      have hmem2 : t₁ ∈ D.B c ⊓ D.B (!c) := ⟨ht₁, by rw [← ht]; exact ht₂⟩
      rw [PreA.B_inf hb c, mem_bot] at hmem2
      exact hmem2
    rw [← e₁, hs₁1, ht₁1, one_mul]
  · exfalso
    have hy1 : s₂⁻¹ * s₁ = D.z := by rw [← hk, h1]
    have hs : s₁ = s₂ * D.z := inv_mul_eq_iff_eq_mul.1 hy1
    have hcomm : Commute s₂ D.z := hb.K_comm s₂ hs₂K D.z hb.z_mem_K₂
    have hp1 : s₁ ^ D.p = 1 := PreA.A_exp hb b s₁ hs₁
    have hp2 : s₂ ^ D.p = 1 := PreA.A_exp hb (!b) s₂ hs₂
    have hsz : s₁ ^ D.p = D.z := by
      rw [hs, hcomm.mul_pow, hp2, one_mul, PreA.z_pow_p hb]
    rw [hp1] at hsz
    exact PreA.z_ne_one hb hsz.symm

theorem Ch6Pre.opp (h : Ch6Pre D) : D.P ⊓ conjBy (D.w₁ * D.w₂) D.P = ⊥ := by
  have hb := h.basics
  have hp := h.pre
  obtain ⟨α, β, γ, δ, -, hz, hu, hzu⟩ := hp.shape
  have hw₀N : D.w₁ * D.w₂ ∈ normalizer (D.H : Set G) := mul_mem hb.w₁_normH hb.w₂_normH
  have hPH : PreA.HInvar D.H D.P := hp.P_normH
  have hQH : PreA.HInvar D.H (D.P ⊓ conjBy (D.w₁ * D.w₂) D.P) :=
    hPH.inf (hPH.map_conjBy hw₀N)
  have hPfin : Finite ↥D.P := by
    apply Nat.finite_of_card_ne_zero
    rw [hp.P_card]
    have h1 : 0 < D.q₁ := by have := hb.q₁_ge; omega
    have h2 : 0 < D.q₂ := by have := hb.q₂_ge; omega
    positivity
  have : Finite ↥(D.P ⊓ conjBy (D.w₁ * D.w₂) D.P) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : D.P ⊓ conjBy (D.w₁ * D.w₂) D.P ≤ D.P))
      (Subgroup.inclusion_injective _)
  have hzH : D.z ∈ D.H := hb.z_mem_H
  have huH : D.u ∈ D.H := by
    have := (mem_normalizer_iff.1 (inv_mem hb.a_normH) D.z).1 hb.z_mem_H
    simpa [Ch6Notation.u] using this
  have hzz : D.z * D.z = 1 := by rw [← pow_two]; exact PreA.z_pow_two hb
  have huu : D.u * D.u = 1 := by
    have e : D.u * D.u = D.a⁻¹ * (D.z * D.z) * D.a := by
      simp only [Ch6Notation.u]
      group
    rw [e, hzz]
    group
  have hcz : D.w₁ * D.w₂ * D.z = D.z * (D.w₁ * D.w₂) := by
    have h1 : D.w₁ * D.z = D.z * D.w₁ := by
      rw [← hb.w₁_sq]
      group
    have h2 : D.w₂ * D.z = D.z * D.w₂ := by
      rw [← hb.w₂_sq]
      group
    calc D.w₁ * D.w₂ * D.z = D.w₁ * (D.w₂ * D.z) := by group
      _ = D.w₁ * (D.z * D.w₂) := by rw [h2]
      _ = (D.w₁ * D.z) * D.w₂ := by group
      _ = (D.z * D.w₁) * D.w₂ := by rw [h1]
      _ = D.z * (D.w₁ * D.w₂) := by group
  have hcu : D.w₁ * D.w₂ * D.u = D.u * (D.w₁ * D.w₂) := by
    obtain ⟨k, hk, hrel⟩ := PreA.w₀_a hb
    have hzc : D.w₁ * D.w₂ * D.z * (D.w₁ * D.w₂)⁻¹ = D.z := by
      rw [hcz]
      group
    have hu1 : D.w₁ * D.w₂ * D.u * (D.w₁ * D.w₂)⁻¹ = D.u := by
      have e : D.w₁ * D.w₂ * D.u * (D.w₁ * D.w₂)⁻¹ =
          (D.w₁ * D.w₂ * D.a * (D.w₁ * D.w₂)⁻¹)⁻¹ * (D.w₁ * D.w₂ * D.z * (D.w₁ * D.w₂)⁻¹) *
            (D.w₁ * D.w₂ * D.a * (D.w₁ * D.w₂)⁻¹) := by
        simp only [Ch6Notation.u]
        group
      rw [e, hrel, hzc]
      calc (D.a * k)⁻¹ * D.z * (D.a * k) = k⁻¹ * (D.a⁻¹ * D.z * D.a) * k := by group
        _ = k⁻¹ * (D.u * k) := by simp only [Ch6Notation.u]; group
        _ = k⁻¹ * (k * D.u) := by rw [hb.H_comm D.u huH k hk]
        _ = D.u := by group
    calc D.w₁ * D.w₂ * D.u = (D.w₁ * D.w₂ * D.u * (D.w₁ * D.w₂)⁻¹) * (D.w₁ * D.w₂) := by group
      _ = D.u * (D.w₁ * D.w₂) := by rw [hu1]
  have hczu : D.w₁ * D.w₂ * (D.z * D.u) = (D.z * D.u) * (D.w₁ * D.w₂) := by
    calc D.w₁ * D.w₂ * (D.z * D.u) = (D.w₁ * D.w₂ * D.z) * D.u := by group
      _ = (D.z * (D.w₁ * D.w₂)) * D.u := by rw [hcz]
      _ = D.z * (D.w₁ * D.w₂ * D.u) := by group
      _ = D.z * (D.u * (D.w₁ * D.w₂)) := by rw [hcu]
      _ = (D.z * D.u) * (D.w₁ * D.w₂) := by group
  have hAB : ∀ b c : Bool, PreA.HInvar D.H (D.A b ⊔ D.B c) := fun b c =>
    (PreA.hinvar_A hb b).sup (PreA.hinvar_B hb c)
  have hSz : (D.X₁ ⊔ D.X₂) ⊓ conjBy (D.w₁ * D.w₂) (D.X₁ ⊔ D.X₂) = ⊥ := by
    show (D.A false ⊔ D.B false) ⊓ conjBy (D.w₁ * D.w₂) (D.A false ⊔ D.B false) = ⊥
    rw [PreA.conjBy_w₀_pair hb]
    exact h.pair_inf false false
  have hSu : conjBy D.a (D.A α ⊔ D.B β) ⊓
      conjBy (D.w₁ * D.w₂) (conjBy D.a (D.A α ⊔ D.B β)) = ⊥ := by
    rw [PreA.conjBy_w₀_conjBy_a hb (hAB α β), PreA.conjBy_w₀_pair hb, ← PreA.conjBy_inf,
      h.pair_inf α β, PreA.conjBy_bot]
  have hSzu : conjBy (D.a ^ 2) (D.A γ ⊔ D.B δ) ⊓
      conjBy (D.w₁ * D.w₂) (conjBy (D.a ^ 2) (D.A γ ⊔ D.B δ)) = ⊥ := by
    rw [PreA.conjBy_w₀_conjBy_a_pow hb (hAB γ δ) 2, PreA.conjBy_w₀_pair hb, ← PreA.conjBy_inf,
      h.pair_inf γ δ, PreA.conjBy_bot]
  refine PreA.eq_bot_of_fixedPointFree_pair hzz huu
    (mem_normalizer_iff.2 fun y => inv_iff_of_inv hQH hzH y)
    (mem_normalizer_iff.2 fun y => inv_iff_of_inv hQH huH y) ?_
  intro v hv r hr hvr
  have hrv : r ∈ centralizer ({v} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc r * v = (v * r * v⁻¹) * v := by rw [hvr]
      _ = v * r := by group
  rcases hv with rfl | rfl | rfl
  · have := PreA.fixed_le hcz hz (Subgroup.mem_inf.2 ⟨hr, hrv⟩)
    rw [hSz] at this
    exact mem_bot.1 this
  · have := PreA.fixed_le hcu hu (Subgroup.mem_inf.2 ⟨hr, hrv⟩)
    rw [hSu] at this
    exact mem_bot.1 this
  · have := PreA.fixed_le hczu hzu (Subgroup.mem_inf.2 ⟨hr, hrv⟩)
    rw [hSzu] at this
    exact mem_bot.1 this

end CFSG.GH74.GLS.Stage4.Rest
