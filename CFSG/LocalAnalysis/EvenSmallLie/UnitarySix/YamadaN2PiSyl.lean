module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2U3
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Syl2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaEnd CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem eq_one_of_central {Γ : Type*} [Group Γ] {z : Γ} (hz3 : z ^ 3 = 1)
    (hzc : ∀ g, z * g = g * z) {a b : Γ} {N : ℕ} (hN : Nat.Coprime N 3) (ha : a ^ N = 1)
    (hb : b ^ N = 1) (hab : a = b * z) : z = 1 := by
  have hc : Commute b z := (hzc b).symm
  have hzN : z ^ N = 1 := by
    rw [hab, hc.mul_pow, hb, one_mul] at ha
    exact ha
  have h1 : orderOf z ∣ Nat.gcd N 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzN) (orderOf_dvd_of_pow_eq_one hz3)
  rw [hN, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem card_map_of_injOn {A B : Type*} [Group A] [Group B] (f : A →* B) (H : Subgroup A)
    (hf : ∀ a ∈ H, ∀ b ∈ H, f a = f b → a = b) : Nat.card (H.map f) = Nat.card H := by
  have hb : Function.Bijective
      (fun x : H => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : H.map f)) := by
    refine ⟨fun x y hxy => Subtype.ext (hf _ x.2 _ y.2 (congrArg Subtype.val hxy)), ?_⟩
    rintro ⟨_, ⟨a, ha, rfl⟩⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hb)).symm

theorem pow_four_conj {g x : SL3} (hx : g * x * g⁻¹ ∈ U3) : x ^ 4 = 1 := by
  have h := pow_four_of_mem_U3 hx
  have e : (g * x * g⁻¹) ^ 4 = g * x ^ 4 * g⁻¹ := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, pow_mul, sq, sq, sq, sq]; group
  rw [e] at h
  have : x ^ 4 = g⁻¹ * (g * x ^ 4 * g⁻¹) * g := by group
  rw [this, h]; group

variable {Γ : Type*} [Group Γ] {τ : Γ →* Γ} {X : Subgroup Γ} {ψ : SL3 →* X}

@[expose] def psiG (ψ : SL3 →* X) : SL3 →* Γ := X.subtype.comp ψ

theorem psiG_apply (g : SL3) : psiG ψ g = (ψ g : Γ) := rfl

theorem psiG_mem (g : SL3) : psiG ψ g ∈ X := (ψ g).2

theorem central_of_mem_inf (h1 : X ⊔ X.map τ = ⊤) (h2 : ⁅X, X.map τ⁆ = ⊥) {z : Γ}
    (hz : z ∈ X ⊓ X.map τ) : ∀ g, z * g = g * z := fun g => by
  have hc := comm_of_commutator_eq_bot h2
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc (h1 ▸ Subgroup.mem_top g)
  have e1 : z * a = a * z := (hc a ha z hz.2).symm
  have e2 : z * b = b * z := hc z hz.1 b hb
  calc z * (a * b) = (z * a) * b := by group
    _ = a * (z * b) := by rw [e1]; group
    _ = a * b * z := by rw [e2]; group

@[expose] def phiG (τ : Γ →* Γ) (ψ : SL3 →* X) (h2 : ⁅X, X.map τ⁆ = ⊥) : SL3 × SL3 →* Γ :=
  MonoidHom.noncommCoprod (psiG ψ) (τ.comp (psiG ψ)) fun a b =>
    comm_of_commutator_eq_bot h2 _ (psiG_mem a) _ ⟨_, psiG_mem b, rfl⟩

theorem phiG_apply (h2 : ⁅X, X.map τ⁆ = ⊥) (p : SL3 × SL3) :
    phiG τ ψ h2 p = psiG ψ p.1 * τ (psiG ψ p.2) := rfl

section Inj

variable [Finite Γ] (h1 : X ⊔ X.map τ = ⊤) (h2 : ⁅X, X.map τ⁆ = ⊥)
  (h3 : Nat.card (X ⊓ X.map τ : Subgroup Γ) ∣ 3) (hk : ψ.ker ≤ center SL3)
include h1 h2 h3 hk

theorem eq_of_psiG {u u' : SL3} (hu : u ^ 4 = 1) (hu' : u' ^ 4 = 1)
    (h : (psiG ψ u)⁻¹ * psiG ψ u' ∈ X.map τ) : u = u' := by
  have hzX : (psiG ψ u)⁻¹ * psiG ψ u' ∈ X := mul_mem (inv_mem (psiG_mem u)) (psiG_mem u')
  have hz : (psiG ψ u)⁻¹ * psiG ψ u' ∈ X ⊓ X.map τ := ⟨hzX, h⟩
  have hz1 := eq_one_of_central (pow_three_of_mem h3 hz) (central_of_mem_inf h1 h2 hz)
    (N := 4) (by norm_num) (by rw [← map_pow, hu', map_one]) (by rw [← map_pow, hu, map_one])
    (by group : psiG ψ u' = psiG ψ u * ((psiG ψ u)⁻¹ * psiG ψ u'))
  have hψ : ψ (u⁻¹ * u') = 1 := by
    apply Subtype.ext
    rw [map_mul, map_inv]
    simpa [psiG_apply] using hz1
  have hc : u⁻¹ * u' ∈ center SL3 := hk hψ
  have hc1 := eq_one_of_central (pow_three_of_mem_center hc)
    (fun g => (Subgroup.mem_center_iff.mp hc g).symm) (N := 4) (by norm_num) hu' hu
    (by group : u' = u * (u⁻¹ * u'))
  rw [inv_mul_eq_one] at hc1
  exact hc1

theorem phiG_inj (hττ : ∀ g, τ (τ g) = g) {u v u' v' : SL3} (hu : u ^ 4 = 1) (hv : v ^ 4 = 1)
    (hu' : u' ^ 4 = 1) (hv' : v' ^ 4 = 1) (h : phiG τ ψ h2 (u, v) = phiG τ ψ h2 (u', v')) :
    u = u' ∧ v = v' := by
  rw [phiG_apply, phiG_apply] at h
  have hY : (psiG ψ u')⁻¹ * psiG ψ u ∈ X.map τ := by
    have e : (psiG ψ u')⁻¹ * psiG ψ u = τ (psiG ψ v') * (τ (psiG ψ v))⁻¹ := by
      calc (psiG ψ u')⁻¹ * psiG ψ u
          = (psiG ψ u')⁻¹ * (psiG ψ u * τ (psiG ψ v)) * (τ (psiG ψ v))⁻¹ := by group
        _ = τ (psiG ψ v') * (τ (psiG ψ v))⁻¹ := by rw [h]; group
    rw [e]
    exact mul_mem ⟨_, psiG_mem _, rfl⟩ (inv_mem ⟨_, psiG_mem _, rfl⟩)
  have huu := (eq_of_psiG h1 h2 h3 hk hu' hu hY).symm
  subst huu
  refine ⟨rfl, ?_⟩
  have hτ : τ (psiG ψ v) = τ (psiG ψ v') := mul_left_cancel h
  have hτinj : Function.Injective τ := fun x y hxy => by rw [← hττ x, ← hττ y, hxy]
  have := hτinj hτ
  exact eq_of_psiG h1 h2 h3 hk hv hv' (by rw [this, inv_mul_cancel]; exact one_mem _)

theorem card_Pi (hττ : ∀ g, τ (τ g) = g) :
    Nat.card ((U3.prod U3).map (phiG τ ψ h2)) = 2 ^ 12 := by
  rw [card_map_of_injOn _ _ fun a ha b hb hab => ?_, card_prod', card_U3]
  · norm_num
  · obtain ⟨h₁, h₂⟩ := phiG_inj h1 h2 h3 hk hττ (pow_four_of_mem_U3 ha.1)
      (pow_four_of_mem_U3 ha.2) (pow_four_of_mem_U3 hb.1) (pow_four_of_mem_U3 hb.2) hab
    exact Prod.ext h₁ h₂

omit [Finite Γ] h3 hk in
theorem normal_map_tau : (X.map τ).Normal := by
  have hc := comm_of_commutator_eq_bot h2
  constructor
  intro y hy g
  obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute hc (h1 ▸ Subgroup.mem_top g)
  have e : a' * b' * y * (a' * b')⁻¹ = b' * y * b'⁻¹ := by
    have h1' := hc a' ha' (b' * y * b'⁻¹) (mul_mem (mul_mem hb' hy) (inv_mem hb'))
    calc a' * b' * y * (a' * b')⁻¹ = a' * (b' * y * b'⁻¹) * a'⁻¹ := by group
      _ = (b' * y * b'⁻¹) * a' * a'⁻¹ := by rw [h1']
      _ = b' * y * b'⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hb' hy) (inv_mem hb')

omit [Finite Γ] h3 hk in
theorem normal_X : X.Normal := by
  have hc := comm_of_commutator_eq_bot h2
  constructor
  intro x hx g
  obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute hc (h1 ▸ Subgroup.mem_top g)
  have e : a' * b' * x * (a' * b')⁻¹ = a' * x * a'⁻¹ := by
    have h1' := hc x hx b' hb'
    calc a' * b' * x * (a' * b')⁻¹ = a' * (b' * x) * b'⁻¹ * a'⁻¹ := by group
      _ = a' * (x * b') * b'⁻¹ * a'⁻¹ := by rw [h1']
      _ = a' * x * a'⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem ha' hx) (inv_mem ha')

omit [Finite Γ] h1 h2 h3 hk in
theorem card_map_tau (hττ : ∀ g, τ (τ g) = g) : Nat.card (X.map τ) = Nat.card X :=
  Subgroup.card_map_of_injective fun x y hxy => by rw [← hττ x, ← hττ y, hxy]

omit [Finite Γ] h1 h2 h3 in
theorem card_X (hψ : Function.Surjective ψ) : ∃ a, Nat.card X = 2 ^ 6 * a ∧ ¬ 2 ∣ a := by
  have hX : Nat.card X * Nat.card ψ.ker = 2 ^ 6 * 945 := by
    rw [← card_SL3, Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
  exact two_pow_mul_of_dvd hX (not_two_dvd_card_of_le_center hk) (by norm_num)

theorem card_quot (hττ : ∀ g, τ (τ g) = g) (hψ : Function.Surjective ψ) :
    (∃ m, Nat.card (Γ ⧸ X.map τ) = 2 ^ 6 * m ∧ ¬ 2 ∣ m) ∧
      ∃ m, Nat.card (Γ ⧸ X) = 2 ^ 6 * m ∧ ¬ 2 ∣ m := by
  have hYn := normal_map_tau h1 h2
  obtain ⟨a, ha, ha2⟩ := card_X hk hψ
  have hΓ := card_sup_mul_card_inf X (X.map τ)
  rw [h1, Subgroup.card_top, card_map_tau hττ] at hΓ
  have hodd : ¬ 2 ∣ Nat.card (X ⊓ X.map τ : Subgroup _) := fun h2' =>
    absurd (h2'.trans h3) (by norm_num)
  have hXpos : 0 < Nat.card X := Nat.card_pos
  refine ⟨two_pow_mul_of_dvd (k := Nat.card (X ⊓ X.map τ : Subgroup _)) (m := a) ?_ hodd ha2,
    two_pow_mul_of_dvd (k := Nat.card (X ⊓ X.map τ : Subgroup _)) (m := a) ?_ hodd ha2⟩
  · have e := Subgroup.card_eq_card_quotient_mul_card_subgroup (X.map τ)
    rw [card_map_tau hττ] at e
    rw [e] at hΓ
    rw [← ha]
    have : Nat.card (Γ ⧸ X.map τ) * Nat.card (X ⊓ X.map τ : Subgroup _) * Nat.card X =
        Nat.card X * Nat.card X := by rw [← hΓ]; ring
    exact Nat.eq_of_mul_eq_mul_right hXpos this
  · have e := Subgroup.card_eq_card_quotient_mul_card_subgroup X
    rw [e] at hΓ
    rw [← ha]
    have : Nat.card (Γ ⧸ X) * Nat.card (X ⊓ X.map τ : Subgroup _) * Nat.card X =
        Nat.card X * Nat.card X := by rw [← hΓ]; ring
    exact Nat.eq_of_mul_eq_mul_right hXpos this

omit [Finite Γ] h1 h3 hk in
theorem phiG_pow_four {u v : SL3} (hu : u ^ 4 = 1) (hv : v ^ 4 = 1) :
    phiG τ ψ h2 (u, v) ^ 4 = 1 := by
  rw [← map_pow, Prod.pow_mk, hu, hv, Prod.mk_one_one, map_one]

theorem le_Pi (hττ : ∀ g, τ (τ g) = g) (hψ : Function.Surjective ψ) {T : Subgroup Γ}
    (hT : IsPGroup 2 T) (hθT : ∀ u ∈ U3, phiG τ ψ h2 (u, u) ∈ T) :
    T ≤ (U3.prod U3).map (phiG τ ψ h2) := by
  have hYn := normal_map_tau h1 h2
  have hXn := normal_X h1 h2
  obtain ⟨⟨m₁, hm₁, hm₁2⟩, ⟨m₂, hm₂, hm₂2⟩⟩ := card_quot h1 h2 h3 hk hττ hψ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q₁, hq₁def⟩ : ∃ q : Γ →* Γ ⧸ X.map τ, q = QuotientGroup.mk' _ := ⟨_, rfl⟩
  obtain ⟨q₂, hq₂def⟩ : ∃ q : Γ →* Γ ⧸ X, q = QuotientGroup.mk' _ := ⟨_, rfl⟩
  have hq₁ : ∀ a b : Γ, q₁ a = q₁ b ↔ a⁻¹ * b ∈ X.map τ := fun a b => by
    rw [hq₁def]; exact QuotientGroup.eq
  have hq₂ : ∀ a b : Γ, q₂ a = q₂ b ↔ a⁻¹ * b ∈ X := fun a b => by
    rw [hq₂def]; exact QuotientGroup.eq
  have hq₁1 : ∀ a ∈ X.map τ, q₁ a = 1 := fun a ha => by
    rw [← map_one q₁, hq₁]; simpa using inv_mem ha
  have hq₂1 : ∀ a ∈ X, q₂ a = 1 := fun a ha => by
    rw [← map_one q₂, hq₂]; simpa using inv_mem ha
  have hinj₁ : ∀ u ∈ U3, ∀ u' ∈ U3, (q₁.comp (psiG ψ)) u = (q₁.comp (psiG ψ)) u' → u = u' :=
    fun u hu u' hu' h => eq_of_psiG h1 h2 h3 hk (pow_four_of_mem_U3 hu) (pow_four_of_mem_U3 hu')
      ((hq₁ _ _).mp h)
  have hle₁ : U3.map (q₁.comp (psiG ψ)) ≤ T.map q₁ := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨_, hθT u hu, ?_⟩
    rw [MonoidHom.comp_apply, phiG_apply, map_mul]
    rw [hq₁1 _ ⟨_, psiG_mem u, rfl⟩, mul_one]
  have hT₁ : U3.map (q₁.comp (psiG ψ)) = T.map q₁ := Subgroup.eq_of_le_of_card_ge hle₁ (by
    rw [card_map_of_injOn _ _ hinj₁, card_U3]
    exact card_le_of_isPGroup (hT.map q₁) hm₁2 hm₁)
  have hinj₂ : ∀ v ∈ U3, ∀ v' ∈ U3,
      (q₂.comp (τ.comp (psiG ψ))) v = (q₂.comp (τ.comp (psiG ψ))) v' → v = v' := by
    intro v hv v' hv' h
    have h' := (hq₂ _ _).mp h
    refine eq_of_psiG h1 h2 h3 hk (pow_four_of_mem_U3 hv) (pow_four_of_mem_U3 hv') ?_
    refine ⟨_, h', ?_⟩
    simp only [MonoidHom.comp_apply, map_mul, map_inv, hττ]
  have hle₂ : U3.map (q₂.comp (τ.comp (psiG ψ))) ≤ T.map q₂ := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨_, hθT u hu, ?_⟩
    rw [MonoidHom.comp_apply, phiG_apply, map_mul]
    rw [hq₂1 _ (psiG_mem u), one_mul]
    rfl
  have hT₂ : U3.map (q₂.comp (τ.comp (psiG ψ))) = T.map q₂ :=
    Subgroup.eq_of_le_of_card_ge hle₂ (by
      rw [card_map_of_injOn _ _ hinj₂, card_U3]
      exact card_le_of_isPGroup (hT.map q₂) hm₂2 hm₂)
  intro t ht
  obtain ⟨u, hu, hut⟩ : ∃ u ∈ U3, q₁ (psiG ψ u) = q₁ t := by
    have : q₁ t ∈ T.map q₁ := ⟨t, ht, rfl⟩
    rw [← hT₁] at this
    obtain ⟨u, hu, hut⟩ := this
    exact ⟨u, hu, hut⟩
  obtain ⟨v, hv, hvt⟩ : ∃ v ∈ U3, q₂ (τ (psiG ψ v)) = q₂ t := by
    have : q₂ t ∈ T.map q₂ := ⟨t, ht, rfl⟩
    rw [← hT₂] at this
    obtain ⟨v, hv, hvt⟩ := this
    exact ⟨v, hv, hvt⟩
  have hy := (hq₁ _ _).mp hut
  have hx := (hq₂ _ _).mp hvt
  have hcomm : psiG ψ u * τ (psiG ψ v) = τ (psiG ψ v) * psiG ψ u :=
    comm_of_commutator_eq_bot h2 _ (psiG_mem u) _ ⟨_, psiG_mem v, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = (phiG τ ψ h2 (u, v))⁻¹ * t := ⟨_, rfl⟩
  have hzY : z ∈ X.map τ := by
    have e : z = (τ (psiG ψ v))⁻¹ * ((psiG ψ u)⁻¹ * t) := by
      rw [hzdef, phiG_apply]; group
    rw [e]
    exact mul_mem (inv_mem ⟨_, psiG_mem v, rfl⟩) hy
  have hzX : z ∈ X := by
    have e : z = (psiG ψ u)⁻¹ * ((τ (psiG ψ v))⁻¹ * t) := by
      rw [hzdef, phiG_apply]
      calc (psiG ψ u * τ (psiG ψ v))⁻¹ * t = (τ (psiG ψ v) * psiG ψ u)⁻¹ * t := by rw [hcomm]
        _ = (psiG ψ u)⁻¹ * ((τ (psiG ψ v))⁻¹ * t) := by group
    rw [e]
    exact mul_mem (inv_mem (psiG_mem u)) hx
  have hz : z ∈ X ⊓ X.map τ := ⟨hzX, hzY⟩
  obtain ⟨k, hkt⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := congrArg Subtype.val hkt
  have hN : Nat.Coprime (2 ^ k * 4) 3 :=
    Nat.coprime_mul_iff_left.mpr ⟨Nat.Coprime.pow_left k (by norm_num), by norm_num⟩
  have hz1 := eq_one_of_central (pow_three_of_mem h3 hz) (central_of_mem_inf h1 h2 hz) hN
    (a := t) (b := phiG τ ψ h2 (u, v)) (by rw [pow_mul, htk, one_pow])
    (by rw [mul_comm, pow_mul, phiG_pow_four h2 (pow_four_of_mem_U3 hu) (pow_four_of_mem_U3 hv),
      one_pow]) (by rw [hzdef, mul_inv_cancel_left])
  have : t = phiG τ ψ h2 (u, v) := by
    rw [hzdef, inv_mul_eq_one] at hz1
    exact hz1.symm
  rw [this]
  exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩

theorem Pi_inf_conjR (hττ : ∀ g, τ (τ g) = g) (g : SL3) :
    (U3.prod U3).map (phiG τ ψ h2) ⊓
        conjR ((U3.prod U3).map (phiG τ ψ h2)) (phiG τ ψ h2 (g, g)) =
      ((U3 ⊓ conjR U3 g).prod (U3 ⊓ conjR U3 g)).map (phiG τ ψ h2) := by
  have hconj : ∀ u v : SL3, phiG τ ψ h2 (g, g) * phiG τ ψ h2 (u, v) * (phiG τ ψ h2 (g, g))⁻¹ =
      phiG τ ψ h2 (g * u * g⁻¹, g * v * g⁻¹) := fun u v => by
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := hx1
    rw [mem_conjR, hconj] at hx
    obtain ⟨⟨u', v'⟩, ⟨hu', hv'⟩, he⟩ := hx
    have hgu : (g * u * g⁻¹) ^ 4 = 1 := pow_four_conj (g := g⁻¹) (by
      rw [show g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u by group]; exact hu)
    have hgv : (g * v * g⁻¹) ^ 4 = 1 := pow_four_conj (g := g⁻¹) (by
      rw [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group]; exact hv)
    obtain ⟨e1, e2⟩ := phiG_inj h1 h2 h3 hk hττ (pow_four_of_mem_U3 hu') (pow_four_of_mem_U3 hv')
      hgu hgv he
    refine ⟨(u, v), ⟨Subgroup.mem_inf.mpr ⟨hu, ?_⟩, Subgroup.mem_inf.mpr ⟨hv, ?_⟩⟩, rfl⟩
    · rw [mem_conjR, ← e1]; exact hu'
    · rw [mem_conjR, ← e2]; exact hv'
  · rintro ⟨⟨u, v⟩, ⟨⟨hu, hu'⟩, ⟨hv, hv'⟩⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨(u, v), ⟨hu, hv⟩, rfl⟩, ?_⟩
    rw [mem_conjR, hconj]
    exact ⟨_, ⟨mem_conjR.mp hu', mem_conjR.mp hv'⟩, rfl⟩

theorem card_Pi_inf_conjR (hττ : ∀ g, τ (τ g) = g) (g : SL3) :
    Nat.card ((U3.prod U3).map (phiG τ ψ h2) ⊓
        conjR ((U3.prod U3).map (phiG τ ψ h2)) (phiG τ ψ h2 (g, g)) : Subgroup Γ) =
      Nat.card (U3 ⊓ conjR U3 g : Subgroup SL3) ^ 2 := by
  rw [Pi_inf_conjR h1 h2 h3 hk hττ g, card_map_of_injOn _ _ fun a ha b hb hab => ?_, card_prod', sq]
  obtain ⟨h₁, h₂⟩ := phiG_inj h1 h2 h3 hk hττ (pow_four_of_mem_U3 ha.1.1)
    (pow_four_of_mem_U3 ha.2.1) (pow_four_of_mem_U3 hb.1.1) (pow_four_of_mem_U3 hb.2.1) hab
  exact Prod.ext h₁ h₂

end Inj

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
