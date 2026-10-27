module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

theorem exists_mul_of_mem_sup_of_comm {G : Type} [Group G] {H₁ H₂ : Subgroup G}
    (h : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) {g : G} (hg : g ∈ H₁ ⊔ H₂) :
    ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, g = g₁ * g₂ := by
  let S : Subgroup G :=
    { carrier := {g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, g = g₁ * g₂}
      one_mem' := ⟨1, H₁.one_mem, 1, H₂.one_mem, (one_mul 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, rfl⟩
        refine ⟨a₁ * b₁, H₁.mul_mem ha₁ hb₁, a₂ * b₂, H₂.mul_mem ha₂ hb₂, ?_⟩
        have hab := h b₁ hb₁ a₂ ha₂
        calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [← hab]
          _ = a₁ * b₁ * (a₂ * b₂) := by group
      inv_mem' := by
        rintro _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩
        refine ⟨a₁⁻¹, H₁.inv_mem ha₁, a₂⁻¹, H₂.inv_mem ha₂, ?_⟩
        have hab := h a₁ ha₁ a₂ ha₂
        calc (a₁ * a₂)⁻¹ = (a₂ * a₁)⁻¹ := by rw [hab]
          _ = a₁⁻¹ * a₂⁻¹ := by group }
  have hS : H₁ ⊔ H₂ ≤ S :=
    sup_le (fun x hx => ⟨x, hx, 1, H₂.one_mem, (mul_one x).symm⟩)
      (fun x hx => ⟨1, H₁.one_mem, x, hx, (one_mul x).symm⟩)
  exact hS hg

theorem exists_mul_of_odd_pow {G : Type} [Group G] {H H₁ H₂ : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (h₁ : H₁ ≤ H) (h₂ : H₂ ≤ H)
    (hidx : (H₁ ⊔ H₂).relIndex H = 2) {r : ℕ} (hr : Odd r) {g : G} (hg : g ∈ H)
    (hgr : g ^ r = 1) : ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, g = g₁ * g₂ := by
  have hcomm' : ∀ a b : ↥H, a * b = b * a := fun a b => Subtype.ext (hc a a.2 b b.2)
  have : ((H₁ ⊔ H₂).subgroupOf H).Normal := ⟨fun n hn g' => by
    have h1 : g' * n * g'⁻¹ = n := by rw [hcomm' g' n]; group
    rw [h1]; exact hn⟩
  have hidx' : ((H₁ ⊔ H₂).subgroupOf H).index = 2 := hidx
  have hg2 : g ^ 2 ∈ H₁ ⊔ H₂ := by
    have h1 := Subgroup.pow_index_mem ((H₁ ⊔ H₂).subgroupOf H) (⟨g, hg⟩ : ↥H)
    rw [hidx'] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hgL : g ∈ H₁ ⊔ H₂ := by
    obtain ⟨k, hk⟩ := hr
    have h1 : g = (g ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      have h2 : 2 * (k + 1) = r + 1 := by omega
      rw [h2, pow_succ, hgr, one_mul]
    rw [h1]
    exact Subgroup.pow_mem _ hg2 (k + 1)
  exact exists_mul_of_mem_sup_of_comm (fun a ha b hb => hc a (h₁ ha) b (h₂ hb)) hgL

theorem torus_fixed_of_nonsingular {G : Type} [Group G] {H H₁ H₂ : Subgroup G} {a f w : G}
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hH₁ : H₁ ≤ H) (hH₂ : H₂ ≤ H) (hidx : (H₁ ⊔ H₂).relIndex H = 2)
    (haH : ∀ x ∈ H, a * x * a⁻¹ ∈ H) (ha3 : a ^ 3 ∈ H)
    (hfH₂ : ∀ x ∈ H₂, f * x * f⁻¹ ∈ H₂)
    (hfa : ∃ h ∈ H, f * a * f⁻¹ = a * h)
    (hf₁ : ∀ x ∈ H₁, f * x * f⁻¹ = x)
    (hwa : ∃ h ∈ H, w * a * w⁻¹ = a⁻¹ * h)
    (hw₂ : ∀ x ∈ H₂, w * x * w⁻¹ = x⁻¹)
    (hns : ∀ y ∈ H₂, Odd (orderOf y) → a * y * a⁻¹ = y → y = 1)
    {x : G} (hx : x ∈ H₂) (hxo : Odd (orderOf x)) :
    f * x * f⁻¹ = x := by
  obtain ⟨h₀, hh₀, hfa'⟩ := hfa
  obtain ⟨h₁, hh₁, hwa'⟩ := hwa
  have hxH : x ∈ H := hH₂ hx
  have hfxH₂ : f * x * f⁻¹ ∈ H₂ := hfH₂ x hx
  have hfxH : f * x * f⁻¹ ∈ H := hH₂ hfxH₂
  have hyH₂ : f * x * f⁻¹ * x⁻¹ ∈ H₂ := H₂.mul_mem hfxH₂ (H₂.inv_mem hx)
  have hyH : f * x * f⁻¹ * x⁻¹ ∈ H := hH₂ hyH₂
  have hyodd : Odd (orderOf (f * x * f⁻¹ * x⁻¹)) := by
    have hcomm : Commute (f * x * f⁻¹) x⁻¹ := hHc _ hfxH _ (H.inv_mem hxH)
    have hpow : (f * x * f⁻¹ * x⁻¹) ^ orderOf x = 1 := by
      rw [hcomm.mul_pow, conj_pow, pow_orderOf_eq_one, inv_pow, pow_orderOf_eq_one]
      group
    exact hxo.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  have hx'H : a * x * a⁻¹ ∈ H := haH x hxH
  have hx'n : (a * x * a⁻¹) ^ orderOf x = 1 := by
    rw [conj_pow, pow_orderOf_eq_one]
    group
  obtain ⟨x₁, hx₁, x₂, hx₂, hx'⟩ := exists_mul_of_odd_pow hHc hH₁ hH₂ hidx hxo hx'H hx'n
  have hfx₂ : f * x₂ * f⁻¹ ∈ H₂ := hfH₂ x₂ hx₂
  have hcomm₁ : x₁ * (f * x₂ * f⁻¹) = (f * x₂ * f⁻¹) * x₁ := hHc _ (hH₁ hx₁) _ (hH₂ hfx₂)
  have hcomm₁₂ : x₁ * x₂ = x₂ * x₁ := hHc _ (hH₁ hx₁) _ (hH₂ hx₂)
  have hkey : f * (a * x * a⁻¹) * f⁻¹ * (a * x * a⁻¹)⁻¹ ∈ H₂ := by
    have : f * (a * x * a⁻¹) * f⁻¹ * (a * x * a⁻¹)⁻¹ = (f * x₂ * f⁻¹) * x₂⁻¹ := by
      rw [hx']
      calc f * (x₁ * x₂) * f⁻¹ * (x₁ * x₂)⁻¹
          = (f * x₁ * f⁻¹) * (f * x₂ * f⁻¹) * (x₁ * x₂)⁻¹ := by group
        _ = x₁ * (f * x₂ * f⁻¹) * (x₁ * x₂)⁻¹ := by rw [hf₁ x₁ hx₁]
        _ = (f * x₂ * f⁻¹) * x₁ * (x₁ * x₂)⁻¹ := by rw [hcomm₁]
        _ = (f * x₂ * f⁻¹) * x₁ * (x₂ * x₁)⁻¹ := by rw [hcomm₁₂]
        _ = (f * x₂ * f⁻¹) * x₂⁻¹ := by group
    rw [this]
    exact H₂.mul_mem hfx₂ (H₂.inv_mem hx₂)
  have hay : a * (f * x * f⁻¹ * x⁻¹) * a⁻¹ = f * (a * x * a⁻¹) * f⁻¹ * (a * x * a⁻¹)⁻¹ := by
    have e1 : f * (a * x * a⁻¹) * f⁻¹ = a * (f * x * f⁻¹) * a⁻¹ := by
      calc f * (a * x * a⁻¹) * f⁻¹
          = (f * a * f⁻¹) * (f * x * f⁻¹) * (f * a * f⁻¹)⁻¹ := by group
        _ = (a * h₀) * (f * x * f⁻¹) * (a * h₀)⁻¹ := by rw [hfa']
        _ = a * (h₀ * (f * x * f⁻¹) * h₀⁻¹) * a⁻¹ := by group
        _ = a * (f * x * f⁻¹) * a⁻¹ := by rw [hHc h₀ hh₀ _ hfxH]; group
    rw [e1]
    group
  have hayH₂ : a * (f * x * f⁻¹ * x⁻¹) * a⁻¹ ∈ H₂ := by rw [hay]; exact hkey
  have hw1 := hw₂ _ hayH₂
  have hw2 : w * (a * (f * x * f⁻¹ * x⁻¹) * a⁻¹) * w⁻¹
      = a⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * a := by
    calc w * (a * (f * x * f⁻¹ * x⁻¹) * a⁻¹) * w⁻¹
        = (w * a * w⁻¹) * (w * (f * x * f⁻¹ * x⁻¹) * w⁻¹) * (w * a * w⁻¹)⁻¹ := by group
      _ = (a⁻¹ * h₁) * (f * x * f⁻¹ * x⁻¹)⁻¹ * (a⁻¹ * h₁)⁻¹ := by rw [hwa', hw₂ _ hyH₂]
      _ = a⁻¹ * (h₁ * (f * x * f⁻¹ * x⁻¹)⁻¹ * h₁⁻¹) * a := by group
      _ = a⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * a := by
        rw [hHc h₁ hh₁ _ (H.inv_mem hyH)]; group
  have h3 : a * (f * x * f⁻¹ * x⁻¹) * a⁻¹ = a⁻¹ * (f * x * f⁻¹ * x⁻¹) * a := by
    calc a * (f * x * f⁻¹ * x⁻¹) * a⁻¹
        = ((a * (f * x * f⁻¹ * x⁻¹) * a⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (a⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * a)⁻¹ := by rw [← hw2, hw1]
      _ = a⁻¹ * (f * x * f⁻¹ * x⁻¹) * a := by group
  have h4 : a * (f * x * f⁻¹ * x⁻¹) * a⁻¹ = f * x * f⁻¹ * x⁻¹ := by
    have h5 : a ^ 3 * (f * x * f⁻¹ * x⁻¹) * (a ^ 3)⁻¹ = f * x * f⁻¹ * x⁻¹ := by
      rw [hHc (a ^ 3) ha3 _ hyH]; group
    calc a * (f * x * f⁻¹ * x⁻¹) * a⁻¹
        = a * (a * (a⁻¹ * (f * x * f⁻¹ * x⁻¹) * a) * a⁻¹) * a⁻¹ := by group
      _ = a * (a * (a * (f * x * f⁻¹ * x⁻¹) * a⁻¹) * a⁻¹) * a⁻¹ := by rw [h3]
      _ = a ^ 3 * (f * x * f⁻¹ * x⁻¹) * (a ^ 3)⁻¹ := by rw [pow_three']; group
      _ = f * x * f⁻¹ * x⁻¹ := h5
  exact mul_inv_eq_one.1 (hns _ hyH₂ hyodd h4)

theorem modEq_one_of_pow_odd {k r e : ℕ} (hr : Odd r) (h : k ^ r ≡ 1 [MOD 2 ^ e]) :
    k ≡ 1 [MOD 2 ^ e] := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact Nat.modEq_one
  · have : NeZero (2 ^ e) := ⟨pow_ne_zero _ two_ne_zero⟩
    have hr0 : r ≠ 0 := hr.pos.ne'
    have hu : (k : ZMod (2 ^ e)) ^ r = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
      simpa using this
    have hv : Units.ofPowEqOne _ r hu hr0 ^ r = 1 := Units.pow_ofPowEqOne hu hr0
    have hv2 : Units.ofPowEqOne _ r hu hr0 ^ Nat.totient (2 ^ e) = 1 := by
      rw [← ZMod.card_units_eq_totient]
      exact pow_card_eq_one
    have hcop : r.Coprime (Nat.totient (2 ^ e)) := by
      rw [Nat.totient_prime_pow Nat.prime_two he]
      simpa using Nat.Coprime.pow_right (e - 1) (Nat.coprime_two_right.2 hr)
    have hv1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hv, hv2⟩
    have hk : (k : ZMod (2 ^ e)) = ((1 : ℕ) : ZMod (2 ^ e)) := by
      have := congrArg (fun u : (ZMod (2 ^ e))ˣ => (u : ZMod (2 ^ e))) hv1
      simpa using this
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hk

theorem cyclic_odd_conj_trivial {G : Type} [Group G] {C : Subgroup G} [Finite C] (hC : IsCyclic C)
    {f : G} (hfC : ∀ x ∈ C, f * x * f⁻¹ ∈ C) {r : ℕ} (hr : Odd r) (hfr : f ^ r = 1)
    (hodd : ∀ x ∈ C, Odd (orderOf x) → f * x * f⁻¹ = x) :
    ∀ x ∈ C, f * x * f⁻¹ = x := by
  obtain ⟨⟨g, hgC⟩, hgen⟩ := hC
  have hpow : ∀ x ∈ C, ∃ k : ℕ, g ^ k = x := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥C) ∈ Submonoid.powers (⟨g, hgC⟩ : ↥C) := by
      rw [mem_powers_iff_mem_zpowers]
      exact hgen _
    obtain ⟨k, hk⟩ := h1
    exact ⟨k, congrArg Subtype.val hk⟩
  have hn0 : orderOf g ≠ 0 := by
    have := orderOf_pos (⟨g, hgC⟩ : ↥C)
    rw [Subgroup.orderOf_mk] at this
    exact this.ne'
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  obtain ⟨k, hk⟩ := hpow _ (hfC g hgC)
  have hconj : ∀ i : ℕ, f ^ i * g * (f ^ i)⁻¹ = g ^ (k ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc f ^ (i + 1) * g * (f ^ (i + 1))⁻¹ = f * (f ^ i * g * (f ^ i)⁻¹) * f⁻¹ := by group
        _ = f * g ^ (k ^ i) * f⁻¹ := by rw [ih]
        _ = (f * g * f⁻¹) ^ (k ^ i) := conj_pow.symm
        _ = g ^ (k ^ (i + 1)) := by rw [← hk, ← pow_mul, pow_succ']
  have h1 : k ^ r ≡ 1 [MOD orderOf g] := by
    have := hconj r
    rw [hfr] at this
    have h2 : g ^ 1 = g ^ (k ^ r) := by simpa using this
    exact (pow_eq_pow_iff_modEq.1 h2).symm
  have h2e : k ≡ 1 [MOD 2 ^ e] := by
    refine modEq_one_of_pow_odd hr (Nat.ModEq.of_mul_right m ?_)
    rw [← hn]
    exact h1
  have hgm : g ^ (2 ^ e) ∈ C := C.pow_mem hgC _
  have hord : orderOf (g ^ (2 ^ e)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hn ▸ dvd_mul_right _ _), hn,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hfix := hodd _ hgm (hord ▸ hm)
  have h3 : g ^ (2 ^ e * k) = g ^ (2 ^ e * 1) := by
    rw [mul_one, pow_mul', hk, conj_pow]
    exact hfix
  have hkm : k ≡ 1 [MOD m] := by
    have := pow_eq_pow_iff_modEq.1 h3
    rw [hn] at this
    exact Nat.ModEq.mul_left_cancel' (pow_ne_zero _ two_ne_zero) this
  have hcop : (2 ^ e).Coprime m := Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hm)
  have hkn : k ≡ 1 [MOD orderOf g] := by
    rw [hn]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h2e, hkm⟩
  have hfg : f * g * f⁻¹ = g := by
    rw [← hk]
    have := pow_eq_pow_iff_modEq.2 hkn
    simpa using this
  intro x hx
  obtain ⟨j, rfl⟩ := hpow x hx
  rw [← conj_pow, hfg]

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
