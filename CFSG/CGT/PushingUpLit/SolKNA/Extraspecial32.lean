module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open scoped commutatorElement

section Extraspecial32

variable {G : Type} [Group G]

private theorem comm_mem_of_sq_mem {R N : Subgroup G} (hN : ∀ r ∈ R, ∀ e ∈ N, r * e = e * r)
    (hsq : ∀ r ∈ R, r * r ∈ N) {r s : G} (hr : r ∈ R) (hs : s ∈ R) :
    r * s * r⁻¹ * s⁻¹ ∈ N := by
  have hu : (r * r)⁻¹ ∈ N := N.inv_mem (hsq r hr)
  have hv : (s * s)⁻¹ ∈ N := N.inv_mem (hsq s hs)
  have h1 : s * (r * r)⁻¹ = (r * r)⁻¹ * s := hN s hs _ hu
  have e : r * s * r⁻¹ * s⁻¹ = r * s * (r * s) * ((r * r)⁻¹ * (s * s)⁻¹) :=
    calc r * s * r⁻¹ * s⁻¹ = r * s * r * ((r * r)⁻¹ * s) * (s * s)⁻¹ := by group
      _ = r * s * r * (s * (r * r)⁻¹) * (s * s)⁻¹ := by rw [h1]
      _ = r * s * (r * s) * ((r * r)⁻¹ * (s * s)⁻¹) := by group
  rw [e]
  exact N.mul_mem (hsq (r * s) (R.mul_mem hr hs)) (N.mul_mem hu hv)

private theorem conj_commutator_eq_inv {t x : G} (hc : x * x * t = t * (x * x)) :
    x * (t * x * t⁻¹ * x⁻¹) * x⁻¹ = (t * x * t⁻¹ * x⁻¹)⁻¹ := by
  have hc' : x * x * t⁻¹ = t⁻¹ * (x * x) :=
    (Commute.inv_right (show Commute (x * x) t from hc)).eq
  calc x * (t * x * t⁻¹ * x⁻¹) * x⁻¹
      = x * t * x⁻¹ * (x * x * t⁻¹ * x⁻¹ * x⁻¹) := by group
    _ = x * t * x⁻¹ * t⁻¹ := by rw [hc']; group
    _ = (t * x * t⁻¹ * x⁻¹)⁻¹ := by group

private theorem comm_eq_mul_self_of_inv {p x : G} (h : x * p * x⁻¹ = p⁻¹) :
    p * x * p⁻¹ * x⁻¹ = p * p :=
  calc p * x * p⁻¹ * x⁻¹ = p * (x * p * x⁻¹)⁻¹ := by group
    _ = p * p := by rw [h, inv_inv]

private theorem comm_of_inv {x : G} {H : Subgroup G} (hinv : ∀ h ∈ H, x * h * x⁻¹ = h⁻¹) :
    ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ * h₂ = h₂ * h₁ := by
  intro h₁ h₁H h₂ h₂H
  have e1 : x * (h₁ * h₂) * x⁻¹ = (h₁ * h₂)⁻¹ := hinv _ (H.mul_mem h₁H h₂H)
  have e2 : x * (h₁ * h₂) * x⁻¹ = x * h₁ * x⁻¹ * (x * h₂ * x⁻¹) := by group
  rw [e2, hinv h₁ h₁H, hinv h₂ h₂H, mul_inv_rev] at e1
  have e3 := congrArg (fun y => y⁻¹) e1
  simp only [mul_inv_rev, inv_inv] at e3
  exact e3.symm

private theorem mul_mem_iff_of_relIndex_two {R H : Subgroup G} (hidx : H.relIndex R = 2) {a b : G}
    (ha : a ∈ R) (hb : b ∈ R) : a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) :=
  Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf R) hidx (a := (⟨a, ha⟩ : R))
    (b := (⟨b, hb⟩ : R))

private theorem card_le_of_cover [Finite G] {K Z : Subgroup G} (A : Finset G)
    (hcov : ∀ h ∈ K, ∃ a ∈ A, ∃ z ∈ Z, h = a * z) :
    Nat.card K ≤ A.card * Nat.card Z := by
  choose! a ha z hz hh using hcov
  have hF : Function.Injective
      (fun h : K => ((⟨a h.1, ha h.1 h.2⟩ : A), (⟨z h.1, hz h.1 h.2⟩ : Z))) := by
    intro h h' hhh'
    have h1 : a h.1 = a h'.1 := congrArg (fun p => (p.1 : G)) hhh'
    have h2 : z h.1 = z h'.1 := congrArg (fun p => (p.2 : G)) hhh'
    apply Subtype.ext
    calc (h : G) = a h.1 * z h.1 := hh h.1 h.2
      _ = a h'.1 * z h'.1 := by rw [h1, h2]
      _ = h' := (hh h'.1 h'.2).symm
  calc Nat.card K ≤ Nat.card (A × Z) := Nat.card_le_card_of_injective _ hF
    _ = A.card * Nat.card Z := by rw [Nat.card_prod, Nat.card_eq_finsetCard]

private theorem exists_avoid [Finite G] {H Z : Subgroup G} (A : Finset G)
    (hA : A.card * Nat.card Z < Nat.card H) : ∃ h ∈ H, ∀ a ∈ A, ∀ z ∈ Z, h ≠ a * z := by
  by_contra hcon
  push Not at hcon
  exact absurd (card_le_of_cover A hcon) (not_le.mpr hA)

private theorem mem_map_aut {K : Subgroup G} (α : MulAut G) {y : G} :
    y ∈ K.map α.toMonoidHom ↔ ∃ k ∈ K, α k = y :=
  Subgroup.mem_map

private theorem card_map_aut (K : Subgroup G) (α : MulAut G) :
    Nat.card (K.map α.toMonoidHom) = Nat.card K :=
  Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective

private structure Setup (R H Z T : Subgroup G) : Prop where
  hHR : H ≤ R
  hidx : H.relIndex R = 2
  hZH : Z ≤ H
  hZR : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z
  hZc : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z
  hZ2 : ∀ z ∈ Z, z * z = 1
  hsq : ∀ h ∈ H, h * h ∈ Z
  hinv1 : ∀ h ∈ H, h * h = 1 → h ∈ Z
  hcard : Nat.card H = Nat.card Z ^ 2
  h4 : 4 ≤ Nat.card Z
  hTZ : Nat.card T = Nat.card Z
  hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z
  hgen : ∀ x ∈ R, x ∉ H → ∀ h ∈ H, ∃ t ∈ T, ∃ z ∈ Z, h = z * (t * x * t⁻¹ * x⁻¹)
  hmem : ∀ x ∈ R, x ∉ H → ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ H
  hord : ∀ x ∈ R, x ∉ H → ∀ t ∈ T, t ≠ 1 → t * x * t⁻¹ * x⁻¹ ∉ Z

namespace Setup

variable {R H Z T : Subgroup G}

private theorem hcard' (S : Setup R H Z T) : Nat.card H = Nat.card Z * Nat.card Z := by
  rw [S.hcard, sq]

private theorem comm_mem (S : Setup R H Z T) {h h' : G} (hh : h ∈ H) (hh' : h' ∈ H) :
    h * h' * h⁻¹ * h'⁻¹ ∈ Z :=
  comm_mem_of_sq_mem (R := H) (N := Z) (fun r hr e he => (S.hZc e he r hr).symm) S.hsq hh hh'

private theorem inv_mul_mem_of_mul_mem (S : Setup R H Z T) {h h' : G} (hh : h ∈ H)
    (hmul : h * h' ∈ Z) : h⁻¹ * h' ∈ Z := by
  have e : h⁻¹ * h' = (h * h)⁻¹ * (h * h') := by group
  rw [e]
  exact Z.mul_mem (Z.inv_mem (S.hsq h hh)) hmul

private theorem conj_mem (S : Setup R H Z T) {r h : G} (hr : r ∈ R) (hh : h ∈ H) :
    r * h * r⁻¹ ∈ H := by
  refine (mul_mem_iff_of_relIndex_two S.hidx (R.mul_mem hr (S.hHR hh)) (R.inv_mem hr)).mpr ?_
  rw [inv_mem_iff]
  exact Subgroup.mul_mem_cancel_right H hh

private theorem inv_of_sq_mem (S : Setup R H Z T) {x : G} (hxR : x ∈ R) (hxH : x ∉ H)
    (hx2 : x * x ∈ Z) (hxZ : ∀ z ∈ Z, x * z = z * x) : ∀ h ∈ H, x * h * x⁻¹ = h⁻¹ := by
  intro h hh
  obtain ⟨t, ht, z, hz, rfl⟩ := S.hgen x hxR hxH h hh
  have hpH := S.hmem x hxR hxH t ht
  have hinv := conj_commutator_eq_inv (S.hZT _ hx2 t ht)
  generalize t * x * t⁻¹ * x⁻¹ = p at hpH hinv ⊢
  have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (S.hZ2 z hz)
  have hxz : x * z * x⁻¹ = z := by rw [hxZ z hz]; group
  have hzp : z * p⁻¹ = p⁻¹ * z :=
    (Commute.inv_right (show Commute z p from S.hZc z hz p hpH)).eq
  calc x * (z * p) * x⁻¹ = x * z * x⁻¹ * (x * p * x⁻¹) := by group
    _ = z * p⁻¹ := by rw [hxz, hinv]
    _ = p⁻¹ * z := hzp
    _ = (z * p)⁻¹ := by rw [mul_inv_rev, hzz]

private theorem false_of_inv [Finite G] (S : Setup R H Z T) {H' : Subgroup G} {x : G}
    (hH'R : H' ≤ R) (hH'ab : ∀ y ∈ H', ∀ y' ∈ H', y * y' = y' * y) (hxH' : x ∈ H')
    (hxH : x ∉ H) (hinv : ∀ h ∈ H, x * h * x⁻¹ = h⁻¹)
    (hcardH' : Nat.card H' = Nat.card H) : False := by
  classical
  have hxR : x ∈ R := hH'R hxH'
  have hK : ∀ k ∈ H, k ∈ H' → k ∈ Z := by
    intro k hk hk'
    apply S.hinv1 k hk
    have h1 := hinv k hk
    rw [hH'ab x hxH' k hk', mul_inv_cancel_right] at h1
    exact mul_eq_one_iff_eq_inv.mpr h1
  have hcov : ∀ y ∈ H', ∃ a ∈ ({1, x} : Finset G), ∃ z ∈ Z, y = a * z := by
    intro y hy
    by_cases hyH : y ∈ H
    · exact ⟨1, by simp, y, hK y hyH hy, (one_mul y).symm⟩
    · have hyR : y ∈ R := hH'R hy
      have hxy : x⁻¹ * y ∈ H :=
        (mul_mem_iff_of_relIndex_two S.hidx (R.inv_mem hxR) hyR).mpr (by simp [hxH, hyH])
      exact ⟨x, by simp, x⁻¹ * y, hK _ hxy (H'.mul_mem (H'.inv_mem hxH') hy), by group⟩
  have hc := card_le_of_cover ({1, x} : Finset G) hcov
  have h2 : ({1, x} : Finset G).card ≤ 2 := Finset.card_le_two
  have h3 : Nat.card H' ≤ 2 * Nat.card Z := hc.trans (Nat.mul_le_mul_right _ h2)
  have h4 := S.h4
  have h5 : 4 * Nat.card Z ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul_right _ h4
  rw [hcardH', S.hcard'] at h3
  omega

private theorem caseB [Finite G] (S : Setup R H Z T) {H' : Subgroup G} {x₀ : G}
    (hx₀R : x₀ ∈ R) (hx₀H : x₀ ∉ H) (hx₀2 : x₀ * x₀ = 1)
    (hH'idx : ∀ a ∈ R, ∀ b ∈ R, a * b ∈ H' ↔ (a ∈ H' ↔ b ∈ H'))
    (hcomm : ∀ y ∈ H', y * x₀ = x₀ * y) (hHH' : ¬ H ≤ H') :
    Nat.card T = 4 ∧ ∃ c ∈ Z, c ≠ 1 ∧ (∀ r ∈ R, r * c = c * r) ∧ ⁅R, R⁆ = Subgroup.zpowers c ∧
      (∀ h ∈ H, h ∉ Z → h * h = c) ∧
      (∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → y ∈ Subgroup.zpowers c) := by
  classical
  have hTne : T ≠ ⊥ := by
    intro hT
    have h1 := S.hTZ
    rw [hT, Subgroup.card_bot] at h1
    have h4 := S.h4
    omega
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have hinvp : ∀ t : G, x₀ * (t * x₀ * t⁻¹ * x₀⁻¹) * x₀⁻¹ = (t * x₀ * t⁻¹ * x₀⁻¹)⁻¹ :=
    fun t => conj_commutator_eq_inv (by rw [hx₀2]; simp)
  have hnc : ∃ r ∈ R, r * x₀ ≠ x₀ * r := by
    by_contra hcon
    push Not at hcon
    have hpH := S.hmem x₀ hx₀R hx₀H t₀ ht₀
    have hpZ := S.hord x₀ hx₀R hx₀H t₀ ht₀ ht₀1'
    have h1 := hinvp t₀
    generalize t₀ * x₀ * t₀⁻¹ * x₀⁻¹ = p at hpH hpZ h1
    have h2 : x₀ * p * x₀⁻¹ = p := by rw [← hcon p (S.hHR hpH), mul_inv_cancel_right]
    exact hpZ (S.hinv1 p hpH (mul_eq_one_iff_eq_inv.mpr (h2.symm.trans h1)))
  obtain ⟨r₁, hr₁R, hr₁⟩ := hnc
  have hr₁H' : r₁ ∉ H' := fun h => hr₁ (hcomm r₁ h)
  obtain ⟨c, hc⟩ : ∃ c, c = r₁ * x₀ * r₁⁻¹ * x₀⁻¹ := ⟨_, rfl⟩
  have hcval : ∀ r ∈ R, r ∉ H' → r * x₀ * r⁻¹ * x₀⁻¹ = c := by
    intro r hr hrH'
    have hs : r₁⁻¹ * r ∈ H' := by
      refine (hH'idx _ (R.inv_mem hr₁R) _ hr).mpr ?_
      simp [hr₁H', hrH']
    have hsx := hcomm _ hs
    rw [hc]
    calc r * x₀ * r⁻¹ * x₀⁻¹ = r₁ * (r₁⁻¹ * r * x₀ * (r₁⁻¹ * r)⁻¹) * r₁⁻¹ * x₀⁻¹ := by group
      _ = r₁ * x₀ * r₁⁻¹ * x₀⁻¹ := by rw [hsx]; group
  have hcmem : ∀ r ∈ R, r * x₀ * r⁻¹ * x₀⁻¹ ∈ Subgroup.zpowers c := by
    intro r hr
    by_cases hrH' : r ∈ H'
    · rw [hcomm r hrH']
      simp
    · rw [hcval r hr hrH']
      exact Subgroup.mem_zpowers c
  have hpnH : ∀ t ∈ T, t ≠ 1 → t * x₀ * t⁻¹ * x₀⁻¹ ∉ H' := by
    intro t ht ht1
    have hpH := S.hmem x₀ hx₀R hx₀H t ht
    have hpZ := S.hord x₀ hx₀R hx₀H t ht ht1
    have h1 := hinvp t
    generalize t * x₀ * t⁻¹ * x₀⁻¹ = p at hpH hpZ h1 ⊢
    have h3 : p * x₀ * p⁻¹ * x₀⁻¹ = p * p := comm_eq_mul_self_of_inv h1
    have hpp1 : p * p ≠ 1 := fun h => hpZ (S.hinv1 p hpH h)
    exact fun h => hpp1 (by rw [← h3, hcomm p h]; group)
  have hpp : ∀ t ∈ T, t ≠ 1 → t * x₀ * t⁻¹ * x₀⁻¹ * (t * x₀ * t⁻¹ * x₀⁻¹) = c := by
    intro t ht ht1
    have hpH := S.hmem x₀ hx₀R hx₀H t ht
    have hpn := hpnH t ht ht1
    have h1 := hinvp t
    generalize t * x₀ * t⁻¹ * x₀⁻¹ = p at hpH hpn h1 ⊢
    rw [← comm_eq_mul_self_of_inv h1]
    exact hcval p (S.hHR hpH) hpn
  have hpt₀H := S.hmem x₀ hx₀R hx₀H t₀ ht₀
  have hpt₀Z := S.hord x₀ hx₀R hx₀H t₀ ht₀ ht₀1'
  have hcZ : c ∈ Z := by
    rw [← hpp t₀ ht₀ ht₀1']
    exact S.hsq _ hpt₀H
  have hc1 : c ≠ 1 := by
    intro h
    apply hpt₀Z
    apply S.hinv1 _ hpt₀H
    rw [hpp t₀ ht₀ ht₀1']
    exact h
  have hsqH : ∀ h ∈ H, h ∉ Z → h * h = c := by
    intro h hh hhZ
    obtain ⟨t, ht, z, hz, rfl⟩ := S.hgen x₀ hx₀R hx₀H h hh
    have ht1 : t ≠ 1 := by
      rintro rfl
      apply hhZ
      simpa using hz
    have hpH := S.hmem x₀ hx₀R hx₀H t ht
    have hp := hpp t ht ht1
    generalize t * x₀ * t⁻¹ * x₀⁻¹ = p at hpH hp ⊢
    rw [Commute.mul_mul_mul_comm (show Commute p z from (S.hZc z hz p hpH).symm), S.hZ2 z hz,
      hp, one_mul]
  obtain ⟨h₁, h₁H, h₁Z⟩ : ∃ h ∈ H, h ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hle : H ≤ Z := fun x hx => hcon x hx
    have h2 := Subgroup.card_le_of_le hle
    have h4 := S.h4
    have h5 : 4 * Nat.card Z ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul_right _ h4
    rw [S.hcard'] at h2
    omega
  have hcent : ∀ r ∈ R, r * c = c * r := by
    intro r hr
    have hrH : r * h₁ * r⁻¹ ∈ H := S.conj_mem hr h₁H
    have hrZ : r * h₁ * r⁻¹ ∉ Z := by
      intro hz
      apply h₁Z
      have h2 := S.hZR r⁻¹ (R.inv_mem hr) _ hz
      have e' : r⁻¹ * (r * h₁ * r⁻¹) * r⁻¹⁻¹ = h₁ := by group
      rwa [e'] at h2
    have h11 : h₁ * h₁ = c := hsqH h₁ h₁H h₁Z
    have h2 := hsqH _ hrH hrZ
    have e : r * h₁ * r⁻¹ * (r * h₁ * r⁻¹) = r * (h₁ * h₁) * r⁻¹ := by group
    rw [e, h11] at h2
    calc r * c = r * c * r⁻¹ * r := by group
      _ = c * r := by rw [h2]
  have pair : ∀ h ∈ H, h ∉ Z → ∀ h' ∈ H, h' ∉ Z → h⁻¹ * h' ∉ Z →
      h' * h * h'⁻¹ * h⁻¹ = c := by
    intro h hh hhZ h' hh' hh'Z hne
    have hdZ : h' * h * h'⁻¹ * h⁻¹ ∈ Z := S.comm_mem hh' hh
    have hk : h * h' ∈ H := H.mul_mem hh hh'
    have hkZ : h * h' ∉ Z := fun hz => hne (S.inv_mul_mem_of_mul_mem hh hz)
    have hkk := hsqH _ hk hkZ
    have hh2 := hsqH h hh hhZ
    have hh'2 := hsqH h' hh' hh'Z
    have h1 : h' * h = h' * h * h'⁻¹ * h⁻¹ * (h * h') := by group
    generalize h' * h * h'⁻¹ * h⁻¹ = d at hdZ h1 ⊢
    have hdh : h * d = d * h := (S.hZc d hdZ h hh).symm
    have e : h * h' * (h * h') = d * (h * h) * (h' * h') :=
      calc h * h' * (h * h') = h * (h' * h) * h' := by group
        _ = h * (d * (h * h')) * h' := by rw [h1]
        _ = h * d * h * h' * h' := by group
        _ = d * h * h * h' * h' := by rw [hdh]
        _ = d * (h * h) * (h' * h') := by group
    rw [e, hh2, hh'2, mul_assoc, S.hZ2 c hcZ, mul_one] at hkk
    exact hkk
  have hav : ∀ (A : Finset G) (n : ℕ), A.card ≤ n → n < Nat.card Z →
      ∃ h ∈ H, ∀ a ∈ A, ∀ z ∈ Z, h ≠ a * z := by
    intro A n hA hn
    apply exists_avoid
    rw [S.hcard']
    have h4 := S.h4
    have hn' : n + 1 ≤ Nat.card Z := hn
    have h1 : A.card * Nat.card Z ≤ n * Nat.card Z := Nat.mul_le_mul_right _ hA
    have h2 : (n + 1) * Nat.card Z ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul_right _ hn'
    rw [add_mul, one_mul] at h2
    omega
  have avoid_not_mem : ∀ g a : G, (∀ z ∈ Z, g ≠ a * z) → a⁻¹ * g ∉ Z :=
    fun g a hg hz => hg _ hz (by group)
  have flip : ∀ a b : G, a⁻¹ * b ∉ Z → b⁻¹ * a ∉ Z := fun a b h hz => by
    apply h
    have h2 := Z.inv_mem hz
    simpa using h2
  have hZ4 : Nat.card Z ≤ 4 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨g₁, g₁H, g₁c⟩ := hav {1} 1 (by simp) (by omega)
    obtain ⟨g₂, g₂H, g₂c⟩ := hav {1, g₁} 2 Finset.card_le_two (by omega)
    obtain ⟨g₃, g₃H, g₃c⟩ := hav {1, g₁, g₂, g₁ * g₂} 4 Finset.card_le_four (by omega)
    have g₁Z : g₁ ∉ Z := fun hz => g₁c 1 (by simp) g₁ hz (one_mul g₁).symm
    have g₂Z : g₂ ∉ Z := fun hz => g₂c 1 (by simp) g₂ hz (one_mul g₂).symm
    have g₃Z : g₃ ∉ Z := fun hz => g₃c 1 (by simp) g₃ hz (one_mul g₃).symm
    have g₂₁ : g₁⁻¹ * g₂ ∉ Z := avoid_not_mem g₂ g₁ (g₂c g₁ (by simp))
    have g₃₁ : g₁⁻¹ * g₃ ∉ Z := avoid_not_mem g₃ g₁ (g₃c g₁ (by simp))
    have g₃₂ : g₂⁻¹ * g₃ ∉ Z := avoid_not_mem g₃ g₂ (g₃c g₂ (by simp))
    have g₃₁₂ : (g₁ * g₂)⁻¹ * g₃ ∉ Z := avoid_not_mem g₃ (g₁ * g₂) (g₃c (g₁ * g₂) (by simp))
    have hkZ : g₁ * g₂ ∉ Z := fun hz => g₂₁ (S.inv_mul_mem_of_mul_mem g₁H hz)
    have hkH : g₁ * g₂ ∈ H := H.mul_mem g₁H g₂H
    have c₁ := pair g₃ g₃H g₃Z g₁ g₁H g₁Z (flip _ _ g₃₁)
    have c₂ := pair g₃ g₃H g₃Z g₂ g₂H g₂Z (flip _ _ g₃₂)
    have c₁₂ := pair g₃ g₃H g₃Z (g₁ * g₂) hkH hkZ (flip _ _ g₃₁₂)
    have hcom : g₁ * c * g₁⁻¹ = c := by
      rw [← S.hZc c hcZ g₁ g₁H]
      group
    have key : g₁ * g₂ * g₃ * (g₁ * g₂)⁻¹ * g₃⁻¹ =
        g₁ * (g₂ * g₃ * g₂⁻¹ * g₃⁻¹) * g₁⁻¹ * (g₁ * g₃ * g₁⁻¹ * g₃⁻¹) := by group
    rw [key, c₂, hcom, c₁, S.hZ2 c hcZ] at c₁₂
    exact hc1 c₁₂.symm
  have hZ : Nat.card Z = 4 := le_antisymm hZ4 S.h4
  have hcentH' : ∀ r ∈ R, r * x₀ = x₀ * r → r ∈ H' := by
    intro r hr hrx
    by_contra hrH'
    have h1 := hcval r hr hrH'
    rw [hrx] at h1
    have h2 : x₀ * r * r⁻¹ * x₀⁻¹ = 1 := by group
    exact hc1 (h1.symm.trans h2)
  have hcinR : c ∈ R := S.hHR (S.hZH hcZ)
  have hcH' : c ∈ H' := hcentH' c hcinR (hcent x₀ hx₀R).symm
  have hzcH' : Subgroup.zpowers c ≤ H' := Subgroup.zpowers_le.mpr hcH'
  have hexZ : ∃ e ∈ Z, e ∉ H' := by
    by_contra hcon
    push Not at hcon
    have hK : ∀ h ∈ H, h ∈ H' → h ∈ Z := by
      intro h hh hh'
      by_contra hhZ
      obtain ⟨t, ht, z, hz, rfl⟩ := S.hgen x₀ hx₀R hx₀H h hh
      have ht1 : t ≠ 1 := by
        rintro rfl
        apply hhZ
        simpa using hz
      apply hpnH t ht ht1
      have h2 := H'.mul_mem (H'.inv_mem (hcon z hz)) hh'
      rwa [inv_mul_cancel_left] at h2
    obtain ⟨a, haH, haH'⟩ := IsConcreteLE.not_le_iff_exists.mp hHH'
    have haR : a ∈ R := S.hHR haH
    have hcov : ∀ h ∈ H, ∃ b ∈ ({1, a} : Finset G), ∃ k ∈ H ⊓ H', h = b * k := by
      intro h hh
      by_cases hh' : h ∈ H'
      · exact ⟨1, by simp, h, ⟨hh, hh'⟩, (one_mul h).symm⟩
      · refine ⟨a, by simp, a⁻¹ * h, ⟨H.mul_mem (H.inv_mem haH) hh, ?_⟩, by group⟩
        exact (hH'idx _ (R.inv_mem haR) _ (S.hHR hh)).mpr (by simp [haH', hh'])
    have hc := card_le_of_cover (K := H) (Z := H ⊓ H') ({1, a} : Finset G) hcov
    have h2 : ({1, a} : Finset G).card ≤ 2 := Finset.card_le_two
    have hKZ : Nat.card (H ⊓ H' : Subgroup G) ≤ Nat.card Z :=
      Subgroup.card_le_of_le fun h hh => hK h hh.1 hh.2
    have h3 : ({1, a} : Finset G).card * Nat.card (H ⊓ H' : Subgroup G) ≤ 2 * Nat.card Z :=
      (Nat.mul_le_mul_right _ h2).trans (Nat.mul_le_mul_left 2 hKZ)
    have h16 := S.hcard'
    rw [hZ] at h16
    omega
  have hcenH : ∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → y ∈ H := by
    intro y hyR hycen
    by_contra hyH
    have hh : x₀⁻¹ * y ∈ H :=
      (mul_mem_iff_of_relIndex_two S.hidx (R.inv_mem hx₀R) hyR).mpr (by simp [hx₀H, hyH])
    obtain ⟨h, hhH, rfl⟩ : ∃ h ∈ H, y = x₀ * h := ⟨x₀⁻¹ * y, hh, by group⟩
    obtain ⟨e, heZ, heH'⟩ := hexZ
    have heR : e ∈ R := S.hHR (S.hZH heZ)
    have h1 : e * (x₀ * h) = x₀ * h * e := hycen e heR
    have h2 : e * h = h * e := S.hZc e heZ h hhH
    have h3 : e * x₀ * h = x₀ * e * h :=
      calc e * x₀ * h = e * (x₀ * h) := by group
        _ = x₀ * h * e := h1
        _ = x₀ * (h * e) := by group
        _ = x₀ * (e * h) := by rw [h2]
        _ = x₀ * e * h := by group
    exact heH' (hcentH' e heR (mul_right_cancel h3))
  have hcenZ : ∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → y ∈ Z := by
    intro y hyR hycen
    have hyH : y ∈ H := hcenH y hyR hycen
    by_contra hyZ
    obtain ⟨h₂, h₂H, h₂c⟩ := hav {1, y} 2 Finset.card_le_two (by omega)
    have h₂Z : h₂ ∉ Z := fun hz => h₂c 1 (by simp) h₂ hz (one_mul h₂).symm
    have h₂y : y⁻¹ * h₂ ∉ Z := avoid_not_mem h₂ y (h₂c y (by simp))
    have hcomm2 := pair h₂ h₂H h₂Z y hyH hyZ (flip _ _ h₂y)
    have hone : y * h₂ * y⁻¹ * h₂⁻¹ = 1 := by
      rw [← hycen h₂ (S.hHR h₂H)]
      group
    exact hc1 (hcomm2.symm.trans hone)
  have hcZ2 : Subgroup.zpowers c ≤ Z := Subgroup.zpowers_le.mpr hcZ
  have hcard2 : Nat.card (Subgroup.zpowers c) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact S.hZ2 c hcZ) hc1
  have hidxZ : (Subgroup.zpowers c).relIndex Z = 2 := by
    have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (Subgroup.zpowers c) Z bot_le hcZ2
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hcard2, hZ] at h1
    omega
  have hcenC : ∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → y ∈ Subgroup.zpowers c := by
    intro y hyR hycen
    have hyZ : y ∈ Z := hcenZ y hyR hycen
    have hyH' : y ∈ H' := hcentH' y hyR (hycen x₀ hx₀R).symm
    by_contra hyc
    obtain ⟨e, heZ, heH'⟩ := hexZ
    have hec : e ∉ Subgroup.zpowers c := fun h => heH' (hzcH' h)
    have hmul : y * e ∈ Subgroup.zpowers c :=
      (mul_mem_iff_of_relIndex_two hidxZ hyZ heZ).mpr (by simp [hyc, hec])
    apply heH'
    have h2 := H'.mul_mem (H'.inv_mem hyH') (hzcH' hmul)
    rwa [inv_mul_cancel_left] at h2
  refine ⟨S.hTZ.trans hZ, c, hcZ, hc1, hcent, ?_, hsqH, hcenC⟩
  have hzcen : ∀ r ∈ R, ∀ e ∈ Subgroup.zpowers c, r * e = e * r := by
    intro r hr e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (Commute.zpow_right (show Commute r c from hcent r hr) k).eq
  have hsqzH : ∀ h ∈ H, h * h ∈ Subgroup.zpowers c := by
    intro h hh
    by_cases hhZ : h ∈ Z
    · rw [S.hZ2 h hhZ]
      exact Subgroup.one_mem _
    · rw [hsqH h hh hhZ]
      exact Subgroup.mem_zpowers c
  have hsqR : ∀ r ∈ R, r * r ∈ Subgroup.zpowers c := by
    intro r hr
    by_cases hrH : r ∈ H
    · exact hsqzH r hrH
    · have hh : x₀⁻¹ * r ∈ H :=
        (mul_mem_iff_of_relIndex_two S.hidx (R.inv_mem hx₀R) hr).mpr (by simp [hx₀H, hrH])
      obtain ⟨h, hhH, rfl⟩ : ∃ h ∈ H, r = x₀ * h := ⟨x₀⁻¹ * r, hh, by group⟩
      have he : h * x₀ * h⁻¹ * x₀⁻¹ ∈ Subgroup.zpowers c := hcmem h (S.hHR hhH)
      have hhx : h * x₀ = h * x₀ * h⁻¹ * x₀⁻¹ * x₀ * h := by group
      generalize h * x₀ * h⁻¹ * x₀⁻¹ = e at he hhx
      have hex : x₀ * e = e * x₀ := hzcen x₀ hx₀R e he
      have h1 : x₀ * h * (x₀ * h) = e * (x₀ * x₀) * (h * h) :=
        calc x₀ * h * (x₀ * h) = x₀ * (h * x₀) * h := by group
          _ = x₀ * (e * x₀ * h) * h := by rw [hhx]
          _ = x₀ * e * x₀ * h * h := by group
          _ = e * x₀ * x₀ * h * h := by rw [hex]
          _ = e * (x₀ * x₀) * (h * h) := by group
      rw [h1, hx₀2, mul_one]
      exact Subgroup.mul_mem _ he (hsqzH h hhH)
  have hle : ⁅R, R⁆ ≤ Subgroup.zpowers c := by
    refine Subgroup.commutator_le.mpr fun r hr s hs => ?_
    rw [commutatorElement_def]
    exact comm_mem_of_sq_mem (R := R) (N := Subgroup.zpowers c) hzcen hsqR hr hs
  have hcR : c ∈ ⁅R, R⁆ := by
    have h := Subgroup.commutator_mem_commutator hr₁R hx₀R
    rwa [commutatorElement_def, ← hc] at h
  exact le_antisymm hle (Subgroup.zpowers_le.mpr hcR)

end Setup

end Extraspecial32

theorem caseII5_dichotomy' {G : Type} [Group G] [Finite G] {R H Z T : Subgroup G}
    (hR2 : IsPGroup 2 R) (hHR : H ≤ R) (hidx : H.relIndex R = 2)
    (hZH : Z ≤ H) (hZR : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hsq : ∀ h ∈ H, h * h ∈ Z) (hinv1 : ∀ h ∈ H, h * h = 1 → h ∈ Z)
    (hcard : Nat.card H = Nat.card Z ^ 2) (h4 : 4 ≤ Nat.card Z)
    (hT2 : ∀ t ∈ T, t * t = 1) (hTZ : Nat.card T = Nat.card Z)
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z)
    (hgen : ∀ x ∈ R, x ∉ H → ∀ h ∈ H, ∃ t ∈ T, ∃ z ∈ Z, h = z * (t * x * t⁻¹ * x⁻¹))
    (hmem : ∀ x ∈ R, x ∉ H → ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ H)
    (hord : ∀ x ∈ R, x ∉ H → ∀ t ∈ T, t ≠ 1 → t * x * t⁻¹ * x⁻¹ ∉ Z)
    (α : MulAut G) (hα : R.map α.toMonoidHom = R) (hne : H.map α.toMonoidHom ≠ H) :
    Nat.card T = 4 ∧ ∃ c ∈ Z, c ≠ 1 ∧ (∀ r ∈ R, r * c = c * r) ∧ ⁅R, R⁆ = Subgroup.zpowers c ∧
      (∀ h ∈ H, h ∉ Z → h * h = c) ∧
      (∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → y ∈ Subgroup.zpowers c) := by
  have _ := hR2
  have _ := hT2
  have S : Setup R H Z T :=
    ⟨hHR, hidx, hZH, hZR, hZc, hZ2, hsq, hinv1, hcard, h4, hTZ, hZT, hgen, hmem, hord⟩
  have hR : ∀ x : G, x ∈ R ↔ α.symm x ∈ R := fun x => by
    rw [← Subgroup.mem_map_equiv (f := α), hα]
  have hH' : ∀ x : G, x ∈ H.map α.toMonoidHom ↔ α.symm x ∈ H := fun x => Subgroup.mem_map_equiv
  have hα1 : ∀ k ∈ R, α k ∈ R := fun k hk => by
    have h : α k ∈ R.map α.toMonoidHom := (mem_map_aut α).mpr ⟨k, hk, rfl⟩
    rwa [hα] at h
  by_cases hZ' : Z.map α.toMonoidHom ≤ H
  · exfalso
    have hZZ : Z.map α.toMonoidHom = Z := by
      refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [card_map_aut])
      obtain ⟨z, hz, rfl⟩ := (mem_map_aut α).mp hy
      refine hinv1 _ (hZ' hy) ?_
      rw [← map_mul α, hZ2 z hz, map_one α]
    have hZmap : ∀ z ∈ Z, α z ∈ Z := fun z hz => by
      have h : α z ∈ Z.map α.toMonoidHom := (mem_map_aut α).mpr ⟨z, hz, rfl⟩
      rwa [hZZ] at h
    have hZmap' : ∀ y ∈ Z, ∃ z ∈ Z, α z = y := fun y hy => by
      rw [← hZZ] at hy
      exact (mem_map_aut α).mp hy
    have hnle : ¬ H.map α.toMonoidHom ≤ H := fun hle =>
      hne (Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_aut]))
    obtain ⟨x, hxH', hxH⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    obtain ⟨a, haH, rfl⟩ := (mem_map_aut α).mp hxH'
    have hxR : α a ∈ R := hα1 a (hHR haH)
    have hx2 : α a * α a ∈ Z := by
      rw [← map_mul α]
      exact hZmap _ (hsq a haH)
    have hxZ : ∀ z ∈ Z, α a * z = z * α a := fun z hz => by
      obtain ⟨z₀, hz₀, rfl⟩ := hZmap' z hz
      rw [← map_mul α, ← map_mul α, hZc z₀ hz₀ a haH]
    have hinv := S.inv_of_sq_mem hxR hxH hx2 hxZ
    have hHab := comm_of_inv hinv
    refine S.false_of_inv (H' := H.map α.toMonoidHom) ?_ ?_ hxH' hxH hinv (card_map_aut H α)
    · intro y hy
      obtain ⟨k, hk, rfl⟩ := (mem_map_aut α).mp hy
      exact hα1 k (hHR hk)
    · intro y hy y' hy'
      obtain ⟨k, hk, rfl⟩ := (mem_map_aut α).mp hy
      obtain ⟨k', hk', rfl⟩ := (mem_map_aut α).mp hy'
      rw [← map_mul α, ← map_mul α, hHab k hk k' hk']
  · obtain ⟨x₀, hx₀Z', hx₀H⟩ := IsConcreteLE.not_le_iff_exists.mp hZ'
    obtain ⟨z₀, hz₀, rfl⟩ := (mem_map_aut α).mp hx₀Z'
    have hHH' : ¬ H ≤ H.map α.toMonoidHom := fun hle =>
      hne (Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_aut])).symm
    refine S.caseB (H' := H.map α.toMonoidHom) (x₀ := α z₀) (hα1 z₀ (hHR (hZH hz₀))) hx₀H
      ?_ ?_ ?_ hHH'
    · rw [← map_mul α, hZ2 z₀ hz₀, map_one α]
    · intro a ha b hb
      rw [hH', hH', hH', map_mul]
      exact mul_mem_iff_of_relIndex_two hidx ((hR a).mp ha) ((hR b).mp hb)
    · intro y hy
      obtain ⟨k, hk, rfl⟩ := (mem_map_aut α).mp hy
      rw [← map_mul α, ← map_mul α, hZc z₀ hz₀ k hk]

end CFSG.CGT.PushingUpLit.SolKNA
