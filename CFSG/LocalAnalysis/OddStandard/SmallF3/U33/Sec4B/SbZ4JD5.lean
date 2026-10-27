module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD3A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement Pointwise

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

@[expose] def ZJBound (t : H) : Prop :=
  ∀ P : Subgroup H, P ≤ centralizer ({t} : Set H) → IsPGroup 2 P → Nat.card P ≤ 128

private theorem mem_zpowers_of_sq_eq_one {G : Type*} [Group G] {g x : G} (hg : g * g = 1)
    (hx : x ∈ zpowers g) : x = 1 ∨ x = g := by
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  have hg2 : g ^ (2 : ℤ) = 1 := by
    have h2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := by norm_num
    rw [h2, zpow_natCast, pow_two]
    exact hg
  rw [zpow_eq_zpow_emod k hg2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp

private theorem card_zpowers_of_sq_eq_one {G : Type*} [Group G] {g : G} (hg : g * g = 1)
    (hg1 : g ≠ 1) : Nat.card (zpowers g) = 2 := by
  rw [Nat.card_zpowers]
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hg1
  · exact h

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

theorem card_Y : Nat.card Y = 16 := by
  classical
  let f : Fin 16 → Y := fun n => ⟨zjVec y z v₁ v₂ n, h.vec_mem n⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro n m hnm
      have hval : zjVec y z v₁ v₂ n = zjVec y z v₁ v₂ m := congrArg Subtype.val hnm
      exact Fin.ext (h.vec_inj n.2 m.2 hval)
    · intro u
      obtain ⟨n, hn, hnu⟩ := h.vec_surj u.2
      exact ⟨⟨n, hn⟩, Subtype.ext hnu⟩
  calc Nat.card Y = Nat.card (Fin 16) := (Nat.card_eq_of_bijective f hf).symm
    _ = 16 := Nat.card_fin 16

private theorem tau_ne_one : τ ≠ 1 := by
  intro hτ
  apply h.tau_not_mem_Q
  rw [hτ]
  exact Subgroup.one_mem Q

private theorem zpowers_tau_le_normalizer_B : zpowers τ ≤ Subgroup.normalizer (B : Set H) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h.tau_inv x (h.B_le_Q hx)]
    exact Subgroup.inv_mem _ hx
  · intro hx
    have hy : τ * (τ * x * τ⁻¹) * τ⁻¹ = (τ * x * τ⁻¹)⁻¹ := h.tau_inv _ (h.B_le_Q hx)
    have h2 : τ * (τ * x * τ⁻¹) * τ⁻¹ = x := by
      rw [inv_eq_of_mul_eq_one_right h.tau_sq]
      calc τ * (τ * x * τ) * τ = (τ * τ) * x * (τ * τ) := by group
        _ = x := by rw [h.tau_sq]; group
    rw [← h2, hy]
    exact Subgroup.inv_mem _ hx

private theorem mem_sup_B_zpowers_tau_iff {x : H} :
    x ∈ B ⊔ zpowers τ ↔ ∃ b ∈ B, ∃ s ∈ zpowers τ, b * s = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left B (zpowers τ)
    (zpowers_tau_le_normalizer_B h), Set.mem_mul]
  simp only [SetLike.mem_coe]

private theorem card_sup_B_zpowers_tau : Nat.card ↥(B ⊔ zpowers τ) = 32 := by
  have hdisj : B ⊓ zpowers τ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxB, hxτ⟩ := Subgroup.mem_inf.mp hx
    rcases mem_zpowers_of_sq_eq_one h.tau_sq hxτ with rfl | rfl
    · rfl
    · exact absurd (h.B_le_Q hxB) h.tau_not_mem_Q
  have hcardτ : Nat.card (zpowers τ) = 2 := card_zpowers_of_sq_eq_one h.tau_sq (tau_ne_one h)
  let φ : B × zpowers τ → ↥(B ⊔ zpowers τ) := fun p =>
    ⟨(p.1 : H) * (p.2 : H),
      mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hbij : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨b, s⟩ ⟨b', s'⟩ heq
      have hval : (b : H) * (s : H) = (b' : H) * (s' : H) := congrArg Subtype.val heq
      have h1 : (b' : H)⁻¹ * (b : H) = (s' : H) * (s : H)⁻¹ := by
        have h2 : ((b' : H)⁻¹ * (b : H)) * (s : H) = (s' : H) := by
          rw [mul_assoc, hval]; group
        exact eq_mul_inv_of_mul_eq h2
      have hb : (b' : H)⁻¹ * (b : H) = 1 := by
        have hmem : (b' : H)⁻¹ * (b : H) ∈ (⊥ : Subgroup H) := by
          rw [← hdisj]
          exact Subgroup.mem_inf.mpr ⟨mul_mem (Subgroup.inv_mem _ b'.2) b.2,
            by rw [h1]; exact mul_mem s'.2 (Subgroup.inv_mem _ s.2)⟩
        exact Subgroup.mem_bot.mp hmem
      have hbb : b = b' := Subtype.ext (eq_of_inv_mul_eq_one hb).symm
      have hss : s = s' := by
        have hbb2 : (b : H) * (s : H) = (b : H) * (s' : H) := by rw [hval, hbb]
        exact Subtype.ext (mul_left_cancel hbb2)
      exact Prod.ext hbb hss
    · rintro ⟨w, hw⟩
      obtain ⟨b, hb, s, hs, hbs⟩ := (mem_sup_B_zpowers_tau_iff h).mp hw
      exact ⟨(⟨b, hb⟩, ⟨s, hs⟩), Subtype.ext hbs⟩
  have hcard : Nat.card (B × zpowers τ) = Nat.card ↥(B ⊔ zpowers τ) :=
    Nat.card_eq_of_bijective φ hbij
  rw [← hcard, Nat.card_prod, h.card_B, hcardτ]

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

private theorem l_ne_one : l ≠ 1 := by
  intro hl
  apply l_not_mem_Mh h hMh
  rw [hl]
  exact Subgroup.one_mem Mh

private theorem l_ne_t : l ≠ t := by
  intro hlt
  apply tl_not_mem_Mh h hMh
  rw [← hlt, h.l_sq]
  exact Subgroup.one_mem Mh

private theorem zpowers_l_le_normalizer_zpowers_t :
    zpowers l ≤ Subgroup.normalizer (zpowers t : Set H) := by
  rw [Subgroup.zpowers_le]
  refine (Subgroup.centralizer_le_normalizer (zpowers t : Set H)) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((show Commute t l from h.t_l).zpow_left k).eq

private theorem mem_sup_zpowers_iff {x : H} :
    x ∈ zpowers l ⊔ zpowers t ↔ ∃ a ∈ zpowers l, ∃ b ∈ zpowers t, a * b = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (zpowers l) (zpowers t)
    (zpowers_l_le_normalizer_zpowers_t h hMh), Set.mem_mul]
  simp only [SetLike.mem_coe]

private theorem eq_one_of_mem_sup_zpowers_of_mem_Mh {x : H}
    (hx : x ∈ zpowers l ⊔ zpowers t) (hxM : x ∈ Mh) : x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_zpowers_iff h hMh).mp hx
  rcases mem_zpowers_of_sq_eq_one h.l_sq ha with rfl | rfl <;>
    rcases mem_zpowers_of_sq_eq_one h.t_sq hb with rfl | rfl
  · simp
  · exact absurd (by simpa using hxM) (t_not_mem_Mh h hMh)
  · exact absurd (by simpa using hxM) (l_not_mem_Mh h hMh)
  · exact absurd (by simpa [h.t_l] using hxM) (tl_not_mem_Mh h hMh)

private theorem inf_zpowers_l_t_eq_bot : zpowers l ⊓ zpowers t = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxl, hxt⟩ := Subgroup.mem_inf.mp hx
  rcases mem_zpowers_of_sq_eq_one h.l_sq hxl with rfl | rfl
  · rfl
  · rcases mem_zpowers_of_sq_eq_one h.t_sq hxt with ht | ht
    · exact ht
    · exact absurd ht (l_ne_t h hMh)

private theorem inf_sup_zpowers_K_eq_bot :
    (zpowers l ⊔ zpowers t) ⊓ (Mh ⊓ centralizer ({t} : Set H)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxW, hxK⟩ := Subgroup.mem_inf.mp hx
  exact eq_one_of_mem_sup_zpowers_of_mem_Mh h hMh hxW (Subgroup.mem_inf.mp hxK).1

private theorem mem_K_of_conj_l {x : H} (hx : x ∈ Mh ⊓ centralizer ({t} : Set H)) :
    l * x * l⁻¹ ∈ Mh ⊓ centralizer ({t} : Set H) := by
  refine Subgroup.mem_inf.mpr ⟨Mh_normal h hMh hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hlt_inv : l⁻¹ * t = t * l⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right h.l_sq, h.t_l]
  calc l * x * l⁻¹ * t = l * x * (l⁻¹ * t) := by group
    _ = l * x * (t * l⁻¹) := by rw [hlt_inv]
    _ = l * (x * t) * l⁻¹ := by group
    _ = l * (t * x) * l⁻¹ := by rw [hxt]
    _ = (l * t) * x * l⁻¹ := by group
    _ = (t * l) * x * l⁻¹ := by rw [← h.t_l]
    _ = t * (l * x * l⁻¹) := by group

private theorem sup_zpowers_le_normalizer_K :
    zpowers l ⊔ zpowers t ≤
      Subgroup.normalizer ((Mh ⊓ centralizer ({t} : Set H) : Subgroup H) : Set H) := by
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => mem_K_of_conj_l h hMh hx
    · intro hx
      have hy := mem_K_of_conj_l h hMh hx
      rwa [show l * (l * x * l⁻¹) * l⁻¹ = x by
        rw [inv_eq_of_mul_eq_one_right h.l_sq]
        calc l * (l * x * l) * l = (l * l) * x * (l * l) := by group
          _ = x := by rw [h.l_sq]; group] at hy
  · rw [Subgroup.zpowers_le]
    refine (Subgroup.centralizer_le_normalizer
      ((Mh ⊓ centralizer ({t} : Set H) : Subgroup H) : Set H)) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp hx.2

theorem card_cent_Mh_t_le (hb : ZJBound t) :
    Nat.card ↥(Mh ⊓ centralizer ({t} : Set H)) ≤ 32 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup H := Mh ⊓ centralizer ({t} : Set H)
  let W : Subgroup H := zpowers l ⊔ zpowers t
  let P : Subgroup H := W ⊔ K
  change Nat.card K ≤ 32
  have hKp : IsPGroup 2 K := (Mh_isPGroup h hMh).to_le inf_le_left
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := ↥K)).mp hKp
  have hcard_l : Nat.card (zpowers l) = 2 := card_zpowers_of_sq_eq_one h.l_sq (l_ne_one h hMh)
  have hcard_t : Nat.card (zpowers t) = 2 := card_zpowers_of_sq_eq_one h.t_sq h.t_ne_one
  have hWnorm : W ≤ Subgroup.normalizer (K : Set H) := sup_zpowers_le_normalizer_K h hMh
  have hPcoe : (↑(W ⊔ K) : Set H) = (W : Set H) * (K : Set H) :=
    Subgroup.coe_mul_of_left_le_normalizer_right W K hWnorm
  let φ : (zpowers l × zpowers t) × K → P := fun p =>
    ⟨(p.1.1 : H) * (p.1.2 : H) * (p.2 : H),
      mul_mem (Subgroup.mem_sup_left (mul_mem (Subgroup.mem_sup_left p.1.1.2)
        (Subgroup.mem_sup_right p.1.2.2))) (Subgroup.mem_sup_right p.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨⟨a, b⟩, k⟩ ⟨⟨a', b'⟩, k'⟩ heq
    have hval : (a : H) * (b : H) * (k : H) = (a' : H) * (b' : H) * (k' : H) :=
      congrArg Subtype.val heq
    have h1 : ((a' : H) * (b' : H))⁻¹ * ((a : H) * (b : H)) = (k' : H) * (k : H)⁻¹ := by
      have h2 : (((a' : H) * (b' : H))⁻¹ * ((a : H) * (b : H))) * (k : H) = (k' : H) := by
        rw [mul_assoc, hval]; group
      exact eq_mul_inv_of_mul_eq h2
    have hmemW : ((a' : H) * (b' : H))⁻¹ * ((a : H) * (b : H)) ∈ W :=
      mul_mem (Subgroup.inv_mem _
          (mul_mem (Subgroup.mem_sup_left a'.2) (Subgroup.mem_sup_right b'.2)))
        (mul_mem (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right b.2))
    have hmemK : ((a' : H) * (b' : H))⁻¹ * ((a : H) * (b : H)) ∈ K := by
      rw [h1]; exact mul_mem k'.2 (Subgroup.inv_mem _ k.2)
    have hbot : ((a' : H) * (b' : H))⁻¹ * ((a : H) * (b : H)) = 1 := by
      have hmem : ((a' : H) * (b' : H))⁻¹ * ((a : H) * (b : H)) ∈ (⊥ : Subgroup H) := by
        rw [← inf_sup_zpowers_K_eq_bot h hMh]
        exact Subgroup.mem_inf.mpr ⟨hmemW, hmemK⟩
      exact Subgroup.mem_bot.mp hmem
    have hab : (a : H) * (b : H) = (a' : H) * (b' : H) := (eq_of_inv_mul_eq_one hbot).symm
    have haa : a = a' := by
      have h2 : (a' : H)⁻¹ * (a : H) = (b' : H) * (b : H)⁻¹ := by
        have h3 : ((a' : H)⁻¹ * (a : H)) * (b : H) = (b' : H) := by
          rw [mul_assoc, hab]; group
        exact eq_mul_inv_of_mul_eq h3
      have hmem : (a' : H)⁻¹ * (a : H) ∈ (⊥ : Subgroup H) := by
        rw [← inf_zpowers_l_t_eq_bot h hMh]
        exact Subgroup.mem_inf.mpr ⟨mul_mem (Subgroup.inv_mem _ a'.2) a.2,
          by rw [h2]; exact mul_mem b'.2 (Subgroup.inv_mem _ b.2)⟩
      exact Subtype.ext (eq_of_inv_mul_eq_one (Subgroup.mem_bot.mp hmem)).symm
    have hbb : b = b' := by
      have hb' : (a : H) * (b : H) = (a : H) * (b' : H) := by rw [hab, haa]
      exact Subtype.ext (mul_left_cancel hb')
    have hkk : k = k' := by
      have hk' : (a : H) * (b : H) * (k : H) = (a : H) * (b : H) * (k' : H) := by
        rw [hval, hab]
      exact Subtype.ext (mul_left_cancel hk')
    exact Prod.ext (Prod.ext haa hbb) hkk
  have hsurj : Function.Surjective φ := by
    rintro ⟨p, hp⟩
    have hp' : p ∈ (↑(W ⊔ K) : Set H) := hp
    rw [hPcoe, Set.mem_mul] at hp'
    obtain ⟨w, hw, k, hk, hwk⟩ := hp'
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_zpowers_iff h hMh).mp hw
    refine ⟨((⟨a, ha⟩, ⟨b, hb⟩), ⟨k, hk⟩), ?_⟩
    apply Subtype.ext
    show (a : H) * (b : H) * (k : H) = p
    rw [hab, hwk]
  have hcard : Nat.card ((zpowers l × zpowers t) × K) = Nat.card P :=
    Nat.card_eq_of_bijective φ ⟨hinj, hsurj⟩
  have hPcard : Nat.card P = 4 * Nat.card K := by
    rw [← hcard, Nat.card_prod, Nat.card_prod, hcard_l, hcard_t]
  have hPp : IsPGroup 2 P := by
    refine (IsPGroup.iff_card (p := 2) (G := ↥P)).mpr ⟨m + 2, ?_⟩
    rw [hPcard, hm, pow_add]
    ring
  have hPle : P ≤ centralizer ({t} : Set H) := by
    refine sup_le (sup_le ?_ ?_) inf_le_right
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact h.t_l.symm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbound := hb P hPle hPp
  rw [hPcard] at hbound
  omega

theorem cent_Mh_t_eq (hb : ZJBound t) :
    Mh ⊓ centralizer ({t} : Set H) = B ⊔ zpowers τ := by
  let D : Subgroup H := B ⊔ zpowers τ
  change Mh ⊓ centralizer ({t} : Set H) = D
  have hDle : D ≤ Mh ⊓ centralizer ({t} : Set H) := by
    refine sup_le ?_ ?_
    · intro b hb'
      exact Subgroup.mem_inf.mpr ⟨h.B_le_Q.trans (Q_le_Mh h hMh) hb',
        Subgroup.mem_centralizer_singleton_iff.mpr (h.B_cent_t b hb').symm⟩
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨tau_mem_Mh h hMh,
        Subgroup.mem_centralizer_singleton_iff.mpr h.t_tau.symm⟩
  have hBleD : B ≤ D := le_sup_left
  have h16dvd : 16 ∣ Nat.card D := by
    have hdvd := Subgroup.card_dvd_of_le hBleD
    rwa [h.card_B] at hdvd
  have hDle32 : Nat.card D ≤ 32 :=
    (Subgroup.card_le_of_le hDle).trans (card_cent_Mh_t_le h hMh hb)
  have hDne : Nat.card D ≠ 16 := by
    intro h16
    have hBD : B = D := Subgroup.eq_of_le_of_card_ge hBleD (by rw [h16, h.card_B])
    have hτD : τ ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
    rw [← hBD] at hτD
    exact h.tau_not_mem_Q (h.B_le_Q hτD)
  have hDcard : Nat.card D = 32 := by
    obtain ⟨k, hk⟩ := h16dvd
    have hpos : 0 < Nat.card D := Nat.card_pos
    omega
  exact (Subgroup.eq_of_le_of_card_ge hDle
    (by rw [hDcard]; exact card_cent_Mh_t_le h hMh hb)).symm

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem Mc_cent_t (hb : ZJBound t) {m : H} (hm : m ∈ Mc) (hc : t * m = m * t) : m ∈ B := by
  have hmMh : m ∈ Mh := Mc_le_Mh h hMh hMc hm
  have hmD : m ∈ B ⊔ zpowers τ := by
    rw [← cent_Mh_t_eq h hMh hb]
    exact Subgroup.mem_inf.mpr ⟨hmMh, Subgroup.mem_centralizer_singleton_iff.mpr hc.symm⟩
  let E : Subgroup H := Mc ⊓ (B ⊔ zpowers τ)
  have hBleE : B ≤ E := by
    intro b hb'
    exact Subgroup.mem_inf.mpr ⟨h.B_le_Q.trans (Q_le_Mc h hMh hMc) hb',
      Subgroup.mem_sup_left hb'⟩
  have hEneD : E ≠ B ⊔ zpowers τ := by
    intro hE
    have hτE : τ ∈ E := by
      rw [hE]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
    exact tau_not_mem_Mc h hMh hMc (Subgroup.mem_inf.mp hτE).1
  have h16dvdE : 16 ∣ Nat.card E := by
    have hdvd := Subgroup.card_dvd_of_le hBleE
    rwa [h.card_B] at hdvd
  have hE32 : Nat.card E ∣ 32 := by
    have hdvd := Subgroup.card_dvd_of_le (inf_le_right : E ≤ B ⊔ zpowers τ)
    rwa [card_sup_B_zpowers_tau h] at hdvd
  have hEcard : Nat.card E = 16 := by
    have hne : Nat.card E ≠ 32 := by
      intro h32
      exact hEneD (Subgroup.eq_of_le_of_card_ge inf_le_right
        (by rw [h32, card_sup_B_zpowers_tau h]))
    have hle : Nat.card E ≤ 32 := Nat.le_of_dvd (by norm_num) hE32
    obtain ⟨k, hk⟩ := h16dvdE
    have hpos : 0 < Nat.card E := Nat.card_pos
    omega
  have hBE : B = E := Subgroup.eq_of_le_of_card_ge hBleE (by rw [hEcard, h.card_B])
  have hmE : m ∈ E := Subgroup.mem_inf.mpr ⟨hm, hmD⟩
  rw [← hBE] at hmE
  exact hmE

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
