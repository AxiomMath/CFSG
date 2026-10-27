module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyNorm
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUE1

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

namespace SAU

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}
  {C : ECoord G}

@[expose] def M0 (C : ECoord G) (f : G) : Subgroup G :=
  centralizer ({f ^ 2} : Set G) ⊓ normalizer (C.E : Set G)

theorem mem_M0 {x : G} : x ∈ M0 C f ↔ x * f ^ 2 = f ^ 2 * x ∧ x ∈ normalizer (C.E : Set G) := by
  unfold M0
  rw [Subgroup.mem_inf, mem_centralizer_singleton_iff]

@[expose] def IsW (C : ECoord G) (f : G) (L : Subgroup G) (y u : G) : Prop :=
  u ∈ M0 C f ∧ (∀ e ∈ C.E, u * e * u⁻¹ = e⁻¹) ∧ u ∈ L ⊔ zpowers y

@[expose] def OmegaE (C : ECoord G) : Subgroup G where
  carrier := {e | e ∈ C.E ∧ e * e = 1}
  one_mem' := ⟨C.E.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, haa⟩ ⟨hb, hbb⟩
    refine ⟨C.E.mul_mem ha hb, ?_⟩
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [C.comm hb ha]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb]; group
  inv_mem' := by
    rintro a ⟨ha, haa⟩
    refine ⟨C.E.inv_mem ha, ?_⟩
    have : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [this, haa]
    simp

theorem natCard_OmegaE (hQ : Q0Facts) : Nat.card (OmegaE C) = 16 := by
  classical
  let φ : OmegaE C ≃ {v : V4 // v + v = 0} :=
    { toFun := fun e => ⟨C.vec (e : G), (C.mul_self_eq_one_iff' e.2.1).1 e.2.2⟩
      invFun := fun v => ⟨C.elt v.1, C.elt_mem _, (C.mul_self_eq_one_iff' (C.elt_mem _)).2
        (by rw [C.vec_elt]; exact v.2)⟩
      left_inv := fun e => Subtype.ext (C.elt_vec e.2.1)
      right_inv := fun v => Subtype.ext (C.vec_elt v.1) }
  rw [Nat.card_congr φ, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hQ.om_card

namespace IsW

variable {u w : G}

theorem normalizes (hu : IsW C f L y u) : u ∈ normalizer (C.E : Set G) := (mem_M0.1 hu.1).2

theorem comm_t (hu : IsW C f L y u) : u * f ^ 2 = f ^ 2 * u := (mem_M0.1 hu.1).1

theorem inv_conj (hu : IsW C f L y u) {e : G} (he : e ∈ C.E) : u⁻¹ * e * u = e⁻¹ := by
  have hn := hu.normalizes
  have he' : u⁻¹ * e * u ∈ C.E := by
    have := (mem_normalizer_iff.1 (inv_mem hn) e).1 he
    simpa using this
  have h1 := hu.2.1 _ he'
  have h2 : u * (u⁻¹ * e * u) * u⁻¹ = e := by group
  rw [h2] at h1
  have h3 : e⁻¹ = u⁻¹ * e * u := by simpa using congrArg (·⁻¹) h1
  exact h3.symm

theorem conj (H : Sect7Hyps G L f s y S₀ n) (hu : IsW C f L y u) {m : G} (hm : m ∈ M0 C f) :
    IsW C f L y (m * u * m⁻¹) := by
  refine ⟨mul_mem (mul_mem hm hu.1) (inv_mem hm), fun e he => ?_, ?_⟩
  · have hmn := (mem_M0.1 hm).2
    have he' : m⁻¹ * e * m ∈ C.E := by
      have := (mem_normalizer_iff.1 (inv_mem hmn) e).1 he
      simpa using this
    have h1 := hu.2.1 _ he'
    calc m * u * m⁻¹ * e * (m * u * m⁻¹)⁻¹ = m * (u * (m⁻¹ * e * m) * u⁻¹) * m⁻¹ := by group
      _ = m * (m⁻¹ * e * m)⁻¹ * m⁻¹ := by rw [h1]
      _ = e⁻¹ := by group
  · exact (H.normalizes_y (mem_M0.1 hm).1 u).1 hu.2.2

theorem inv_mul_mem_E (h : Sect8Hyp C f n S₀) (hu : IsW C f L y u) (hw : IsW C f L y w) :
    u⁻¹ * w ∈ C.E := by
  refine h.centN _ ?_ fun e he => ?_
  · have h1 : Commute u⁻¹ (f ^ 2) := (show Commute u (f ^ 2) from hu.comm_t).inv_left
    have h2 : Commute w (f ^ 2) := hw.comm_t
    exact (h1.mul_left h2).eq
  · have h1 : u⁻¹ * e⁻¹ * u = e := by
      have := hu.inv_conj (C.E.inv_mem he)
      rw [inv_inv] at this
      exact this
    calc u⁻¹ * w * e = u⁻¹ * (w * e * w⁻¹) * w := by group
      _ = u⁻¹ * e⁻¹ * w := by rw [hw.2.1 e he]
      _ = (u⁻¹ * e⁻¹ * u) * (u⁻¹ * w) := by group
      _ = e * (u⁻¹ * w) := by rw [h1]

end IsW

theorem card_dvd_of_rmul_closed {H : Subgroup G} {S : Set G}
    (hS : ∀ s ∈ S, ∀ h ∈ H, s * h ∈ S) : Nat.card H ∣ Nat.card S := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let π : G → G ⧸ H := QuotientGroup.mk
  let T : Finset G := (Set.toFinite S).toFinset
  have hT : ∀ g, g ∈ T ↔ g ∈ S := fun g => by simp [T]
  have hfiber : ∀ q ∈ T.image π, (T.filter fun g => π g = q).card = Nat.card H := by
    intro q hq
    obtain ⟨g₀, hg₀T, rfl⟩ := Finset.mem_image.1 hq
    have hset : T.filter (fun g => π g = π g₀) =
        (Finset.univ : Finset H).image (fun h : H => g₀ * (h : G)) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, hg⟩
        have hh : g₀⁻¹ * g ∈ H := QuotientGroup.eq.1 hg.symm
        exact ⟨⟨g₀⁻¹ * g, hh⟩, by simp⟩
      · rintro ⟨h, rfl⟩
        refine ⟨(hT _).2 (hS g₀ ((hT g₀).1 hg₀T) h h.2), ?_⟩
        exact QuotientGroup.eq.2 (by simp)
    rw [hset, Finset.card_image_of_injective _ (fun a b hab => Subtype.ext (mul_left_cancel hab)),
      Finset.card_univ, Nat.card_eq_fintype_card]
  have hcard := Finset.card_eq_sum_card_fiberwise (f := π) (s := T) (t := T.image π)
    (fun x hx => Finset.mem_image_of_mem _ hx)
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul] at hcard
  refine ⟨(T.image π).card, ?_⟩
  have h2 : Nat.card S = T.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card S (Set.toFinite S)]
  rw [h2, hcard, mul_comm]

section Orbit

@[expose] def Cls (C : ECoord G) (f w : G) : Set G := {u | ∃ m ∈ M0 C f, u = m * w * m⁻¹}

theorem mem_Cls_self {w : G} : w ∈ Cls C f w := ⟨1, one_mem _, by simp⟩

theorem Cls_conj {w : G} {g : G} (hg : g ∈ M0 C f) {u : G} (hu : u ∈ Cls C f w) :
    g * u * g⁻¹ ∈ Cls C f w := by
  obtain ⟨m, hm, rfl⟩ := hu
  refine ⟨g * m, mul_mem hg hm, ?_⟩
  group

theorem Cls_isW (H : Sect7Hyps G L f s y S₀ n) {w : G} (hw : IsW C f L y w) {u : G}
    (hu : u ∈ Cls C f w) : IsW C f L y u := by
  obtain ⟨m, hm, rfl⟩ := hu
  exact hw.conj H hm

theorem Cls_rmul (h : Sect8Hyp C f n S₀) (hQ : Q0Facts) (H : Sect7Hyps G L f s y S₀ n) {w : G}
    (hw : IsW C f L y w) {u : G} (hu : u ∈ Cls C f w) {ω : G} (hω : ω ∈ OmegaE C) :
    u * ω ∈ Cls C f w := by
  have hui := Cls_isW H hw hu
  obtain ⟨e, heE, hee⟩ := h.exists_sqrt hQ hω.1 hω.2
  have hf2E : f ^ 2 ∈ C.E := pow_mem h.f_mem 2
  have heM : e⁻¹ ∈ M0 C f :=
    mem_M0.2 ⟨C.comm (C.E.inv_mem heE) hf2E, le_normalizer (C.E.inv_mem heE)⟩
  have h1 : u * ω = e⁻¹ * u * (e⁻¹)⁻¹ := by
    have hue : u * e = e⁻¹ * u := by
      have := hui.2.1 e heE
      calc u * e = (u * e * u⁻¹) * u := by group
        _ = e⁻¹ * u := by rw [this]
    calc u * ω = u * (e * e) := by rw [hee]
      _ = (u * e) * e := by group
      _ = e⁻¹ * u * (e⁻¹)⁻¹ := by rw [hue, inv_inv]
  obtain ⟨m, hm, rfl⟩ := hu
  rw [h1]
  refine ⟨e⁻¹ * m, mul_mem heM hm, ?_⟩
  group

theorem card_Ey_le (h : Sect8Hyp C f n S₀) (H : Sect7Hyps G L f s y S₀ n) :
    Nat.card (C.E ⊓ (L ⊔ zpowers y) : Subgroup G) ≤ 128 := by
  have hle : (C.E ⊓ (L ⊔ zpowers y) : Subgroup G) ≤ C.E := inf_le_left
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hE : Nat.card C.E = 256 := C.natCard_E
  have hpos : 0 < Nat.card (C.E ⊓ (L ⊔ zpowers y) : Subgroup G) := Nat.card_pos
  have hne : (C.E ⊓ (L ⊔ zpowers y) : Subgroup G) ≠ C.E := by
    intro heq
    apply SAU.f_not_mem_H1 H
    have : f ∈ (C.E ⊓ (L ⊔ zpowers y) : Subgroup G) := by rw [heq]; exact h.f_mem
    exact this.2
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exfalso
    interval_cases k
    · omega
    · apply hne
      exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  · nlinarith

@[expose] def permOf (O : Set G) (hO : ∀ g ∈ M0 C f, ∀ u ∈ O, g * u * g⁻¹ ∈ O) (g : G)
    (hg : g ∈ M0 C f) : Equiv.Perm O where
  toFun u := ⟨g * u * g⁻¹, hO g hg u u.2⟩
  invFun u := ⟨g⁻¹ * u * g, by simpa using hO g⁻¹ (inv_mem hg) u u.2⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])

theorem permOf_apply (O : Set G) (hO : ∀ g ∈ M0 C f, ∀ u ∈ O, g * u * g⁻¹ ∈ O) {g : G}
    (hg : g ∈ M0 C f) (u : O) : ((permOf O hO g hg u : O) : G) = g * u * g⁻¹ := rfl

theorem permOf_pow (O : Set G) (hO : ∀ g ∈ M0 C f, ∀ u ∈ O, g * u * g⁻¹ ∈ O) {g : G}
    (hg : g ∈ M0 C f) (k : ℕ) (u : O) :
    (((permOf O hO g hg ^ k) u : O) : G) = g ^ k * u * (g ^ k)⁻¹ := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, permOf_apply]
    group

theorem permOf_pow_eq_one (O : Set G) (hO : ∀ g ∈ M0 C f, ∀ u ∈ O, g * u * g⁻¹ ∈ O) {g : G}
    (hg : g ∈ M0 C f) {p : ℕ} (hgp : g ^ p = 1) : permOf O hO g hg ^ p = 1 := by
  ext u
  rw [permOf_pow, hgp]
  simp

theorem permOf_fixed_iff (O : Set G) (hO : ∀ g ∈ M0 C f, ∀ u ∈ O, g * u * g⁻¹ ∈ O) {g : G}
    (hg : g ∈ M0 C f) (u : O) : permOf O hO g hg u = u ↔ g * (u : G) = (u : G) * g := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    rw [permOf_apply] at this
    calc g * (u : G) = (g * (u : G) * g⁻¹) * g := by group
      _ = (u : G) * g := by rw [this]
  · intro h
    apply Subtype.ext
    rw [permOf_apply]
    calc g * (u : G) * g⁻¹ = ((u : G) * g) * g⁻¹ := by rw [h]
      _ = u := by group

theorem exists_fixed_conj (h : Sect8Hyp C f n S₀) (hQ : Q0Facts) (hU : UFactsQ)
    (H : Sect7Hyps G L f s y S₀ n) {w : G} (hw : IsW C f L y w) {r v₀ : G} (hr : r ∈ M0 C f)
    (hr3 : r ^ 3 = 1) (hv : v₀ ∈ M0 C f) (hv7 : v₀ ^ 7 = 1)
    (hvfix : ∀ x ∈ C.E, x ∈ L → v₀ * x * v₀⁻¹ = x → x = 1 ∨ x = f ^ 2) :
    ∃ m ∈ M0 C f, r * (m * w * m⁻¹) = (m * w * m⁻¹) * r := by
  classical
  set O : Set G := Cls C f w with hOdef
  have hO : ∀ g ∈ M0 C f, ∀ u ∈ O, g * u * g⁻¹ ∈ O := fun g hg u hu => Cls_conj hg hu
  let _ : Fintype O := Fintype.ofFinite O
  have hOW : ∀ u ∈ O, IsW C f L y u := fun u hu => Cls_isW H hw hu
  have hcard128 : Nat.card O ≤ 128 := by
    have : Nat.card O ≤ Nat.card (C.E ⊓ (L ⊔ zpowers y) : Subgroup G) := by
      refine Nat.card_le_card_of_injective (fun u => ⟨w⁻¹ * u, ?_⟩) ?_
      · exact ⟨IsW.inv_mul_mem_E h hw (hOW u u.2),
          (L ⊔ zpowers y).mul_mem ((L ⊔ zpowers y).inv_mem hw.2.2) (hOW u u.2).2.2⟩
      · intro a b hab
        have := congrArg Subtype.val hab
        exact Subtype.ext (mul_left_cancel this)
    exact this.trans (card_Ey_le h H)
  have h16 : 16 ∣ Nat.card O := by
    have := card_dvd_of_rmul_closed (H := OmegaE C) (S := O)
      (fun u hu ω hω => Cls_rmul h hQ H hw hu hω)
    rwa [natCard_OmegaE hQ] at this
  have hpos : 0 < Nat.card O := by
    have : Nonempty O := ⟨⟨w, mem_Cls_self⟩⟩
    exact Nat.card_pos
  have h7 : Nat.card O % 7 ≤ 2 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    set σ := permOf O hO v₀ hv with hσ
    have hσ7 : σ ^ 7 ^ 1 = 1 := by
      rw [pow_one]
      exact permOf_pow_eq_one O hO hv hv7
    have hmod := Equiv.Perm.card_compl_support_modEq hσ7
    have hfix : ∀ u : O, u ∈ σ.supportᶜ ↔ v₀ * (u : G) = (u : G) * v₀ := by
      intro u
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not, hσ]
      exact permOf_fixed_iff O hO hv u
    have hle : σ.supportᶜ.card ≤ 2 := by
      by_cases hne : σ.supportᶜ.Nonempty
      · obtain ⟨u₀, hu₀⟩ := hne
        have hf2Ω : f ^ 2 ∈ OmegaE C := by
          refine ⟨pow_mem h.f_mem 2, ?_⟩
          rw [← pow_add]
          exact H.four.pow_four
        let u₀' : O := ⟨(u₀ : G) * f ^ 2, Cls_rmul h hQ H hw u₀.2 hf2Ω⟩
        refine (Finset.card_le_card (t := {u₀, u₀'}) ?_).trans Finset.card_le_two
        intro u hu
        have hc₀ := (hfix u₀).1 hu₀
        have hc := (hfix u).1 hu
        have hx : (u₀ : G)⁻¹ * u ∈ C.E := IsW.inv_mul_mem_E h (hOW u₀ u₀.2) (hOW u u.2)
        have hxH : (u₀ : G)⁻¹ * u ∈ L ⊔ zpowers y :=
          (L ⊔ zpowers y).mul_mem ((L ⊔ zpowers y).inv_mem (hOW u₀ u₀.2).2.2) (hOW u u.2).2.2
        have hxL : (u₀ : G)⁻¹ * u ∈ L :=
          Sect8Hyp.E1_le_L h hQ H hU (Sect8Hyp.mem_E1sub_of_mem_H1 h hQ H hU hx hxH)
        have hxc : v₀ * ((u₀ : G)⁻¹ * u) * v₀⁻¹ = (u₀ : G)⁻¹ * u := by
          have hca : Commute v₀ (u₀ : G) := hc₀
          have hcb : Commute v₀ (u : G) := hc
          have hcx := hca.inv_right.mul_right hcb
          calc v₀ * ((u₀ : G)⁻¹ * u) * v₀⁻¹ = ((u₀ : G)⁻¹ * u) * v₀ * v₀⁻¹ := by rw [hcx.eq]
            _ = (u₀ : G)⁻¹ * u := by group
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hvfix _ hx hxL hxc with h1 | h1
        · left
          apply Subtype.ext
          have : (u : G) = u₀ * ((u₀ : G)⁻¹ * u) := by group
          rw [this, h1]
          simp
        · right
          apply Subtype.ext
          have : (u : G) = u₀ * ((u₀ : G)⁻¹ * u) := by group
          rw [this, h1]
      · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
        simp
    rw [Nat.card_eq_fintype_card]
    have h2 := hmod.symm
    unfold Nat.ModEq at h2
    omega
  have h3 : ¬ 3 ∣ Fintype.card O := by
    intro h3
    rw [← Nat.card_eq_fintype_card] at h3
    obtain ⟨k, hk⟩ := h16
    rw [hk] at h3 hcard128 hpos h7
    have hk8 : k ≤ 8 := by omega
    interval_cases k <;> omega
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (n := 1) h3
    (by rw [pow_one]; exact permOf_pow_eq_one O hO hr hr3 : permOf O hO r hr ^ 3 ^ 1 = 1)
  obtain ⟨m, hm, hma⟩ := a.2
  refine ⟨m, hm, ?_⟩
  have := (permOf_fixed_iff O hO hr a).1 ha
  rw [hma] at this
  exact this

end Orbit

end SAU

end CFSG.EvenSporadicStandard.TwoHS
