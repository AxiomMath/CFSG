module

public import CFSG.GH74.Uniqueness.SU.SU13TC3Abel
public import CFSG.GH74.Uniqueness.SU.SU13TC3Sylow
public import CFSG.GH74.Uniqueness.SU.SU13TC3Ord

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

theorem W_inf_F (e : Elts G z) (f : FPart z e) :
    oc (centralizer ({e.s₁} : Set G)) ⊓ f.F = ⊥ := by
  refine f.F_noOdd _ inf_le_right ?_ ?_
  · intro g hg n hn
    obtain ⟨hnW, hnF⟩ := mem_inf.mp hn
    have hgX : g ∈ centralizer ({e.s₁} : Set G) := mem_centralizer_singleton_iff.mpr (f.F_s₁ g hg)
    exact mem_inf.mpr ⟨conj_mem_oc hgX hnW, f.F.mul_mem (f.F.mul_mem hg hnF) (f.F.inv_mem hg)⟩
  · exact Odd.of_dvd_nat (odd_card_oc _) (Subgroup.card_dvd_of_le inf_le_left)

omit [Finite G] in
theorem card_TT_eq {W D : Subgroup G} (hD : ∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W) (hWD : W ⊓ D = ⊥) :
    Nat.card (TT W D hD) = Nat.card W * Nat.card D := by
  have hbij : Function.Bijective
      (fun p : W × D => (⟨(p.1 : G) * (p.2 : G), ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩ : TT W D hD)) := by
    constructor
    · rintro ⟨⟨w, hw⟩, ⟨d, hd⟩⟩ ⟨⟨w', hw'⟩, ⟨d', hd'⟩⟩ h
      have h1 : w * d = w' * d' := congrArg Subtype.val h
      have h2 : w'⁻¹ * w = d' * d⁻¹ := by
        calc w'⁻¹ * w = w'⁻¹ * (w * d) * d⁻¹ := by group
          _ = w'⁻¹ * (w' * d') * d⁻¹ := by rw [h1]
          _ = d' * d⁻¹ := by group
      have hmem : d' * d⁻¹ ∈ W ⊓ D :=
        mem_inf.mpr ⟨h2 ▸ W.mul_mem (W.inv_mem hw') hw, D.mul_mem hd' (D.inv_mem hd)⟩
      rw [hWD, mem_bot] at hmem
      have hdd : d' = d := by
        have := mul_inv_eq_one.mp hmem
        exact this
      have hww : w = w' := by
        rw [hdd] at h1
        exact mul_right_cancel h1
      subst hdd; subst hww; rfl
    · rintro ⟨x, w, hw, d, hd, rfl⟩
      exact ⟨(⟨w, hw⟩, ⟨d, hd⟩), rfl⟩
  calc Nat.card (TT W D hD) = Nat.card (W × D) := (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card W * Nat.card D := Nat.card_prod _ _

theorem center_W_eq (hz : orderOf z = 2) (e : Elts G z) (f : FPart9 z e)
    (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (hnc : ¬ ∀ a ∈ oc (centralizer ({e.s₁} : Set G)), ∀ b ∈ oc (centralizer ({e.s₁} : Set G)), a * b = b * a) :
    ∀ x ∈ oc (centralizer ({e.s₁} : Set G)),
      (∀ y ∈ oc (centralizer ({e.s₁} : Set G)), x * y = y * x) → x ∈ zpowers e.s₁ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  let ZW : Subgroup G :=
    { carrier := {x | x ∈ W ∧ ∀ y ∈ W, x * y = y * x}
      one_mem' := ⟨W.one_mem, fun y _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
        refine ⟨W.mul_mem ha hb, fun y hy => ?_⟩
        calc a * b * y = a * (b * y) := by group
          _ = a * (y * b) := by rw [hbc y hy]
          _ = (a * y) * b := by group
          _ = (y * a) * b := by rw [hac y hy]
          _ = y * (a * b) := by group
      inv_mem' := by
        rintro a ⟨ha, hac⟩
        exact ⟨W.inv_mem ha, fun y hy => (Commute.inv_left (show Commute a y from hac y hy)).eq⟩ }
  have hZW_le : ZW ≤ W := fun x hx => hx.1
  have hPZ : zpowers e.s₁ ≤ ZW := by
    intro c hc
    exact ⟨zpowers_le_oc e hc, fun y hy => zpowers_comm_of_mem_centralizer (oc_le _ hy) hc⟩
  have hinv : ∀ g ∈ f.F, ∀ u ∈ ZW, g * u * g⁻¹ ∈ ZW := by
    rintro g hg u ⟨huW, huc⟩
    have hgX := F_le_centralizerF e f.toFPart hg
    refine ⟨conj_mem_oc hgX huW, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ W := by
      have := conj_mem_oc (X := centralizer ({e.s₁} : Set G)) (g := g⁻¹)
        (inv_mem hgX) hy
      simpa using this
    have := huc _ hy'
    calc g * u * g⁻¹ * y = g * (u * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * u) * g⁻¹ := by rw [this]
      _ = y * (g * u * g⁻¹) := by group
  have hZdvd : Nat.card ZW ∣ 3 ^ 5 := hW5 ▸ Subgroup.card_dvd_of_le hZW_le
  obtain ⟨i, hi, hiZ⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hZdvd
  have h3Z : 3 ∣ Nat.card ZW := by
    have := Subgroup.card_dvd_of_le hPZ
    rwa [Nat.card_zpowers, e.s₁_ord] at this
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0, pow_zero] at hiZ; rw [hiZ] at h3Z; exact absurd (Nat.le_of_dvd one_pos h3Z) (by norm_num)
    · exact h0
  have hi5 : i ≠ 5 := by
    intro h5
    apply hnc
    have hZWW : ZW = W :=
      Subgroup.eq_of_le_of_card_ge hZW_le (by rw [hW5, hiZ, h5])
    intro a ha b hb
    have : a ∈ ZW := hZWW ▸ ha
    exact this.2 b hb
  have hi4 : i ≤ 4 := by omega
  have hi1' : i = 1 := by
    by_contra hne
    have hge : 2 ≤ i := by omega
    obtain ⟨g, hgF, hg⟩ := F_five9 f
    have hjm : 3 ^ i = 3 * 3 ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hU := orbit_stepF hz e f.toFPart (p := 3) (q := 5) (r := 3) (m := i - 1) (U := ZW) hPZ
      hZW_le hinv hgF hg (by rw [hiZ, hjm]) (dvd_refl 3) (by norm_num) (by norm_num)
      (fun k hk hkm => by
        have : k ≤ 3 := by omega
        interval_cases k <;> norm_num)
    have hle := Subgroup.card_le_of_le hU
    rw [hiZ, Nat.card_zpowers, e.s₁_ord] at hle
    have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hge
    omega
  have hZPcard : Nat.card ZW = Nat.card (zpowers e.s₁) := by
    rw [hiZ, hi1', Nat.card_zpowers, e.s₁_ord]; norm_num
  have hZP : zpowers e.s₁ = ZW := Subgroup.eq_of_le_of_card_ge hPZ (by rw [hZPcard])
  intro x hx hxc
  have : x ∈ ZW := ⟨hx, hxc⟩
  rw [← hZP] at this
  exact this

theorem W_comm (hz : orderOf z = 2) (e : Elts G z) (f : FPart9 z e) (l : Lem232 z e)
    (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (h38 : 3 ^ 8 ∣ Nat.card (centralizer ({e.s₂} : Set G))) :
    ∀ a ∈ oc (centralizer ({e.s₁} : Set G)), ∀ b ∈ oc (centralizer ({e.s₁} : Set G)), a * b = b * a := by
  by_contra hnc
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have hZW := center_W_eq hz e f hW5 hnc
  obtain ⟨D, hDF, hD9⟩ := F_sylow9 f
  have hDN : ∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W := fun d hd w hw =>
    conj_mem_oc (F_le_centralizerF e f.toFPart (hDF hd)) hw
  set T := TT W D hDN with hT
  have hWle : ¬ W ≤ zpowers e.s₁ := by
    intro h
    have := Subgroup.card_le_of_le h
    rw [hW5, Nat.card_zpowers, e.s₁_ord] at this
    norm_num at this
  have hPW : zpowers e.s₁ ≤ W := zpowers_le_oc e
  have hPT : zpowers e.s₁ ≤ T := hPW.trans (le_TT hDN)
  have hPc : ∀ x ∈ zpowers e.s₁, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    obtain ⟨w, hw, d, hd, rfl⟩ := hy
    have h1 : x * w = w * x := zpowers_comm_of_mem_centralizer (oc_le _ hw) hx
    have h2 : x * d = d * x := zpowers_comm_of_mem_centralizer (F_le_centralizerF e f.toFPart (hDF hd)) hx
    calc x * (w * d) = (x * w) * d := by group
      _ = (w * x) * d := by rw [h1]
      _ = w * (x * d) := by group
      _ = w * (d * x) := by rw [h2]
      _ = w * d * x := by group
  have hZT : ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x ∈ zpowers e.s₁ := by
    rintro x ⟨w, hw, d, hd, rfl⟩ hx
    have hd1 : d = 1 := by
      by_contra hd1
      refine hWle (W_le_of_acts_trivially hz e f.toFPart (hDF hd) hd1 (fun u hu => ?_))
      have hcomm := hx u (le_TT hDN hu)
      have h1 : d * u * d⁻¹ * u⁻¹ = w⁻¹ * u * w * u⁻¹ := by
        calc d * u * d⁻¹ * u⁻¹ = w⁻¹ * (w * d * u) * d⁻¹ * u⁻¹ := by group
          _ = w⁻¹ * (u * (w * d)) * d⁻¹ * u⁻¹ := by rw [hcomm]
          _ = w⁻¹ * u * w * u⁻¹ := by group
      rw [h1]
      simpa using comm_mem_PF hz e f.toFPart (W.inv_mem hw) hu
    rw [hd1, mul_one] at hx ⊢
    exact hZW w hw (fun y hy => by simpa using hx y (le_TT hDN hy))
  have hmax : ∀ R : Subgroup G, R ≤ normalizer (zpowers e.s₁ : Set G) → IsPGroup 3 R → T ≤ R → R = T := by
    intro R hRN hRp hTR
    refine le_antisymm (fun g hg => ?_) hTR
    have hodd : Odd (orderOf g) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hRp ⟨g, hg⟩
      rw [Subgroup.orderOf_mk] at hk
      rw [hk]
      exact Odd.pow (by decide)
    have hgc : g * e.s₁ = e.s₁ * g := centralizes_of_normalizes_zpowers e.s₁_ord (hRN hg) hodd
    obtain ⟨c, k, hc, hcz, hk, hgck⟩ := l.a g hgc
    have hkT : k ∈ T := le_TT hDN hk
    have hcR : c ∈ R := by
      have : c = g * k⁻¹ := by rw [hgck]; group
      rw [this]; exact R.mul_mem hg (R.inv_mem (hTR hkT))
    have hcH : c ∈ centralizer ({e.s₁} : Set G) ⊓ centralizer ({z} : Set G) :=
      mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc, mem_centralizer_singleton_iff.mpr hcz⟩
    rw [f.cent] at hcH
    obtain ⟨p, hp, f', hf', hpf⟩ := SU1.mem_sup_of_commute (A := zpowers e.s₁) (B := f.F)
      (fun p hp a ha => zpowers_comm_of_mem_centralizer
        (mem_centralizer_singleton_iff.mpr (f.F_s₁ a ha)) hp) hcH
    have hpW : p ∈ W := hPW hp
    have hf'R : f' ∈ R := by
      have : f' = p⁻¹ * c := by rw [← hpf]; group
      rw [this]
      exact R.mul_mem (R.inv_mem (hTR (hPT hp))) hcR
    have hFR : f.F ⊓ R = D := by
      have hDle : D ≤ f.F ⊓ R := le_inf hDF ((le_TT' hDN).trans hTR)
      have hp3 : IsPGroup 3 (f.F ⊓ R : Subgroup G) := hRp.to_le inf_le_right
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).mp hp3
      have hdvd : Nat.card (f.F ⊓ R : Subgroup G) ∣ Nat.card f.F := Subgroup.card_dvd_of_le inf_le_left
      rw [f.F_card, hj] at hdvd
      have hj2 : j ≤ 2 := by
        by_contra hlt
        have h3 : 3 ^ 3 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
        have := h3.trans hdvd
        norm_num at this
      have hle : Nat.card (f.F ⊓ R : Subgroup G) ≤ Nat.card D := by
        rw [hj, hD9]
        calc 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj2
          _ = 9 := by norm_num
      exact (Subgroup.eq_of_le_of_card_ge hDle hle).symm
    have hf'D : f' ∈ D := hFR ▸ mem_inf.mpr ⟨hf', hf'R⟩
    have hf'k : f' * k * f'⁻¹ ∈ W := conj_mem_oc (F_le_centralizerF e f.toFPart hf') hk
    refine ⟨p * (f' * k * f'⁻¹), W.mul_mem hpW hf'k, f', hf'D, ?_⟩
    rw [hgck, ← hpf]; group
  have hWD : W ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ W ⊓ f.F := mem_inf.mpr ⟨(mem_inf.mp hx).1, hDF (mem_inf.mp hx).2⟩
    rw [W_inf_F e f.toFPart] at this
    exact this
  have hTcard : Nat.card T = 3 ^ 7 := by
    rw [hT, card_TT_eq hDN hWD, hW5, hD9]; norm_num
  have hTp : IsPGroup 3 T := IsPGroup.of_card hTcard
  have hmaxG : ∀ R : Subgroup G, IsPGroup 3 R → T ≤ R → R = T := fun R hR hTR =>
    eq_of_isPGroup_le_of_normalizer (p := 3) (H := normalizer (zpowers e.s₁ : Set G))
      (E := zpowers e.s₁) (Es := T) (R := R) le_rfl
      (fun g hg => mem_normalizer_of_center hPc hPT hZT hg)
      (fun R' hR'H hR'p hTR' => hmax R' hR'H hR'p hTR') hR hTR
  obtain ⟨Q, hQ⟩ := hTp.exists_le_sylow
  have hQeq : (Q : Subgroup G) = T := hmaxG Q Q.isPGroup' hQ
  have hQcard : Nat.card Q = 3 ^ 7 := by
    have : Nat.card (Q : Subgroup G) = Nat.card T := by rw [hQeq]
    rw [← hTcard]; exact this
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := centralizer ({e.s₂} : Set G)) 3 h38
  have hKp : IsPGroup 3 (K.map (centralizer ({e.s₂} : Set G)).subtype) :=
    (IsPGroup.of_card hK).map _
  obtain ⟨Q', hQ'⟩ := hKp.exists_le_sylow
  have hQ'card : Nat.card Q' = 3 ^ 7 := by
    have h1 : Nat.card Q' = 3 ^ (Nat.card G).factorization 3 := Sylow.card_eq_multiplicity Q'
    have h2 : Nat.card Q = 3 ^ (Nat.card G).factorization 3 := Sylow.card_eq_multiplicity Q
    rw [h1, ← h2, hQcard]
  have hle := Subgroup.card_le_of_le hQ'
  rw [Subgroup.card_map_of_injective (centralizer ({e.s₂} : Set G)).subtype_injective, hK] at hle
  have : Nat.card (Q' : Subgroup G) = 3 ^ 7 := hQ'card
  rw [this] at hle
  norm_num at hle

end CFSG.GH74.Uniqueness.SU.SU13
