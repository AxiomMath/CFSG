module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G33S
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Dih

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

section S2

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

omit [Finite G] in
theorem zCenter_conj {V : Subgroup G} {g : G} (hg : g ∈ normalizer (V : Set G)) :
    (∀ w ∈ zCenter V, g * w * g⁻¹ ∈ zCenter V) ∧ (∀ w ∈ zCenter V, g⁻¹ * w * g ∈ zCenter V) := by
  obtain ⟨hgn, hgn'⟩ := normalizer_conj_mem hg
  constructor
  · intro w hw
    refine ⟨hgn w hw.1, fun v hv => ?_⟩
    have h1 := hw.2 (g⁻¹ * v * g) (hgn' v hv)
    calc v * (g * w * g⁻¹) = g * ((g⁻¹ * v * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = (g * w * g⁻¹) * v := by group
  · intro w hw
    refine ⟨hgn' w hw.1, fun v hv => ?_⟩
    have h1 := hw.2 (g * v * g⁻¹) (hgn v hv)
    calc v * (g⁻¹ * w * g) = g⁻¹ * ((g * v * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * v * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * w * g) * v := by group

theorem Env33.hZV' (E : Env33 x y K T V W f z) (hx : x ∉ zCenter V) :
    zCenter V = zpowers z ⊔ zpowers f := by
  have hfZ : f ∈ zCenter V := ⟨E.cfg.f_mem_V, fun v hv => E.hVf v hv⟩
  apply le_antisymm
  · intro w hw
    have hM : zpowers z ⊔ zpowers f ≤ centralizer ({x} : Set G) := by
      refine sup_le ((zpowers_le).2 ?_) ((zpowers_le).2 ?_)
      · exact mem_centralizer_singleton_iff.2 (E.hxcommK z E.hzP.2)
      · exact mem_centralizer_singleton_iff.2 E.cfg.hxf.symm
    obtain ⟨m, hm, c, hc, hwmc⟩ := Thm1P310.exists_mul_of_mem_sup
      (P := zpowers z ⊔ zpowers f) (D := zpowers x)
      (fun p hp d hd => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hd
        have hpx : p * x = x * p := mem_centralizer_singleton_iff.1 (hM hp)
        exact (Commute.zpow_right (show Commute p x from hpx) k).eq)
      (E.hZVle w hw)
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers E.hx2 hc with h | h
    · rw [hwmc, h, mul_one]; exact hm
    · exfalso
      apply hx
      have hmZ : m ∈ zCenter V := by
        have : zpowers z ⊔ zpowers f ≤ zCenter V :=
          sup_le ((zpowers_le).2 E.hzZ) ((zpowers_le).2 hfZ)
        exact this hm
      have : x = m⁻¹ * w := by rw [hwmc, h]; group
      rw [this]
      exact (zCenter V).mul_mem ((zCenter V).inv_mem hmZ) hw
  · exact sup_le ((zpowers_le).2 E.hzZ) ((zpowers_le).2 hfZ)

theorem Env33.conj_data (E : Env33 x y K T V W f z) (hZV : zCenter V = zpowers z ⊔ zpowers f)
    {b : G} (hbN : b ∈ normalizer (V : Set G)) (hbf : b * f * b⁻¹ ≠ f) :
    (secD K f V).map (MulAut.conj b).toMonoidHom ≤ V ∧
    (∀ v ∈ V, ∀ e ∈ (secD K f V).map (MulAut.conj b).toMonoidHom,
      v * e * v⁻¹ ∈ (secD K f V).map (MulAut.conj b).toMonoidHom) ∧
    secD K f V ⊓ (secD K f V).map (MulAut.conj b).toMonoidHom = ⊥ ∧
    ∀ d ∈ secD K f V, ∀ e ∈ (secD K f V).map (MulAut.conj b).toMonoidHom, d * e = e * d := by
  classical
  obtain ⟨hbn, hbn'⟩ := normalizer_conj_mem hbN
  obtain ⟨hZb, hZb'⟩ := zCenter_conj hbN
  have hzf_comm : z * f = f * z := (E.hfP z E.hzP).symm
  have hfZ : f ∈ zCenter V := ⟨E.cfg.f_mem_V, fun v hv => E.hVf v hv⟩
  have hD'V : (secD K f V).map (MulAut.conj b).toMonoidHom ≤ V := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := mem_map_conj.1 he
    exact hbn d (E.hDV hd)
  have hD'n : ∀ v ∈ V, ∀ e ∈ (secD K f V).map (MulAut.conj b).toMonoidHom,
      v * e * v⁻¹ ∈ (secD K f V).map (MulAut.conj b).toMonoidHom := by
    intro v hv e he
    obtain ⟨d, hd, rfl⟩ := mem_map_conj.1 he
    refine mem_map_conj.2 ⟨(b⁻¹ * v * b) * d * (b⁻¹ * v * b)⁻¹, E.hDn _ (hbn' v hv) d hd, ?_⟩
    group
  have hDD' : secD K f V ⊓ (secD K f V).map (MulAut.conj b).toMonoidHom = ⊥ := by
    by_contra hne
    obtain ⟨w, ⟨hwD, hwD'⟩, hw1, hwc⟩ := exists_central_of_normal'
      (U := secD K f V ⊓ (secD K f V).map (MulAut.conj b).toMonoidHom) (B := V) hne
      (inf_le_left.trans E.hDV)
      (fun v hv u hu => ⟨E.hDn v hv u hu.1, hD'n v hv u hu.2⟩) E.hV2
    have hwZ : w ∈ zCenter V := ⟨E.hDV hwD, fun v hv => hwc v hv⟩
    rw [hZV] at hwZ
    have hwf : w = f := by
      rcases klein_cases E.hz2' E.hf2' hzf_comm hwZ with h | h | h | h
      · exact absurd h hw1
      · exact absurd (h ▸ hwD) E.hzD
      · exact h
      · exfalso
        apply E.hzD
        have : z = w * f⁻¹ := by rw [h]; group
        rw [this]
        exact (secD K f V).mul_mem hwD ((secD K f V).inv_mem E.hfD)
    obtain ⟨d, hd, hdw⟩ := mem_map_conj.1 hwD'
    have hdZ : d ∈ zCenter V := by
      have : d = b⁻¹ * w * b := by rw [← hdw]; group
      rw [this]
      apply hZb'
      rw [hwf]
      exact hfZ
    rw [hZV] at hdZ
    have hdf : d = f := by
      rcases klein_cases E.hz2' E.hf2' hzf_comm hdZ with h | h | h | h
      · exfalso
        apply hw1
        rw [← hdw, h]
        group
      · exact absurd (h ▸ hd) E.hzD
      · exact h
      · exfalso
        apply E.hzD
        have : z = d * f⁻¹ := by rw [h]; group
        rw [this]
        exact (secD K f V).mul_mem hd ((secD K f V).inv_mem E.hfD)
    apply hbf
    rw [hdf] at hdw
    rw [hdw, hwf]
  exact ⟨hD'V, hD'n, hDD', commute_of_inf_eq_bot E.hDV hD'V E.hDn hD'n hDD'⟩

omit [Finite G] in
theorem card_of_isDihedralTwoGroup {P : Subgroup G} {n : ℕ} (h : IVK.IsDihedralTwoGroup ↥P n) :
    Nat.card ↥P = 2 ^ n := by
  obtain ⟨-, k, hk, -, ⟨φ⟩⟩ := h
  rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  omega

omit [Finite G] in
theorem sixteen_dvd_of_odd_sq {s : ℕ} (hs : Odd s) : 16 ∣ (s * s) * ((s * s) ^ 2 - 1) := by
  have h1 : (s * s) ^ 2 % 16 = 1 := by
    have h2 : s % 16 < 16 := Nat.mod_lt s (by norm_num)
    have h3 : s % 2 = 1 := Nat.odd_iff.1 hs
    have h4 : (s * s) ^ 2 % 16 = ((s % 16) * (s % 16) % 16) ^ 2 % 16 := by
      rw [Nat.pow_mod, Nat.mul_mod]
    rw [h4]
    have h5 : s % 16 % 2 = 1 := by omega
    interval_cases h : s % 16 <;> simp_all
  exact Dvd.dvd.mul_left (by omega) _

theorem Env33.hV_eq_PD (E : Env33 x y K T V W f z) (hP8 : Nat.card ↥(T ⊓ K) = 8) :
    ∀ v ∈ V, ∃ p ∈ T ⊓ K, ∃ d ∈ secD K f V, v = p * d := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrodd, hr5, hI, hKshape⟩ := E.hr
  obtain ⟨eIJ⟩ := kBar_pumpJ_equiv E.hsup
  have hJmodel : HasL2Model (kBar (pumpJ K f)) (fun q => q = r) :=
    TwoThin.hasL2Model_of_mulEquiv eIJ hI
  obtain ⟨F₀, _, _, hF₀card, hF₀, ⟨e₀⟩⟩ := exists_l2_model_card hrodd hr5 hJmodel
  have hdvdK : r ^ 2 - 1 ∣ Nat.card (kBar K) := by
    rcases hKshape with hK2 | ⟨hr5', hKA7⟩
    · rw [Thm1L34.card_kBar_of_hasL2Model hK2]
      obtain ⟨k, hk⟩ := hrodd
      have hr2 : r ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by rw [hk]; ring
      rw [hr2, PumpClass.ordA_one_odd, Nat.add_sub_cancel]
      exact ⟨(2 * k * (k + 1) + 1) * (2 * (2 * k * (k + 1)) + 1), by ring⟩
    · rw [Thm1L34.card_kBar_of_alt7 hKA7, hr5']
      norm_num
  have hrsq : ¬ ∃ s : ℕ, r = s * s := by
    rintro ⟨s, hs⟩
    have hs_odd : Odd s := (Nat.odd_mul.1 (hs ▸ hrodd)).1
    have h16 : 2 ^ 4 ∣ r * (r ^ 2 - 1) := by
      rw [hs]; exact sixteen_dvd_of_odd_sq hs_odd
    have := two_pow_le_card_of_dvd E.hPK hrodd hdvdK h16
    omega
  have hFcyc : ∀ τ : F₀ ≃+* F₀, (∃ k : ℕ, τ ^ (2 ^ k) = 1) → τ = 1 := by
    rintro τ ⟨k, hk⟩
    by_contra hτ1
    have hdvd : orderOf τ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hj1 : j ≠ 0 := by
      rintro rfl
      apply hτ1
      exact orderOf_eq_one_iff.1 (by simpa using hj)
    have h2 : 2 ∣ orderOf τ := by rw [hj]; exact dvd_pow_self 2 hj1
    have hord0 : orderOf τ ≠ 0 := by rw [hj]; positivity
    have hτ' : orderOf (τ ^ (orderOf τ / 2)) = 2 := orderOf_pow_orderOf_div hord0 h2
    have hpow := fixedField_card_pow (τ ^ (orderOf τ / 2))
    rw [hτ', hF₀card] at hpow
    exact hrsq ⟨Nat.card (fixedField (τ ^ (orderOf τ / 2))), by rw [← hpow]; ring⟩
  have hVC := E.hVC
  let ρ : ↥V →* MulAut (kBar (pumpJ K f)) :=
    (Back.actHom E.hJn).comp (Subgroup.inclusion hVC)
  have hρker : ∀ w : ↥V, ρ w = 1 ↔ (w : G) ∈ secD K f V := by
    intro w
    have h1 : ρ w = Back.actHom E.hJn ⟨(w : G), hVC w.2⟩ := rfl
    rw [h1, ← MonoidHom.mem_ker, Back.actHom_ker E.hJn, Subgroup.mem_subgroupOf, E.hDeq]
    exact ⟨fun h => ⟨w.2, h⟩, fun h => h.2⟩
  have hρE : ∀ v : ↥V, ρ v ∈ innDiagSub e₀ := by
    intro v
    rw [mem_innDiagSub_iff]
    obtain ⟨k, hk⟩ := E.hV2 v
    apply hFcyc
    refine ⟨k, ?_⟩
    rw [← map_pow, ← map_pow, hk, map_one, map_one]
  set P' : Subgroup ↥V := (T ⊓ K).subgroupOf V with hP'
  have hker' : ∀ p ∈ P', ρ p = 1 → p = 1 := by
    intro p hp hρp
    have hpP : (p : G) ∈ T ⊓ K := hp
    have hpD : (p : G) ∈ secD K f V := (hρker p).1 hρp
    have : (p : G) ∈ (T ⊓ K) ⊓ secD K f V := ⟨hpP, hpD⟩
    rw [E.hPD, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hEcard : Nat.card (innDiagSub e₀) = r * (r ^ 2 - 1) := by
    rw [IVK.card_innDiagSub e₀ hF₀, Thm1L34.card_kBar_of_hasL2Model hJmodel]
    obtain ⟨k, rfl⟩ := hrodd
    rw [PumpClass.ordA_one_odd]
    have h2 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
      have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
      omega
    rw [h2]; ring
  have hcard : ∀ j : ℕ, 2 ^ j ∣ Nat.card (innDiagSub e₀) → 2 ^ j ≤ Nat.card ↥P' := by
    intro j hj
    rw [hEcard] at hj
    have h1 := two_pow_le_card_of_dvd E.hPK hrodd hdvdK hj
    have h2 : Nat.card ↥P' = Nat.card ↥(T ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe E.hPV).toEquiv
    rw [h2]
    exact h1
  have himg := image_inf_eq_image E.hV2 ρ (innDiagSub e₀) P' hker' (fun p _ => hρE p) hcard
  intro v hv
  obtain ⟨p, hp, hpv⟩ := himg ⟨v, hv⟩ (hρE ⟨v, hv⟩)
  have hq : ρ (p⁻¹ * ⟨v, hv⟩) = 1 := by rw [map_mul, map_inv, hpv]; group
  have hqD : ((p⁻¹ * ⟨v, hv⟩ : ↥V) : G) ∈ secD K f V := (hρker _).1 hq
  have hpP : (p : G) ∈ T ⊓ K := hp
  refine ⟨(p : G), hpP, ((p⁻¹ * ⟨v, hv⟩ : ↥V) : G), hqD, ?_⟩
  simp

omit [Finite G] in
theorem unique_decomp {P D : Subgroup G} (hPD : P ⊓ D = ⊥) {p p' d d' : G} (hp : p ∈ P)
    (hp' : p' ∈ P) (hd : d ∈ D) (hd' : d' ∈ D) (h : p * d = p' * d') : p = p' ∧ d = d' := by
  have h1 : p'⁻¹ * p = d' * d⁻¹ := by
    calc p'⁻¹ * p = p'⁻¹ * (p * d) * d⁻¹ := by group
      _ = p'⁻¹ * (p' * d') * d⁻¹ := by rw [h]
      _ = d' * d⁻¹ := by group
  have h2 : p'⁻¹ * p ∈ P ⊓ D := ⟨P.mul_mem (P.inv_mem hp') hp, h1 ▸ D.mul_mem hd' (D.inv_mem hd)⟩
  rw [hPD, Subgroup.mem_bot] at h2
  have h3 : p = p' := by
    calc p = p' * (p'⁻¹ * p) := by group
      _ = p' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

theorem Env33.key_d (E : Env33 x y K T V W f z) (hD4 : Nat.card ↥(secD K f V) = 4) {g : G}
    (hgN : g ∈ normalizer (V : Set G))
    (hg : (secD K f V).map (MulAut.conj g).toMonoidHom ≠ secD K f V) : x ∈ zCenter V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hx
  have hZV := E.hZV' hx
  obtain ⟨hgn, hgn'⟩ := normalizer_conj_mem hgN
  have hzf_comm : z * f = f * z := (E.hfP z E.hzP).symm
  have hDeq : secD K f V = zpowers x ⊔ zpowers f := by
    have hle : zpowers x ⊔ zpowers f ≤ secD K f V :=
      sup_le ((zpowers_le).2 E.hxD) ((zpowers_le).2 E.hfD)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hD4, E.hkleinCard])).symm
  have hDcl : ∀ d ∈ secD K f V, d = 1 ∨ d = x ∨ d = f ∨ d = x * f := fun d hd =>
    klein_cases E.hx2 E.hf2' E.cfg.hxf (hDeq ▸ hd)
  have hdd : ∀ d ∈ secD K f V, d * d = 1 := fun d hd =>
    mul_self_eq_one_of_mem_klein E.hx2 E.hf2' E.cfg.hxf (hDeq ▸ hd)
  have hPcD : ∀ p ∈ T ⊓ K, ∀ d ∈ secD K f V, p * d = d * p := by
    intro p hp d hd
    have hpx : p * x = x * p := E.hxcommK p hp.2
    have hpf : p * f = f * p := (E.hfP p hp).symm
    rcases hDcl d hd with h | h | h | h <;> rw [h]
    · simp
    · exact hpx
    · exact hpf
    · calc p * (x * f) = (p * x) * f := by group
        _ = (x * p) * f := by rw [hpx]
        _ = x * (p * f) := by group
        _ = x * (f * p) := by rw [hpf]
        _ = (x * f) * p := by group
  have hgf : g * f * g⁻¹ ≠ f := by
    intro h
    apply hg
    have hgC : g ∈ centralizer ({f} : Set G) := mem_centralizer_singleton_iff.2 (by
      calc g * f = (g * f * g⁻¹) * g := by group
        _ = f * g := by rw [h])
    have hle : (secD K f V).map (MulAut.conj g).toMonoidHom ≤ secD K f V := by
      intro e he
      obtain ⟨d, hd, rfl⟩ := mem_map_conj.1 he
      rw [E.hDeq] at hd ⊢
      exact ⟨hgn d hd.1, P34Real.CMK_conj E.hJn hgC hd.2⟩
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  obtain ⟨hD'V, hD'n, hDD', hcommD⟩ := E.conj_data hZV hgN hgf
  have hfZ : f ∈ zCenter V := ⟨E.cfg.f_mem_V, fun v hv => E.hVf v hv⟩
  have hgfZ : g * f * g⁻¹ ∈ zpowers z ⊔ zpowers f := by
    rw [← hZV]; exact (zCenter_conj hgN).1 f hfZ
  have hgf1 : g * f * g⁻¹ ≠ 1 := by
    intro h
    apply E.hf1
    calc f = g⁻¹ * (g * f * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hfg : g * f * g⁻¹ = z ∨ g * f * g⁻¹ = z * f := by
    rcases klein_cases E.hz2' E.hf2' hzf_comm hgfZ with h | h | h | h
    · exact absurd h hgf1
    · exact Or.inl h
    · exact absurd h hgf
    · exact Or.inr h
  obtain ⟨d₁, hd₁D, hd₁2, hfg'⟩ : ∃ d₁ ∈ secD K f V, d₁ * d₁ = 1 ∧ g * f * g⁻¹ = z * d₁ := by
    rcases hfg with h | h
    · exact ⟨1, (secD K f V).one_mem, by simp, by rw [h]; simp⟩
    · exact ⟨f, E.hfD, E.hf2', h⟩
  have hxg' : g * x * g⁻¹ ∈ (secD K f V).map (MulAut.conj g).toMonoidHom :=
    mem_map_conj.2 ⟨x, E.hxD, rfl⟩
  have hfg'' : g * f * g⁻¹ ∈ (secD K f V).map (MulAut.conj g).toMonoidHom :=
    mem_map_conj.2 ⟨f, E.hfD, rfl⟩
  have hxgV : g * x * g⁻¹ ∈ V := hD'V hxg'
  have hxgx : g * x * g⁻¹ * x = x * (g * x * g⁻¹) := (hcommD x E.hxD _ hxg').symm
  have hxg2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [E.hx2]; group
  have hmemPD : g * x * g⁻¹ ∈ (T ⊓ K) ⊔ secD K f V := by
    rw [hDeq]; exact E.hOmega1S _ hxgV hxgx hxg2
  obtain ⟨p, hp, d, hd, hxgpd⟩ := Thm1P310.exists_mul_of_mem_sup hPcD hmemPD
  have hdd1 := hdd d hd
  have hp2 : p * p = 1 := by
    have h1 : (p * d) * (p * d) = p * p * (d * d) := by
      calc (p * d) * (p * d) = p * (d * p) * d := by group
        _ = p * (p * d) * d := by rw [← hPcD p hp d hd]
        _ = p * p * (d * d) := by group
    rw [← hxgpd, hxg2, hdd1, mul_one] at h1
    exact h1.symm
  have hxg1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply E.hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hxgf : g * x * g⁻¹ ≠ g * f * g⁻¹ := by
    intro h
    apply E.hxf_ne
    have := (MulAut.conj g).injective (show (MulAut.conj g) x = (MulAut.conj g) f from h)
    exact this
  have hp1 : p ≠ 1 := by
    intro h
    apply hxg1
    have hmem : g * x * g⁻¹ ∈ secD K f V ⊓ (secD K f V).map (MulAut.conj g).toMonoidHom := by
      refine ⟨?_, hxg'⟩
      rw [hxgpd, h, one_mul]; exact hd
    rw [hDD', Subgroup.mem_bot] at hmem
    exact hmem
  have hpz : p ≠ z := by
    intro h
    apply hxgf
    have hprod : g * x * g⁻¹ * (g * f * g⁻¹) = d * d₁ := by
      rw [hxgpd, hfg', h]
      have hz : z * d = d * z := hPcD z E.hzP d hd
      calc z * d * (z * d₁) = z * (d * z) * d₁ := by group
        _ = z * (z * d) * d₁ := by rw [hz]
        _ = (z * z) * (d * d₁) := by group
        _ = d * d₁ := by rw [E.hz2', one_mul]
    have hmem : d * d₁ ∈ secD K f V ⊓ (secD K f V).map (MulAut.conj g).toMonoidHom :=
      ⟨(secD K f V).mul_mem hd hd₁D, hprod ▸ ((secD K f V).map (MulAut.conj g).toMonoidHom).mul_mem hxg' hfg''⟩
    rw [hDD', Subgroup.mem_bot] at hmem
    have hdd' : d = d₁ := by
      have h1 : d = d₁⁻¹ := eq_inv_of_mul_eq_one_left hmem
      rw [h1]
      exact inv_eq_of_mul_eq_one_right hd₁2
    rw [hxgpd, hfg', h, hdd']
  have hconj : ∀ c ∈ T ⊓ K, c * p * c⁻¹ = p ∨ c * p * c⁻¹ = p * z := by
    intro c hc
    have hcxg : c * (g * x * g⁻¹) * c⁻¹ ∈ (secD K f V).map (MulAut.conj g).toMonoidHom :=
      hD'n c (E.hPV hc) _ hxg'
    have hcd : c * d * c⁻¹ = d := by
      have := hPcD c hc d hd
      calc c * d * c⁻¹ = (d * c) * c⁻¹ := by rw [this]
        _ = d := by group
    have hcxg_eq : c * (g * x * g⁻¹) * c⁻¹ = (c * p * c⁻¹) * d := by
      rw [hxgpd]
      calc c * (p * d) * c⁻¹ = (c * p * c⁻¹) * (c * d * c⁻¹) := by group
        _ = (c * p * c⁻¹) * d := by rw [hcd]
    obtain ⟨e, he, hec⟩ := mem_map_conj.1 hcxg
    rcases hDcl e he with h | h | h | h
    · exfalso
      have h1 : c * (g * x * g⁻¹) * c⁻¹ = 1 := by rw [← hec, h]; group
      apply hxg1
      calc g * x * g⁻¹ = c⁻¹ * (c * (g * x * g⁻¹) * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    · left
      have hxc : c * (g * x * g⁻¹) * c⁻¹ = g * x * g⁻¹ := by rw [← hec, h]
      have h1 : (c * p * c⁻¹) * d = p * d :=
        calc (c * p * c⁻¹) * d = c * (g * x * g⁻¹) * c⁻¹ := hcxg_eq.symm
          _ = g * x * g⁻¹ := hxc
          _ = p * d := hxgpd
      exact (unique_decomp E.hPD ((T ⊓ K).mul_mem ((T ⊓ K).mul_mem hc hp) ((T ⊓ K).inv_mem hc))
        hp hd hd h1).1
    · exfalso
      have hxc : c * (g * x * g⁻¹) * c⁻¹ = g * f * g⁻¹ := by rw [← hec, h]
      have hZ : g * f * g⁻¹ ∈ zCenter V := (zCenter_conj hgN).1 f hfZ
      have h2 := hZ.2 c (E.hPV hc)
      have h1 : g * x * g⁻¹ = g * f * g⁻¹ := by
        calc g * x * g⁻¹ = c⁻¹ * (c * (g * x * g⁻¹) * c⁻¹) * c := by group
          _ = c⁻¹ * (g * f * g⁻¹) * c := by rw [hxc]
          _ = c⁻¹ * ((g * f * g⁻¹) * c) := by group
          _ = c⁻¹ * (c * (g * f * g⁻¹)) := by rw [← h2]
          _ = g * f * g⁻¹ := by group
      exact hxgf h1
    · right
      have hxc : c * (g * x * g⁻¹) * c⁻¹ = (g * x * g⁻¹) * (g * f * g⁻¹) := by
        rw [← hec, h]; group
      have hz : z * d = d * z := hPcD z E.hzP d hd
      have h1 : (c * p * c⁻¹) * d = (p * z) * (d * d₁) :=
        calc (c * p * c⁻¹) * d = c * (g * x * g⁻¹) * c⁻¹ := hcxg_eq.symm
          _ = (g * x * g⁻¹) * (g * f * g⁻¹) := hxc
          _ = (p * d) * (z * d₁) := by rw [hxgpd, hfg']
          _ = p * (d * z) * d₁ := by group
          _ = p * (z * d) * d₁ := by rw [hz]
          _ = (p * z) * (d * d₁) := by group
      exact (unique_decomp E.hPD ((T ⊓ K).mul_mem ((T ⊓ K).mul_mem hc hp) ((T ⊓ K).inv_mem hc))
        ((T ⊓ K).mul_mem hp E.hzP) hd ((secD K f V).mul_mem hd hd₁D) h1).1
  obtain ⟨n, hn3, hdihn⟩ := E.hdih
  have hn : n = 3 := by
    by_contra hn3'
    have hn4 : 4 ≤ n := by omega
    obtain ⟨c, hcP, hc1, hc2⟩ := exists_conj_not_mem_of_dihedral hn4 hdihn E.hzP E.hz1
      (fun q hq => (E.cfg.z_mem.2.2 q hq.1).symm) hp hp2 hp1 hpz
    have hzp : z * p = p * z := (E.cfg.z_mem.2.2 p hp.1).symm
    rcases hconj c hcP with h | h
    · exact hc1 h
    · exact hc2 (by rw [h, hzp])
  have hP8 : Nat.card ↥(T ⊓ K) = 8 := by
    rw [card_of_isDihedralTwoGroup hdihn, hn]; norm_num
  apply hx
  refine ⟨E.cfg.x_mem_V, fun v hv => ?_⟩
  obtain ⟨p', hp', d', hd', rfl⟩ := E.hV_eq_PD hP8 v hv
  have hp'x : p' * x = x * p' := E.hxcommK p' hp'.2
  have hd'x : d' * x = x * d' := by
    rcases hDcl d' hd' with h | h | h | h <;> rw [h]
    · simp
    · exact E.cfg.hxf.symm
    · calc x * f * x = x * (f * x) := by group
        _ = x * (x * f) := by rw [← E.cfg.hxf]
  calc p' * d' * x = p' * (d' * x) := by group
    _ = p' * (x * d') := by rw [hd'x]
    _ = (p' * x) * d' := by group
    _ = (x * p') * d' := by rw [hp'x]
    _ = x * (p' * d') := by group

theorem Env33.false_of_xf (E : Env33 x y K T V W f z) {b : G} (hbN : b ∈ normalizer (V : Set G))
    (hb2el : ∃ k : ℕ, b ^ (2 ^ k) = 1) (hb2 : b ^ 2 ∈ V) (hbf : b * f * b⁻¹ = x * f) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbn, hbn'⟩ := normalizer_conj_mem hbN
  have hbb : b * b ∈ V := by rw [← sq]; exact hb2
  have hxeq : f * (x * f) = x := by
    calc f * (x * f) = (f * x) * f := by group
      _ = (x * f) * f := by rw [← E.cfg.hxf]
      _ = x * (f * f) := by group
      _ = x := by rw [E.hf2', mul_one]
  have hbx : b * x * b⁻¹ = x := by
    have h1 : b * (x * f) * b⁻¹ = f := by
      calc b * (x * f) * b⁻¹ = (b * b) * f * (b * b)⁻¹ := by rw [← hbf]; group
        _ = (f * (b * b)) * (b * b)⁻¹ := by rw [E.hVf (b * b) hbb]
        _ = f := by group
    calc b * x * b⁻¹ = b * (f * (x * f)) * b⁻¹ := by rw [hxeq]
      _ = (b * f * b⁻¹) * (b * (x * f) * b⁻¹) := by group
      _ = (x * f) * f := by rw [hbf, h1]
      _ = x := by
        calc (x * f) * f = x * (f * f) := by group
          _ = x := by rw [E.hf2', mul_one]
  have hbxc : b * x = x * b := by
    calc b * x = (b * x * b⁻¹) * b := by group
      _ = x * b := by rw [hbx]
  have hbC : b ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hbxc
  set S : Subgroup G := V ⊓ centralizer ({x} : Set G) with hS
  have hSC : S ≤ centralizer ({x} : Set G) := inf_le_right
  have hS2 : IsPGroup 2 ↥S := E.hV2.to_le inf_le_left
  have hbSn : ∀ s ∈ S, b * s * b⁻¹ ∈ S := by
    intro s hs
    refine ⟨hbn s hs.1, mem_centralizer_singleton_iff.2 ?_⟩
    have hsx : s * x = x * s := mem_centralizer_singleton_iff.1 hs.2
    calc b * s * b⁻¹ * x = b * s * (b⁻¹ * x) := by group
      _ = b * s * (x * b⁻¹) := by rw [show b⁻¹ * x = x * b⁻¹ by
            calc b⁻¹ * x = b⁻¹ * (x * b) * b⁻¹ := by group
              _ = b⁻¹ * (b * x) * b⁻¹ := by rw [hbxc]
              _ = x * b⁻¹ := by group]
      _ = b * (s * x) * b⁻¹ := by group
      _ = b * (x * s) * b⁻¹ := by rw [hsx]
      _ = x * (b * s * b⁻¹) := by
        calc b * (x * s) * b⁻¹ = (b * x * b⁻¹) * (b * s * b⁻¹) := by group
          _ = x * (b * s * b⁻¹) := by rw [hbx]
  have hbSN : b ∈ normalizer (S : Set G) := Thm1L3.mem_normalizer_of_conj_le hbSn
  set N : Subgroup G := S ⊔ zpowers b with hN
  have hNC : N ≤ centralizer ({x} : Set G) := sup_le hSC ((zpowers_le).2 hbC)
  have hN2 : IsPGroup 2 ↥N :=
    hS2.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_eq_one hb2el) ((zpowers_le).2 hbSN)
  have hPS : T ⊓ K ≤ S :=
    le_inf E.hPV (fun p hp => mem_centralizer_singleton_iff.2 (E.hxcommK p hp.2))
  have hPN : T ⊓ K ≤ N := hPS.trans le_sup_left
  have hSN : S ≤ N := le_sup_left
  have hbNn : b ∈ N := Subgroup.mem_sup_right (mem_zpowers b)
  have hfN : f ∈ N := hSN E.hS_f
  have hNnV : N ≤ normalizer (V : Set G) :=
    sup_le (inf_le_left.trans Subgroup.le_normalizer) ((zpowers_le).2 hbN)
  have hNP : ∀ n ∈ N, ∀ p ∈ T ⊓ K, n * p * n⁻¹ ∈ T ⊓ K := by
    intro n hn p hp
    rw [← E.hPeq] at hp ⊢
    exact ⟨(normalizer_conj_mem (hNnV hn)).1 p hp.1, E.hKN n (hNC hn) p hp.2⟩
  have hσσ : Back.actHom E.hKN ⟨f, E.hfC⟩ * Back.actHom E.hKN ⟨f, E.hfC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f, E.hfC⟩ : ↥(centralizer ({x} : Set G))) * ⟨f, E.hfC⟩ = 1 := Subtype.ext E.hf2'
    rw [this, map_one]
  have hσ1 : Back.actHom E.hKN ⟨f, E.hfC⟩ ≠ 1 := fun h => E.hfout (h ▸ (innAut _).one_mem)
  have hσ2 : orderOf (Back.actHom E.hKN ⟨f, E.hfC⟩) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  obtain ⟨C, hC, hCc, ω, hω1, hωσ, hω3⟩ := omegaData_of_isFAut hσ2 E.hfFaut
  set σ := Back.actHom E.hKN ⟨f, E.hfC⟩ with hσdef
  have hxker := E.hxker
  have hcommσ : ∀ n (hn : n ∈ N), σ * Back.actHom E.hKN ⟨n, hNC hn⟩ =
      Back.actHom E.hKN ⟨n, hNC hn⟩ * σ := by
    let Λ : Subgroup ↥(centralizer ({x} : Set G)) :=
      (Subgroup.centralizer ({σ} : Set (MulAut (kBar K)))).comap (Back.actHom E.hKN)
    have hle : N ≤ Λ.map (centralizer ({x} : Set G)).subtype := by
      refine sup_le ?_ ?_
      · intro s hs
        refine ⟨⟨s, hSC hs⟩, ?_, rfl⟩
        show Back.actHom E.hKN ⟨s, hSC hs⟩ ∈ Subgroup.centralizer ({σ} : Set (MulAut (kBar K)))
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc Back.actHom E.hKN ⟨s, hSC hs⟩ * σ
            = Back.actHom E.hKN (⟨s, hSC hs⟩ * ⟨f, E.hfC⟩) := (map_mul _ _ _).symm
          _ = Back.actHom E.hKN (⟨f, E.hfC⟩ * ⟨s, hSC hs⟩) := by
            congr 1
            exact Subtype.ext (E.hVf s hs.1)
          _ = σ * Back.actHom E.hKN ⟨s, hSC hs⟩ := map_mul _ _ _
      · rw [zpowers_le]
        refine ⟨⟨b, hbC⟩, ?_, rfl⟩
        show Back.actHom E.hKN ⟨b, hbC⟩ ∈ Subgroup.centralizer ({σ} : Set (MulAut (kBar K)))
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : (⟨b, hbC⟩ : ↥(centralizer ({x} : Set G))) * ⟨f, E.hfC⟩ =
            (⟨x, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({x} : Set G))) *
              ⟨f, E.hfC⟩ * ⟨b, hbC⟩ := by
          apply Subtype.ext
          show b * f = x * f * b
          calc b * f = (b * f * b⁻¹) * b := by group
            _ = x * f * b := by rw [hbf]
        calc Back.actHom E.hKN ⟨b, hbC⟩ * σ
            = Back.actHom E.hKN (⟨b, hbC⟩ * ⟨f, E.hfC⟩) := (map_mul _ _ _).symm
          _ = Back.actHom E.hKN (⟨x, mem_centralizer_singleton_iff.2 rfl⟩ * ⟨f, E.hfC⟩ * ⟨b, hbC⟩) := by
            rw [h1]
          _ = σ * Back.actHom E.hKN ⟨b, hbC⟩ := by
            rw [map_mul, map_mul, hxker, one_mul]
    intro n hn
    obtain ⟨c, hc, hcn⟩ := hle hn
    have hc' : c = ⟨n, hNC hn⟩ := Subtype.ext hcn
    subst hc'
    have h2 : Back.actHom E.hKN ⟨n, hNC hn⟩ ∈
        Subgroup.centralizer ({σ} : Set (MulAut (kBar K))) := hc
    rw [Subgroup.mem_centralizer_singleton_iff] at h2
    exact h2.symm
  have := hCc
  let ωN : ↥N →* C := ω.comp ((Back.actHom E.hKN).comp (Subgroup.inclusion hNC))
  set P' : Subgroup ↥N := (T ⊓ K).subgroupOf N with hP'
  have hP'n : P'.Normal := ⟨fun p hp g => by
    have hp' : (p : G) ∈ T ⊓ K := hp
    exact hNP (g : G) g.2 (p : G) hp'⟩
  have hPker : P' ≤ ωN.ker := by
    intro p hp
    have hpP : (p : G) ∈ T ⊓ K := hp
    show ω (Back.actHom E.hKN ⟨(p : G), hNC p.2⟩) = 1
    rw [Back.actHom_of_mem E.hKN hpP.2 (hNC p.2)]
    exact hω1 _ ⟨_, rfl⟩
  let ωb : (↥N ⧸ P') →* C := QuotientGroup.lift P' ωN hPker
  have hxS : x ∈ S := ⟨E.cfg.x_mem_V, mem_centralizer_singleton_iff.2 rfl⟩
  have hker : ωb.ker ≤ Subgroup.center (↥N ⧸ P') := by
    intro q hq
    obtain ⟨⟨n, hn⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hωn : ωN ⟨n, hn⟩ = 1 := by
      have := MonoidHom.mem_ker.1 hq
      rwa [show ωb (QuotientGroup.mk ⟨n, hn⟩) = ωN ⟨n, hn⟩ from QuotientGroup.lift_mk _ _ _] at this
    have hinn : Back.actHom E.hKN ⟨n, hNC hn⟩ ∈ innAut (kBar K) := hω3 _ (hcommσ n hn) hωn
    have hnP := E.exists_mem_P_of_inn hN2 hNC hPN n hn hinn
    obtain ⟨p, hp, c, hc, hpc⟩ := Thm1P310.exists_mul_of_mem_sup (P := T ⊓ K) (D := zpowers x)
      (fun p hp d hd => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hd
        exact (Commute.zpow_right (show Commute p x from E.hxcommK p hp.2) k).eq) hnP
    have hcN : c ∈ N := hSN (((zpowers_le).2 hxS) hc)
    have hpN : p ∈ N := hPN hp
    have hpcc : p * c = c * p := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      exact (Commute.zpow_right (show Commute p x from E.hxcommK p hp.2) k).eq
    have hmk : (QuotientGroup.mk ⟨n, hn⟩ : ↥N ⧸ P') = QuotientGroup.mk ⟨c, hcN⟩ := by
      rw [QuotientGroup.eq]
      show (⟨n, hn⟩ : ↥N)⁻¹ * ⟨c, hcN⟩ ∈ P'
      have : ((⟨n, hn⟩ : ↥N)⁻¹ * ⟨c, hcN⟩ : ↥N) = ((⟨p, hpN⟩ : ↥N))⁻¹ := by
        apply Subtype.ext
        show n⁻¹ * c = p⁻¹
        calc n⁻¹ * c = (p * c)⁻¹ * c := by rw [hpc]
          _ = (c * p)⁻¹ * c := by rw [hpcc]
          _ = p⁻¹ := by group
      rw [this]
      exact P'.inv_mem hp
    rw [hmk]
    refine Subgroup.mem_center_iff.2 (fun m => ?_)
    obtain ⟨⟨m', hm'⟩, rfl⟩ := QuotientGroup.mk_surjective m
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show m' * c = c * m'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have hm'x : m' * x = x * m' := mem_centralizer_singleton_iff.1 (hNC hm')
    exact (Commute.zpow_right (show Commute m' x from hm'x) k).eq
  have : IsMulCommutative (↥N ⧸ P') :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center ωb hker
  have hcomm : (QuotientGroup.mk ⟨f, hfN⟩ : ↥N ⧸ P') * QuotientGroup.mk ⟨b, hbNn⟩ =
      QuotientGroup.mk ⟨b, hbNn⟩ * QuotientGroup.mk ⟨f, hfN⟩ :=
    (inferInstance : IsMulCommutative (↥N ⧸ P')).is_comm.comm _ _
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
  have hbf' : b * f = x * f * b := by
    calc b * f = (b * f * b⁻¹) * b := by group
      _ = x * f * b := by rw [hbf]
  have hfx : f⁻¹ * x * f = x := by
    calc f⁻¹ * x * f = f⁻¹ * (x * f) := by group
      _ = f⁻¹ * (f * x) := by rw [E.cfg.hxf]
      _ = x := by group
  have hbx' : b⁻¹ * x * b = x := by
    calc b⁻¹ * x * b = b⁻¹ * (x * b) := by group
      _ = b⁻¹ * (b * x) := by rw [← hbxc]
      _ = x := by group
  have hxP : x ∈ T ⊓ K := by
    have h1 : ((⟨f, hfN⟩ * ⟨b, hbNn⟩ : ↥N)⁻¹ * (⟨b, hbNn⟩ * ⟨f, hfN⟩ : ↥N) : ↥N) ∈ P' := hcomm
    have h2 : (f * b)⁻¹ * (b * f) ∈ T ⊓ K := h1
    have h3 : (f * b)⁻¹ * (b * f) = x := by
      calc (f * b)⁻¹ * (b * f) = b⁻¹ * f⁻¹ * (b * f) := by group
        _ = b⁻¹ * f⁻¹ * (x * f * b) := by rw [hbf']
        _ = b⁻¹ * (f⁻¹ * x * f) * b := by group
        _ = b⁻¹ * x * b := by rw [hfx]
        _ = x := hbx'
    rwa [h3] at h2
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  exact E.hx1 (E.hPker x hxP hxC hxker)

theorem Env33.hDeq4 (E : Env33 x y K T V W f z) (hD4 : Nat.card ↥(secD K f V) = 4) :
    secD K f V = zpowers x ⊔ zpowers f := by
  have hle : zpowers x ⊔ zpowers f ≤ secD K f V :=
    sup_le ((zpowers_le).2 E.hxD) ((zpowers_le).2 E.hfD)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hD4, E.hkleinCard])).symm

theorem Env33.hPcD4 (E : Env33 x y K T V W f z) (hD4 : Nat.card ↥(secD K f V) = 4) :
    ∀ p ∈ T ⊓ K, ∀ d ∈ secD K f V, p * d = d * p := by
  intro p hp d hd
  have hpx : p * x = x * p := E.hxcommK p hp.2
  have hpf : p * f = f * p := (E.hfP p hp).symm
  rcases klein_cases E.hx2 E.hf2' E.cfg.hxf (E.hDeq4 hD4 ▸ hd) with h | h | h | h <;> rw [h]
  · simp
  · exact hpx
  · exact hpf
  · calc p * (x * f) = (p * x) * f := by group
      _ = (x * p) * f := by rw [hpx]
      _ = x * (p * f) := by group
      _ = x * (f * p) := by rw [hpf]
      _ = (x * f) * p := by group

theorem Env33.false_of_VW (E : Env33 x y K T V W f z) (hD4 : Nat.card ↥(secD K f V) = 4)
    (hx : x ∉ zCenter V) (hVW : V ≠ W) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b₀, hb₀W, hb₀N, hb₀V⟩ := exists_mem_normalizer_not_mem E.cfg.V_le_W hVW
    E.cfg.sylowW.isPGroup
  have hb₀2 : ∃ k : ℕ, b₀ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.sylowW.isPGroup ⟨b₀, hb₀W⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨b, hb, hbV, hb2⟩ := exists_pow_not_mem_sq_mem hb₀2 hb₀V
  have hbW : b ∈ W := (zpowers_le).2 hb₀W hb
  have hbN : b ∈ normalizer (V : Set G) := (zpowers_le).2 hb₀N hb
  have hb2el : ∃ k : ℕ, b ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.sylowW.isPGroup ⟨b, hbW⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨hbn, hbn'⟩ := normalizer_conj_mem hbN
  by_cases hDb : (secD K f V).map (MulAut.conj b).toMonoidHom ≠ secD K f V
  · exact hx (E.key_d hD4 hbN hDb)
  · push Not at hDb
    have hbf : b * f * b⁻¹ ≠ f := by
      intro h
      apply hbV
      refine mem_of_isSylowOf_of_normalizes E.cfg.sylowV ?_ hbN hb2el
      refine mem_centralizer_singleton_iff.2 ?_
      calc b * f = (b * f * b⁻¹) * b := by group
        _ = f * b := by rw [h]
    have hbfD : b * f * b⁻¹ ∈ secD K f V := by
      rw [← hDb]; exact mem_map_conj.2 ⟨f, E.hfD, rfl⟩
    have hbf1 : b * f * b⁻¹ ≠ 1 := by
      intro h
      apply E.hf1
      calc f = b⁻¹ * (b * f * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group
    rcases klein_cases E.hx2 E.hf2' E.cfg.hxf (E.hDeq4 hD4 ▸ hbfD) with h | h | h | h
    · exact hbf1 h
    · apply hx
      refine ⟨E.cfg.x_mem_V, fun v hv => ?_⟩
      calc v * x = v * (b * f * b⁻¹) := by rw [h]
        _ = b * ((b⁻¹ * v * b) * f) * b⁻¹ := by group
        _ = b * (f * (b⁻¹ * v * b)) * b⁻¹ := by rw [E.hVf _ (hbn' v hv)]
        _ = (b * f * b⁻¹) * v := by group
        _ = x * v := by rw [h]
    · exact hbf h
    · exact E.false_of_xf hbN hb2el hb2 h

end S2

end CFSG.GH74.GLS.C3.Layer1.Thm1G33

