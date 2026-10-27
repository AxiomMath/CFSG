module

public import CFSG.LocalAnalysis.OddStandard.ONanEndStage

public section

namespace CFSG.OddStandard.ONanRec.B2

open Subgroup CFSG.GorensteinWalter

theorem d8_center_iff : ∀ x : DihedralGroup 4,
    (∀ y : DihedralGroup 4, y * x = x * y) ↔ x = 1 ∨ x = DihedralGroup.r 2 := by decide

theorem d8_exists_pair : ∃ u : DihedralGroup 4, u * u = 1 ∧ u ≠ 1 ∧ u ≠ DihedralGroup.r 2 ∧
    u * DihedralGroup.r 2 = DihedralGroup.r 2 * u ∧
    u * DihedralGroup.r 2 * (u * DihedralGroup.r 2) = 1 ∧ u * DihedralGroup.r 2 ≠ 1 ∧
    ¬ (∀ y : DihedralGroup 4, y * u = u * y) :=
  ⟨DihedralGroup.sr 0, by decide⟩

theorem d8_mul_invol : ∀ x : DihedralGroup 4, ∃ a b : DihedralGroup 4,
    a * a = 1 ∧ b * b = 1 ∧ x = a * b := by decide

section General

variable {X : Type} [Group X]

@[expose] def CentD8 (X : Type) [Group X] : Prop :=
  ∀ t : X, orderOf t = 2 → Nonempty (centralizer ({t} : Set X) ≃* DihedralGroup 4)

theorem orderOf_eq_two_iff {x : X} : orderOf x = 2 ↔ x * x = 1 ∧ x ≠ 1 := by
  constructor
  · intro h
    refine ⟨by rw [← pow_two, ← h, pow_orderOf_eq_one], fun h1 => ?_⟩
    rw [h1, orderOf_one] at h
    exact absurd h (by norm_num)
  · rintro ⟨h2, h1⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact h2) h1

theorem card_centralizer_of_centD8 (h : CentD8 X) {t : X} (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set X)) = 8 := by
  obtain ⟨e⟩ := h t ht
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem isPGroup_centralizer_of_centD8 (h : CentD8 X) {t : X} (ht : orderOf t = 2) :
    IsPGroup 2 (centralizer ({t} : Set X)) :=
  IsPGroup.of_card (n := 3) (by rw [card_centralizer_of_centD8 h ht]; norm_num)

theorem eq_of_central_d8 {Q : Subgroup X} (e : Q ≃* DihedralGroup 4) {x y : X} (hx : x ∈ Q)
    (hy : y ∈ Q) (hxc : ∀ q ∈ Q, q * x = x * q) (hyc : ∀ q ∈ Q, q * y = y * q) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : x = y := by
  have hc : ∀ (z : X) (hz : z ∈ Q), (∀ q ∈ Q, q * z = z * q) → z ≠ 1 →
      e ⟨z, hz⟩ = DihedralGroup.r 2 := by
    intro z hz hzc hz1
    have hcen : ∀ w : DihedralGroup 4, w * e ⟨z, hz⟩ = e ⟨z, hz⟩ * w := by
      intro w
      obtain ⟨q, rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hzc q q.2)
    rcases (d8_center_iff _).1 hcen with h1 | h2
    · exfalso
      apply hz1
      have := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
      exact this
    · exact h2
  have h := (hc x hx hxc hx1).trans (hc y hy hyc hy1).symm
  exact congrArg Subtype.val (e.injective h)

theorem sylow_eq_centralizer [Finite X] (h : CentD8 X) (hinv : ∃ t : X, orderOf t = 2) (P : Sylow 2 X) :
    ∃ t ∈ (P : Subgroup X), orderOf t = 2 ∧ (P : Subgroup X) = centralizer ({t} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀⟩ := hinv
  have h2X : 2 ∣ Nat.card X := by rw [← ht₀]; exact orderOf_dvd_natCard t₀
  have hP2 : 2 ∣ Nat.card P := by
    rw [P.card_eq_multiplicity]
    have h1 : 1 ≤ (Nat.card X).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2X
    exact dvd_pow_self 2 (by omega)
  have hnt : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos hP2
    omega
  have hcen : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  have hc2 : 2 ∣ Nat.card (center P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (P.isPGroup'.to_subgroup (center P))
    rw [hn]
    rcases n with _ | n
    · exfalso
      rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
      exact (not_subsingleton_iff_nontrivial.2 hcen) hn.1
    · exact dvd_pow_self 2 (by omega)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hc2
  refine ⟨((c : P) : X), (c : P).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hc
  · have hle : (P : Subgroup X) ≤ centralizer ({((c : P) : X)} : Set X) := by
      intro p hp
      rw [mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.1 c.2 ⟨p, hp⟩
      exact congrArg Subtype.val this
    have hC := isPGroup_centralizer_of_centD8 h (t := ((c : P) : X))
      (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hc)
    exact (P.is_maximal' hC hle).symm

theorem nonempty_sylow_equiv [Finite X] (h : CentD8 X) (hinv : ∃ t : X, orderOf t = 2) (P : Sylow 2 X) :
    Nonempty ((P : Subgroup X) ≃* DihedralGroup 4) := by
  obtain ⟨t, -, ht, hP⟩ := sylow_eq_centralizer h hinv P
  obtain ⟨e⟩ := h t ht
  exact ⟨(MulEquiv.subgroupCongr hP).trans e⟩

theorem card_sylow_of_centD8 [Finite X] (h : CentD8 X) (hinv : ∃ t : X, orderOf t = 2) (P : Sylow 2 X) :
    Nat.card P = 8 := by
  obtain ⟨e⟩ := nonempty_sylow_equiv h hinv P
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem exists_sylow_centralizer [Finite X] (h : CentD8 X) {u : X} (hu : orderOf u = 2) :
    ∃ Q : Sylow 2 X, (Q : Subgroup X) = centralizer ({u} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (isPGroup_centralizer_of_centD8 h hu).exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  rw [card_centralizer_of_centD8 h hu, card_sylow_of_centD8 h ⟨u, hu⟩ Q]

theorem isConj_of_centD8 [Finite X] (h : CentD8 X) {u v : X} (hu : orderOf u = 2) (hv : orderOf v = 2) :
    IsConj u v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_centralizer h hu
  obtain ⟨Q', hQ'⟩ := exists_sylow_centralizer h hv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q Q'
  rw [isConj_iff]
  refine ⟨g, ?_⟩
  obtain ⟨e⟩ := nonempty_sylow_equiv h ⟨u, hu⟩ Q'
  have hgQ : ∀ x : X, x ∈ (Q : Subgroup X) → g * x * g⁻¹ ∈ (Q' : Subgroup X) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  have huQ : u ∈ (Q : Subgroup X) := by rw [hQ]; exact mem_centralizer_singleton_iff.2 rfl
  have hvQ' : v ∈ (Q' : Subgroup X) := by rw [hQ']; exact mem_centralizer_singleton_iff.2 rfl
  refine eq_of_central_d8 e (hgQ u huQ) hvQ' ?_ ?_ ?_ ?_
  · intro q hq
    have hq' : g⁻¹ * q * g ∈ (Q : Subgroup X) := by
      have h1 : g⁻¹ * q * g⁻¹⁻¹ ∈ (Q : Subgroup X) := by
        rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
        simpa [MulAut.smul_def] using hq
      simpa using h1
    have hc := mem_centralizer_singleton_iff.1 (hQ ▸ hq')
    calc q * (g * u * g⁻¹) = g * (g⁻¹ * q * g * u) * g⁻¹ := by group
      _ = g * (u * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
      _ = g * u * g⁻¹ * q := by group
  · intro q hq
    exact mem_centralizer_singleton_iff.1 (hQ' ▸ hq)
  · intro h1
    have : u = 1 := by
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · intro h1
    rw [h1, orderOf_one] at hv
    exact absurd hv (by norm_num)

theorem exists_pair (h : CentD8 X) {t : X} (ht : orderOf t = 2) :
    ∃ u : X, u ∈ centralizer ({t} : Set X) ∧ orderOf u = 2 ∧ orderOf (u * t) = 2 ∧
      u * t = t * u ∧ u ≠ t ∧ ∃ q ∈ centralizer ({t} : Set X), q * u ≠ u * q := by
  obtain ⟨e⟩ := h t ht
  have htC : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.2 rfl
  have het : e ⟨t, htC⟩ = DihedralGroup.r 2 := by
    have hcen : ∀ w : DihedralGroup 4, w * e ⟨t, htC⟩ = e ⟨t, htC⟩ * w := by
      intro w
      obtain ⟨q, rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 q.2)
    rcases (d8_center_iff _).1 hcen with h1 | h2
    · exfalso
      have := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
      rw [orderOf_eq_two_iff] at ht
      exact ht.2 this
    · exact h2
  obtain ⟨u₀, h1, h2, h3, h4, h5, h6, h7⟩ := d8_exists_pair
  set u := e.symm u₀ with hu
  have hu1 : (u : X) * u = 1 := by
    have := congrArg (fun w => ((e.symm w : centralizer ({t} : Set X)) : X)) h1
    simpa [hu] using this
  have hut : e (⟨t, htC⟩ : centralizer ({t} : Set X)) = DihedralGroup.r 2 := het
  refine ⟨u, u.2, orderOf_eq_two_iff.2 ⟨hu1, ?_⟩, orderOf_eq_two_iff.2 ⟨?_, ?_⟩,
    (mem_centralizer_singleton_iff.1 u.2), ?_, ?_⟩
  · intro h0
    apply h2
    have : u = 1 := Subtype.ext h0
    rw [hu, MulEquiv.symm_apply_eq, map_one] at this
    exact this
  · have := congrArg (fun w => ((e.symm w : centralizer ({t} : Set X)) : X)) h5
    simp only [map_mul, map_one, OneMemClass.coe_one, Subgroup.coe_mul] at this
    rw [← hut, MulEquiv.symm_apply_apply] at this
    exact this
  · intro h0
    apply h6
    have h0' : (u * ⟨t, htC⟩ : centralizer ({t} : Set X)) = 1 := Subtype.ext h0
    have := congrArg e h0'
    rwa [map_mul, hu, MulEquiv.apply_symm_apply, hut, map_one] at this
  · intro h0
    apply h3
    have h0' : u = ⟨t, htC⟩ := Subtype.ext h0
    rw [← hut, ← h0', hu, MulEquiv.apply_symm_apply]
  · by_contra hall
    push Not at hall
    apply h7
    intro w
    obtain ⟨q, rfl⟩ := e.surjective w
    have hq : q * e.symm u₀ = e.symm u₀ * q := Subtype.ext (hall q q.2)
    have := congrArg e hq
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

theorem pPrimeCore_eq_bot_of_centD8 [Finite X] (h : CentD8 X) (hinv : ∃ t : X, orderOf t = 2) :
    pPrimeCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pPrimeCore 2 X
  have hN : N.Normal := pPrimeCore_normal
  have hcop : Nat.Coprime 2 (Nat.card N) := pPrimeCore_coprime_card
  have hinvN : ∀ w : X, orderOf w = 2 → ∀ n ∈ N, w * n * w⁻¹ = n⁻¹ := by
    intro w hw n hn
    let φ : N →* N := (MulAut.conjNormal w).toMonoidHom
    have hφ : ∀ m : N, ((φ m : N) : X) = w * m * w⁻¹ := fun m => by
      simp [φ, MulAut.conjNormal_apply]
    have hfp : MonoidHom.FixedPointFree φ := by
      intro m hm
      have hmC : (m : X) ∈ centralizer ({w} : Set X) := by
        rw [mem_centralizer_singleton_iff]
        have := congrArg Subtype.val hm
        rw [hφ] at this
        calc (m : X) * w = w * m * w⁻¹ * w := by rw [this]
          _ = w * m := by group
      have h8 : orderOf (m : X) ∣ 8 := by
        rw [← card_centralizer_of_centD8 h hw, ← Subgroup.orderOf_mk (m : X) hmC]
        exact orderOf_dvd_natCard _
      have hodd : orderOf m ∣ Nat.card N := orderOf_dvd_natCard m
      rw [← Subgroup.orderOf_coe] at hodd
      have h1 : orderOf (m : X) = 1 := by
        have hc8 : Nat.Coprime 8 (Nat.card N) := Nat.Coprime.pow_left 3 hcop
        exact Nat.eq_one_of_dvd_coprimes hc8 h8 hodd
      exact Subtype.ext (orderOf_eq_one_iff.1 h1)
    have hinvol : Function.Involutive φ := by
      intro m
      apply Subtype.ext
      rw [hφ, hφ]
      have hw2 : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
      calc w * (w * m * w⁻¹) * w⁻¹ = (w * w) * m * (w * w)⁻¹ := by group
        _ = m := by rw [hw2]; group
    have := congrFun (hfp.coe_eq_inv_of_involutive hinvol) ⟨n, hn⟩
    have h2 := congrArg Subtype.val this
    rw [hφ] at h2
    exact h2
  obtain ⟨t, ht⟩ := hinv
  obtain ⟨u, -, hu, hut, hc, -, -⟩ := exists_pair h ht
  rw [eq_bot_iff]
  intro n hn
  have h1 := hinvN t ht n hn
  have h2 := hinvN u hu n hn
  have h3 := hinvN (u * t) hut n hn
  have hnn : n⁻¹ = n := by
    rw [← h3]
    calc u * t * n * (u * t)⁻¹ = u * (t * n * t⁻¹) * u⁻¹ := by group
      _ = u * n⁻¹ * u⁻¹ := by rw [h1]
      _ = (u * n * u⁻¹)⁻¹ := by group
      _ = n := by rw [h2, inv_inv]
  have hn2 : n * n = 1 := by
    calc n * n = n * n⁻¹ := by rw [hnn]
      _ = 1 := mul_inv_cancel n
  have hord : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hn2)
  have hodd : orderOf n ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk n hn]
    exact orderOf_dvd_natCard _
  have h1' : orderOf n = 1 := Nat.eq_one_of_dvd_coprimes hcop hord hodd
  rw [mem_bot]
  exact orderOf_eq_one_iff.1 h1'

theorem eq_top_of_odd_index [Finite X] (h : CentD8 X) (hinv : ∃ t : X, orderOf t = 2)
    (L : Subgroup X) [hL : L.Normal] (hodd : Odd L.index) : L = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨t, htP, ht, hP⟩ := sylow_eq_centralizer h hinv P
  have hPL : (P : Subgroup X) ≤ L := by
    intro p hp
    have h1 : orderOf (QuotientGroup.mk p : X ⧸ L) ∣ L.index := by
      rw [Subgroup.index]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (QuotientGroup.mk p : X ⧸ L) ∣ orderOf p :=
      orderOf_map_dvd (QuotientGroup.mk' L) p
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    have h3 : orderOf p ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk p hp]
      exact orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime (2 ^ k) L.index :=
      Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.2 (by
        rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hodd))
    have h4 : orderOf (QuotientGroup.mk p : X ⧸ L) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (h2.trans h3) h1
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
    exact h4
  have hF := Sylow.normalizer_sup_eq_top' P hPL
  obtain ⟨e⟩ := nonempty_sylow_equiv h hinv P
  have hN : normalizer ((P : Subgroup X) : Set X) ≤ L := by
    intro g hg
    have hgt : g * t * g⁻¹ ∈ (P : Subgroup X) := (mem_normalizer_iff.1 hg t).1 htP
    have hcen : ∀ q ∈ (P : Subgroup X), q * (g * t * g⁻¹) = g * t * g⁻¹ * q := by
      intro q hq
      have hq' : g⁻¹ * q * g ∈ (P : Subgroup X) := by
        have := (mem_normalizer_iff.1 (inv_mem hg) q).1 hq
        simpa using this
      have hc := mem_centralizer_singleton_iff.1 (hP ▸ hq')
      calc q * (g * t * g⁻¹) = g * (g⁻¹ * q * g * t) * g⁻¹ := by group
        _ = g * (t * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
        _ = g * t * g⁻¹ * q := by group
    have htc : ∀ q ∈ (P : Subgroup X), q * t = t * q := fun q hq =>
      mem_centralizer_singleton_iff.1 (hP ▸ hq)
    have ht1 : t ≠ 1 := (orderOf_eq_two_iff.1 ht).2
    have heq := eq_of_central_d8 e hgt htP hcen htc (fun h0 => ht1 (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group)) ht1
    have hgC : g ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [heq]
    exact hPL (hP ▸ hgC)
  rw [eq_top_iff, ← hF]
  exact sup_le hN le_rfl

theorem index_ne_two [Finite X] (h : CentD8 X) (hinv : ∃ t : X, orderOf t = 2)
    (H : Subgroup X) [hH : H.Normal] : H.index ≠ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  obtain ⟨t, ht⟩ := hinv
  obtain ⟨u, -, hu, hut, -, -, -⟩ := exists_pair h ht
  have hconj : ∀ w : X, orderOf w = 2 → (w ∈ H ↔ t ∈ H) := by
    intro w hw
    obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_of_centD8 h ht hw)
    constructor
    · intro hm
      have := hH.conj_mem _ hm c⁻¹
      simpa [mul_assoc] using this
    · intro hm
      exact hH.conj_mem t hm c
  by_cases htH : t ∈ H
  · obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
    obtain ⟨e⟩ := nonempty_sylow_equiv h ⟨t, ht⟩ P
    have hPH : (P : Subgroup X) ≤ H := by
      intro p hp
      obtain ⟨a, b, ha, hb, hab⟩ := d8_mul_invol (e ⟨p, hp⟩)
      have hmem : ∀ c : DihedralGroup 4, c * c = 1 → ((e.symm c : P) : X) ∈ H := by
        intro c hc
        by_cases hc1 : c = 1
        · rw [hc1, map_one]
          exact one_mem H
        · have hc2 : orderOf ((e.symm c : P) : X) = 2 := by
            rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_eq_two_iff]
            exact ⟨hc, hc1⟩
          exact (hconj _ hc2).2 htH
      have hp' : (⟨p, hp⟩ : P) = e.symm a * e.symm b := by
        rw [← map_mul, ← hab, MulEquiv.symm_apply_apply]
      have : p = ((e.symm a : P) : X) * ((e.symm b : P) : X) := by
        have := congrArg Subtype.val hp'
        simpa using this
      rw [this]
      exact mul_mem (hmem a ha) (hmem b hb)
    have hdvd : Nat.card P ∣ Nat.card H := Subgroup.card_dvd_of_le hPH
    have hcard : Nat.card H * 2 = Nat.card X := by
      rw [← h2]
      exact H.card_mul_index
    rw [P.card_eq_multiplicity] at hdvd
    have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
    have h3 : 2 ^ ((Nat.card X).factorization 2) * 2 ∣ Nat.card X := by
      have := Nat.mul_dvd_mul_right hdvd 2
      rwa [hcard] at this
    rw [← pow_succ] at h3
    have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hX0).1 h3
    omega
  · have hu' : u ∉ H := fun hm => htH ((hconj u hu).1 hm)
    have hmem := (Subgroup.mul_mem_iff_of_index_two h2).2 (iff_of_false hu' htH)
    exact htH ((hconj _ hut).1 hmem)

theorem commutator_eq_top_of_centD8 [Finite X] (h : CentD8 X) (hinv : ∃ t : X, orderOf t = 2) :
    commutator X = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := hinv
  set C := commutator X with hCdef
  have hCn : C.Normal := inferInstance
  set H := C ⊔ zpowers t with hHdef
  have hHn : H.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hc : g * x * g⁻¹ * x⁻¹ ∈ C := by
      rw [hCdef, _root_.commutator_def]
      have := commutator_mem_commutator (mem_top g) (mem_top x)
      rwa [commutatorElement_def] at this
    have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact mul_mem (mem_sup_left hc) hx
  have hHtop : H = ⊤ := by
    apply eq_top_of_odd_index h ⟨t, ht⟩ H
    obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
    obtain ⟨e⟩ := nonempty_sylow_equiv h ⟨t, ht⟩ P
    have htH : t ∈ H := mem_sup_right (mem_zpowers t)
    have hinvH : ∀ w : X, orderOf w = 2 → w ∈ H := by
      intro w hw
      obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_of_centD8 h ht hw)
      exact hHn.conj_mem t htH c
    have hPH : (P : Subgroup X) ≤ H := by
      intro p hp
      obtain ⟨a, b, ha, hb, hab⟩ := d8_mul_invol (e ⟨p, hp⟩)
      have hmem : ∀ c : DihedralGroup 4, c * c = 1 → ((e.symm c : P) : X) ∈ H := by
        intro c hc
        by_cases hc1 : c = 1
        · rw [hc1, map_one]
          exact one_mem H
        · apply hinvH
          rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_eq_two_iff]
          exact ⟨hc, hc1⟩
      have hp' : (⟨p, hp⟩ : P) = e.symm a * e.symm b := by
        rw [← map_mul, ← hab, MulEquiv.symm_apply_apply]
      have : p = ((e.symm a : P) : X) * ((e.symm b : P) : X) := by
        have := congrArg Subtype.val hp'
        simpa using this
      rw [this]
      exact mul_mem (hmem a ha) (hmem b hb)
    have hdvd : Nat.card P ∣ Nat.card H := Subgroup.card_dvd_of_le hPH
    rw [P.card_eq_multiplicity] at hdvd
    have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
    rw [Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ H.index := by omega
    obtain ⟨k, hk⟩ := h2'
    have h3 : 2 ^ ((Nat.card X).factorization 2) * 2 ∣ Nat.card X := by
      have h5 : Nat.card H * 2 ∣ Nat.card X :=
        ⟨k, by rw [← H.card_mul_index, hk]; ring⟩
      exact (Nat.mul_dvd_mul_right hdvd 2).trans h5
    rw [← pow_succ] at h3
    have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hX0).1 h3
    omega
  have hidx : C.index ∣ 2 := by
    have htop : zpowers (QuotientGroup.mk t : X ⧸ C) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      have hle : H ≤ (zpowers (QuotientGroup.mk t : X ⧸ C)).comap (QuotientGroup.mk' C) := by
        rw [hHdef, sup_le_iff]
        constructor
        · intro c hc
          rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff c).2 hc]
          exact one_mem _
        · rw [zpowers_le, mem_comap]
          exact mem_zpowers _
      exact hle (hHtop ▸ mem_top x)
    have hc : C.index = orderOf (QuotientGroup.mk t : X ⧸ C) := by
      rw [Subgroup.index, ← Subgroup.card_top (G := X ⧸ C), ← htop, Nat.card_zpowers]
    rw [hc, ← ht]
    exact orderOf_map_dvd (QuotientGroup.mk' C) t
  have hne2 := index_ne_two h ⟨t, ht⟩ C
  have h1 : C.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h1
    · exact h1
    · exact absurd h1 hne2
  exact Subgroup.index_eq_one.1 h1

end General

section GW


theorem exists_psl2_of_centD8 {X : Type} [Group X] [Finite X] (h : CentD8 X)
    (hinv : ∃ t : X, orderOf t = 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (Nat.card K = 7 ∨ Nat.card K = 9) ∧
      Nonempty (X ≃* PSL2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdih : HasDihedralSylowTwo X := fun S => ⟨2, by norm_num, nonempty_sylow_equiv h hinv S⟩
  have hbot := pPrimeCore_eq_bot_of_centD8 h hinv
  let ι : X ⧸ pPrimeCore 2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  obtain ⟨t, ht⟩ := hinv
  rcases gorensteinWalter X hdih with ⟨-, h2⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, K, hK, L, hLn, hLodd, hLm⟩
  ·
    exfalso
    have hX : IsPGroup 2 X := h2.of_equiv ι
    obtain ⟨u, -, hu, -, -, -, q, -, hqu⟩ := exists_pair h ht
    have hCu : centralizer ({u} : Set X) = ⊤ := by
      obtain ⟨Q, hQ⟩ := exists_sylow_centralizer h hu
      have := Q.is_maximal' (hX.to_subgroup ⊤) le_top
      rw [← hQ, ← this]
    exact hqu (mem_centralizer_singleton_iff.1 (hCu ▸ mem_top q))
  ·
    exfalso
    let φ : X ≃* alternatingGroup (Fin 7) := ι.symm.trans e
    have ht7 : orderOf (φ.symm a7t) = 2 := by
      rw [MulEquiv.orderOf_eq, orderOf_eq_two_iff]
      have := a7t_involution
      exact ⟨by rw [← pow_two]; exact this.2, this.1⟩
    have h1 := card_centralizer_of_centD8 h ht7
    rw [card_centralizer_equiv φ, MulEquiv.apply_symm_apply, a7t_centralizer_card] at h1
    norm_num at h1
  ·
    have hLtop : L = ⊤ := by
      let L' := L.comap ι.symm.toMonoidHom
      have : L'.Normal := hLn.comap _
      have hL'odd : Odd L'.index := by
        rw [Subgroup.index_comap_of_surjective _ ι.symm.surjective]
        exact hLodd
      have hL' := eq_top_of_odd_index h ⟨t, ht⟩ L' hL'odd
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := ι.symm.surjective y
      have hx : x ∈ L' := hL' ▸ mem_top x
      exact hx
    let eL : X ≃* L :=
      ι.symm.trans (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm))
    rcases hLm with he | he
    ·
      obtain ⟨e⟩ := he
      refine ⟨K, inferInstance, inferInstance, ?_, ⟨eL.trans e⟩⟩
      set f := eL.trans e
      have hqodd : Odd (Nat.card K) := by
        obtain ⟨p, n, -, hpodd, -, hqp⟩ := hK
        rw [hqp]
        exact hpodd.pow
      have hs : orderOf (f t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
      have hcs : Nat.card (centralizer ({f t} : Set (PSL2 K))) = 8 := by
        rw [← card_centralizer_equiv f t]
        exact card_centralizer_of_centD8 h ht
      have h4 : Nat.card K % 4 = 1 ∨ Nat.card K % 4 = 3 := by
        obtain ⟨k, hk⟩ := hqodd
        omega
      rcases h4 with h1 | h3
      · obtain ⟨m, hm, ⟨e'⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hK
          (ε := 1) (by show (Nat.card K : ℤ) % 4 = 1 % 4; omega) (Or.inl rfl) hs
        have h2m : 2 * m = 8 := by
          rw [← DihedralGroup.nat_card, ← Nat.card_congr e'.toEquiv, hcs]
        right
        omega
      · obtain ⟨m, hm, ⟨e'⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hK
          (ε := -1) (by show (Nat.card K : ℤ) % 4 = -1 % 4; omega) (Or.inr rfl) hs
        have h2m : 2 * m = 8 := by
          rw [← DihedralGroup.nat_card, ← Nat.card_congr e'.toEquiv, hcs]
        left
        omega
    ·
      exfalso
      obtain ⟨e⟩ := he
      exact (commutator_ne_bot_ne_top_of_mulEquiv_pgl2_odd K hK (eL.trans e)).2
        (commutator_eq_top_of_centD8 h ⟨t, ht⟩)

end GW

end CFSG.OddStandard.ONanRec.B2
