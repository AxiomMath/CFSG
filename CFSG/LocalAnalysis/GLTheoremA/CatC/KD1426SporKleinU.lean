module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426SporKlein

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426SporKlein

variable {G : Type} [Group G]

theorem card_sup_zpowers [Finite G] {x y : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hyx : y ≠ x) (hyx2 : y ≠ x ^ 2) (hxy : x * y = y * x) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyNx : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    refine Subgroup.zpowers_le.2 ?_
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rw [((Commute.symm hxy).zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers x k
    · intro hg
      have hcm : Commute y⁻¹ x := (Commute.inv_left (Commute.symm hxy))
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
      have e : g = y⁻¹ * x ^ k * y := by rw [hk]; group
      rw [e, (hcm.zpow_right k).eq, inv_mul_cancel_right]
      exact Subgroup.zpow_mem_zpowers x k
  have hprod := card_sup_mul_card_inf_of_le_normalizer hyNx
  have hcx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hcy : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have hinf : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) = 1 := by
    have hd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ∣ 3 := by
      rw [← hcy]; exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
    · exact h1
    · exfalso
      have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hcy])
      have hy' : y ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y := by
        rw [heq]; exact Subgroup.mem_zpowers y
      rcases mem_zpowers_of_pow_three hx3 (Subgroup.mem_inf.1 hy').1 with h' | h' | h'
      · exact hy1 h'
      · exact hyx h'
      · exact hyx2 h'
  rw [hinf, mul_one, hcx, hcy] at hprod
  exact hprod

theorem eq_sup_zpowers [Finite G] {D : Subgroup G} (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 9)
    {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers y = D := by
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hxy : x * y = y * x := congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc := card_sup_zpowers (hD.2 x hx) hx1 (hD.2 y hy) hy1
    (fun h => hyx (h ▸ Subgroup.mem_zpowers x))
    (fun h => hyx (h ▸ Subgroup.npow_mem_zpowers x 2)) hxy
  exact Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.2 hx) (Subgroup.zpowers_le.2 hy))
    (by rw [hc, hDc])

theorem exists_not_mem_zpowers [Finite G] {D : Subgroup G} (hD : IsElemAbelian 3 D)
    (hDc : Nat.card D = 9) {x : G} (hx : x ∈ D) : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
  by_contra h
  push Not at h
  have hle : D ≤ Subgroup.zpowers x := fun y hy => h y hy
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hDc] at h1
  have h2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hD.2 x hx)
  have h3 := Nat.le_of_dvd (by norm_num) h2
  omega

theorem exists_ne_one_mem [Finite G] {D : Subgroup G} (hDc : Nat.card D = 9) :
    ∃ x ∈ D, x ≠ 1 := by
  by_contra h
  push Not at h
  have hbot : D = ⊥ := eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx)
  rw [hbot, Subgroup.card_bot] at hDc
  omega

theorem klein_of_U [Finite G] (D : Subgroup G) (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 9)
    (U : Subgroup G) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hDU : ∀ d ∈ D, ∀ u ∈ U, d * u * d⁻¹ ∈ U)
    (hinv : ∀ t : G, t ≠ 1 → t ^ 2 = 1 → ¬ ∀ d ∈ D, d * t = t * d) :
    ∃ T0 : Subgroup G, IsElemAbelian 2 T0 ∧ Nat.card T0 = 4 ∧
      (∀ d ∈ D, ∀ t ∈ T0, d * t * d⁻¹ ∈ T0) ∧
      (∀ t ∈ T0, ∃ d ∈ D, ∃ s ∈ T0, d * s * d⁻¹ * s⁻¹ = t) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Zg : Subgroup G := (Subgroup.center ↥U).map U.subtype with hZg
  have memZ : ∀ z, z ∈ Zg ↔ z ∈ U ∧ ∀ u ∈ U, z * u = u * z := by
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, fun u hu => ?_⟩
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨u, hu⟩)).symm
    · rintro ⟨hzU, hz⟩
      exact ⟨⟨z, hzU⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hz g g.2).symm, rfl⟩
  have hZU : ∀ z ∈ Zg, z ∈ U := fun z hz => ((memZ z).1 hz).1
  have hZc : ∀ z ∈ Zg, ∀ z' ∈ Zg, z * z' = z' * z := fun z hz z' hz' =>
    ((memZ z).1 hz).2 z' (hZU z' hz')
  have hZD : ∀ d ∈ D, ∀ z ∈ Zg, d * z * d⁻¹ ∈ Zg := by
    intro d hd z hz
    obtain ⟨hzU, hzc⟩ := (memZ z).1 hz
    refine (memZ _).2 ⟨hDU d hd z hzU, fun u hu => ?_⟩
    have hu' : d⁻¹ * u * d ∈ U := by simpa using hDU d⁻¹ (D.inv_mem hd) u hu
    have := hzc _ hu'
    calc d * z * d⁻¹ * u = d * (z * (d⁻¹ * u * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * u * d) * z) * d⁻¹ := by rw [this]
      _ = u * (d * z * d⁻¹) := by group
  have hconj2 : ∀ (g z : G), z ^ 2 = 1 → (g * z * g⁻¹) ^ 2 = 1 := by
    intro g z hz
    rw [sq, show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, ← sq, hz]
    group
  haveI : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).2 hU
  haveI : Nontrivial ↥(Subgroup.center ↥U) := hU2.center_nontrivial
  obtain ⟨m, hm⟩ := (hU2.to_subgroup (Subgroup.center ↥U)).exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := ↥(Subgroup.center ↥U))
    rw [hm, pow_zero] at this
    exact lt_irrefl _ this
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥U)) 2
    (by rw [hm]; exact dvd_pow_self 2 hm0)
  set v : G := ((c : ↥U) : G) with hvdef
  have hvZ : v ∈ Zg := ⟨c, c.2, rfl⟩
  have hvo : orderOf v = 2 := by rw [hvdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hc
  have hv2 : v ^ 2 = 1 := by rw [← hvo]; exact pow_orderOf_eq_one v
  have hv1 : v ≠ 1 := by
    intro h; rw [h, orderOf_one] at hvo; omega
  letI cD : CommGroup ↥D :=
    { (inferInstance : Group ↥D) with mul_comm := fun x y => hD.1.is_comm.comm x y }
  letI cZ : CommGroup ↥Zg :=
    { (inferInstance : Group ↥Zg) with mul_comm := fun x y => Subtype.ext (hZc x x.2 y y.2) }
  have hD3 : ∀ d : ↥D, d ^ 3 = 1 := fun d => Subtype.ext (by simpa using hD.2 d d.2)
  let conjZ : ↥D → ↥Zg →* ↥Zg := fun d =>
    { toFun := fun z => ⟨(d : G) * z * (d : G)⁻¹, hZD d d.2 z z.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp only [Subgroup.coe_mul]; group }
  have conjZ_apply : ∀ (d : ↥D) (z : ↥Zg), ((conjZ d z : ↥Zg) : G) = (d : G) * z * (d : G)⁻¹ :=
    fun _ _ => rfl
  let E : ↥D → ↥Zg := fun d => ⟨(d : G) * v * (d : G)⁻¹, hZD d d.2 v hvZ⟩
  have E_apply : ∀ d : ↥D, ((E d : ↥Zg) : G) = (d : G) * v * (d : G)⁻¹ := fun _ => rfl
  have conjZ_E : ∀ d e : ↥D, conjZ d (E e) = E (d * e) := by
    intro d e; ext; rw [conjZ_apply, E_apply, E_apply, Subgroup.coe_mul]; group
  have E_sq : ∀ d : ↥D, E d ^ 2 = 1 := fun d => Subtype.ext (by
    rw [Subgroup.coe_pow, E_apply, Subgroup.coe_one]; exact hconj2 _ v hv2)
  have E_one : ((E 1 : ↥Zg) : G) = v := by rw [E_apply]; simp
  let Nm : ↥D → ↥Zg := fun h => E 1 * E h * E (h * h)
  have Nm_sq : ∀ h : ↥D, Nm h ^ 2 = 1 := by
    intro h; simp only [Nm, mul_pow, E_sq, mul_one]
  have Nm_fixed : ∀ h : ↥D, conjZ h (Nm h) = Nm h := by
    intro h
    simp only [Nm, map_mul, conjZ_E, mul_one]
    have e3 : h * (h * h) = 1 := by rw [← hD3 h, pow_three]
    rw [e3]
    ac_rfl
  have hfix : ∃ h : ↥D, h ≠ 1 ∧ ∃ w : ↥Zg, w ≠ 1 ∧ w ^ 2 = 1 ∧ conjZ h w = w := by
    obtain ⟨a, haD, ha1⟩ := exists_ne_one_mem hDc
    obtain ⟨b, hbD, hba⟩ := exists_not_mem_zpowers hD hDc haD
    set a' : ↥D := ⟨a, haD⟩
    set b' : ↥D := ⟨b, hbD⟩
    have hb1 : b' ≠ 1 := fun h => hba (by
      have : b = 1 := congrArg Subtype.val h
      rw [this]; exact Subgroup.one_mem _)
    have ha1' : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    have hab1 : a' * b' ≠ 1 := fun h => hba (by
      have h' : b = a⁻¹ := by
        have := congrArg Subtype.val h
        simp only [Subgroup.coe_mul, Subgroup.coe_one] at this
        exact eq_inv_of_mul_eq_one_right this
      rw [h']; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
    have habb1 : a' * b' * b' ≠ 1 := fun h => hba (by
      have hb3 := hD3 b'
      have h' : a' = b' := by
        calc a' = a' * b' * b' * b' := by rw [mul_assoc, mul_assoc, ← pow_three, hb3, mul_one]
          _ = b' := by rw [h, one_mul]
      have : a = b := congrArg Subtype.val h'
      rw [← this]; exact Subgroup.mem_zpowers a)
    by_cases hna : Nm a' = 1
    ·
      have X1 : conjZ b' (Nm a') = 1 := by rw [hna, map_one]
      have X2 : conjZ (b' * b') (Nm a') = 1 := by rw [hna, map_one]
      simp only [Nm, map_mul, conjZ_E] at X1 X2
      have hb3 := hD3 b'
      have r1 : (a' * b') * (a' * b') = a' * a' * (b' * b') := by ac_rfl
      have r2 : (a' * b' * b') * (a' * b' * b') = a' * a' * b' := by
        calc (a' * b' * b') * (a' * b' * b') = a' * a' * b' * (b' * b' * b') := by ac_rfl
          _ = a' * a' * b' := by rw [← pow_three', hb3, mul_one]
      have r3 : b' * a' = a' * b' := mul_comm _ _
      have r4 : b' * (a' * a') = a' * a' * b' := mul_comm _ _
      have r5 : b' * b' * a' = a' * (b' * b') := mul_comm _ _
      have r6 : b' * b' * (a' * a') = a' * a' * (b' * b') := mul_comm _ _
      have r7 : b' * b' * 1 = b' * b' := mul_one _
      have r8 : b' * 1 = b' := mul_one _
      rw [r3, r4, r8] at X1
      rw [r5, r6, r7] at X2
      have key : Nm b' * Nm (a' * b') * Nm (a' * b' * b') = E 1 * E 1 * E 1 *
          ((E b' * E (a' * b') * E (a' * a' * b')) *
            (E (b' * b') * E (a' * (b' * b')) * E (a' * a' * (b' * b')))) := by
        simp only [Nm, r1, r2]
        have : a' * (b' * b') = a' * b' * b' := (mul_assoc _ _ _).symm
        rw [this]
        ac_rfl
      rw [X1, X2, mul_one, mul_one] at key
      have hE1 : E 1 * E 1 * E 1 = E 1 := by
        rw [mul_assoc, ← sq, E_sq, mul_one]
      rw [hE1] at key
      by_contra hcon
      push Not at hcon
      have z1 : Nm b' = 1 := by
        by_contra hne; exact hcon b' hb1 _ hne (Nm_sq b') (Nm_fixed b')
      have z2 : Nm (a' * b') = 1 := by
        by_contra hne; exact hcon _ hab1 _ hne (Nm_sq _) (Nm_fixed _)
      have z3 : Nm (a' * b' * b') = 1 := by
        by_contra hne; exact hcon _ habb1 _ hne (Nm_sq _) (Nm_fixed _)
      rw [z1, z2, z3, mul_one, mul_one] at key
      apply hv1
      rw [← E_one, ← key]
      rfl
    · exact ⟨a', ha1', Nm a', hna, Nm_sq a', Nm_fixed a'⟩
  obtain ⟨h, hh1, w, hw1, hw2, hhw⟩ := hfix
  obtain ⟨k, hkD, hkh⟩ := exists_not_mem_zpowers hD hDc h.2
  set k' : ↥D := ⟨k, hkD⟩
  have hDeq : Subgroup.zpowers (h : G) ⊔ Subgroup.zpowers k = D :=
    eq_sup_zpowers hD hDc h.2 hkD (fun e => hh1 (Subtype.ext e)) hkh
  have hhk : (h : G) * k = k * h := congrArg Subtype.val (mul_comm h k')
  have hhw' : (h : G) * w = w * h := by
    have := congrArg Subtype.val hhw
    rw [conjZ_apply] at this
    calc (h : G) * w = (h : G) * w * (h : G)⁻¹ * h := by group
      _ = w * h := by rw [this]
  set t2 : ↥Zg := conjZ k' w with ht2
  have hw2G : (w : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hw2
  have hw1G : (w : G) ≠ 1 := fun e => hw1 (Subtype.ext e)
  have hcentD : ∀ z : G, (h : G) * z = z * h → k * z = z * k → ∀ d ∈ D, d * z = z * d := by
    intro z hz1 hz2 d hd
    have hle : Subgroup.zpowers (h : G) ⊔ Subgroup.zpowers k ≤
        Subgroup.centralizer ({z} : Set G) :=
      sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hz1))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hz2))
    rw [hDeq] at hle
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)
  have hwt2 : (w : G) ≠ t2 := by
    intro he
    refine hinv w hw1G hw2G (hcentD w hhw' ?_)
    have : (t2 : G) = k * w * k⁻¹ := conjZ_apply k' w
    rw [← he] at this
    calc k * (w : G) = k * w * k⁻¹ * k := by group
      _ = w * k := by rw [← this]
  have hNk : w * t2 * conjZ (k' * k') w = 1 := by
    have hfk : conjZ k' (w * t2 * conjZ (k' * k') w) = w * t2 * conjZ (k' * k') w := by
      have e : ∀ d e : ↥D, conjZ d (conjZ e w) = conjZ (d * e) w := by
        intro d e; ext; simp only [conjZ_apply, Subgroup.coe_mul]; group
      rw [map_mul, map_mul, ht2, e, e]
      have e3 : k' * (k' * k') = 1 := by rw [← hD3 k', pow_three]
      rw [e3]
      have e1 : conjZ 1 w = w := by ext; simp [conjZ_apply]
      rw [e1]
      ac_rfl
    have hfh : conjZ h (w * t2 * conjZ (k' * k') w) = w * t2 * conjZ (k' * k') w := by
      have e : ∀ e : ↥D, conjZ h (conjZ e w) = conjZ e w := by
        intro e
        ext
        simp only [conjZ_apply]
        have hc : (h : G) * e = e * h := congrArg Subtype.val (mul_comm h e)
        calc (h : G) * (e * w * (e : G)⁻¹) * (h : G)⁻¹
            = e * ((h : G) * w * (h : G)⁻¹) * (e : G)⁻¹ := by
              rw [show (h : G) * (e * w * (e : G)⁻¹) * (h : G)⁻¹ =
                ((h : G) * e) * w * ((h : G) * e)⁻¹ by group, hc]; group
          _ = e * w * (e : G)⁻¹ := by
              rw [show (h : G) * w * (h : G)⁻¹ = w from by rw [hhw', mul_inv_cancel_right]]
      rw [map_mul, map_mul, hhw, ht2, e, e]
    by_contra hne
    have hne' : ((w * t2 * conjZ (k' * k') w : ↥Zg) : G) ≠ 1 := fun e => hne (Subtype.ext e)
    have hsq : ((w * t2 * conjZ (k' * k') w : ↥Zg) : G) ^ 2 = 1 := by
      have : (w * t2 * conjZ (k' * k') w) ^ 2 = 1 := by
        rw [mul_pow, mul_pow, hw2]
        have q2 : t2 ^ 2 = 1 := by rw [ht2, ← map_pow, hw2, map_one]
        have q3 : conjZ (k' * k') w ^ 2 = 1 := by rw [← map_pow, hw2, map_one]
        rw [q2, q3, one_mul, one_mul]
      simpa using congrArg Subtype.val this
    refine hinv _ hne' hsq (hcentD _ ?_ ?_)
    · have := congrArg Subtype.val hfh
      rw [conjZ_apply] at this
      calc (h : G) * ((w * t2 * conjZ (k' * k') w : ↥Zg) : G)
          = (h : G) * ((w * t2 * conjZ (k' * k') w : ↥Zg) : G) * (h : G)⁻¹ * h := by group
        _ = _ := by rw [this]
    · have := congrArg Subtype.val hfk
      rw [conjZ_apply] at this
      calc (k : G) * ((w * t2 * conjZ (k' * k') w : ↥Zg) : G)
          = (k : G) * ((w * t2 * conjZ (k' * k') w : ↥Zg) : G) * (k : G)⁻¹ * k := by group
        _ = _ := by rw [this]
  have hk3 : k ^ 3 = 1 := hD.2 k hkD
  have hh3 : (h : G) ^ 3 = 1 := hD.2 h h.2
  have hyt2 : (k : G) * t2 * k⁻¹ = (w : G) * t2 := by
    have e1 : (k : G) * t2 * k⁻¹ = ((conjZ (k' * k') w : ↥Zg) : G) := by
      rw [ht2, conjZ_apply, conjZ_apply, Subgroup.coe_mul]
      show (k : G) * ((k : G) * w * (k : G)⁻¹) * (k : G)⁻¹ = ((k : G) * k) * w * ((k : G) * k)⁻¹
      group
    have e2 : conjZ (k' * k') w = (w * t2)⁻¹ := eq_inv_of_mul_eq_one_right hNk
    rw [e1, e2]
    have hinvZ : (w * t2)⁻¹ = w * t2 := by
      have : (w * t2) ^ 2 = 1 := by
        rw [mul_pow, hw2]
        rw [ht2, ← map_pow, hw2, map_one, one_mul]
      exact inv_eq_of_mul_eq_one_left (by rw [← sq]; exact this)
    rw [hinvZ, Subgroup.coe_mul]
  have hdata : KleinData (h : G) k (w : G) (t2 : G) :=
    { x3 := hh3
      x1 := fun e => hh1 (Subtype.ext e)
      y3 := hk3
      y1 := fun e => hkh (e ▸ Subgroup.one_mem _)
      yx := fun e => hkh (e ▸ Subgroup.mem_zpowers _)
      yx2 := fun e => hkh (e ▸ Subgroup.npow_mem_zpowers _ 2)
      xy := hhk
      t12 := hw2G
      t22 := by
        have : t2 ^ 2 = 1 := by rw [ht2, ← map_pow, hw2, map_one]
        simpa using congrArg Subtype.val this
      t11 := hw1G
      t21 := by
        intro e
        apply hw1G
        have : (t2 : G) = k * w * k⁻¹ := conjZ_apply k' w
        rw [e] at this
        have := congrArg (fun z => k⁻¹ * z * k) this
        simpa [mul_assoc] using this.symm
      t1t2 := hwt2
      tc := hZc _ w.2 _ t2.2
      xt1 := hhw'
      xt2 := by
        have : (t2 : G) = k * w * k⁻¹ := conjZ_apply k' w
        rw [this]
        have hk' : (h : G) * k⁻¹ = k⁻¹ * h := by
          calc (h : G) * k⁻¹ = k⁻¹ * (k * h) * k⁻¹ := by group
            _ = k⁻¹ * (h * k) * k⁻¹ := by rw [hhk]
            _ = k⁻¹ * h := by group
        calc (h : G) * (k * w * k⁻¹) = ((h : G) * k) * w * k⁻¹ := by group
          _ = (k * h) * w * k⁻¹ := by rw [hhk]
          _ = k * (h * w) * k⁻¹ := by group
          _ = k * (w * h) * k⁻¹ := by rw [hhw']
          _ = k * w * (h * k⁻¹) := by group
          _ = k * w * k⁻¹ * h := by rw [hk']; group
      yt1 := (conjZ_apply k' w).symm
      yt2 := hyt2 }
  obtain ⟨-, hPn, hPcov⟩ := kleinData_spec hdata
  rw [hDeq] at hPn hPcov
  exact ⟨kleinSub hdata.t12 hdata.t22 hdata.tc, kleinSub_isElemAbelian _ _ _,
    card_kleinSub _ _ _ hdata.t11 hdata.t21 hdata.t1t2, hPn, hPcov⟩

end CFSG.LocalAnalysis.GLTheoremA.KD1426SporKlein
