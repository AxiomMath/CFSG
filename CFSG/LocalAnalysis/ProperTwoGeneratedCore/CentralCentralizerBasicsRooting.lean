module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasics

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G}

omit [Finite G] in
theorem orderOf_inv_mul_mul_eq (x g : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq x

theorem centralInvolution_exists_transport {z t : G}
    (hz : IsCentralInvolution (S : Subgroup G) z) (htz : IsConj t z) :
    ∃ g : G, g⁻¹ * t * g = z ∧
      ∀ y ∈ (S : Subgroup G), Commute y t → g⁻¹ * y * g ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp htz
  set M := Subgroup.centralizer ({z} : Set G) with hM
  set P := rightConjugate ((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)) c⁻¹ with hP
  have hmemP : ∀ y : G, c * y * c⁻¹ ∈ P ↔
      y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) := by
    intro y
    rw [hP, mem_rightConjugate_iff_conj_mem]
    have hy : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
    rw [hy]
  have hPM : P ≤ M := by
    intro p hp
    have hp' : c⁻¹ * p * c ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) := by
      rw [← hmemP]
      convert hp using 1
      group
    have hpt := Subgroup.mem_centralizer_singleton_iff.mp hp'.2
    rw [hM, Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc p * (c * t * c⁻¹) = c * (c⁻¹ * p * c * t) * c⁻¹ := by group
      _ = c * (t * (c⁻¹ * p * c)) * c⁻¹ := by rw [hpt]
      _ = c * t * c⁻¹ * p := by group
  have hPp : IsPGroup 2 P := (S.isPGroup'.to_le inf_le_left).map _
  have hmax : ∀ Q : Subgroup G, Q ≤ M → IsPGroup 2 Q →
      Nat.card Q ≤ Nat.card (S : Subgroup G) := by
    intro Q _ hQ
    obtain ⟨R, hQR⟩ := hQ.exists_le_sylow
    calc Nat.card Q ≤ Nat.card R := Subgroup.card_le_of_le hQR
      _ = Nat.card (S : Subgroup G) := by
        rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  obtain ⟨d, hdM, hd⟩ := exists_conj_mem_of_card_le hz.le_centralizer S.isPGroup' hmax hPM hPp
  have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.mp hdM
  refine ⟨c⁻¹ * d, ?_, fun y hyS hyt => ?_⟩
  · calc (c⁻¹ * d)⁻¹ * t * (c⁻¹ * d) = d⁻¹ * (c * t * c⁻¹) * d := by group
      _ = d⁻¹ * (d * z) := by rw [hc, mul_assoc, hdz]
      _ = z := by group
  · have hyP : c * y * c⁻¹ ∈ P :=
      (hmemP y).mpr ⟨hyS, Subgroup.mem_centralizer_singleton_iff.mpr hyt.eq⟩
    convert hd _ hyP using 1
    group

theorem centralInvolution_transport {z t : G} (hz : IsCentralInvolution (S : Subgroup G) z)
    (htS : t ∈ (S : Subgroup G)) (htz : IsConj t z) (hne : t ≠ z) :
    ∃ g : G, g⁻¹ * t * g = z ∧
      (∀ y ∈ (S : Subgroup G), Commute y t →
        g⁻¹ * y * g ∈ (S : Subgroup G) ∧ Commute (g⁻¹ * y * g) (g⁻¹ * z * g)) ∧
      g⁻¹ * z * g ∈ (S : Subgroup G) ∧ orderOf (g⁻¹ * z * g) = 2 ∧ g⁻¹ * z * g ≠ z := by
  obtain ⟨g, hgt, hgS⟩ := centralInvolution_exists_transport hz htz
  refine ⟨g, hgt, fun y hyS hyt => ⟨hgS y hyS hyt, ?_⟩, hgS z hz.1 (hz.2.2 t htS).symm,
    (orderOf_inv_mul_mul_eq z g).trans hz.2.1, fun hs => hne ?_⟩
  · have hyz : y * z = z * y := hz.2.2 y hyS
    calc g⁻¹ * y * g * (g⁻¹ * z * g) = g⁻¹ * (y * z) * g := by group
      _ = g⁻¹ * (z * y) * g := by rw [hyz]
      _ = g⁻¹ * z * g * (g⁻¹ * y * g) := by group
  · have h := hgt.trans hs.symm
    rwa [mul_left_inj, mul_right_inj] at h

theorem centralInvolution_conj_mem_eq_of_rooting {z : G}
    (hz : IsCentralInvolution (S : Subgroup G) z) (n : ℕ)
    (hroot : ∀ y ∈ (S : Subgroup G), orderOf (y ^ n) = 2 → y ^ n = z)
    (hcover : ∀ t ∈ (S : Subgroup G), orderOf t = 2 → t ≠ z →
      ∃ y ∈ (S : Subgroup G), Commute y t ∧ y ^ n = z)
    (g : G) (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) : g⁻¹ * z * g = z := by
  by_contra hne
  have ht : orderOf (g⁻¹ * z * g) = 2 := (orderOf_inv_mul_mul_eq z g).trans hz.2.1
  have htz : IsConj (g⁻¹ * z * g) z := isConj_iff.mpr ⟨g, by group⟩
  obtain ⟨k, hk, hkS⟩ := centralInvolution_exists_transport hz htz
  obtain ⟨y, hyS, hyt, hyn⟩ := hcover _ hg ht hne
  have hpow : (k⁻¹ * y * k) ^ n = k⁻¹ * z * k := by
    have h := map_pow (MulAut.conj k⁻¹) y n
    simp only [MulAut.conj_apply, inv_inv] at h
    rw [← h, hyn]
  have hs := hroot _ (hkS y hyS hyt) (by rw [hpow, orderOf_inv_mul_mul_eq]; exact hz.2.1)
  rw [hpow] at hs
  apply hne
  have h := hk.trans hs.symm
  rwa [mul_left_inj, mul_right_inj] at h

theorem centralInvolution_exists_conj_mem_ne (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : IsCentralInvolution (S : Subgroup G) z) :
    ∃ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) ∧ g⁻¹ * z * g ≠ z := by
  by_contra hcon
  have hwc : ∀ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) → g⁻¹ * z * g = z := fun g hg => by
    by_contra hne
    exact hcon ⟨g, hg, hne⟩
  have hzZ : (⟨z, hz.1⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) :=
    Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hz.2.2 s s.property)
  obtain ⟨hgen, -⟩ := CFSG.Adapters.glauberman_zStar S ⟨z, hz.1⟩ hzZ
    (by rw [Subgroup.orderOf_mk]; exact hz.2.1) hwc
  rcases (inferInstance : (CFSG.oddCore G).Normal).eq_bot_or_eq_top with hbot | htop
  · have hcenter : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨c, hc, k, hk, rfl⟩ := hgen g
      rw [hbot, Subgroup.mem_bot] at hk
      rw [hk, mul_one]
      exact Subgroup.mem_centralizer_singleton_iff.mp hc
    rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with hc | hc
    · have hz1 : z = 1 := Subgroup.mem_bot.mp (hc ▸ hcenter)
      have h := hz.2.1
      rw [hz1, orderOf_one] at h
      norm_num at h
    · obtain ⟨a, b, hab⟩ := hnonab
      have ha : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  · exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz.2.1 (htop ▸ Subgroup.mem_top z)

theorem rooting_false_of_isSimpleGroup (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : IsCentralInvolution (S : Subgroup G) z)
    (n : ℕ) (hroot : ∀ y ∈ (S : Subgroup G), orderOf (y ^ n) = 2 → y ^ n = z)
    (hcover : ∀ t ∈ (S : Subgroup G), orderOf t = 2 → t ≠ z →
      ∃ y ∈ (S : Subgroup G), Commute y t ∧ y ^ n = z) : False := by
  obtain ⟨g, hgS, hgne⟩ := centralInvolution_exists_conj_mem_ne hsimple hnonab hz
  exact hgne (centralInvolution_conj_mem_eq_of_rooting hz n hroot hcover g hgS)

theorem coreSetting_rooting_false (hset : CoreSetting G S H) {z : G}
    (hz : IsCentralInvolution (S : Subgroup G) z) (n : ℕ)
    (hroot : ∀ y ∈ (S : Subgroup G), orderOf (y ^ n) = 2 → y ^ n = z)
    (hcover : ∀ t ∈ (S : Subgroup G), orderOf t = 2 → t ≠ z →
      ∃ y ∈ (S : Subgroup G), Commute y t ∧ y ^ n = z) : False :=
  rooting_false_of_isSimpleGroup hset.simple hset.nonabelian hz n hroot hcover

omit [Finite G] in
theorem orderOf_eq_four_of_orderOf_sq_eq_two {y : G} (h : orderOf (y ^ 2) = 2) :
    orderOf y = 4 := by
  have h4 : y ^ 4 = 1 := by
    have hp := pow_orderOf_eq_one (y ^ 2)
    rwa [h, ← pow_mul] at hp
  have hdvd : orderOf y ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hn2 : ¬ orderOf y ∣ 2 := by
    intro h2
    rw [orderOf_dvd_iff_pow_eq_one.mp h2, orderOf_one] at h
    norm_num at h
  have hle : orderOf y ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < orderOf y := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  interval_cases hy : orderOf y <;> omega

theorem coreSetting_rooting_order_four_false (hset : CoreSetting G S H) {z : G}
    (hz : IsCentralInvolution (S : Subgroup G) z)
    (hsq : ∀ y ∈ (S : Subgroup G), orderOf y = 4 → y ^ 2 = z)
    (hcover : ∀ t ∈ (S : Subgroup G), orderOf t = 2 → t ≠ z →
      ∃ y ∈ (S : Subgroup G), Commute y t ∧ orderOf y = 4) : False := by
  refine coreSetting_rooting_false hset hz 2
    (fun y hyS hy2 => hsq y hyS (orderOf_eq_four_of_orderOf_sq_eq_two hy2))
    (fun t htS ht hne => ?_)
  obtain ⟨y, hyS, hyt, hy4⟩ := hcover t htS ht hne
  exact ⟨y, hyS, hyt, hsq y hyS hy4⟩

theorem coreSetting_central_fusion (hset : CoreSetting G S H) {a g : G}
    (ha : a ∈ Subgroup.centralizer ((S : Subgroup G) : Set G))
    (hga : g⁻¹ * a * g ∈ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n ∈ H ∧
      g⁻¹ * a * g = n⁻¹ * a * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hgn⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer S a g ha hga
  exact ⟨n, hn, coreSetting_sylow_normalizer_le hset hn, hgn⟩

theorem coreSetting_centralInvolution_fusion (hset : CoreSetting G S H) {z w : G}
    (hz : IsCentralInvolution (S : Subgroup G) z) (hw : IsCentralInvolution (S : Subgroup G) w)
    (hzw : IsConj z w) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n ∈ H ∧ n⁻¹ * z * n = w := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hzw
  have hcw : c⁻¹⁻¹ * z * c⁻¹ = w := by rw [inv_inv, hc]
  obtain ⟨n, hn, hnH, hnz⟩ := coreSetting_central_fusion hset (g := c⁻¹)
    (Subgroup.mem_centralizer_iff.mpr hz.2.2) (hcw ▸ Subgroup.mem_centralizer_iff.mpr hw.2.2)
  exact ⟨n, hn, hnH, hnz.symm.trans hcw⟩

end CFSG.ProperTwoGeneratedCore.Assembly
