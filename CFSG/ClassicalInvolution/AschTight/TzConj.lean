module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem mem_normalizer_of_mul_self_eq_one {H : Subgroup G} {b : G} (hb : b * b = 1)
    (h : ∀ x ∈ H, b * x * b⁻¹ ∈ H) : b ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 := h _ hx
  have e : b * (b * x * b⁻¹) * b⁻¹ = (b * b) * x * (b * b)⁻¹ := by group
  rwa [e, hb, one_mul, inv_one, mul_one] at h1

theorem mem_or_mul_mem_of_mem_sup_zpowers {R : Subgroup G} {t : G} (ht : t * t = 1)
    (htN : t ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R ⊔ Subgroup.zpowers t) :
    x ∈ R ∨ x * t ∈ R := by
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr htN
  have hx' : x ∈ ((R ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R _ hle] at hx'
  obtain ⟨r, hr, s, hs, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rwa [← two_mul, zpow_mul, h2, one_zpow, mul_one]
  · right
    rwa [zpow_add_one, zpow_mul, h2, one_zpow, one_mul, mul_assoc, ht, mul_one]

theorem mul_self_mem_of_mem_sup_zpowers {R : Subgroup G} {t : G} (ht : t * t = 1)
    (htN : t ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R ⊔ Subgroup.zpowers t) :
    x * x ∈ R := by
  rcases mem_or_mul_mem_of_mem_sup_zpowers ht htN hx with h | h
  · exact R.mul_mem h h
  · have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hconj : t * (x * t) * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp htN _).mp h
    have e : x * t * (t * (x * t) * t⁻¹) = x * x := by
      rw [ht']
      simp only [mul_assoc]
      rw [ht, mul_one, ← mul_assoc t t x, ht, one_mul]
    rw [← e]
    exact R.mul_mem h hconj

theorem closure_pair_eq_sup_zpowers (a b : G) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

theorem zpow_eq_zpow_of_mul_self_eq_one {g : G} {i j : ℤ} (hi : g ^ i * g ^ i = 1)
    (hj : g ^ j * g ^ j = 1) (hi1 : g ^ i ≠ 1) (hj1 : g ^ j ≠ 1) : g ^ i = g ^ j := by
  have hi' : g ^ (i + i) = 1 := by rw [zpow_add]; exact hi
  have hj' : g ^ (j + j) = 1 := by rw [zpow_add]; exact hj
  obtain ⟨e, he⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hi'
  obtain ⟨f, hf⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hj'
  have hodd : ∀ {k c : ℤ}, g ^ k ≠ 1 → k + k = (orderOf g : ℤ) * c → Odd c := by
    intro k c hk hc
    rcases Int.even_or_odd c with ⟨c', rfl⟩ | h
    · exact absurd (orderOf_dvd_iff_zpow_eq_one.mp ⟨c', by linarith⟩) hk
    · exact h
  obtain ⟨d, hd⟩ := (hodd hi1 he).sub_odd (hodd hj1 hf)
  have h2 : 2 * (i - j) = 2 * ((orderOf g : ℤ) * d) := by
    linear_combination he - hf + (orderOf g : ℤ) * hd
  have hij : g ^ (i - j) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp ⟨d, mul_left_cancel₀ two_ne_zero h2⟩
  rw [zpow_sub, mul_inv_eq_one] at hij
  exact hij

theorem exists_conj_eq_mul_of_isSemidihedral [Finite G] {R : Subgroup G} {z t : G}
    (hR2 : IsPGroup 2 R) (hz : IsUniqueInvolution R z) (ht : t * t = 1) (htR : t ∉ R)
    (htN : t ∈ Subgroup.normalizer (R : Set G))
    (hsd : IsSemidihedral (R ⊔ Subgroup.zpowers t)) : ∃ r ∈ R, r * t * r⁻¹ = z * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, ha8, -, hb2, -, hbab, hcl⟩ := hsd
  have haP : a ∈ R ⊔ Subgroup.zpowers t := hcl ▸ Subgroup.subset_closure (by simp)
  have htP : t ∈ R ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have ht1 : t ≠ 1 := fun h => htR (h ▸ R.one_mem)
  have hzt2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact ht) ht1
  have hP2 : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers t) :=
    hR2.to_sup_of_normal_left' hzt2 (Subgroup.zpowers_le.mpr htN)
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hadvd : orderOf a ∣ 2 ^ n := hn ▸ Subgroup.orderOf_dvd_natCard _ haP
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hadvd
  have he3 : 3 ≤ e := by
    by_contra h
    have : 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨M, hM⟩ : ∃ M : ℕ, orderOf a = 8 * M :=
    ⟨2 ^ (e - 3), by rw [he, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, Nat.add_sub_cancel' he3]⟩
  have hM1 : 1 ≤ M := by omega
  have ha2 : a * a ∈ R := mul_self_mem_of_mem_sup_zpowers ht htN haP
  have hpow : ∀ m : ℕ, a ^ (2 * m) ∈ R := fun m => by
    rw [pow_mul, sq]
    exact R.pow_mem ha2 m
  have htA : t ∉ Subgroup.zpowers a := by
    intro hta
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hta
    have hk2 : a ^ (k + k) = 1 := by rw [zpow_add]; exact ht
    obtain ⟨d, hd⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hk2
    rw [hM] at hd
    push_cast at hd
    have hk : k = 2 * (2 * M * d) := by linarith
    apply htR
    rw [hk, zpow_mul, zpow_two]
    exact R.zpow_mem ha2 _
  have hbN : b ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    refine mem_normalizer_of_mul_self_eq_one hb2 fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hbab]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _) _
  have htab : t ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [← closure_pair_eq_sup_zpowers, hcl]
    exact htP
  obtain ⟨i, hi⟩ : ∃ i : ℤ, a ^ i = t * b := by
    rcases mem_or_mul_mem_of_mem_sup_zpowers hb2 hbN htab with h | h
    · exact absurd h htA
    · exact Subgroup.mem_zpowers_iff.mp h
  have hti : t = a ^ i * b := by rw [hi, mul_assoc, hb2, mul_one]
  obtain ⟨s, hs⟩ : ∃ s : G, a ^ (2 * M) = s := ⟨_, rfl⟩
  have hk : orderOf a / 2 - 1 = 4 * M - 1 := by omega
  have hbs : b * s * b⁻¹ = s⁻¹ := by
    rw [← hs, ← conj_pow, hbab, hk, ← pow_mul]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    have h1 : (4 * M - 1) * (2 * M) + 2 * M = orderOf a * M := by
      rw [hM, ← add_one_mul, Nat.sub_add_cancel (by omega)]
      ring
    rw [h1, pow_mul, pow_orderOf_eq_one, one_pow]
  have hbs' : b * s⁻¹ = s * b := by
    have h1 : (b * s * b⁻¹)⁻¹ = s := by rw [hbs, inv_inv]
    calc b * s⁻¹ = (b * s * b⁻¹)⁻¹ * b := by group
      _ = s * b := by rw [h1]
  have hcomm : a ^ i * s = s * a ^ i := by
    rw [← hs, ← zpow_natCast, zpow_mul_comm]
  have hssR : s * s ∈ R := by rw [← hs]; exact R.mul_mem (hpow M) (hpow M)
  have hss1 : s * s ≠ 1 := by
    rw [← hs, ← pow_add]
    exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hM]; omega)
  have hss2 : s * s * (s * s) = 1 := by
    rw [← hs, ← pow_add, ← pow_add, show 2 * M + 2 * M + (2 * M + 2 * M) = orderOf a by
      rw [hM]; ring, pow_orderOf_eq_one]
  have hzs : s * s = z := (hz.unique _ hssR hss2).resolve_left hss1
  refine ⟨s, by rw [← hs]; exact hpow M, ?_⟩
  calc s * t * s⁻¹ = s * a ^ i * (b * s⁻¹) := by rw [hti]; group
    _ = s * (a ^ i * s) * b := by rw [hbs']; group
    _ = s * (s * a ^ i) * b := by rw [hcomm]
    _ = s * s * (a ^ i * b) := by group
    _ = z * t := by rw [hzs, ← hti]

theorem exists_zpow_mul_zpow_of_mem_sup {a c : G} (hac : a * c = c * a) {x : G}
    (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c) : ∃ i j : ℤ, a ^ i * c ^ j = x := by
  have hle : Subgroup.zpowers a ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute c a from hac.symm) k).eq
  have hx' : x ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx'
  obtain ⟨y, hy, w, hw, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨i, j, rfl⟩

theorem mul_comm_of_mem_sup_zpowers {a c : G} (hac : a * c = c * a) {x y : G}
    (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c)
    (hy : y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c) : x * y = y * x := by
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac hx
  obtain ⟨k, l, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac hy
  have h : Commute a c := hac
  have h1 : Commute (a ^ i * c ^ j) (a ^ k) :=
    (Commute.zpow_zpow_self a i k).mul_left (h.symm.zpow_zpow j k)
  have h2 : Commute (a ^ i * c ^ j) (c ^ l) :=
    (h.zpow_zpow i l).mul_left (Commute.zpow_zpow_self c j l)
  exact (h1.mul_right h2).eq

theorem exists_conj_eq_mul_of_isWreathed [Finite G] {R V : Subgroup G} {z t : G}
    (hz : IsUniqueInvolution R z) (hRnc : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x)
    (hVN : V ≤ Subgroup.normalizer (R : Set G)) (htV : t ∈ V) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htz : t ≠ z) (hsq : ∃ w ∈ V, w * w = t) (hwr : IsWreathed (R ⊔ V)) :
    ∃ r ∈ R, r * t * r⁻¹ = z * t := by
  obtain ⟨a, c, b, ha4, hca, hac, hcard, hb2, hbac, hbca, hcl⟩ := hwr
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, Subgroup.zpowers a ⊔ Subgroup.zpowers c = B := ⟨_, rfl⟩
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_sup_zpowers hac (hB ▸ hx) (hB ▸ hy)
  have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have haB : a ∈ B := hB ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hconj : ∀ i j : ℤ, b * (a ^ i * c ^ j) * b⁻¹ = c ^ i * a ^ j := by
    intro i j
    rw [show b * (a ^ i * c ^ j) * b⁻¹ = (b * a * b⁻¹) ^ i * (b * c * b⁻¹) ^ j by
      rw [conj_zpow, conj_zpow]; group, hbac, hbca]
  have hbB : b ∈ Subgroup.normalizer (B : Set G) := by
    refine mem_normalizer_of_mul_self_eq_one hb2 fun x hx => ?_
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac (hB ▸ hx)
    rw [hconj, ← hB]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _))
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _))
  have hP : R ⊔ V = B ⊔ Subgroup.zpowers b := by
    rw [← hcl, ← hB, Set.insert_eq, Set.insert_eq, Subgroup.closure_union, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure,
      sup_assoc]
  have hPB : ∀ x ∈ R ⊔ V, x ∈ B ∨ x * b ∈ B := fun x hx =>
    mem_or_mul_mem_of_mem_sup_zpowers hb2 hbB (hP ▸ hx)
  have hac1 : ∀ x ∈ Subgroup.zpowers a, x ∈ Subgroup.zpowers c → x = 1 := by
    intro x hxa hxc
    by_contra hx1
    have hcomm : ∀ (m : ↥(Subgroup.zpowers a)) (n : ↥(Subgroup.zpowers c)),
        Commute ((Subgroup.zpowers a).subtype m) ((Subgroup.zpowers c).subtype n) := fun m n =>
      mul_comm_of_mem_sup_zpowers hac (Subgroup.mem_sup_left (by simp))
        (Subgroup.mem_sup_right (by simp))
    let φ := (Subgroup.zpowers a).subtype.noncommCoprod (Subgroup.zpowers c).subtype hcomm
    have hrange : φ.range = B := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hB]
    have hker : 2 ≤ Nat.card φ.ker := by
      have hne : φ.ker ≠ ⊥ := by
        intro hbot
        have hmem : ((⟨x, hxa⟩, ⟨x⁻¹, Subgroup.inv_mem _ hxc⟩) :
            ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers c)) ∈ φ.ker := by
          rw [MonoidHom.mem_ker]
          exact mul_inv_cancel x
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hx1 (congrArg (fun p => (p.1 : G)) hmem)
      exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hrange, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hca] at h1
    have hPcard : Nat.card ↥(R ⊔ V) ≤ Nat.card B * 2 := by
      have e : Nat.card ↥(R ⊔ V) =
          Nat.card ↥(((B ⊔ Subgroup.zpowers b : Subgroup G) : Set G)) := by rw [hP]; rfl
      rw [e, Subgroup.coe_mul_of_right_le_normalizer_left B _ (Subgroup.zpowers_le.mpr hbB)]
      refine Set.natCard_mul_le.trans (Nat.mul_le_mul_left _ ?_)
      change Nat.card ↥(Subgroup.zpowers b) ≤ 2
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hb2))
    have h2 : 2 * Nat.card B ≤ orderOf a * orderOf a := by
      calc 2 * Nat.card B ≤ Nat.card φ.ker * Nat.card B := Nat.mul_le_mul_right _ hker
        _ = orderOf a * orderOf a := h1
    rw [hcard] at hPcard
    nlinarith
  have hzc : R ⊔ V ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hz.conj_eq (conjSub_eq_self_of_mem hx)
      calc x * z = x * z * x⁻¹ * x := by group
        _ = z * x := by rw [h1]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hz.conj_eq (conjSub_eq_of_mem_normalizer (hVN hx))
      calc x * z = x * z * x⁻¹ * x := by group
        _ = z * x := by rw [h1]
  have haP : a ∈ R ⊔ V := hcl ▸ Subgroup.subset_closure (by simp)
  have hbP : b ∈ R ⊔ V := hcl ▸ Subgroup.subset_closure (by simp)
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha4
    omega
  have hzB : z ∈ B := by
    rcases hPB z (Subgroup.mem_sup_left hz.mem) with h | h
    · exact h
    · exfalso
      apply ha1
      apply hac1 a (Subgroup.mem_zpowers a)
      have hza : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (hzc haP)
      have hy := hBc _ h a haB
      have h1 : z * (b * a) = z * (a * b) := by
        calc z * (b * a) = z * b * a := by group
          _ = a * (z * b) := hy
          _ = (a * z) * b := by group
          _ = (z * a) * b := by rw [hza]
          _ = z * (a * b) := by group
      have h2 : c = a := by rw [← hbac, mul_left_cancel h1, mul_inv_cancel_right]
      rw [← h2]
      exact Subgroup.mem_zpowers c
  have hfix : ∀ x ∈ B, b * x * b⁻¹ = x → x ∈ Subgroup.zpowers (a * c) := by
    intro x hx hbx
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac (hB ▸ hx)
    have h : Commute a c := hac
    have hx' : a ^ i * c ^ j = (a * c) ^ i * c ^ (j - i) := by
      rw [h.mul_zpow, mul_assoc, ← zpow_add, add_sub_cancel]
    have hx'' : c ^ i * a ^ j = (a * c) ^ i * a ^ (j - i) := by
      rw [h.mul_zpow, show a ^ i * c ^ i = c ^ i * a ^ i from (h.zpow_zpow i i).eq, mul_assoc,
        ← zpow_add, add_sub_cancel]
    rw [hconj, hx'', hx'] at hbx
    have h1 : a ^ (j - i) = c ^ (j - i) := mul_left_cancel hbx
    have h2 : c ^ (j - i) = 1 := by
      rw [← h1]
      refine hac1 _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _) ?_
      rw [h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _
    rw [hx', h2, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  obtain ⟨w, hwV, hwt⟩ := hsq
  have htB : t ∈ B :=
    hwt ▸ mul_self_mem_of_mem_sup_zpowers hb2 hbB (hP ▸ Subgroup.mem_sup_right hwV)
  have hbt : b * t * b⁻¹ ≠ t := by
    intro hbt
    have hzfix : b * z * b⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hzc hbP), mul_inv_cancel_right]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hfix t htB hbt)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hfix z hzB hzfix)
    apply htz
    rw [← hi, ← hj]
    refine zpow_eq_zpow_of_mul_self_eq_one (by rw [hi]; exact ht2) (by rw [hj]; exact hz.sq)
      (by rw [hi]; exact ht1) (by rw [hj]; exact hz.ne_one)
  obtain ⟨r, hrR, hrB⟩ : ∃ r ∈ R, r ∉ B := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := hRnc
    exact hxy (hBc x (hcon x hx) y (hcon y hy))
  refine ⟨r, hrR, ?_⟩
  obtain ⟨t', ht'⟩ : ∃ t' : G, b * t * b⁻¹ = t' := ⟨_, rfl⟩
  have ht'B : t' ∈ B := ht' ▸ (Subgroup.mem_normalizer_iff.mp hbB t).mp htB
  obtain ⟨y, hy⟩ : ∃ y : G, r * b = y := ⟨_, rfl⟩
  have hyB : y ∈ B := hy ▸ (hPB r (Subgroup.mem_sup_left hrR)).resolve_left hrB
  have hrt : r * t * r⁻¹ = t' := by
    have hr : r = y * b⁻¹ := by rw [← hy, mul_inv_cancel_right]
    calc r * t * r⁻¹ = y * (b⁻¹ * t * b) * y⁻¹ := by rw [hr]; group
      _ = y * (b * t * b⁻¹) * y⁻¹ := by rw [hbb]
      _ = t' * y * y⁻¹ := by rw [ht', hBc _ hyB _ ht'B]
      _ = t' := by group
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hxR : t' * t ∈ R := by
    rw [← hrt]
    have h1 : t * r⁻¹ * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hVN htV) _).mp (R.inv_mem hrR)
    have e : r * t * r⁻¹ * t = r * (t * r⁻¹ * t⁻¹) := by rw [htt]; group
    rw [e]
    exact R.mul_mem hrR h1
  have ht'2 : t' * t' = 1 := by
    rw [← ht']
    calc b * t * b⁻¹ * (b * t * b⁻¹) = b * (t * t) * b⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hcomm := hBc _ ht'B _ htB
  have hx2 : t' * t * (t' * t) = 1 := by
    calc t' * t * (t' * t) = t' * (t * t') * t := by group
      _ = t' * (t' * t) * t := by rw [← hcomm]
      _ = t' * t' * (t * t) := by group
      _ = 1 := by rw [ht'2, ht2, one_mul]
  have hx1 : t' * t ≠ 1 := by
    intro h
    apply hbt
    rw [ht', ← htt]
    exact eq_inv_of_mul_eq_one_left h
  have hxz : t' * t = z := (hz.unique _ hxR hx2).resolve_left hx1
  rw [hrt]
  calc t' = t' * t * t := by rw [mul_assoc, ht2, mul_one]
    _ = z * t := by rw [hxz]

end CFSG.ClassicalInvolution.Disconnected.AschTight
