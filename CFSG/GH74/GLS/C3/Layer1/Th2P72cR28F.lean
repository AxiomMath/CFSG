module

public import CFSG.GH74.GLS.IVK.Lifted.DSDGroup
public import CFSG.GH74.Uniqueness.SU.SU1BgMaxClass
public import CFSG.GroupTheory.DihedralTwoClassFusionSupport

public section

namespace CFSG.GH74.GLS.Th2.R714Dsd

open CFSG.GH74.GLS.IVK.Lifted

@[expose] def Cl3 {M : Type} [Group M] (z : M) : Prop :=
  ∀ a b c : M, a * a = 1 → b * b = 1 → c * c = 1 → a ≠ 1 → b ≠ 1 → c ≠ 1 → a ≠ z → b ≠ z → c ≠ z →
    (∃ q : M, q * a * q⁻¹ = b) ∨ (∃ q : M, q * a * q⁻¹ = c) ∨ (∃ q : M, q * b * q⁻¹ = c)

section General

theorem cl3_of_two_classes {M : Type} [Group M] (z p q : M)
    (h : ∀ a : M, a * a = 1 → a ≠ 1 → a ≠ z → IsConj a p ∨ IsConj a q) : Cl3 z := by
  intro a b c ha hb hc ha1 hb1 hc1 haz hbz hcz
  rcases h a ha ha1 haz with h1 | h1 <;> rcases h b hb hb1 hbz with h2 | h2 <;>
    rcases h c hc hc1 hcz with h3 | h3
  · exact Or.inl (isConj_iff.1 (h1.trans h2.symm))
  · exact Or.inl (isConj_iff.1 (h1.trans h2.symm))
  · exact Or.inr (Or.inl (isConj_iff.1 (h1.trans h3.symm)))
  · exact Or.inr (Or.inr (isConj_iff.1 (h2.trans h3.symm)))
  · exact Or.inr (Or.inr (isConj_iff.1 (h2.trans h3.symm)))
  · exact Or.inr (Or.inl (isConj_iff.1 (h1.trans h3.symm)))
  · exact Or.inl (isConj_iff.1 (h1.trans h2.symm))
  · exact Or.inl (isConj_iff.1 (h1.trans h2.symm))

theorem Cl3.of_equiv {M G : Type} [Group M] [Group G] (e : M ≃* G) {z : M} (h : Cl3 (e z)) :
    Cl3 z := by
  intro a b c ha hb hc ha1 hb1 hc1 haz hbz hcz
  have key : ∀ x : M, x * x = 1 → x ≠ 1 → x ≠ z → e x * e x = 1 ∧ e x ≠ 1 ∧ e x ≠ e z := by
    intro x hx hx1 hxz
    exact ⟨by rw [← map_mul, hx, map_one], fun h1 => hx1 (e.injective (h1.trans (map_one e).symm)),
      fun h1 => hxz (e.injective h1)⟩
  have back : ∀ x y : M, (∃ q : G, q * e x * q⁻¹ = e y) → ∃ q : M, q * x * q⁻¹ = y := by
    rintro x y ⟨q, hq⟩
    refine ⟨e.symm q, e.injective ?_⟩
    simpa using hq
  obtain ⟨ha2, ha3, ha4⟩ := key a ha ha1 haz
  obtain ⟨hb2, hb3, hb4⟩ := key b hb hb1 hbz
  obtain ⟨hc2, hc3, hc4⟩ := key c hc hc1 hcz
  rcases h (e a) (e b) (e c) ha2 hb2 hc2 ha3 hb3 hc3 ha4 hb4 hc4 with h1 | h1 | h1
  · exact Or.inl (back a b h1)
  · exact Or.inr (Or.inl (back a c h1))
  · exact Or.inr (Or.inr (back b c h1))

theorem card_centralizer_le_four_aux {M : Type} [Group M] (t a b c d : M)
    (h : ∀ y : M, y * t = t * y → y = a ∨ y = b ∨ y = c ∨ y = d) :
    Nat.card (Subgroup.centralizer ({t} : Set M)) ≤ 4 := by
  have hsub : (Subgroup.centralizer ({t} : Set M) : Set M) ⊆ ({a, b, c, d} : Set M) := by
    intro y hy
    have hy' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    rcases h y hy' with h | h | h | h <;> simp [h]
  calc Nat.card (Subgroup.centralizer ({t} : Set M))
      = Set.ncard (Subgroup.centralizer ({t} : Set M) : Set M) := Nat.card_coe_set_eq _
    _ ≤ Set.ncard ({a, b, c, d} : Set M) := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by
      calc Set.ncard ({a, b, c, d} : Set M) ≤ Set.ncard ({b, c, d} : Set M) + 1 :=
            Set.ncard_insert_le _ _
        _ ≤ (Set.ncard ({c, d} : Set M) + 1) + 1 := by
            have := Set.ncard_insert_le b ({c, d} : Set M)
            omega
        _ ≤ ((Set.ncard ({d} : Set M) + 1) + 1) + 1 := by
            have := Set.ncard_insert_le c ({d} : Set M)
            omega
        _ = 4 := by rw [Set.ncard_singleton]

end General

section Dihedral

open DihedralGroup CFSG.GorensteinWalter.TwoClassFusion

theorem two_ne_zero_zmod_pow {m : ℕ} (hm : 2 ≤ m) : (2 : ZMod (2 ^ m)) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have h1 := Nat.le_of_dvd (by norm_num) h'
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem dih_central_involution {m : ℕ} (hm : 2 ≤ m) (g : DihedralGroup (2 ^ m)) (hg2 : g * g = 1)
    (hg1 : g ≠ 1) (hgc : ∀ h : DihedralGroup (2 ^ m), h * g = g * h) :
    g = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have hg : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  rcases eq_r_half_or_sr_of_orderOf_eq_two hm hg with h | ⟨k, hk⟩
  · exact h
  · exfalso
    have h1 := hgc (r 1)
    rw [hk, r_mul_sr, sr_mul_r, sr.injEq] at h1
    exact two_ne_zero_zmod_pow hm (by linear_combination (-1 : ZMod (2 ^ m)) * h1)

theorem dih_involution_classes {m : ℕ} (hm : 2 ≤ m) (a : DihedralGroup (2 ^ m)) (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (haz : a ≠ r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) :
    IsConj a (sr 0) ∨ IsConj a (sr 1) := by
  have ha : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  rcases eq_r_half_or_sr_of_orderOf_eq_two hm ha with h | ⟨k, hk⟩
  · exact absurd h haz
  · rw [hk]
    exact isConj_sr_zero_or_one k

theorem dih_cl3 {m : ℕ} (hm : 2 ≤ m) : Cl3 (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) :=
  cl3_of_two_classes _ (sr 0) (sr 1) (dih_involution_classes hm)

end Dihedral

section Semidihedral

open CFSG.Semidihedral CFSG.Open

theorem sd_not_central_s (n : ℕ) (hn : 4 ≤ n) : ¬ ∀ h : SemidihedralGroup n, h * s n = s n * h := by
  intro hc
  obtain ⟨h1, h2⟩ := sd_quarter_facts n hn
  have h3 : s n * (r n ^ (half n / 2)) * (s n)⁻¹ = r n ^ (half n / 2) := by
    rw [← hc (r n ^ (half n / 2)), mul_inv_cancel_right]
  have h4 : r n ^ (half n / 2) = (r n ^ (half n / 2))⁻¹ := h3.symm.trans h2
  have h5 : r n ^ (half n / 2) * r n ^ (half n / 2) = 1 := by
    nth_rewrite 1 [h4]
    exact inv_mul_cancel _
  exact z_ne_one n (by omega) (h1.symm.trans h5)

theorem sd_central_involution (n : ℕ) (hn : 4 ≤ n) (g : SemidihedralGroup n) (hg2 : g * g = 1)
    (hg1 : g ≠ 1) (hgc : ∀ h : SemidihedralGroup n, h * g = g * h) : g = z n := by
  have hg : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  rcases CFSG.QuasiDihedralFusion.sd_involution_cases hn g hg with h | h
  · exact h
  · exfalso
    obtain ⟨q, hq⟩ := isConj_iff.1 h
    have hsg : s n = g := by
      calc s n = q⁻¹ * (q * s n * q⁻¹) * q := by group
        _ = q⁻¹ * g * q := by rw [hq]
        _ = g := by rw [hgc q⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    refine sd_not_central_s n hn ?_
    intro h
    rw [hsg]
    exact hgc h

theorem sd_involution_conj (n : ℕ) (hn : 4 ≤ n) (g : SemidihedralGroup n) (hg2 : g * g = 1)
    (hg1 : g ≠ 1) (hgz : g ≠ z n) : ∃ q : SemidihedralGroup n, q * s n * q⁻¹ = g := by
  have hg : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  rcases CFSG.QuasiDihedralFusion.sd_involution_cases hn g hg with h | h
  · exact absurd h hgz
  · exact isConj_iff.1 h

theorem sd_cl3 (n : ℕ) (hn : 4 ≤ n) : Cl3 (z n) := by
  intro a b c ha hb _ ha1 hb1 _ haz hbz _
  obtain ⟨qa, hqa⟩ := sd_involution_conj n hn a ha ha1 haz
  obtain ⟨qb, hqb⟩ := sd_involution_conj n hn b hb hb1 hbz
  refine Or.inl ⟨qb * qa⁻¹, ?_⟩
  rw [← hqa, ← hqb]
  group

theorem sd_centralizer_of_involution (n : ℕ) (hn : 4 ≤ n) (g : SemidihedralGroup n) (hg2 : g * g = 1)
    (hg1 : g ≠ 1) (hgz : g ≠ z n) (y : SemidihedralGroup n) (hy : y * g = g * y) :
    y = 1 ∨ y = z n ∨ y = g ∨ y = z n * g := by
  obtain ⟨q, hq⟩ := sd_involution_conj n hn g hg2 hg1 hgz
  have hzc : ∀ h : SemidihedralGroup n, h * z n = z n * h := fun h =>
    Subgroup.mem_center_iff.mp (z_mem_center n hn) h
  have hy' : (q⁻¹ * y * q) * s n = s n * (q⁻¹ * y * q) := by
    rw [← hq] at hy
    calc q⁻¹ * y * q * s n = q⁻¹ * (y * (q * s n * q⁻¹)) * q := by group
      _ = q⁻¹ * ((q * s n * q⁻¹) * y) * q := by rw [hy]
      _ = s n * (q⁻¹ * y * q) := by group
  have hyq : y = q * (q⁻¹ * y * q) * q⁻¹ := by group
  have hqz : q * z n * q⁻¹ = z n := by rw [hzc q, mul_inv_cancel_right]
  rcases sd_centralizer_s n hn _ hy' with h | h | h | h
  · left
    rw [hyq, h]
    group
  · right; left
    rw [hyq, h, hqz]
  · right; right; left
    rw [hyq, h, hq]
  · right; right; right
    rw [hyq, h]
    calc q * (z n * s n) * q⁻¹ = (q * z n * q⁻¹) * (q * s n * q⁻¹) := by group
      _ = z n * g := by rw [hqz, hq]

end Semidihedral

section Main

theorem dsd_assemble {M : Type} [Group M] (z : M) (hnab : ¬ ∀ a b : M, a * b = b * a) (m : ℕ)
    (hm : Nat.card M = 2 ^ m) (h9 : 8 < Nat.card M) (hD : DSDData M) (hCl : Cl3 z) :
    ∃ (A : Subgroup M) (ρ : M), IsCyclic ↥A ∧ ρ ∈ A ∧ orderOf ρ = 4 ∧ 8 ≤ Nat.card A ∧
      Nat.card M = 2 * Nat.card A ∧ (∀ s : M, s ∉ A → s * ρ * s⁻¹ = ρ⁻¹) ∧
      (∀ s : M, s ∉ A → orderOf s < Nat.card A) ∧ Cl3 z := by
  obtain ⟨A, u, hA, hu, hu4, hout, hinv⟩ := hD
  obtain ⟨y, hy⟩ : ∃ y : M, y ∉ A := by
    by_contra hno
    push Not at hno
    apply hnab
    intro a b
    exact congrArg Subtype.val ((hA.isMulCommutative).is_comm.comm ⟨a, hno a⟩ ⟨b, hno b⟩)
  have hmul : ∀ x w : M, x ∉ A → w ∉ A → x * w ∈ A := by
    intro x w hx hw
    by_contra hxw
    have h1 := hinv x hx
    have h2 := hinv w hw
    have h3 := hinv _ hxw
    have h4 : (x * w) * u * (x * w)⁻¹ = u := by
      calc (x * w) * u * (x * w)⁻¹ = x * (w * u * w⁻¹) * x⁻¹ := by group
        _ = x * u⁻¹ * x⁻¹ := by rw [h2]
        _ = (x * u * x⁻¹)⁻¹ := by group
        _ = u := by rw [h1, inv_inv]
    have h5 : u = u⁻¹ := h4.symm.trans h3
    have h6 : u * u = 1 := by
      nth_rewrite 1 [h5]
      exact inv_mul_cancel u
    have h7 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h6)
    rw [hu4] at h7
    omega
  have hidx : A.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨y, fun b => ?_⟩
    by_cases hb : b ∈ A
    · refine Or.inr ⟨hb, fun hby => hy ?_⟩
      have := A.mul_mem (A.inv_mem hb) hby
      simpa using this
    · exact Or.inl ⟨hmul b y hb hy, hb⟩
  have hcard : Nat.card M = 2 * Nat.card A := by
    have := A.card_mul_index
    rw [hidx] at this
    omega
  have hA8 : 8 ≤ Nat.card A := by
    have h16 : 16 ≤ Nat.card M := by
      by_contra hlt
      push Not at hlt
      rcases Nat.lt_or_ge m 4 with h | h
      · have : 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
        omega
    omega
  exact ⟨A, u, hA, hu, hu4, hA8, hcard, hinv, hout, hCl⟩

theorem dsd_of_small_centralizer {M : Type} [Group M] [Finite M] (hM : IsPGroup 2 M)
    (z t : M) (hzc : ∀ g : M, g * z = z * g) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ z)
    {E : Subgroup M} (hE2 : ∀ e ∈ E, e * e = 1) (hE4 : Nat.card E = 4)
    (h8 : 8 ≤ Nat.card M) (hnab : ¬ ∀ a b : M, a * b = b * a)
    (hC : Nat.card (Subgroup.centralizer ({t} : Set M)) ≤ 4) :
    Nat.card M = 8 ∨
      ∃ (A : Subgroup M) (ρ : M), IsCyclic ↥A ∧ ρ ∈ A ∧ orderOf ρ = 4 ∧ 8 ≤ Nat.card A ∧
        Nat.card M = 2 * Nat.card A ∧ (∀ s : M, s ∉ A → s * ρ * s⁻¹ = ρ⁻¹) ∧
        (∀ s : M, s ∉ A → orderOf s < Nat.card A) ∧ Cl3 z := by
  have _ : t * t = 1 ∧ t ≠ 1 ∧ t ≠ z := ⟨ht2, ht1, htz⟩
  by_cases hc8 : Nat.card M = 8
  · exact Or.inl hc8
  right
  have h8' : 2 ^ 3 ≤ Nat.card M := by simpa using h8
  have hC' : Nat.card (Subgroup.centralizer ({t} : Set M)) ≤ 2 ^ 2 := by simpa using hC
  obtain ⟨m, hm, hγ⟩ := CFSG.GH74.Uniqueness.SU.SU1.b_maximalClass_of_small_centralizer 2
    Nat.prime_two M hM h8' t hC'
  have h9 : 8 < Nat.card M := lt_of_le_of_ne h8 (Ne.symm hc8)
  rcases CFSG.GH74.Uniqueness.SU.SU1.b_two_maximalClass_shape M hM h9 m hm hγ with
    ⟨k, hk, ⟨e⟩⟩ | ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hNk : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
    have hcd : Nat.card M = 2 * 2 ^ k := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hk3 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : 4 ∣ 2 ^ k := by
      have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk3
      simpa using this
    have hez : e z = DihedralGroup.r ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) :=
      dih_central_involution hk3 (e z) (by rw [← map_mul, hz2, map_one])
        (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
        (fun h => by
          obtain ⟨g, rfl⟩ := e.surjective h
          rw [← map_mul, ← map_mul, hzc g])
    refine dsd_assemble z hnab m hm h9 (DSDData.congr e.symm (dsdData_dihedral (2 ^ k) h4))
      (Cl3.of_equiv e ?_)
    rw [hez]
    exact dih_cl3 hk3
  · exfalso
    have hNk : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
    have hfin : Finite ↥E := inferInstance
    obtain ⟨v, hv, w, hw, hv1, hw1, hvw⟩ :=
      exists_two_ne_one_aux (E := E) (by rw [hE4]; norm_num)
    have hq : ∀ x ∈ E, x ≠ 1 → e x = QuaternionGroup.a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) := by
      intro x hx hx1
      have h1 : e x * e x = 1 := by
        rw [← map_mul, hE2 x hx, map_one]
      rcases CFSG.GH74.GLS.Stage1.Thm3.Sec6.B.quat_invol (e x) h1 with h | h
      · exact absurd (e.injective (h.trans (map_one e).symm)) hx1
      · exact h
    exact hvw (e.injective ((hq v hv hv1).trans (hq w hw hw1).symm))
  · have hez : e z = CFSG.Semidihedral.z n :=
      sd_central_involution n hn (e z) (by rw [← map_mul, hz2, map_one])
        (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
        (fun h => by
          obtain ⟨g, rfl⟩ := e.surjective h
          rw [← map_mul, ← map_mul, hzc g])
    refine dsd_assemble z hnab m hm h9 (DSDData.congr e.symm (dsdData_semidihedral n hn))
      (Cl3.of_equiv e ?_)
    rw [hez]
    exact sd_cl3 n hn

theorem card_centralizer_le_four_of_model {M : Type} [Group M] [Finite M] (z t : M)
    (hzc : ∀ g : M, g * z = z * g) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ z) (h8 : 8 ≤ Nat.card M)
    (hmodel : (∃ m : ℕ, 1 ≤ m ∧ Nonempty (M ≃* DihedralGroup (2 ^ m))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (M ≃* CFSG.Open.SemidihedralGroup n)) :
    Nat.card (Subgroup.centralizer ({t} : Set M)) ≤ 4 := by
  rcases hmodel with ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hNm : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
    have hcd : Nat.card M = 2 * 2 ^ m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hm2 : 2 ≤ m := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hez : e z = DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) :=
      dih_central_involution hm2 (e z) (by rw [← map_mul, hz2, map_one])
        (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
        (fun h => by
          obtain ⟨g, rfl⟩ := e.surjective h
          rw [← map_mul, ← map_mul, hzc g])
    have het : orderOf (e t) = 2 :=
      orderOf_eq_prime (by rw [pow_two, ← map_mul, ht2, map_one])
        (fun h => ht1 (e.injective (h.trans (map_one e).symm)))
    rcases CFSG.GorensteinWalter.TwoClassFusion.eq_r_half_or_sr_of_orderOf_eq_two hm2 het with
      h | ⟨k, hk⟩
    · exact absurd (e.injective (h.trans hez.symm)) htz
    · refine card_centralizer_le_four_aux t 1 z t
        (e.symm (DihedralGroup.sr (k + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))))) ?_
      intro y hy
      have hcomm : DihedralGroup.sr k * e y = e y * DihedralGroup.sr k := by
        calc DihedralGroup.sr k * e y = e (t * y) := by rw [map_mul, hk]
          _ = e (y * t) := by rw [hy]
          _ = e y * DihedralGroup.sr k := by rw [map_mul, hk]
      rcases CFSG.GorensteinWalter.TwoClassFusion.eq_of_commute_sr hm2
        (show Commute (DihedralGroup.sr k) (e y) from hcomm) with h | h | h | h
      · exact Or.inl (e.injective (h.trans (map_one e).symm))
      · exact Or.inr (Or.inl (e.injective (h.trans hez.symm)))
      · exact Or.inr (Or.inr (Or.inl (e.injective (h.trans hk.symm))))
      · exact Or.inr (Or.inr (Or.inr (e.injective (h.trans (e.apply_symm_apply _).symm))))
  · have hez : e z = CFSG.Semidihedral.z n :=
      sd_central_involution n hn (e z) (by rw [← map_mul, hz2, map_one])
        (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
        (fun h => by
          obtain ⟨g, rfl⟩ := e.surjective h
          rw [← map_mul, ← map_mul, hzc g])
    have het2 : e t * e t = 1 := by rw [← map_mul, ht2, map_one]
    have het1 : e t ≠ 1 := fun h => ht1 (e.injective (h.trans (map_one e).symm))
    have hetz : e t ≠ CFSG.Semidihedral.z n := fun h => htz (e.injective (h.trans hez.symm))
    refine card_centralizer_le_four_aux t 1 z t (z * t) ?_
    intro y hy
    have hy' : e y * e t = e t * e y := by rw [← map_mul, ← map_mul, hy]
    rcases sd_centralizer_of_involution n hn (e t) het2 het1 hetz (e y) hy' with h | h | h | h
    · exact Or.inl (e.injective (h.trans (map_one e).symm))
    · exact Or.inr (Or.inl (e.injective (h.trans hez.symm)))
    · exact Or.inr (Or.inr (Or.inl (e.injective h)))
    · exact Or.inr (Or.inr (Or.inr (e.injective (by rw [h, map_mul, hez]))))

end Main

end CFSG.GH74.GLS.Th2.R714Dsd
