module

public import CFSG.GH74.GLS.SP.Local.SPLL33b
public import CFSG.GH74.GLS.SP.Local.SPLZStar
public import CFSG.GH74.GLS.SP.Local.SPLL33a

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section L33c

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem X_comm (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : ∀ x ∈ D.X, ∀ y ∈ D.X, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (X₁_X₂_comm D hs h3) hx
  obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute (X₁_X₂_comm D hs h3) hy
  have e1 : a * a' = a' * a := h3.X₁_eab.1 a ha a' ha'
  have e2 : b * b' = b' * b := (isEAb_conjBy h3.X₁_eab D.t).1 b hb b' hb'
  have e3 : a' * b = b * a' := X₁_X₂_comm D hs h3 a' ha' b hb
  have e4 : a * b' = b' * a := X₁_X₂_comm D hs h3 a ha b' hb'
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [← e3]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [e1, e2]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [e4]
    _ = a' * b' * (a * b) := by group

omit [Finite G] in
theorem Y₀_le_X : D.Y₀ ≤ D.X := inf_le_right

omit [Finite G] in
theorem Y₀_le_Ct : D.Y₀ ≤ D.Ct := inf_le_left

theorem Y₀_exp (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : ∀ y ∈ D.Y₀, y ^ D.p = 1 :=
  fun y hy => X_exp D hs h3 y (Y₀_le_X D hy)

omit [Finite G] in
theorem mem_C₀ {g : G} : g ∈ D.C₀ ↔ ∀ y ∈ D.Y₀, y * g = g * y :=
  mem_centralizer_iff

theorem X_le_C₀ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.X ≤ D.C₀ := fun x hx =>
  (mem_C₀ D).mpr (fun y hy => X_comm D hs h3 y (Y₀_le_X D hy) x hx)

theorem Y₀_le_C₀ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.Y₀ ≤ D.C₀ :=
  (Y₀_le_X D).trans (X_le_C₀ D hs h3)

omit [Finite G] in
theorem t_mem_C₀ : D.t ∈ D.C₀ := (mem_C₀ D).mpr (fun _ hy => mem_centralizer_singleton_iff.mp (Y₀_le_Ct D hy))

theorem z_mem_C₀ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.z ∈ D.C₀ :=
  (mem_C₀ D).mpr (fun y hy => (z_cen_K D hs y (X_le_K' D hs h3 (Y₀_le_X D hy))).symm)

theorem x2_mem_C₀ (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) :
    D.x ^ 2 ∈ D.C₀ :=
  (mem_C₀ D).mpr (fun y hy =>
    (hc.x2_cen y (Subgroup.mem_sup_left (Y₀_le_I D hs hc h3 hy))).symm)

theorem T0_le_C₀ (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) :
    D.T₀ ≤ D.C₀ := by
  refine sup_le ?_ ?_
  · rw [zpowers_le]; exact x2_mem_C₀ D hs hc h3
  · rw [zpowers_le]; exact z_mem_C₀ D hs h3

theorem A_le_C₀ (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) :
    D.A ≤ D.C₀ := fun a ha =>
  (mem_C₀ D).mpr (fun y hy => (hc.AI_comm a ha y (Y₀_le_I D hs hc h3 hy)).symm)

omit [Finite G] in
theorem A_le_Ct (hc : SPL2Ct D.toSPLNot2) : D.A ≤ D.Ct := by
  intro a ha
  rw [hc.A_eq] at ha
  obtain ⟨a', _, rfl⟩ := Subgroup.mem_map.mp ha
  exact a'.2

theorem Y₀_A_comm (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) :
    ∀ y ∈ D.Y₀, ∀ a ∈ D.A, y * a = a * y :=
  fun y hy a ha => (hc.AI_comm a ha y (Y₀_le_I D hs hc h3 hy)).symm

omit [Finite G] in
theorem e_odd (hs : SPLSetup D.toSPLNot0) : Odd D.e := by
  have hq := hs.odd_q
  have hd0 : D.d ≠ 0 := by
    unfold SPLNot0.d
    split_ifs with h
    · have := hs.q_ge; omega
    · omega
  have hcop := Nat.coprime_ordCompl Nat.prime_two hd0
  exact (Nat.coprime_two_left.mp hcop)

omit [Finite G] in
theorem e_coprime (hs : SPLSetup D.toSPLNot0) : Nat.Coprime D.e D.p := by
  have hp := hs.prime
  obtain ⟨k, hk1, hkq⟩ := hs.q_pow
  have hpq : D.p ∣ D.q := by rw [hkq]; exact dvd_pow_self _ (by omega)
  have hnd : ¬ D.p ∣ D.d := by
    intro hd
    unfold SPLNot0.d at hd
    have h2 := hp.two_le
    have hq5 := hs.q_ge
    split_ifs at hd with h
    · have h1 : D.p ∣ 1 := (Nat.dvd_add_right hd).mp (by rw [show D.q - 1 + 1 = D.q by omega]; exact hpq)
      exact absurd (Nat.le_of_dvd one_pos h1) (by omega)
    · have h1 : D.p ∣ 1 := (Nat.dvd_add_right hpq).mp hd
      exact absurd (Nat.le_of_dvd one_pos h1) (by omega)
  have hne : ¬ D.p ∣ D.e := by
    intro h
    exact hnd (h.trans (Nat.ordCompl_dvd D.d 2))
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hne).symm

theorem N_odd_order (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) :
    ∀ n ∈ D.Y₀ ⊔ D.A, Odd (orderOf n) := by
  intro n hn
  obtain ⟨y, hy, a, ha, rfl⟩ := mem_sup_of_commute (Y₀_A_comm D hs hc h3) hn
  have hpodd : Odd D.p := hs.prime.odd_of_ne_two hs.p_ne_two
  have heodd := e_odd D hs
  have hye : y ^ (D.p * D.e) = 1 := by
    rw [pow_mul, Y₀_exp D hs h3 y hy, one_pow]
  have hae : a ^ (D.p * D.e) = 1 := by
    have : orderOf a ∣ D.e := by
      have := Subgroup.orderOf_dvd_natCard D.A ha
      rwa [hc.A_card] at this
    rw [mul_comm, pow_mul]
    have h1 : a ^ D.e = 1 := orderOf_dvd_iff_pow_eq_one.mp this
    rw [h1, one_pow]
  have hcomm : Commute y a := Y₀_A_comm D hs hc h3 y hy a ha
  have h1 : (y * a) ^ (D.p * D.e) = 1 := by rw [hcomm.mul_pow, hye, hae, one_mul]
  exact (hpodd.mul heodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

theorem N_odd (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) :
    Odd (Nat.card ↥(D.Y₀ ⊔ D.A)) := by
  by_contra hcon
  have h2 : 2 ∣ Nat.card ↥(D.Y₀ ⊔ D.A) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hcon)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hg' : orderOf (g : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  have := N_odd_order D hs hc h3 g g.2
  rw [hg'] at this
  exact (Nat.not_odd_iff_even.mpr even_two) this

omit [Finite G] in
theorem eq_one_of_odd_of_mem_two_group {S : Subgroup G} (hS : IsPGroup 2 ↥S) {s : G} (hsS : s ∈ S)
    (hodd : Odd (orderOf s)) : s = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨s, hsS⟩
  have hk' : s ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hdvd : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hodd
    have : Even (2 ^ i) := Nat.even_pow.mpr ⟨even_two, hne⟩
    exact (Nat.not_odd_iff_even.mpr this) hodd
  rw [hi0, pow_zero] at hi
  exact orderOf_eq_one_iff.mp hi

theorem T0_sylow_Q (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D)
    (S : Subgroup G) (hSC : S ≤ D.C₀) (hS2 : IsPGroup 2 ↥S) (hTS : D.T₀ ≤ S)
    (hSt : ∀ s ∈ S, s * D.t = D.t * s) : S = D.T₀ := by
  refine le_antisymm ?_ hTS
  intro s hsS
  have hsC : s ∈ D.Ct := mem_centralizer_singleton_iff.mpr (hSt s hsS)
  have hs0 : ∀ y ∈ D.Y₀, s * y = y * s := fun y hy => ((mem_C₀ D).mp (hSC hsS) y hy).symm
  obtain ⟨y, hy, a, ha, s₀, hs₀, hdec⟩ := Q_decomp D hs hc h3 hsC hs0
  have hn : y * a = s * s₀⁻¹ := by
    calc y * a = (y * (a * s₀)) * s₀⁻¹ := by group
      _ = s * s₀⁻¹ := by rw [← hdec]
  have hnS : y * a ∈ S := by
    rw [hn]; exact Subgroup.mul_mem _ hsS (Subgroup.inv_mem _ (hTS hs₀))
  have hnN : y * a ∈ D.Y₀ ⊔ D.A :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ha)
  have hn1 : y * a = 1 :=
    eq_one_of_odd_of_mem_two_group hS2 hnS (N_odd_order D hs hc h3 _ hnN)
  have : s = s₀ := by
    have h2 : s * s₀⁻¹ = 1 := by rw [← hn]; exact hn1
    exact mul_inv_eq_one.mp h2
  rw [this]
  exact hs₀

theorem exists_V₀ (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) :
    ∃ V : Subgroup G, V ≤ D.C₀ ∧ (∀ g ∈ D.C₀, ∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧ Odd (Nat.card ↥V) ∧
      (D.Y₀ ⊔ D.A ≤ V) ∧ (∀ g ∈ D.C₀, Odd (orderOf g) → g ∈ V) ∧
      (∀ g ∈ D.C₀, ∃ v ∈ V, ∃ s ∈ D.T₀, g = v * s) := by
  have htt := t_mul_t D hs
  have hT0C := T0_le_C₀ D hs hc h3
  have hT02 := T0_pgroup D hs hc
  have htT := t_mem_T0 D hs hc
  have hTt := T0_comm_t D hs hc
  have hmax : ∀ S : Subgroup G, S ≤ D.C₀ → IsPGroup 2 ↥S → D.T₀ ≤ S → S = D.T₀ :=
    sylow2_of_isolated D.C₀ D.T₀ D.t D.z hT0C hT02 htT htt hTt
      (fun S hSC hS2 hTS hSt => T0_sylow_Q D hs hc h3 S hSC hS2 hTS hSt)
      (fun s hsT hs2 hst hs1 => T0_inv_conj D hs hc hsT hs2 hst hs1) hs.syl.t_nconj
  have ht1 : D.t ≠ 1 := by
    intro h
    have := hs.syl.t_ord
    rw [h, orderOf_one] at this
    omega
  have hweak : ∀ g ∈ D.C₀, g⁻¹ * D.t * g ∈ D.T₀ → g⁻¹ * D.t * g = D.t := by
    intro g _ hg
    by_contra hne
    have hu2 : (g⁻¹ * D.t * g) * (g⁻¹ * D.t * g) = 1 := by
      calc (g⁻¹ * D.t * g) * (g⁻¹ * D.t * g) = g⁻¹ * (D.t * D.t) * g := by group
        _ = 1 := by rw [htt]; group
    have hu1 : g⁻¹ * D.t * g ≠ 1 := by
      intro h
      apply ht1
      calc D.t = g * (g⁻¹ * D.t * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hconj := T0_inv_conj D hs hc hg hu2 hne hu1
    have htconj : IsConj D.t (g⁻¹ * D.t * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
    exact hs.syl.t_nconj (hconj.trans htconj.symm)
  have hNt : ∀ n ∈ D.Y₀ ⊔ D.A, n * D.t = D.t * n := by
    intro n hn
    obtain ⟨y, hy, a, ha, rfl⟩ := mem_sup_of_commute (Y₀_A_comm D hs hc h3) hn
    have h1 : y * D.t = D.t * y := mem_centralizer_singleton_iff.mp (Y₀_le_Ct D hy)
    have h2 : a * D.t = D.t * a := mem_centralizer_singleton_iff.mp (A_le_Ct D hc ha)
    calc y * a * D.t = y * (a * D.t) := by group
      _ = y * (D.t * a) := by rw [h2]
      _ = (y * D.t) * a := by group
      _ = (D.t * y) * a := by rw [h1]
      _ = D.t * (y * a) := by group
  have hNnorm : ∀ q ∈ D.C₀, q * D.t = D.t * q → ∀ n ∈ D.Y₀ ⊔ D.A, q * n * q⁻¹ ∈ D.Y₀ ⊔ D.A := by
    intro q hqC hqt n hn
    have hqCt : q ∈ D.Ct := mem_centralizer_singleton_iff.mpr hqt
    obtain ⟨y, hy, a, ha, rfl⟩ := mem_sup_of_commute (Y₀_A_comm D hs hc h3) hn
    have hqy : q * y * q⁻¹ = y := by
      have := (mem_C₀ D).mp hqC y hy
      calc q * y * q⁻¹ = (y * q) * q⁻¹ := by rw [this]
        _ = y := by group
    have hqa : q * a * q⁻¹ ∈ D.A := A_norm_Ct D hc q hqCt a ha
    have e : q * (y * a) * q⁻¹ = (q * y * q⁻¹) * (q * a * q⁻¹) := by group
    rw [e, hqy]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hqa)
  have hQ : ∀ q ∈ D.C₀, q * D.t = D.t * q → ∃ n ∈ D.Y₀ ⊔ D.A, ∃ s ∈ D.T₀, q = n * s := by
    intro q hqC hqt
    have hqCt : q ∈ D.Ct := mem_centralizer_singleton_iff.mpr hqt
    have hq0 : ∀ y ∈ D.Y₀, q * y = y * q := fun y hy => ((mem_C₀ D).mp hqC y hy).symm
    obtain ⟨y, hy, a, ha, s, hsT, hdec⟩ := Q_decomp D hs hc h3 hqCt hq0
    refine ⟨y * a, Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ha), s, hsT, ?_⟩
    rw [hdec]; group
  have hNC : D.Y₀ ⊔ D.A ≤ D.C₀ := sup_le (Y₀_le_C₀ D hs h3) (A_le_C₀ D hs hc h3)
  obtain ⟨V, hVC, hVn, hVodd, hNV, hVall, hVT⟩ :=
    normal_twoComplement_of_zstar D.C₀ D.T₀ D.t hT0C hT02 hmax htT hs.syl.t_ord hTt hweak
      (D.Y₀ ⊔ D.A) hNC hNt (N_odd D hs hc h3) hNnorm hQ
  exact ⟨V, hVC, hVn, hVodd, hNV, hVall, hVT⟩

end L33c

end CFSG.GH74.GLS.SP.Local
