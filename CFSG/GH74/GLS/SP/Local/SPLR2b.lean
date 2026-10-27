module

public import CFSG.GH74.GLS.SP.Local.SPLR2Defs
public import CFSG.GH74.GLS.SP.Local.SPLM2b

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section PowComm

variable {G : Type} [Group G]

theorem comm_pow_of_comm {q y : G} (hq : ⁅q, y⁆ * q = q * ⁅q, y⁆) (m : ℕ) :
    ⁅q ^ m, y⁆ = ⁅q, y⁆ ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcm : ⁅q, y⁆ ^ m * q = q * ⁅q, y⁆ ^ m := (Commute.pow_left hq m)
    have e : q ^ (m + 1) * y * (q ^ (m + 1))⁻¹ * y⁻¹ =
        q * (q ^ m * y * (q ^ m)⁻¹ * y⁻¹ * y) * q⁻¹ * y⁻¹ := by
      rw [pow_succ']; group
    have h2 : q ^ m * y * (q ^ m)⁻¹ * y⁻¹ = ⁅q, y⁆ ^ m := by
      have := ih
      simpa [commutatorElement_def] using this
    show q ^ (m + 1) * y * (q ^ (m + 1))⁻¹ * y⁻¹ = ⁅q, y⁆ ^ (m + 1)
    rw [e, h2]
    have h3 : q * (⁅q, y⁆ ^ m * y) * q⁻¹ * y⁻¹ = ⁅q, y⁆ ^ m * ⁅q, y⁆ := by
      calc q * (⁅q, y⁆ ^ m * y) * q⁻¹ * y⁻¹ = (q * ⁅q, y⁆ ^ m * q⁻¹) * (q * y * q⁻¹ * y⁻¹) := by group
        _ = ⁅q, y⁆ ^ m * ⁅q, y⁆ := by
          rw [show q * ⁅q, y⁆ ^ m * q⁻¹ = ⁅q, y⁆ ^ m by rw [← hcm]; group]
          rfl
    rw [h3, pow_succ]

end PowComm

section Block

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem V₂_le_C₂ : D.V₂ ≤ D.C₂ := by
  unfold SPLNot3.V₂ pPrimeCoreOf
  exact Subgroup.map_subtype_le _

omit [Finite G] in
theorem V₂_comm_X₂ {v : G} (hv : v ∈ D.V₂) {x : G} (hx : x ∈ D.X₂) : x * v = v * x :=
  mem_centralizer_iff.mp (V₂_le_C₂ D hv) x hx

omit [Finite G] in
theorem X₂_exp (h3 : SPL3X D) : ∀ x ∈ D.X₂, x ^ D.p = 1 :=
  (isEAb_conjBy h3.X₁_eab D.t).2

omit [Finite G] in
theorem pprime_comm (h3 : SPL3X D) (hRA : R2A D) {u : G} (hu : u ∈ D.V₂) {m : ℕ}
    (hm : Nat.Coprime m D.p) (hum : u ^ m = 1) {v : G} (hv : v ∈ D.V₂) : u * v = v * u := by
  have hc : ⁅u, v⁆ ∈ D.X₂ := hRA.V₂_class2 u hu v hv
  have hcu : ⁅u, v⁆ * u = u * ⁅u, v⁆ := V₂_comm_X₂ D hu hc
  have h1 := comm_pow_of_comm hcu m
  rw [hum] at h1
  have h2 : ⁅u, v⁆ ^ m = 1 := by rw [← h1]; simp
  have h3' : ⁅u, v⁆ ^ D.p = 1 := X₂_exp D h3 _ hc
  have hord : orderOf ⁅u, v⁆ = 1 := by
    have d1 := orderOf_dvd_of_pow_eq_one h2
    have d2 := orderOf_dvd_of_pow_eq_one h3'
    have := Nat.dvd_gcd d1 d2
    rw [hm.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  exact commutatorElement_eq_one_iff_mul_comm.mp (orderOf_eq_one_iff.mp hord)

omit [Finite G] in
theorem odd_orderOf_of_mem_V₂ (hRA : R2A D) {u : G} (hu : u ∈ D.V₂) : Odd (orderOf u) :=
  Odd.of_dvd_nat hRA.V₂_odd (Subgroup.orderOf_dvd_natCard D.V₂ hu)

theorem pprime_triv (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) (hA : SPL3Aa D) (hRA : R2A D)
    (hX3 : D.X₃ ≤ D.V₂) (hD2 : L34Concl D) {u : G} (hu : u ∈ D.V₂) {m : ℕ}
    (hm : Nat.Coprime m D.p) (hum : u ^ m = 1) : u = 1 := by
  classical
  obtain ⟨V, hVC, hVN, hVodd, ⟨k, hVk⟩, hVcomm⟩ := hD2
  have hoddu := odd_orderOf_of_mem_V₂ D hRA hu
  have hcomm_y : ∀ y ∈ D.X₃, u * y = y * u := fun y hy =>
    pprime_comm D h3 hRA hu hm hum (hX3 hy)
  have hgC : D.a * u * D.a⁻¹ ∈ centralizer (D.Y₁ : Set G) := by
    rw [mem_centralizer_iff]
    intro y₁ hy₁
    have hx : D.a⁻¹ * y₁ * D.a ∈ D.X₃ := by
      show _ ∈ conjBy D.a D.Y₁
      rw [mem_conjBy_iff]
      have e : D.a * (D.a⁻¹ * y₁ * D.a) * D.a⁻¹ = y₁ := by group
      rw [e]; exact hy₁
    have := hcomm_y _ hx
    calc y₁ * (D.a * u * D.a⁻¹) = D.a * ((D.a⁻¹ * y₁ * D.a) * u) * D.a⁻¹ := by group
      _ = D.a * (u * (D.a⁻¹ * y₁ * D.a)) * D.a⁻¹ := by rw [this]
      _ = (D.a * u * D.a⁻¹) * y₁ := by group
  have hgV : D.a * u * D.a⁻¹ ∈ V := by
    set C₁ : Subgroup G := centralizer (D.Y₁ : Set G) with hC₁
    have hcardQ : Nat.card (↥C₁ ⧸ V.subgroupOf C₁) = 2 ^ k := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf C₁)
      have h2 : Nat.card ↥(V.subgroupOf C₁) = Nat.card ↥V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv
      rw [h2, hVk] at h1
      have hpos : 0 < Nat.card ↥V := Nat.card_pos
      exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
    set gbar : ↥C₁ ⧸ V.subgroupOf C₁ := QuotientGroup.mk ⟨D.a * u * D.a⁻¹, hgC⟩ with hgbar
    have h1 : gbar ^ (orderOf u) = 1 := by
      rw [hgbar, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      have : ((⟨D.a * u * D.a⁻¹, hgC⟩ : ↥C₁) ^ orderOf u : ↥C₁) = 1 := by
        apply Subtype.ext
        show (D.a * u * D.a⁻¹) ^ orderOf u = 1
        rw [conj_pow, pow_orderOf_eq_one]; group
      rw [this]; exact Subgroup.one_mem _
    have h2 : gbar ^ (2 ^ k) = 1 := by
      rw [← hcardQ]; exact pow_card_eq_one'
    have hcop2 : Nat.Coprime (orderOf u) 2 := by
      have : ¬ 2 ∣ orderOf u := by rcases hoddu with ⟨j, hj⟩; omega
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr this).symm
    have hcop : Nat.Coprime (orderOf u) (2 ^ k) := Nat.Coprime.pow_right k hcop2
    have hord : orderOf gbar = 1 := by
      have d1 := orderOf_dvd_of_pow_eq_one h1
      have d2 := orderOf_dvd_of_pow_eq_one h2
      have := Nat.dvd_gcd d1 d2
      rw [hcop.gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    have : gbar = 1 := orderOf_eq_one_iff.mp hord
    rw [hgbar, QuotientGroup.eq_one_iff] at this
    exact this
  have hzmem : D.z ∈ D.C₂ := hRA.z_mem_C₂
  have hcomm_mem : ⁅D.a * u * D.a⁻¹, D.z * D.t⁆ ∈ D.Y₁ := by
    rw [← hVcomm]
    exact Subgroup.commutator_mem_commutator hgV (Subgroup.mem_zpowers _)
  have haz := a_z_conj D hs hA
  have hX3mem : ⁅u, D.z⁆ ∈ D.X₃ := by
    show _ ∈ conjBy D.a D.Y₁
    rw [mem_conjBy_iff]
    have e : D.a * ⁅u, D.z⁆ * D.a⁻¹ = ⁅D.a * u * D.a⁻¹, D.a * D.z * D.a⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, haz]
    exact hcomm_mem
  have hr : D.z * u * D.z⁻¹ ∈ D.V₂ := hRA.V₂_norm D.z hzmem u hu
  have hrm : (D.z * u * D.z⁻¹) ^ m = 1 := by rw [conj_pow, hum]; group
  have hur : u * (D.z * u * D.z⁻¹) = (D.z * u * D.z⁻¹) * u := pprime_comm D h3 hRA hu hm hum hr
  have hc1 : ⁅u, D.z⁆ = u * (D.z * u * D.z⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
  have hc2 : ⁅u, D.z⁆ ^ m = 1 := by
    rw [hc1]
    have hcm : Commute u (D.z * u * D.z⁻¹)⁻¹ := (show Commute u (D.z * u * D.z⁻¹) from hur).inv_right
    rw [hcm.mul_pow, inv_pow, hrm, hum]; simp
  have hc3 : ⁅u, D.z⁆ ^ D.p = 1 := ((isEAb_conjBy h3.Y₁_eab D.a).2 _ hX3mem)
  have hc4 : ⁅u, D.z⁆ = 1 := by
    have d1 := orderOf_dvd_of_pow_eq_one hc2
    have d2 := orderOf_dvd_of_pow_eq_one hc3
    have := Nat.dvd_gcd d1 d2
    rw [hm.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  have hzu : D.z * u * D.z⁻¹ = u := by
    have := commutatorElement_eq_one_iff_mul_comm.mp hc4
    calc D.z * u * D.z⁻¹ = (u * D.z) * D.z⁻¹ := by rw [← this]
      _ = u := by group
  have huu : u * u ∈ D.X₂ := by
    have := hRA.z_inv_mod u hu
    rw [hzu] at this; exact this
  have huu1 : u * u = 1 := by
    have e1 : (u * u) ^ m = 1 := by
      have : (u * u) ^ m = u ^ m * u ^ m := by rw [← pow_two, ← pow_mul, mul_comm, pow_mul, pow_two]
      rw [this, hum]; simp
    have e2 := X₂_exp D h3 _ huu
    have d1 := orderOf_dvd_of_pow_eq_one e1
    have d2 := orderOf_dvd_of_pow_eq_one e2
    have := Nat.dvd_gcd d1 d2
    rw [hm.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  have hord2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact huu1)
  have : orderOf u = 1 := by
    rcases hoddu with ⟨j, hj⟩
    have := Nat.le_of_dvd (by norm_num) hord2
    omega
  exact orderOf_eq_one_iff.mp this


omit [Finite G] in
theorem X₃_exp' (h3 : SPL3X D) : ∀ x ∈ D.X₃, x ^ D.p = 1 :=
  (isEAb_conjBy h3.Y₁_eab D.a).2

theorem X₃_le_V₂ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) (hA : SPL3Aa D) (hRA : R2A D)
    (hD1 : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x) : D.X₃ ≤ D.V₂ := by
  intro y hy
  have hC2 : y ∈ D.C₂ := mem_centralizer_iff.mpr fun x hx => hD1 x (Subgroup.mem_sup_right hx) y hy
  have hzy := z_inv_X₃ D hs h3 hA y hy
  have hcomm : ⁅y, D.z⁆ = y * y := by
    have h2 : D.z * y⁻¹ * D.z⁻¹ = y := by
      have : D.z * y⁻¹ * D.z⁻¹ = (D.z * y * D.z⁻¹)⁻¹ := by group
      rw [this, hzy, inv_inv]
    calc ⁅y, D.z⁆ = y * (D.z * y⁻¹ * D.z⁻¹) := by simp only [commutatorElement_def]; group
      _ = y * y := by rw [h2]
  have hyy : y * y ∈ D.V₂ := by rw [← hcomm]; exact hRA.z_cen_mod y hC2
  have hpodd : Odd D.p := hs.prime.odd_of_ne_two hs.p_ne_two
  obtain ⟨j, hj⟩ := hpodd
  have hyp := X₃_exp' D h3 y hy
  have : y = (y * y) ^ (j + 1) := by
    rw [← pow_two, ← pow_mul]
    have e : y ^ (2 * (j + 1)) = y ^ D.p * y := by
      rw [show 2 * (j + 1) = D.p + 1 by omega, pow_succ]
    rw [e, hyp, one_mul]
  rw [this]
  exact D.V₂.pow_mem hyy _

omit [Finite G] in
theorem X₄_le_V₂ (h1 : SPL2Set D.toSPLNot1) (hRA : R2A D) (hX3 : D.X₃ ≤ D.V₂) : D.X₄ ≤ D.V₂ := by
  intro y hy
  have hy' : D.w₁ * y * D.w₁⁻¹ ∈ D.X₃ := mem_conjBy_iff.mp hy
  have hw : D.w₁⁻¹ ∈ D.C₂ := D.C₂.inv_mem (hRA.K₁_le_C₂ h1.w₁_mem)
  have := hRA.V₂_norm _ hw _ (hX3 hy')
  have e : D.w₁⁻¹ * (D.w₁ * y * D.w₁⁻¹) * D.w₁⁻¹⁻¹ = y := by group
  rwa [e] at this

theorem V₂_pgroup (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) (hA : SPL3Aa D) (hRA : R2A D)
    (hX3 : D.X₃ ≤ D.V₂) (hD2 : L34Concl D) : IsPGroup D.p ↥D.V₂ := by
  have hp := hs.prime
  have : Fact D.p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  by_contra hcon
  push Not at hcon
  have hne : orderOf g ≠ 0 := orderOf_pos g |>.ne'
  have hex : ∃ ℓ, ℓ.Prime ∧ ℓ ∣ orderOf g ∧ ℓ ≠ D.p := by
    by_contra hall
    push Not at hall
    have := Nat.eq_prime_pow_of_unique_prime_dvd hne (p := D.p) (fun {d} hd hdv => hall d hd hdv)
    exact hcon _ this
  obtain ⟨ℓ, hℓ, hℓd, hℓp⟩ := hex
  set u : ↥D.V₂ := g ^ (orderOf g / ℓ) with hu
  have hou : orderOf u = ℓ := by
    rw [hu]; exact orderOf_pow_orderOf_div hne hℓd
  have hcop : Nat.Coprime ℓ D.p := (Nat.coprime_primes hℓ hp).mpr hℓp
  have hu1 : (u : G) = 1 := pprime_triv D hs h3 hA hRA hX3 hD2 u.2 hcop (by
    have := pow_orderOf_eq_one u
    rw [hou] at this
    have := congrArg Subtype.val this
    simpa using this)
  have : u = 1 := Subtype.ext hu1
  rw [this, orderOf_one] at hou
  exact hℓ.one_lt.ne hou

theorem r2B_of_inputs (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D)
    (hA : SPL3Aa D) (hRA : R2A D) (hD1 : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x)
    (hD2 : L34Concl D) : R2B D := by
  have hX3 := X₃_le_V₂ D hs h3 hA hRA hD1
  exact ⟨hX3, X₄_le_V₂ D h1 hRA hX3, V₂_pgroup D hs h3 hA hRA hX3 hD2⟩

end Block


end CFSG.GH74.GLS.SP.Local
