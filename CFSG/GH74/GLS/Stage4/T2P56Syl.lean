module

public import CFSG.GH74.GLS.Stage4.T2P56bSyl
public import CFSG.GH74.GLS.Stage4.T2P56LayerDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def TwoElt {G : Type*} [Group G] (x : G) : Prop := ∃ k : ℕ, x ^ (2 ^ k) = 1

section TwoElt

variable {G : Type*} [Group G]

theorem TwoElt.one : TwoElt (1 : G) := ⟨0, by simp⟩

theorem TwoElt.mono {x : G} (h : TwoElt x) : ∀ j : ℕ, ∃ k, j ≤ k ∧ x ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := h
  intro j
  refine ⟨max j k, le_max_left _ _, ?_⟩
  have : 2 ^ max j k = 2 ^ k * 2 ^ (max j k - k) := by
    rw [← pow_add]; congr 1; omega
  rw [this, pow_mul, hk, one_pow]

theorem TwoElt.mul {x y : G} (hxy : x * y = y * x) (hx : TwoElt x) (hy : TwoElt y) : TwoElt (x * y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  obtain ⟨m, hkm, hxm⟩ := TwoElt.mono ⟨k, hk⟩ l
  obtain ⟨m', hlm, hym⟩ := TwoElt.mono ⟨l, hl⟩ m
  refine ⟨max m m', ?_⟩
  have hcomm : Commute x y := hxy
  rw [hcomm.mul_pow]
  have h1 : x ^ (2 ^ max m m') = 1 := by
    have : 2 ^ max m m' = 2 ^ m * 2 ^ (max m m' - m) := by
      rw [← pow_add]; congr 1; omega
    rw [this, pow_mul, hxm, one_pow]
  have h2 : y ^ (2 ^ max m m') = 1 := by
    have : 2 ^ max m m' = 2 ^ m' * 2 ^ (max m m' - m') := by
      rw [← pow_add]; congr 1; omega
    rw [this, pow_mul, hym, one_pow]
  rw [h1, h2, one_mul]

theorem TwoElt.inv {x : G} (hx : TwoElt x) : TwoElt x⁻¹ := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [inv_pow, hk, inv_one]⟩

theorem TwoElt.conj {x : G} (hx : TwoElt x) (g : G) : TwoElt (g * x * g⁻¹) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [conj_pow, hk]; group⟩

theorem TwoElt.of_sq_eq_one {x : G} (h : x * x = 1) : TwoElt x := ⟨1, by rw [pow_one, pow_two]; exact h⟩

theorem TwoElt.eq_one_of_odd {x : G} (hx : TwoElt x) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hx
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact orderOf_eq_one_iff.1 (by simpa using hi)
  · exfalso
    have h4 : 2 ∣ orderOf x := by rw [hi]; exact dvd_pow_self 2 hi0.ne'
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h4)

end TwoElt

section Cent

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

omit [Finite G] in
theorem twoElt_mem_residual {g : G} (hgz : g * z = z * g) (hg2 : TwoElt g) :
    g ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
  rw [t2C_oPrimeResidualOf_eq_closure]
  exact Subgroup.subset_closure ⟨Subgroup.mem_centralizer_singleton_iff.2 hgz, hg2⟩

theorem twoElt_cent_mem_H
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5 N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) {y : G} (hyH : y ∈ N.H) (hy2 : y * y ≠ 1) {g : G} (hgy : g * y = y * g)
    (hgz : g * N.z = N.z * g) (hgu : g * u = u * g) (hg2 : TwoElt g) : g ∈ N.H := by
  have hgC : g ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) := twoElt_mem_residual hgz hg2
  obtain ⟨hw₀sq, hw₀H, hY1⟩ := t2Ctx_Y1 hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  rcases hY1 g hgC hgu with hgH | ⟨x, hxH, hgx⟩
  · exact hgH
  · exfalso
    have hw : (N.w₁ * N.w₂) * y * (N.w₁ * N.w₂)⁻¹ = y⁻¹ := hLoc.w₀_inv y hyH
    have hxc : x * y⁻¹ = y⁻¹ * x := hLoc.H_comm x hxH y⁻¹ (N.H.inv_mem hyH)
    have h1 : g * y * g⁻¹ = y⁻¹ := by
      rw [hgx]
      calc x * (N.w₁ * N.w₂) * y * (x * (N.w₁ * N.w₂))⁻¹
          = x * ((N.w₁ * N.w₂) * y * (N.w₁ * N.w₂)⁻¹) * x⁻¹ := by group
        _ = x * y⁻¹ * x⁻¹ := by rw [hw]
        _ = y⁻¹ := by rw [hxc]; group
    have h2 : g * y * g⁻¹ = y := by rw [hgy]; group
    have h3 : y = y⁻¹ := h2.symm.trans h1
    apply hy2
    calc y * y = y * y⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel y

end Cent

section Mod3

variable {G : Type} [Group G]

theorem twoElt_mem_zpowers_of_sup [Finite G] {H H₁ H₂ : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (h₁ : H₁ ≤ H) (h₂ : H₂ ≤ H)
    (hcyc₁ : IsCyclic ↥H₁) (hcyc₂ : IsCyclic ↥H₂) {k₁ k₂ : ℕ} (hk₁ : Odd k₁) (hk₂ : Odd k₂)
    (hc₁ : Nat.card ↥H₁ = 2 * k₁) (hc₂ : Nat.card ↥H₂ = 2 * k₂) {z : G} (hzH₁ : z ∈ H₁)
    (hzH₂ : z ∈ H₂) (hz2 : z * z = 1) (hz1 : z ≠ 1) {x : G} (hx : x ∈ H₁ ⊔ H₂) (hx2 : TwoElt x) :
    x ∈ Subgroup.zpowers z := by
  obtain ⟨Q₁, hQ₁H, -, hQ₁odd, hQ₁dec, -⟩ :=
    t2H_cyclic_even_part H₁ hcyc₁ k₁ hk₁ hc₁ z hzH₁ hz2 hz1
  obtain ⟨Q₂, hQ₂H, -, hQ₂odd, hQ₂dec, -⟩ :=
    t2H_cyclic_even_part H₂ hcyc₂ k₂ hk₂ hc₂ z hzH₂ hz2 hz1
  have hcomm12 : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a := fun a ha b hb => hc a (h₁ ha) b (h₂ hb)
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := (mem_sup_iff_of_comm hcomm12 x).1 hx
  obtain ⟨c₁, hc₁z, b₁, hb₁, rfl⟩ := hQ₁dec a₁ ha₁
  obtain ⟨c₂, hc₂z, b₂, hb₂, rfl⟩ := hQ₂dec a₂ ha₂
  have hzH : z ∈ H := h₁ hzH₁
  have hzpH : Subgroup.zpowers z ≤ H := Subgroup.zpowers_le.2 hzH
  have hc₁H : c₁ ∈ H := hzpH hc₁z
  have hc₂H : c₂ ∈ H := hzpH hc₂z
  have hb₁H : b₁ ∈ H := h₁ (hQ₁H hb₁)
  have hb₂H : b₂ ∈ H := h₂ (hQ₂H hb₂)
  have hcc₂ : (c₁ * c₂) ∈ Subgroup.zpowers z := Subgroup.mul_mem _ hc₁z hc₂z
  have hbb : Commute b₁ b₂ := hc b₁ hb₁H b₂ hb₂H
  have hbodd : Odd (orderOf (b₁ * b₂)) := by
    have h1 : orderOf (b₁ * b₂) ∣ Nat.lcm (orderOf b₁) (orderOf b₂) := hbb.orderOf_mul_dvd_lcm
    exact Odd.of_dvd_nat (Odd.mul (hQ₁odd b₁ hb₁) (hQ₂odd b₂ hb₂))
      (h1.trans (Nat.lcm_dvd_mul _ _))
  have hcsq : (c₁ * c₂) * (c₁ * c₂) = 1 := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hcc₂
    have : (c₁ * c₂) * (c₁ * c₂) = z ^ n * z ^ n := by rw [hn]
    rw [this, ← zpow_add]
    have h2 : z ^ (n + n) = 1 := by
      have e : n + n = 2 * n := by ring
      rw [e, zpow_mul, zpow_two, hz2, one_zpow]
    exact h2
  have hxe : c₁ * b₁ * (c₂ * b₂) = (c₁ * c₂) * (b₁ * b₂) := by
    have hcb : Commute c₂ b₁ := hc c₂ hc₂H b₁ hb₁H
    calc c₁ * b₁ * (c₂ * b₂) = c₁ * (b₁ * c₂) * b₂ := by group
      _ = c₁ * (c₂ * b₁) * b₂ := by rw [hcb.symm.eq]
      _ = (c₁ * c₂) * (b₁ * b₂) := by group
  rw [hxe] at hx2 ⊢
  have hcbc : Commute (c₁ * c₂) (b₁ * b₂) := by
    have hc₁₂H : c₁ * c₂ ∈ H := H.mul_mem hc₁H hc₂H
    exact hc _ hc₁₂H _ (H.mul_mem hb₁H hb₂H)
  have hbtwo : TwoElt ((c₁ * c₂)⁻¹ * ((c₁ * c₂) * (b₁ * b₂))) := by
    refine TwoElt.mul ?_ (TwoElt.inv (TwoElt.of_sq_eq_one hcsq)) hx2
    have : (c₁ * c₂)⁻¹ * ((c₁ * c₂) * (b₁ * b₂)) = b₁ * b₂ := by group
    have hc₁₂H : c₁ * c₂ ∈ H := H.mul_mem hc₁H hc₂H
    have hbbH : b₁ * b₂ ∈ H := H.mul_mem hb₁H hb₂H
    have h1 := hc _ (H.inv_mem hc₁₂H) _ (H.mul_mem hc₁₂H hbbH)
    exact h1
  have hb1 : (c₁ * c₂)⁻¹ * ((c₁ * c₂) * (b₁ * b₂)) = b₁ * b₂ := by group
  rw [hb1] at hbtwo
  have hb : b₁ * b₂ = 1 := hbtwo.eq_one_of_odd hbodd
  rw [hb, mul_one]
  exact hcc₂

theorem twoElt_mem_U [Finite G] {H H₁ H₂ : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (h₁ : H₁ ≤ H) (h₂ : H₂ ≤ H)
    (hcyc₁ : IsCyclic ↥H₁) (hcyc₂ : IsCyclic ↥H₂) {k₁ k₂ : ℕ} (hk₁ : Odd k₁) (hk₂ : Odd k₂)
    (hc₁ : Nat.card ↥H₁ = 2 * k₁) (hc₂ : Nat.card ↥H₂ = 2 * k₂)
    (hidx : (H₁ ⊔ H₂).relIndex H = 2) {z u : G} (hzH₁ : z ∈ H₁) (hzH₂ : z ∈ H₂)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (huH : u ∈ H) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    {x : G} (hx : x ∈ H) (hx2 : TwoElt x) : x ∈ t2U z u := by
  have hM2 : ∀ x ∈ H₁ ⊔ H₂, TwoElt x → x ∈ Subgroup.zpowers z := fun x hx hx2 =>
    twoElt_mem_zpowers_of_sup hc h₁ h₂ hcyc₁ hcyc₂ hk₁ hk₂ hc₁ hc₂ hzH₁ hzH₂ hz2 hz1 hx hx2
  have hzU : z ∈ t2U z u := Subgroup.subset_closure (by simp)
  have huU : u ∈ t2U z u := Subgroup.subset_closure (by simp)
  have hzpU : Subgroup.zpowers z ≤ t2U z u := Subgroup.zpowers_le.2 hzU
  have huM : u ∉ H₁ ⊔ H₂ := by
    intro hu
    have h1 := hM2 u hu (TwoElt.of_sq_eq_one hu2)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
    rcases t2H_zpow_invol hz2 n with h | h
    · exact hu1 (hn.symm.trans h)
    · exact huz (hn.symm.trans h)
  by_cases hxM : x ∈ H₁ ⊔ H₂
  · exact hzpU (hM2 x hxM hx2)
  · have hidx' : ((H₁ ⊔ H₂).subgroupOf H).index = 2 := hidx
    have hxuM : x * u ∈ H₁ ⊔ H₂ := by
      have : (⟨x, hx⟩ : ↥H) * ⟨u, huH⟩ ∈ (H₁ ⊔ H₂).subgroupOf H := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx']
        exact iff_of_false (by rwa [Subgroup.mem_subgroupOf]) (by rwa [Subgroup.mem_subgroupOf])
      exact this
    have hxu2 : TwoElt (x * u) :=
      TwoElt.mul (hc x hx u huH) hx2 (TwoElt.of_sq_eq_one hu2)
    have h3 := hzpU (hM2 _ hxuM hxu2)
    have hxe : x = (x * u) * u := by
      calc x = x * (u * u) := by rw [hu2, mul_one]
        _ = (x * u) * u := by group
    rw [hxe]
    exact (t2U z u).mul_mem h3 huU

end Mod3

section SD

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem hasSDSylow_of_loc5
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5 N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) (h₁ : q₁ % 4 = 3) (h₂ : q₂ % 4 = 3) {y : G} (hyH : y ∈ N.H) (hy1 : y ≠ 1)
    (hyodd : Odd (orderOf y)) {Kj : Subgroup G} (hKj : ∀ x ∈ Kj, x * y = y * x) {F : Type} [Field F]
    [Finite F] (hFodd : Odd (Nat.card F)) (e : ↥Kj ≃* SL2 F) :
    HasSDSylow ↥(centralizer ({y} : Set G)) := by
  have hy2 : y * y ≠ 1 := by
    intro h
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
    · exact hy1 (orderOf_eq_one_iff.1 h3)
    · rw [h3] at hyodd
      exact absurd hyodd (by decide)
  have hz2 : N.z * N.z = 1 := by
    have h := pow_orderOf_eq_one N.z
    rw [hLoc.z_ord, sq] at h
    exact h
  have hz1 : N.z ≠ 1 := by
    intro h
    have := hLoc.z_ord
    rw [h, orderOf_one] at this
    omega
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  have hHc := hLoc.H_comm
  have hzu : N.z * u = u * N.z := hHc _ hLoc.z_mem_H u hLoc.u_mem_H
  have hq₁4 : N.q₁ % 4 = 3 := by rw [hq₁]; exact h₁
  have hq₂4 : N.q₂ % 4 = 3 := by rw [hq₂]; exact h₂
  have hq₁0 : 1 ≤ N.q₁ := by omega
  have hq₂0 : 1 ≤ N.q₂ := by omega
  have h2part : ∀ x ∈ N.H, TwoElt x → x ∈ t2U N.z u := by
    intro x hx hx2
    refine twoElt_mem_U hHc inf_le_left inf_le_left hLoc.H₁_cyc hLoc.H₂_cyc
      (k₁ := (N.q₁ - 1) / 2) (k₂ := (N.q₂ - 1) / 2) (Nat.odd_iff.2 (by omega))
      (Nat.odd_iff.2 (by omega)) (by rw [hLoc.card_H_K₁]; omega) (by rw [hLoc.card_H_K₂]; omega)
      hLoc.H_idx ⟨hLoc.z_mem_H, hLoc.z_mem_K₁⟩ ⟨hLoc.z_mem_H, hLoc.z_mem_K₂⟩ hz2 hz1
      hLoc.u_mem_H hu2 hu1 hLoc.u_ne hx hx2
  set X : Subgroup G := centralizer ({y} : Set G) with hXdef
  have hyz' : y * N.z = N.z * y := hHc y hyH _ hLoc.z_mem_H
  have hyu : y * u = u * y := hHc y hyH u hLoc.u_mem_H
  have hzX : N.z ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hyz'.symm
  have huX : u ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hyu.symm
  have hUX : t2U N.z u ≤ X := by
    unfold t2U
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzX
    · simpa using huX
  have hzU : N.z ∈ t2U N.z u := Subgroup.subset_closure (by simp)
  have huU : u ∈ t2U N.z u := Subgroup.subset_closure (by simp)
  have hUH : t2U N.z u ≤ N.H := t2U_le_of_mem hz2 hu2 hzu hLoc.z_mem_H hLoc.u_mem_H
  let U' : Subgroup ↥X := (t2U N.z u).subgroupOf X
  have hUab : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact hHc (a : G) (hUH (Subgroup.mem_subgroupOf.mp ha)) (b : G)
      (hUH (Subgroup.mem_subgroupOf.mp hb))
  have hUexp : ∀ a ∈ U', a ^ 2 = 1 := by
    intro a ha
    apply Subtype.ext
    have h := t2S_closure_sq hz2 hu2 hzu.symm (a : G) (Subgroup.mem_subgroupOf.mp ha)
    simpa [pow_two] using h
  have hUcard : Nat.card ↥U' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv]
    exact t2U_card hz2 hu2 hzu hz1 hu1 hLoc.u_ne.symm
  have hcent : ∀ g : ↥X, (∀ a ∈ U', g * a = a * g) → (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ U' := by
    intro g hg hk2
    obtain ⟨k, hk⟩ := hk2
    have hgz : (g : G) * N.z = N.z * (g : G) :=
      congrArg Subtype.val (hg ⟨N.z, hzX⟩ (Subgroup.mem_subgroupOf.mpr hzU))
    have hgu : (g : G) * u = u * (g : G) :=
      congrArg Subtype.val (hg ⟨u, huX⟩ (Subgroup.mem_subgroupOf.mpr huU))
    have hgy : (g : G) * y = y * (g : G) := Subgroup.mem_centralizer_singleton_iff.mp g.2
    have hg2 : TwoElt (g : G) := ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hgH : (g : G) ∈ N.H :=
      twoElt_cent_mem_H hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂ hyH hy2 hgy hgz hgu hg2
    exact Subgroup.mem_subgroupOf.mpr (h2part _ hgH hg2)
  have hU'p : IsPGroup 2 ↥U' := IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
  obtain ⟨S, hUS⟩ := hU'p.exists_le_sylow
  have hKjX : Kj ≤ X := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hKj x hx)
  rcases t2P56_sylow_shape U' hUab hUexp hUcard hcent S hUS with ⟨m, hm, ⟨φ⟩⟩ | ⟨m, hm, ⟨φ⟩⟩
  · exfalso
    exact t2P56_not_dihedral hFodd (Kj.subgroupOf X) ((Subgroup.subgroupOfEquivOfLe hKjX).trans e) S
      ⟨φ⟩
  · exact ⟨S, m, hm, ⟨φ⟩⟩

end SD

end CFSG.GH74.GLS.Stage4.Rest
