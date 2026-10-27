module

public import CFSG.GH74.GLS.Stage4.T2FourBuild
public import CFSG.GH74.GLS.Stage4.T2P53e

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Conv

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2Four_of_loc5 (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hC₁ : centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)))
    {N : T2N1 G} {u : G} (hLoc : Ch6Loc5 N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) :
    T2Four z u K₁ K₂ N.H N.w₁ N.w₂ := by
  subst hz hK₁ hK₂
  have hzz : N.z * N.z = 1 := t2C_zz hSet
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  have hHiff : ∀ (K : Subgroup G), N.H ⊓ K = centralizer ({u} : Set G) ⊓ K →
      ∀ x ∈ K, x ∈ N.H ↔ x * u = u * x := by
    intro K h x hx
    constructor
    · intro hxH
      have : x ∈ N.H ⊓ K := ⟨hxH, hx⟩
      rw [h] at this
      exact Subgroup.mem_centralizer_singleton_iff.1 this.1
    · intro hxu
      have : x ∈ centralizer ({u} : Set G) ⊓ K :=
        ⟨Subgroup.mem_centralizer_singleton_iff.2 hxu, hx⟩
      rw [← h] at this
      exact this.1
  have hC₁eq : centralizer ({N.z} : Set G) = oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) :=
    le_antisymm hC₁ (Subgroup.map_subtype_le _)
  have hSC : N.S ≤ centralizer ({N.z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (hLoc.z_cent_S s hs)
  have hHC : N.H ≤ centralizer ({N.z} : Set G) := fun x hx => by
    have := hLoc.H_le hx
    exact (sup_le hSet.le_centralizer hSC) this
  have hcardH₁ : 3 ≤ Nat.card ↥(N.H ⊓ N.K₁) := by
    have h1 : Nat.card ↥(N.H ⊓ N.K₁) = N.q₁ - 1 := hLoc.card_H_K₁
    have h2 : 5 ≤ N.q₁ := hLoc.q₁_ge
    omega
  refine
    { zz := hzz, z_ne := t2C_z_ne hSet, uu := hu2, u_ne := hu1, zu_ne := hLoc.u_ne.symm,
      zu_comm := hLoc.u_comm.symm, K_comm := hSet.comm, K_inter := hSet.inter_eq.le,
      K_le_C := hSet.le_centralizer,
      C_norm₁ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).1 c (hC₁ hc),
      C_norm₂ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).2 c (hC₁ hc),
      C_idx := by have := hSet.index_two; rwa [← hC₁eq] at this,
      H_comm := hLoc.H_comm, z_mem_H := hLoc.z_mem_H, u_mem_H := hLoc.u_mem_H, H_le_C := hHC,
      H_not_le_K := hLoc.H_not_le_K, H₁_iff := hHiff _ hLoc.H₁_eq, H₂_iff := hHiff _ hLoc.H₂_eq,
      w₁_mem := hLoc.w₁_mem, w₂_mem := hLoc.w₂_mem, w₁_sq := hLoc.w₁_sq, w₂_sq := hLoc.w₂_sq,
      w₁_u := hLoc.w₁_u, w₂_u := hLoc.w₂_u,
      w₁_normH := fun x hx => (Subgroup.mem_normalizer_iff.1 hLoc.w₁_normH x).1 hx,
      w₂_normH := fun x hx => (Subgroup.mem_normalizer_iff.1 hLoc.w₂_normH x).1 hx,
      w₀_inv := hLoc.w₀_inv,
      w₀_not_mem := t2C_w0_not_mem hLoc.H_comm hLoc.w₀_inv hLoc.H₁_cyc hcardH₁ }

end Conv

section Nine

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2Four_K_nine (hSet : Ch6Setup G Gs 9 9 z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hC₁ : centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G))) :
    ∃ (u : G) (H : Subgroup G) (w₁ w₂ : G), T2Four z u K₁ K₂ H w₁ w₂ ∧ u ∈ K₁ ⊔ K₂ ∧
      ∀ x ∈ H, x ^ 16 = 1 := by
  have := hSet.finite₁
  obtain ⟨u, ⟨C⟩⟩ := exists_P51Coord hSet hRem (rfl : 9 % 4 = 9 % 4)
  obtain ⟨N, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ := loc5_of_coord hSet hRem C
  refine ⟨u, N.H, N.w₁, N.w₂, t2Four_of_loc5 hSet hRem hC₁ hLoc hz hK₁ hK₂, ?_, ?_⟩
  · rcases C.hcase with ⟨x₁, hx₁, x₂, hx₂, hu⟩ | ⟨hut, hτ₁, hτ₂⟩
    · rw [hu]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (C.range₁.le ⟨x₁, rfl⟩))
        (Subgroup.mem_sup_right (C.range₂.le ⟨x₂, rfl⟩))
    · exfalso
      have hF : Nat.card F₁ % 4 = 1 := by rw [hSet.card₁]
      obtain ⟨ι, hι⟩ := exists_unit_sqrt_negOne hF
      apply C.ns₁
      rw [hτ₁]
      have : ((Matrix.GeneralLinearGroup.det (dNeg F₁) : F₁ˣ) : F₁) = -1 := by
        unfold dNeg; rw [t2C_det_diagGL]; simp
      rw [this]
      exact ⟨(ι : F₁), hι.symm⟩
  · intro x hx
    have hmem : x * x ∈ (N.H ⊓ N.K₁) ⊔ (N.H ⊓ N.K₂) := by
      have := Subgroup.mul_self_mem_of_index_two hLoc.H_idx ⟨x, hx⟩
      rwa [Subgroup.mem_subgroupOf] at this
    have hcomm : ∀ a ∈ N.H ⊓ N.K₁, ∀ b ∈ N.H ⊓ N.K₂, a * b = b * a := fun a ha b hb =>
      hLoc.K_comm a ha.2 b hb.2
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hcomm (x * x)).1 hmem
    have h8 : ∀ (P : Subgroup G) (c : G), c ∈ P → Nat.card ↥P = 8 → c ^ 8 = 1 := by
      intro P c hc hP
      have := pow_card_eq_one' (G := ↥P) (x := (⟨c, hc⟩ : ↥P))
      rw [hP] at this
      exact congrArg Subtype.val this
    have h1 : Nat.card ↥(N.H ⊓ N.K₁) = 8 := by rw [hLoc.card_H_K₁, hq₁]
    have h2 : Nat.card ↥(N.H ⊓ N.K₂) = 8 := by rw [hLoc.card_H_K₂, hq₂]
    have hcab : Commute a b := hcomm a ha b hb
    calc x ^ 16 = (x * x) ^ 8 := by rw [show (16 : ℕ) = 2 * 8 from rfl, pow_mul, pow_two]
      _ = (a * b) ^ 8 := by rw [hab]
      _ = a ^ 8 * b ^ 8 := hcab.mul_pow 8
      _ = 1 := by rw [h8 _ a ha h1, h8 _ b hb h2, one_mul]

end Nine

section HCH

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

omit [Finite G] in
theorem t2_a_conj_forms (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {a : G}
    (d1 : a⁻¹ * z * a = u) (d2 : a⁻¹ * u * a = z * u) :
    a * z * a⁻¹ = z * u ∧ a * u * a⁻¹ = z ∧ a * (z * u) * a⁻¹ = u := by
  have e3 : a⁻¹ * (z * u) * a = z := by
    calc a⁻¹ * (z * u) * a = (a⁻¹ * z * a) * (a⁻¹ * u * a) := by group
      _ = u * (z * u) := by rw [d1, d2]
      _ = (u * z) * u := by group
      _ = (z * u) * u := by rw [← hzu]
      _ = z * (u * u) := by group
      _ = z := by rw [hu2, mul_one]
  have f1 : a * z * a⁻¹ = z * u := by
    calc a * z * a⁻¹ = a * (a⁻¹ * (z * u) * a) * a⁻¹ := by rw [e3]
      _ = z * u := by group
  have f2 : a * u * a⁻¹ = z := by
    calc a * u * a⁻¹ = a * (a⁻¹ * z * a) * a⁻¹ := by rw [d1]
      _ = z := by group
  have f3 : a * (z * u) * a⁻¹ = u := by
    calc a * (z * u) * a⁻¹ = (a * z * a⁻¹) * (a * u * a⁻¹) := by group
      _ = (z * u) * z := by rw [f1, f2]
      _ = (u * z) * z := by rw [hzu]
      _ = u * (z * z) := by group
      _ = u := by rw [hz2, mul_one]
  exact ⟨f1, f2, f3⟩

theorem T2Four.hCH_of_exp16 (h : T2Four z u K₁ K₂ H w₁ w₂) (hr : CFSG.pRank 2 G = 3)
    (h16 : ∀ x ∈ H, x ^ 16 = 1) {a : G} (d1 : a⁻¹ * z * a = u) (d2 : a⁻¹ * u * a = z * u) :
    ∀ x ∈ H, a * x * a⁻¹ = x → x = 1 := by
  intro x hx hfix
  by_contra hx1
  obtain ⟨f1, f2, f3⟩ := t2_a_conj_forms h.zz h.uu h.zu_comm d1 d2
  have hdvd : orderOf x ∣ 16 := orderOf_dvd_of_pow_eq_one (h16 x hx)
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hdvd.trans (by norm_num : 16 ∣ 2 ^ 4))
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by simpa using hio))
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  set m : ℕ := 2 ^ j with hm
  have hmpos : m ≠ 0 := by positivity
  have hxo : orderOf x = 2 * m := by rw [hio, hm, pow_succ]; ring
  have hx'1 : x ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hmpos (by rw [hxo]; omega)
  have hx'2 : (x ^ m) * (x ^ m) = 1 := by
    rw [← pow_add, ← two_mul, ← hxo]; exact pow_orderOf_eq_one x
  have hx'H : x ^ m ∈ H := H.pow_mem hx m
  have hx'fix : a * x ^ m * a⁻¹ = x ^ m := by rw [← conj_pow, hfix]
  rcases h.omega1 hr (x ^ m) hx'H hx'2 with h1 | h1 | h1 | h1
  · exact hx'1 h1
  · rw [h1, f1] at hx'fix
    apply h.u_ne
    have : z * u = z * 1 := hx'fix.trans (mul_one z).symm
    exact mul_left_cancel this
  · rw [h1, f2] at hx'fix
    exact h.zu_ne hx'fix
  · rw [h1, f3] at hx'fix
    apply h.z_ne
    have : z * u = 1 * u := hx'fix.symm.trans (one_mul u).symm
    exact mul_right_cancel this

end HCH

section Hnc

variable {G : Type} [Group G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2B_not_cent_K₁ (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    {x : G} (hx : x ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)))
    (hxK : x ∉ K₁ ⊔ K₂) (hcent : ∀ y ∈ K₁, x * y = y * x) : False := by
  have hgen := hRem.gen
  have hidx := hSet.index_two
  have htC₁ : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← hgen]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htK : t ∉ K₁ ⊔ K₂ := t2B_t_notin hSet hRem
  have hxt : x * t⁻¹ ∈ K₁ ⊔ K₂ := t2C_outer_coset hidx hx htC₁ hxK htK
  obtain ⟨e, g, hns, hact⟩ := hRem.diag₁
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hSet.comm _).1 hxt
  have hxe : ∀ y₀ ∈ K₁, t * y₀ * t⁻¹ = a⁻¹ * y₀ * a := by
    intro y₀ hy₀
    have h1 := hcent y₀ hy₀
    have hx' : x = (a * b) * t := by rw [← hab]; group
    rw [hx'] at h1
    have h2 : t * y₀ * t⁻¹ = (a * b)⁻¹ * y₀ * (a * b) := by
      calc t * y₀ * t⁻¹ = (a * b)⁻¹ * ((a * b) * t * y₀) * t⁻¹ := by group
        _ = (a * b)⁻¹ * (y₀ * ((a * b) * t)) * t⁻¹ := by rw [h1]
        _ = (a * b)⁻¹ * y₀ * (a * b) := by group
    rw [h2]
    have hbc : b⁻¹ * (a⁻¹ * y₀ * a) * b = a⁻¹ * y₀ * a := by
      have hw : a⁻¹ * y₀ * a ∈ K₁ := K₁.mul_mem (K₁.mul_mem (K₁.inv_mem ha) hy₀) ha
      have := hSet.comm _ hw b hb
      calc b⁻¹ * (a⁻¹ * y₀ * a) * b = b⁻¹ * (b * (a⁻¹ * y₀ * a)) := by rw [← this]; group
        _ = a⁻¹ * y₀ * a := by group
    calc (a * b)⁻¹ * y₀ * (a * b) = b⁻¹ * (a⁻¹ * y₀ * a) * b := by group
      _ = a⁻¹ * y₀ * a := hbc
  apply hns
  have hainv : (e ⟨a⁻¹, K₁.inv_mem ha⟩)⁻¹ = e ⟨a, ha⟩ := by
    rw [← map_inv]
    exact congrArg e (Subtype.ext (by simp))
  refine t2C_isSquare_of_slConj_eq_inner g (e ⟨a⁻¹, K₁.inv_mem ha⟩) ?_
  intro s
  obtain ⟨y₀, rfl⟩ := e.surjective s
  obtain ⟨y, hy1, hy2⟩ := hact y₀
  have hy : y = ⟨a⁻¹, K₁.inv_mem ha⟩ * y₀ * ⟨a, ha⟩ := by
    apply Subtype.ext
    rw [hy1]
    exact hxe y₀ y₀.2
  apply Subtype.ext
  rw [coe_slConj, ← hy2, hy, hainv, map_mul, map_mul]

theorem t2B_hnc (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hC₁ : centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G))) :
    ∀ y : G, y * y = 1 → y * z = z * y → y ≠ 1 → y ≠ z → ∃ x ∈ K₁, y * x * y⁻¹ ≠ x := by
  intro y hy2 hyz hy1 hyne
  by_contra hcon
  push Not at hcon
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have hzz := t2C_zz hSet
  have hz1 := t2C_z_ne hSet
  have hzc₁ : ∀ k ∈ K₁, k * z = z * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_left hk))
  obtain ⟨-, hZ₁⟩ := t2C_Z_of_sl2 e₁ hz1 hSet.z_mem₁ hzc₁
  have hK₂inv := t2P53_invK hodd₂ e₂ hSet.z_mem₂ hze₂
  have hyC : y ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hyz
  have hyC₁ := hC₁ hyC
  by_cases hyK : y ∈ K₁ ⊔ K₂
  · obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hSet.comm y).1 hyK
    have haz : a ∈ Subgroup.zpowers z := by
      refine hZ₁ a ha (fun k hk => ?_)
      have h1 := hcon k hk
      have h1' : y * k = k * y := by
        have : y * k * y⁻¹ = k := h1
        calc y * k = (y * k * y⁻¹) * y := by group
          _ = k * y := by rw [this]
      rw [hab] at h1'
      have h2 : k * b = b * k := hSet.comm k hk b hb
      have : a * k * b = k * a * b := by
        calc a * k * b = a * (k * b) := by group
          _ = a * (b * k) := by rw [h2]
          _ = a * b * k := by group
          _ = k * (a * b) := h1'
          _ = k * a * b := by group
      exact mul_right_cancel this
    have ha1 : a * a = 1 := by
      rcases t2C_zpowers_cases hzz haz with h | h
      · rw [h]; simp
      · rw [h]; exact hzz
    have hbb : b * b = 1 := by
      have hba : a * b = b * a := hSet.comm a ha b hb
      have : (a * b) * (a * b) = (a * a) * (b * b) := by
        calc (a * b) * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hba]
          _ = (a * a) * (b * b) := by group
      have hy2' := hy2
      rw [hab] at hy2'
      rw [this, ha1, one_mul] at hy2'
      exact hy2'
    rcases t2C_zpowers_cases hzz haz with ha' | ha' <;> rcases hK₂inv b hb hbb with hb' | hb'
    · exact hy1 (by rw [hab, ha', hb']; simp)
    · exact hyne (by rw [hab, ha', hb']; simp)
    · exact hyne (by rw [hab, ha', hb']; simp)
    · exact hy1 (by rw [hab, ha', hb']; exact hzz)
  · exact t2B_not_cent_K₁ hSet hRem hyC₁ hyK (fun x hx => by
      have h1 := hcon x hx
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [h1])

end Hnc

section Exp

theorem t2_not_three_dvd_of_exp16 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h16 : ∀ x ∈ H, x ^ 16 = 1) : ¬ 3 ∣ Nat.card H := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 h3
  have h1 : orderOf (x : G) ∣ 16 := orderOf_dvd_of_pow_eq_one (h16 x x.2)
  rw [Subgroup.orderOf_coe, hx] at h1
  omega

end Exp

end CFSG.GH74.GLS.Stage4.Rest
