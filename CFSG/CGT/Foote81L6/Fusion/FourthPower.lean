module

public import CFSG.CGT.Foote81L6.Fusion.Squares

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

theorem exists_conj_of_sylow_centralizer {G : Type*} [Group G] [Finite G] {X : Subgroup G} {e : G}
    (SK : Sylow 2 ↥(centralizer ({e} : Set G)))
    (hSK : (SK : Subgroup _) = X.subgroupOf (centralizer ({e} : Set G)))
    {P : Subgroup G} (hPC : P ≤ centralizer ({e} : Set G)) (hP : IsPGroup 2 P) :
    ∃ c : G, c * e = e * c ∧ ∀ x ∈ P, c * x * c⁻¹ ∈ X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf (centralizer ({e} : Set G))) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizer ({e} : Set G)) Q SK
  refine ⟨c, mem_centralizer_singleton_iff.1 c.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hPC hx⟩ : centralizer ({e} : Set G)) ∈ (Q : Subgroup _) :=
    hQ (show (⟨x, hPC hx⟩ : centralizer ({e} : Set G)) ∈ P.subgroupOf _ from hx)
  have hmem : c * ⟨x, hPC hx⟩ * c⁻¹ ∈ ((c • Q : Sylow 2 _) : Subgroup _) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hxQ, rfl⟩
  rw [hc, hSK, mem_subgroupOf] at hmem
  simpa using hmem

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem conj_b_of_pow_four (hL3b : ∀ y ∈ D.Zab, IsConj D.b y → y = D.b) {k q : G}
    (hqT : k * q * k⁻¹ ∈ T) (hq4 : q ^ 4 = D.b) : k * D.b * k⁻¹ = D.b := by
  have hv4 : k * D.b * k⁻¹ =
      k * q * k⁻¹ * (k * q * k⁻¹) * (k * q * k⁻¹ * (k * q * k⁻¹)) := by
    rw [← hq4]
    simp only [pow_succ, pow_zero, one_mul]
    group
  have hb2 : k * D.b * k⁻¹ * (k * D.b * k⁻¹) = 1 := by
    rw [show k * D.b * k⁻¹ * (k * D.b * k⁻¹) = k * (D.b * D.b) * k⁻¹ by group, D.b_mul_b,
      mul_one, mul_inv_cancel]
  have hZ : k * D.b * k⁻¹ ∈ D.Zab := by
    rw [hv4]
    refine D.mul_self_mem_Zab (D.mul_self_mem_T₁ hqT) ?_
    rw [← hv4]
    exact hb2
  exact hL3b _ hZ (isConj_iff.2 ⟨k, rfl⟩)

theorem isConj_mul_b_of_pow_four [Finite G] (hL3b : ∀ y ∈ D.Zab, IsConj D.b y → y = D.b)
    {X : Subgroup G} (hXT : X ≤ T) {a₀ : G} (SK : Sylow 2 ↥(centralizer ({a₀} : Set G)))
    (hSK : (SK : Subgroup _) = X.subgroupOf (centralizer ({a₀} : Set G))) {g q : G}
    (hqT : q ∈ T) (hqu : q * (g * a₀ * g⁻¹) = g * a₀ * g⁻¹ * q) (hq4 : q ^ 4 = D.b)
    (hub : IsConj (g * a₀ * g⁻¹) (g * a₀ * g⁻¹ * D.b)) : IsConj a₀ (a₀ * D.b) := by
  have hq'C : g⁻¹ * q * g ∈ centralizer ({a₀} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * q * g * a₀ = g⁻¹ * (q * (g * a₀ * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a₀ * g⁻¹ * q) * g := by rw [hqu]
      _ = a₀ * (g⁻¹ * q * g) := by group
  have hP : IsPGroup 2 (zpowers (g⁻¹ * q * g)) :=
    (D.isPGroup_T.map (MulAut.conj g⁻¹).toMonoidHom).to_le
      (zpowers_le.2 ⟨q, hqT, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
  obtain ⟨c, hce, hc⟩ := exists_conj_of_sylow_centralizer SK hSK (zpowers_le.2 hq'C) hP
  have hcq : c * g⁻¹ * q * (c * g⁻¹)⁻¹ ∈ T := by
    have := hXT (hc _ (mem_zpowers _))
    rwa [show c * (g⁻¹ * q * g) * c⁻¹ = c * g⁻¹ * q * (c * g⁻¹)⁻¹ by group] at this
  have hkb := D.conj_b_of_pow_four hL3b hcq hq4
  have hku : c * g⁻¹ * (g * a₀ * g⁻¹) * (c * g⁻¹)⁻¹ = a₀ := by
    calc c * g⁻¹ * (g * a₀ * g⁻¹) * (c * g⁻¹)⁻¹ = c * a₀ * c⁻¹ := by group
      _ = a₀ := by rw [hce, mul_inv_cancel_right]
  have hkub : c * g⁻¹ * (g * a₀ * g⁻¹ * D.b) * (c * g⁻¹)⁻¹ = a₀ * D.b := by
    rw [show c * g⁻¹ * (g * a₀ * g⁻¹ * D.b) * (c * g⁻¹)⁻¹ =
      (c * g⁻¹ * (g * a₀ * g⁻¹) * (c * g⁻¹)⁻¹) * (c * g⁻¹ * D.b * (c * g⁻¹)⁻¹) by group, hku, hkb]
  have h1 : IsConj a₀ (g * a₀ * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have h2 : IsConj (g * a₀ * g⁻¹ * D.b) (a₀ * D.b) := isConj_iff.2 ⟨c * g⁻¹, hkub⟩
  exact h1.trans (hub.trans h2)

private theorem eq_one_or_eq_of_mem_zpowers {H : Type*} [Group H] {z x : H} (hz : z ^ 2 = 1)
    (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [zpow_eq_zpow_emod' k hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

theorem exists_pow_four_eq_b_CBt : ∃ q ∈ D.B ⊓ centralizer ({D.t} : Set G), q ^ 4 = D.b := by
  obtain ⟨e⟩ := D.CBt_iso
  have hn := D.three_le_n
  have hbH : D.b ∈ D.B ⊓ centralizer ({D.t} : Set G) :=
    mem_inf.2 ⟨D.b_mem_B, mem_centralizer_singleton_iff.2 (D.b_comm_T D.t_mem_T).symm⟩
  have hcen : e ⟨D.b, hbH⟩ ∈ center (CFSG.Open.SemidihedralGroup (n + 1)) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (D.b_comm_T (D.B_le_T (mem_inf.1 y.2).1)))
  rw [CFSG.Semidihedral.center_eq_zpowers (n + 1) (by omega)] at hcen
  have hz2 : CFSG.Semidihedral.z (n + 1) ^ 2 = 1 := CFSG.Semidihedral.z_sq (n + 1) (by omega)
  have hbz : e ⟨D.b, hbH⟩ = CFSG.Semidihedral.z (n + 1) := by
    rcases eq_one_or_eq_of_mem_zpowers hz2 hcen with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))) D.b_ne_one
    · exact h
  refine ⟨(e.symm (CFSG.Semidihedral.r (n + 1) ^ 2 ^ (n - 3)) : G), (e.symm _).2, ?_⟩
  rw [← Subgroup.coe_pow, ← map_pow, ← pow_mul,
    show 2 ^ (n - 3) * 4 = CFSG.Semidihedral.half (n + 1) by
      rw [CFSG.Semidihedral.half, show n + 1 - 2 = (n - 3) + 2 by omega, pow_add]; rfl]
  rw [show CFSG.Semidihedral.r (n + 1) ^ CFSG.Semidihedral.half (n + 1) =
    CFSG.Semidihedral.z (n + 1) from rfl, ← hbz, MulEquiv.symm_apply_apply]

theorem isConj_mul_b_of_not_mem_T₀ [Finite G] (hL3b : ∀ y ∈ D.Zab, IsConj D.b y → y = D.b)
    {X : Subgroup G} (hXT : X ≤ T) {a₀ : G} (SK : Sylow 2 ↥(centralizer ({a₀} : Set G)))
    (hSK : (SK : Subgroup _) = X.subgroupOf (centralizer ({a₀} : Set G)))
    (ha₀ : a₀ * a₀ = 1) {g : G} (hgT : g * a₀ * g⁻¹ ∈ T) (hg₀ : g * a₀ * g⁻¹ ∉ D.T₀) :
    IsConj a₀ (a₀ * D.b) := by
  have hu2 : g * a₀ * g⁻¹ * (g * a₀ * g⁻¹) = 1 := by
    rw [show g * a₀ * g⁻¹ * (g * a₀ * g⁻¹) = g * (a₀ * a₀) * g⁻¹ by group, ha₀, mul_one,
      mul_inv_cancel]
  obtain ⟨h, hh, hht⟩ := D.exists_conj_t hgT hg₀ hu2
  obtain ⟨q₀, hq₀, hq₀4⟩ := D.exists_pow_four_eq_b_CBt
  have hq₀t : q₀ * D.t = D.t * q₀ := mem_centralizer_singleton_iff.1 (mem_inf.1 hq₀).2
  have hhT : h ∈ T := D.T₀_le_T hh
  have hbh : h * D.b * h⁻¹ = D.b := by rw [D.b_comm_T hhT, mul_inv_cancel_right]
  refine D.isConj_mul_b_of_pow_four hL3b hXT SK hSK (g := g) (q := h * q₀ * h⁻¹)
    (mul_mem (mul_mem hhT (D.B_le_T (mem_inf.1 hq₀).1)) (inv_mem hhT)) ?_ ?_ ?_
  · rw [← hht]
    calc h * q₀ * h⁻¹ * (h * D.t * h⁻¹) = h * (q₀ * D.t) * h⁻¹ := by group
      _ = h * (D.t * q₀) * h⁻¹ := by rw [hq₀t]
      _ = h * D.t * h⁻¹ * (h * q₀ * h⁻¹) := by group
  · rw [conj_pow, hq₀4, hbh]
  ·
    have hbt2 : (D.b * D.t) ^ 2 = 1 := by
      rw [pow_two, show D.b * D.t * (D.b * D.t) = D.b * (D.t * D.b) * D.t by group,
        D.b_comm_T D.t_mem_T, show D.b * (D.b * D.t) * D.t = (D.b * D.b) * (D.t * D.t) by group,
        D.b_mul_b, D.t_mul_t, one_mul]
    obtain ⟨y, -, hy⟩ := D.Bt_conj D.b D.b_mem_B hbt2
    rw [← hht]
    refine isConj_iff.2 ⟨h * y⁻¹ * h⁻¹, ?_⟩
    have hy' : y⁻¹ * D.t * y = D.b * D.t := by
      calc y⁻¹ * D.t * y = y⁻¹ * (y * (D.b * D.t) * y⁻¹) * y := by rw [hy]
        _ = D.b * D.t := by group
    calc h * y⁻¹ * h⁻¹ * (h * D.t * h⁻¹) * (h * y⁻¹ * h⁻¹)⁻¹ = h * (y⁻¹ * D.t * y) * h⁻¹ := by
          group
      _ = h * D.t * h⁻¹ * (h * D.b * h⁻¹) := by rw [hy', ← D.b_comm_T D.t_mem_T]; group
      _ = h * D.t * h⁻¹ * D.b := by rw [hbh]

theorem exists_pow_four_eq_b₀ (hn : 4 ≤ n) : ∃ x ∈ D.B₀, x ^ 4 = D.b₀ := by
  obtain ⟨e⟩ := D.B₀_iso
  refine ⟨(e.symm ((r 1) ^ 2 ^ (n - 4)) : G), (e.symm _).2, ?_⟩
  rw [← Subgroup.coe_pow, ← map_pow, ← pow_mul,
    show 2 ^ (n - 4) * 4 = 2 ^ (n - 1 - 1) by
      rw [show n - 1 - 1 = (n - 4) + 2 by omega, pow_add]; rfl,
    rho_pow (by omega : 1 ≤ n - 1), ← D.B₀_iso_apply_b₀ e, MulEquiv.symm_apply_apply]

theorem exists_pow_four_eq_b_sDiag (hn : 4 ≤ n) :
    ∃ q ∈ D.B₀ ⊔ D.B₁, q * D.s = D.s * q ∧ q ^ 4 = D.b := by
  obtain ⟨x, hx, hx4⟩ := D.exists_pow_four_eq_b₀ hn
  refine ⟨D.sDiag ⟨x, hx⟩, ?_, D.sDiag_comm_s _, ?_⟩
  · rw [sDiag_apply]
    exact mul_mem (mem_sup_left hx) (mem_sup_right (D.conj_s_mem_B₁ hx))
  · rw [← map_pow, show (⟨x, hx⟩ : D.B₀) ^ 4 = ⟨D.b₀, D.b₀_mem⟩ from Subtype.ext hx4, sDiag_apply]
    show D.b₀ * (D.s * D.b₀ * D.s⁻¹) = D.b₀ * D.b₁
    rw [D.conj_s_b₀]

theorem isConj_conj_mul_s_mul_b {a' β : G} (ha' : a' ∈ D.A) (hβ : β ∈ D.B₀) :
    IsConj (β * (a' * D.s) * β⁻¹) (β * (a' * D.s) * β⁻¹ * D.b) := by
  have hβT : β ∈ T := D.B_le_T (D.B₀_le_B hβ)
  have hbβ : β * D.b * β⁻¹ = D.b := by rw [D.b_comm_T hβT, mul_inv_cancel_right]
  refine isConj_iff.2 ⟨D.b₀, ?_⟩
  have hc1 : D.b₀ * β * D.b₀⁻¹ = β := by rw [← D.b₀_comm β hβ, mul_inv_cancel_right]
  have hc2 : D.b₀ * a' * D.b₀⁻¹ = a' := by
    rw [← D.A_comm_B a' ha' D.b₀ D.b₀_mem_B, mul_inv_cancel_right]
  have hc3 : D.b₀ * β⁻¹ * D.b₀⁻¹ = β⁻¹ := by
    rw [show D.b₀ * β⁻¹ * D.b₀⁻¹ = (D.b₀ * β * D.b₀⁻¹)⁻¹ by group, hc1]
  have hs3 : D.s⁻¹ * D.b₀ * D.s = D.b₁ := by
    have h := D.conj_s_b₀
    rw [D.s_inv] at h ⊢
    exact h
  have hbs : D.b₀ * D.s * D.b₀⁻¹ = D.s * D.b := by
    calc D.b₀ * D.s * D.b₀⁻¹ = D.s * (D.s⁻¹ * D.b₀ * D.s) * D.b₀⁻¹ := by group
      _ = D.s * (D.b₁ * D.b₀⁻¹) := by rw [hs3]; group
      _ = D.s * D.b := by
        rw [inv_eq_of_mul_eq_one_right D.b₀_mul_b₀,
          ← D.B₀_comm_B₁ D.b₀ D.b₀_mem D.b₁ D.b₁_mem]
        rfl
  calc D.b₀ * (β * (a' * D.s) * β⁻¹) * D.b₀⁻¹ =
      (D.b₀ * β * D.b₀⁻¹) * ((D.b₀ * a' * D.b₀⁻¹) * (D.b₀ * D.s * D.b₀⁻¹)) *
        (D.b₀ * β⁻¹ * D.b₀⁻¹) := by group
    _ = β * (a' * (D.s * D.b)) * β⁻¹ := by rw [hc1, hc2, hbs, hc3]
    _ = β * (a' * D.s) * β⁻¹ * (β * D.b * β⁻¹) := by group
    _ = β * (a' * D.s) * β⁻¹ * D.b := by rw [hbβ]

theorem isConj_mul_b_of_mem_T₀_of_four_le [Finite G] (hn : 4 ≤ n)
    (hL3b : ∀ y ∈ D.Zab, IsConj D.b y → y = D.b)
    {X : Subgroup G} (hXT : X ≤ T) {a₀ : G} (SK : Sylow 2 ↥(centralizer ({a₀} : Set G)))
    (hSK : (SK : Subgroup _) = X.subgroupOf (centralizer ({a₀} : Set G)))
    (ha₀ : a₀ * a₀ = 1) {g : G} (hg₀ : g * a₀ * g⁻¹ ∈ D.T₀) (hg₁ : g * a₀ * g⁻¹ ∉ D.T₁) :
    IsConj a₀ (a₀ * D.b) := by
  have hu2 : g * a₀ * g⁻¹ * (g * a₀ * g⁻¹) = 1 := by
    rw [show g * a₀ * g⁻¹ * (g * a₀ * g⁻¹) = g * (a₀ * a₀) * g⁻¹ by group, ha₀, mul_one,
      mul_inv_cancel]
  obtain ⟨a', ha', -, β, hβ, hβu⟩ := D.exists_conj_mul_s hg₀ hg₁ hu2
  obtain ⟨q₁, hq₁, hq₁s, hq₁4⟩ := D.exists_pow_four_eq_b_sDiag hn
  have hβT : β ∈ T := D.B_le_T (D.B₀_le_B hβ)
  have hbβ : β * D.b * β⁻¹ = D.b := by rw [D.b_comm_T hβT, mul_inv_cancel_right]
  have hq₁a' : q₁ * a' = a' * q₁ := (D.A_comm_B a' ha' q₁ (D.B₀B₁_le_B hq₁)).symm
  refine D.isConj_mul_b_of_pow_four hL3b hXT SK hSK (g := g) (q := β * q₁ * β⁻¹)
    (mul_mem (mul_mem hβT (D.B_le_T (D.B₀B₁_le_B hq₁))) (inv_mem hβT)) ?_ ?_ ?_
  · rw [← hβu]
    calc β * q₁ * β⁻¹ * (β * (a' * D.s) * β⁻¹) = β * (q₁ * a' * D.s) * β⁻¹ := by group
      _ = β * (a' * (q₁ * D.s)) * β⁻¹ := by rw [hq₁a']; group
      _ = β * (a' * (D.s * q₁)) * β⁻¹ := by rw [hq₁s]
      _ = β * (a' * D.s) * β⁻¹ * (β * q₁ * β⁻¹) := by group
  · rw [conj_pow, hq₁4, hbβ]
  · rw [← hβu]
    exact D.isConj_conj_mul_s_mul_b ha' hβ

end FooteCore

end CFSG.CGT.Foote81L6
