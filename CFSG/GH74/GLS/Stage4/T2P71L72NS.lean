module

public import CFSG.GH74.GLS.Stage4.T2F1LocMain

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

@[expose] def Lt3 (G : Type) [Group G] (n : ℕ) : Prop :=
  ∀ R : Subgroup G, IsPGroup 3 ↥R → Nat.card ↥R < (3 ^ n) ^ 3

end CFSG.GH74.GLS.Stage4.Rest.L72

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage4.Rest.L72
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem not_tsing_K₁_lt (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n) (hStd : Std G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hlt : Lt3 G n)
    {N : T2N3 G} {u : G} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) (hSec : Ch6Sec5 N u)
    {y : G} (hyH : y ∈ N.H ⊓ N.K₁) (hyp : (orderOf y).Prime) (hyodd : Odd (orderOf y))
    (hya : N.a * y * N.a⁻¹ = y) : False := by
  have hLoc := hSec.loc
  have h3n : 27 ≤ 3 ^ n := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hNum : Ch6NumD 3 (3 ^ n) (3 ^ n) :=
    ⟨Nat.prime_three, by norm_num, ⟨n, rfl⟩, ⟨n, rfl⟩, Or.inl rfl⟩
  have hz2 : orderOf z = 2 := by rw [← hz]; exact hLoc.z_ord
  have hyz : y ∉ Subgroup.zpowers N.z := by
    intro hy
    have hzz : N.z * N.z = 1 := by
      have h := pow_orderOf_eq_one N.z
      rw [hLoc.z_ord, sq] at h
      exact h
    have hy2 : y ^ 2 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hzz, one_zpow]
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact hyp.one_lt.ne' h
    · rw [h] at hyodd; exact absurd hyodd (by decide)
  have hnp : ¬ 3 ∣ orderOf y := by
    intro h3
    have hd : orderOf y ∣ Nat.card ↥(N.H ⊓ N.K₁) := by
      have := orderOf_dvd_natCard (⟨y, hyH⟩ : ↥(N.H ⊓ N.K₁))
      rwa [Subgroup.orderOf_mk] at this
    rw [hLoc.card_H_K₁, hq₁] at hd
    have h3d : 3 ∣ 3 ^ n - 1 := h3.trans hd
    have h3n' : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega)
    omega
  obtain ⟨J, hJy, hK₂J, hJ⟩ := exists_J_core hL hL3 hStd hSet hRem hNum (by omega) hz hK₁ hK₂ hq₁ hq₂
    hSec hyH hyz hyp hyodd hya
  have hzK₂ : z ∈ K₂ := hSet.z_mem₂
  have hzc : ∀ x ∈ K₂, z * x = x * z := fun x hx =>
    Subgroup.mem_centralizer_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_right hx)) z
      (Set.mem_singleton z)
  have hTS := t5_tsing_of_J hIVK Nat.prime_three (by norm_num) ⟨n, rfl⟩ (z := z) (y := y)
    (Ky := K₁) (K := K₂) (J := J) (by rw [← hK₁]; exact hyH.2) (by rw [← hz]; exact hyz) hnp hJy
    hK₂J hJ hz2 hzK₂ hzc
  obtain ⟨y', -, -, -, hX⟩ := hTS
  have hX₂K : N.X₂ ≤ K₂ := by
    rw [← hK₂, hLoc.K₂_eq]; exact le_sup_left
  have hX₂c : Nat.card ↥N.X₂ = 3 ^ n := by rw [hLoc.card_X₂, hq₂]
  have hX₂p : IsPGroup 3 ↥N.X₂ := IsPGroup.of_card (n := n) hX₂c
  obtain ⟨R, hRp, -, -, hRc, -⟩ := hX N.X₂ hX₂K hX₂p hX₂c
  exact absurd hRc (hlt R hRp).ne

theorem not_tsing_K₂_lt (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n) (hStd : Std G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hlt : Lt3 G n)
    {N : T2N3 G} {u : G} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) (hSec : Ch6Sec5 N u)
    {y : G} (hyH : y ∈ N.H ⊓ N.K₂) (hyp : (orderOf y).Prime) (hyodd : Odd (orderOf y))
    (hya : N.a * y * N.a⁻¹ = y) : False :=
  not_tsing_K₁_lt hL hL3 hIVK hn hStd (hSet.swap rfl) hRem.swap hlt (N := N.swap) (u := u)
    hz hK₂ hK₁ hq₂ hq₁ (hSec.swap (hq₁.trans hq₂.symm)) hyH hyp hyodd hya

theorem no_fixed_odd_K₂_lt (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n) (hStd : Std G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hlt : Lt3 G n)
    {N : T2N3 G} {u : G} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) (hSec : Ch6Sec5 N u) :
    ∀ y ∈ N.H ⊓ N.K₂, Odd (orderOf y) → N.a * y * N.a⁻¹ = y → y = 1 := by
  intro y hyH hodd hya
  by_contra hy1
  have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hne
  set y' : G := y ^ (orderOf y / r) with hy'
  have hy'ord : orderOf y' = r := orderOf_pow_orderOf_div (orderOf_pos y).ne' hrd
  have hy'H : y' ∈ N.H ⊓ N.K₂ := Subgroup.pow_mem _ hyH _
  have hy'a : N.a * y' * N.a⁻¹ = y' := by
    rw [hy', ← conj_pow, hya]
  exact not_tsing_K₂_lt hL hL3 hIVK hn hStd hSet hRem hlt hz hK₁ hK₂ hq₁ hq₂ hSec hy'H
    (hy'ord ▸ hrp) (hy'ord ▸ Odd.of_dvd_nat hodd hrd) hy'a


open CFSG.GH74.GLS.Stage4.Rest.T2 in
theorem sigma₂_eq_one_of_sigma₁_eq_one_lt (hL : SDWreathedLayer)
    (hL3 : LU.Local.L3Cover) (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n) (hStd : Std G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hlt : Lt3 G n)
    {N : T2N3 G} {u : G} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) (hSec : Ch6Sec5 N u)
    {f : G} (hf : f ∈ N.F) {r : ℕ} (hr : Odd r) (hfr : f ^ r = 1)
    {φ₁ : Hex.SL2 F₁ →* G} {σ₁ : F₁ ≃+* F₁} (hHK₁ : N.H ⊓ N.K₁ = (tSub F₁).map φ₁)
    (hσ₁ : ∀ M : Hex.SL2 F₁, f * φ₁ M * f⁻¹ = φ₁ (Matrix.SpecialLinearGroup.map (σ₁ : F₁ →+* F₁) M))
    {φ₂ : Hex.SL2 F₂ →* G} {σ₂ : F₂ ≃+* F₂} (hφ₂ : Function.Injective φ₂)
    (hHK₂ : N.H ⊓ N.K₂ = (tSub F₂).map φ₂)
    (hσ₂ : ∀ M : Hex.SL2 F₂, f * φ₂ M * f⁻¹ = φ₂ (Matrix.SpecialLinearGroup.map (σ₂ : F₂ →+* F₂) M))
    (h1 : σ₁ = 1) : σ₂ = 1 := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have hW := hSec.weyl
  have hw₁w₂ : N.w₁ * N.w₂ = N.w₂ * N.w₁ := by
    have := hSet.comm N.w₁ (hK₁ ▸ hLoc.w₁_mem) N.w₂ (hK₂ ▸ hLoc.w₂_mem)
    exact this
  obtain ⟨h₀, hh₀, hfa⟩ := comm_a_mod_H_of_sec hSec hf hr hfr hw₁w₂
  have hfH : ∀ x ∈ N.H, f * x * f⁻¹ ∈ N.H := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hF5.F_normH hf) x).1 hx
  have hfK₂ : ∀ x ∈ N.K₂, f * x * f⁻¹ ∈ N.K₂ := by
    have := conj_mem_sup (hF5.F_normX₂ f hf) (hF5.F_normX₂' f hf)
    rw [← hLoc.K₂_eq] at this
    exact this
  have hfH₂ : ∀ x ∈ N.H ⊓ N.K₂, f * x * f⁻¹ ∈ N.H ⊓ N.K₂ := fun x hx =>
    ⟨hfH x hx.1, hfK₂ x hx.2⟩
  have hf₁ : ∀ x ∈ N.H ⊓ N.K₁, f * x * f⁻¹ = x := by
    intro x hx
    rw [hHK₁] at hx
    obtain ⟨M, -, rfl⟩ := hx
    exact centralizes_of_eq_one φ₁ f σ₁ hσ₁ h1 M
  have hns := no_fixed_odd_K₂_lt hL hL3 hIVK hn hStd hSet hRem hlt hz hK₁ hK₂ hq₁ hq₂ hSec
  have hodd : ∀ x ∈ N.H ⊓ N.K₂, Odd (orderOf x) → f * x * f⁻¹ = x := fun x hx hxo =>
    torus_fixed_of_nonsingular (H := N.H) (H₁ := N.H ⊓ N.K₁) (H₂ := N.H ⊓ N.K₂) (a := N.a)
      (f := f) (w := N.w₂) hLoc.H_comm inf_le_left inf_le_left hLoc.H_idx
      (fun y hy => (Subgroup.mem_normalizer_iff.1 hW.a_normH y).1 hy) hW.a_cube hfH₂ ⟨h₀, hh₀, hfa⟩
      hf₁ hW.w₂_a hLoc.w₂_inv hns hx hxo
  have hall := cyclic_odd_conj_trivial hLoc.H₂_cyc hfH₂ hr hfr hodd
  refine eq_one_of_centralizes_torus φ₂ f σ₂ hφ₂ hσ₂ ?_
  intro s
  apply hall
  rw [hHK₂]
  exact ⟨sl2D s, sl2D_mem_tSub s, rfl⟩


section Core

variable {Gs : Type} [Group Gs]

theorem f1_core_lt
    (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover) (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n)
    (hStd : Std G) (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hlt : Lt3 G n)
    {N : T2N3 G} {u : G} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) (hSec : Ch6Sec5 N u)
    (hC : Ch6Coord N.toT2N2.toT2N1) {r : ℕ} (hrp : r.Prime) (hr2 : r ≠ 2) {f : G}
    (hfo : orderOf f = r) (hf : f ∈ N.F) (hfS : ∀ s ∈ N.S, f * s = s * f) :
    ∃ m : ℕ, ∃ hzC : z ∈ Subgroup.centralizer ({f} : Set G), n = r * m ∧
      Hyp94Loc (↥(Subgroup.centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(Subgroup.centralizer ({f} : Set G)))
        Gs (QuotientGroup.mk (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({f} : Set G)))) .G2 3 m := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have : Finite F₁ := hSet.finite₁
  have : Finite F₂ := hSet.finite₂
  have hodd : Odd r := hrp.odd_of_ne_two hr2
  have : Fact (Nat.Prime r) := ⟨hrp⟩
  have hfr : f ^ r = 1 := by rw [← hfo]; exact pow_orderOf_eq_one f
  have hq : N.q₁ = N.q₂ := hq₁.trans hq₂.symm
  have hcard₁ : Nat.card F₁ = N.q₁ := by rw [hq₁]; exact hSet.card₁
  have hcard₂ : Nat.card F₂ = N.q₂ := by rw [hq₂]; exact hSet.card₂
  have hw₁w₂ : N.w₁ * N.w₂ = N.w₂ * N.w₁ :=
    hSet.comm N.w₁ (hK₁ ▸ hLoc.w₁_mem) N.w₂ (hK₂ ▸ hLoc.w₂_mem)
  obtain ⟨φ₁, σ₁, hφ₁, hrange₁, hneg₁, -, -, -, hHK₁, hσ₁⟩ := coord_fieldAut hSec hC hcard₁ hf hfS
  obtain ⟨φ₂, σ₂, hφ₂, hrange₂, hneg₂, -, -, -, hHK₂, hσ₂⟩ :=
    coord_fieldAut₂ hSec hq hC hcard₂ hf hfS
  have hσ₁r : σ₁ ^ r = 1 := pow_eq_one_of_pow_eq_one φ₁ hφ₁ f σ₁ hσ₁ hfr
  have hσ₂r : σ₂ ^ r = 1 := pow_eq_one_of_pow_eq_one φ₂ hφ₂ f σ₂ hσ₂ hfr
  have h₁₂ : σ₁ = 1 → σ₂ = 1 := fun h1 =>
    sigma₂_eq_one_of_sigma₁_eq_one_lt hL hL3 hIVK hn hStd hSet hRem hlt hz hK₁ hK₂ hq₁ hq₂ hSec hf hodd
      hfr hHK₁ hσ₁ hφ₂ hHK₂ hσ₂ h1
  have h₂₁ : σ₂ = 1 → σ₁ = 1 := fun h2 =>
    sigma₂_eq_one_of_sigma₁_eq_one_lt (N := N.swap) (u := u) hL hL3 hIVK hn hStd (hSet.swap rfl)
      hRem.swap hlt hz hK₂ hK₁ hq₂ hq₁ (hSec.swap hq) hf hodd hfr hHK₂ hσ₂ hφ₁ hHK₁ hσ₁ h2
  have hσ₁ne : σ₁ ≠ 1 := by
    intro h1
    have h2 := h₁₂ h1
    have hodd' : Odd (orderOf f) := by rw [hfo]; exact hodd
    have hc₁ : ∀ x ∈ N.K₁, x * f = f * x := by
      intro x hx
      rw [← hrange₁] at hx
      obtain ⟨M, rfl⟩ := hx
      have := centralizes_of_eq_one φ₁ f σ₁ hσ₁ h1 M
      calc φ₁ M * f = (f * φ₁ M * f⁻¹) * f := by rw [this]
        _ = f * φ₁ M := by group
    have hc₂ : ∀ x ∈ N.K₂, x * f = f * x := by
      intro x hx
      rw [← hrange₂] at hx
      obtain ⟨M, rfl⟩ := hx
      have := centralizes_of_eq_one φ₂ f σ₂ hσ₂ h2 M
      calc φ₂ M * f = (f * φ₂ M * f⁻¹) * f := by rw [this]
        _ = f * φ₂ M := by group
    have hf1 := f_eq_one_of_trivial hSec hf hfS hodd' hc₁ hc₂
    rw [hf1, orderOf_one] at hfo
    exact hrp.one_lt.ne hfo
  have hr₁ : orderOf σ₁ = r := orderOf_eq_prime hσ₁r hσ₁ne
  have hr₂ : orderOf σ₂ = r := orderOf_eq_prime hσ₂r (fun h2 => hσ₁ne (h₂₁ h2))
  obtain ⟨m₁, hm₁c, hm₁⟩ := card_fixF_eq σ₁ Nat.prime_three (show Nat.card F₁ = 3 ^ n from hSet.card₁)
  obtain ⟨m₂, hm₂c, hm₂⟩ := card_fixF_eq σ₂ Nat.prime_three (show Nat.card F₂ = 3 ^ n from hSet.card₂)
  rw [hr₁] at hm₁
  rw [hr₂] at hm₂
  have hrpos : 0 < r := hrp.pos
  obtain rfl : m₂ = m₁ := Nat.eq_of_mul_eq_mul_right hrpos (hm₂.trans hm₁.symm)
  have hm1 : 1 ≤ m₂ := by
    rcases Nat.eq_zero_or_pos m₂ with h | h
    · rw [h, zero_mul] at hm₁; omega
    · exact h
  have hnm : n = r * m₂ := by rw [← hm₁, mul_comm]
  obtain ⟨a', hfa', ha'z, ha'u⟩ :=
    exists_fusion_elt hSec hf hodd hfr hw₁w₂ hφ₁ hr₁ hHK₁ hσ₁ hφ₂ hr₂ hHK₂ hσ₂
  obtain ⟨t', ht'S, g₁, g₂, hGC⟩ := f1_charts hn hSet hRem hz hK₁ hK₂ hq₁ hq₂ hSec hodd hfr hf hfS
    hφ₁ (hrange₁.trans hK₁) (hneg₁.trans hz) hσ₁ hφ₂ (hrange₂.trans hK₂) (hneg₂.trans hz) hσ₂
  have hctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  let S₂ : Sylow 2 G := hLoc.S_pGroup.toSylow hLoc.S_sylow
  have hS₂ : (S₂ : Subgroup G) = N.S := IsPGroup.toSylow_coe _ _
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  obtain ⟨S₀, S', ⟨e⟩⟩ := hSet.S_iso
  obtain ⟨e'⟩ := sylow_equiv S₂ S₀
  obtain ⟨p, fe, -, -, -, hp, hp2, hmodel, -⟩ := hSet.model
  have hH := hyp94Loc_of_gchart (m := m₂) hm1 (show Nat.card (fixF σ₁) = 3 ^ m₂ from hm₁c)
    (show Nat.card (fixF σ₂) = 3 ^ m₂ from hm₂c) hGC S₂ (fun s hs => (hfS s (hS₂ ▸ hs)).symm)
    (by rw [hS₂, ← hz]; exact hLoc.z_mem_S)
    (fun s hs => by rw [← hz]; exact (hLoc.z_cent_S s (hS₂ ▸ hs)).symm)
    (fun x hx hc => hctx.ZS x (hS₂ ▸ hx) (fun s hs => hc s (hS₂.symm ▸ hs)))
    (hS₂ ▸ hLoc.u_mem_S) hu2 hu1 (by rw [← hz]; exact hLoc.u_ne) (by rw [← hz]; exact hLoc.u_comm.symm)
    ⟨S', ⟨e'.trans e⟩⟩ ⟨p, fe, hp, hp2, hmodel⟩
    ⟨a', hfa', by rw [← hz]; exact ha'z, by rw [← hz]; exact ha'u⟩
  obtain ⟨hzC, hH'⟩ := hH
  exact ⟨m₂, hzC, hnm, hH'⟩

end Core

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
