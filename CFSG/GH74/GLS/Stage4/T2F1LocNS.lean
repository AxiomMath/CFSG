module

public import CFSG.GH74.GLS.Stage4.T2P56Core
public import CFSG.GH74.GLS.Stage4.T2TSingEq
public import CFSG.GH74.GLS.Stage4.T6Defs
public import CFSG.GH74.GLS.Stage4.RestX2Q1

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem not_tsing_K₁ (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n) (hStd : Std G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hab : ∀ T : Subgroup G, IsPGroup 3 ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
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
  obtain ⟨R, hRp, -, -, -, -, hXR, -⟩ := hX N.X₂ hX₂K hX₂p hX₂c
  have hRab := hab R hRp
  have hcomm : ⁅R, R⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hRab g₁ hg₁ g₂ hg₂
  rw [hcomm, le_bot_iff] at hXR
  rw [hXR, Subgroup.card_bot] at hX₂c
  omega

theorem not_tsing_K₂ (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n) (hStd : Std G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hab : ∀ T : Subgroup G, IsPGroup 3 ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {N : T2N3 G} {u : G} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) (hSec : Ch6Sec5 N u)
    {y : G} (hyH : y ∈ N.H ⊓ N.K₂) (hyp : (orderOf y).Prime) (hyodd : Odd (orderOf y))
    (hya : N.a * y * N.a⁻¹ = y) : False :=
  not_tsing_K₁ hL hL3 hIVK hn hStd (hSet.swap rfl) hRem.swap hab (N := N.swap) (u := u)
    hz hK₂ hK₁ hq₂ hq₁ (hSec.swap (hq₁.trans hq₂.symm)) hyH hyp hyodd hya

theorem no_fixed_odd_K₂ (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n) (hStd : Std G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hab : ∀ T : Subgroup G, IsPGroup 3 ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
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
  exact not_tsing_K₂ hL hL3 hIVK hn hStd hSet hRem hab hz hK₁ hK₂ hq₁ hq₂ hSec hy'H
    (hy'ord ▸ hrp) (hy'ord ▸ Odd.of_dvd_nat hodd hrd) hy'a

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
